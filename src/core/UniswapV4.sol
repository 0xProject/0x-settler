// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";

import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {Ternary} from "../utils/Ternary.sol";

import {ZeroSellAmount} from "./SettlerErrors.sol";

import {BalanceDelta, IHooks, IPoolManager, UnsafePoolManager, IUnlockCallback} from "./UniswapV4Types.sol";
import {CreditDebt, Encoder, NotePtr, NotesLib, State, Decoder, Take} from "./FlashAccountingCommon.sol";

abstract contract UniswapV4 is SettlerAbstract {
    using SafeTransferLib for IERC20;
    using UnsafeMath for uint256;
    using UnsafeMath for int256;
    using Ternary for bool;
    using CreditDebt for int256;
    using UnsafePoolManager for IPoolManager;
    using NotesLib for NotesLib.Note[];

    constructor() {
        assert(BASIS == Encoder.BASIS);
        assert(BASIS == Decoder.BASIS);
        assert(address(ETH_ADDRESS) == NotesLib.ETH_ADDRESS);
    }

    function _POOL_MANAGER() internal view virtual returns (IPoolManager);

    //// These two functions are the entrypoints to this set of actions. Because UniV4 has a
    //// mandatory callback, and the vast majority of the business logic has to be executed inside
    //// the callback, they're pretty minimal. Both end up inside the last function in this file
    //// `unlockCallback`, which is where most of the business logic lives. Primarily, these
    //// functions are concerned with correctly encoding the argument to
    //// `POOL_MANAGER.unlock(...)`. Pay special attention to the `payer` field, which is what
    //// signals to the callback whether we should be spending a coupon.

    //// How to generate `fills` for UniV4:
    ////
    //// Linearize your DAG of fills by doing a topological sort on the tokens involved. In the
    //// topological sort of tokens, when there is a choice of the next token, break ties by
    //// preferring a token if it is the lexicographically largest token that is bought among fills
    //// with sell token equal to the previous token in the topological sort. Then sort the fills
    //// belonging to each sell token by their buy token. This technique isn't *quite* optimal, but
    //// it's pretty close. The buy token of the final fill is special-cased. It is the token that
    //// will be transferred to `recipient` and have its slippage checked against `amountOutMin`. In
    //// the event that you are encoding a series of fills with more than one output token, ensure
    //// that at least one of the global buy token's fills is positioned appropriately.
    ////
    //// Now that you have a list of fills, encode each fill as follows.
    //// First encode the `bps` for the fill as 2 bytes. Remember that this `bps` is relative to the
    //// running balance at the moment that the fill is settled.
    //// Second, encode the price caps sqrtPriceLimitX96 as 20 bytes.
    //// Third, encode the packing key for that fill as 1 byte. The packing key byte depends on the
    //// tokens involved in the previous fill. The packing key for the first fill must be 1;
    //// i.e. encode only the buy token for the first fill.
    ////   0 -> sell and buy tokens remain unchanged from the previous fill (pure multiplex)
    ////   1 -> sell token remains unchanged from the previous fill, buy token is encoded (diamond multiplex)
    ////   2 -> sell token becomes the buy token from the previous fill, new buy token is encoded (multihop)
    ////   3 -> both sell and buy token are encoded
    //// Obviously, after encoding the packing key, you encode 0, 1, or 2 tokens (each as 20 bytes),
    //// as appropriate.
    //// The remaining fields of the fill are mandatory.
    //// Fourth, encode the pool fee as 3 bytes, and the pool tick spacing as 3 bytes.
    //// Fifth, encode the hook address as 20 bytes.
    //// Sixth, encode the hook data for the fill. Encode the length of the hook data as 3 bytes,
    //// then append the hook data itself.
    ////
    //// Repeat the process for each fill and concatenate the results without padding.

    function sellToUniswapV4(
        address recipient,
        IERC20 sellToken,
        uint256 bps,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        uint256 amountOutMin
    ) internal returns (uint256 buyAmount) {
        bytes memory data = Encoder.encode(
            uint32(IPoolManager.unlock.selector),
            recipient,
            sellToken,
            bps,
            feeOnTransfer,
            hashMul,
            hashMod,
            fills,
            amountOutMin
        );
        bytes memory encodedBuyAmount = _setOperatorAndCall(
            address(_POOL_MANAGER()), data, uint32(IUnlockCallback.unlockCallback.selector), _uniV4Callback
        );
        // buyAmount = abi.decode(abi.decode(encodedBuyAmount, (bytes)), (uint256));
        assembly ("memory-safe") {
            // We can skip all the checks performed by `abi.decode` because we know that this is the
            // verbatim result from `unlockCallback` and that `unlockCallback` encoded the buy
            // amount correctly.
            buyAmount := mload(add(0x60, encodedBuyAmount))
        }
    }

    function sellToUniswapV4VIP(
        address recipient,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig,
        uint256 amountOutMin
    ) internal returns (uint256 buyAmount) {
        bytes memory data = Encoder.encodeVIP(
            uint32(IPoolManager.unlock.selector),
            recipient,
            feeOnTransfer,
            hashMul,
            hashMod,
            fills,
            permit,
            sig,
            _isForwarded(),
            amountOutMin
        );
        bytes memory encodedBuyAmount = _setOperatorAndCall(
            address(_POOL_MANAGER()), data, uint32(IUnlockCallback.unlockCallback.selector), _uniV4Callback
        );
        // buyAmount = abi.decode(abi.decode(encodedBuyAmount, (bytes)), (uint256));
        assembly ("memory-safe") {
            // We can skip all the checks performed by `abi.decode` because we know that this is the
            // verbatim result from `unlockCallback` and that `unlockCallback` encoded the buy
            // amount correctly.
            buyAmount := mload(add(0x60, encodedBuyAmount))
        }
    }

    function _uniV4Callback(bytes calldata data) private returns (bytes memory) {
        // We know that our calldata is well-formed. Therefore, the first slot is 0x20 and the
        // second slot is the length of the strict ABIEncoded payload
        assembly ("memory-safe") {
            data.length := calldataload(add(0x20, data.offset))
            data.offset := add(0x40, data.offset)
        }
        return unlockCallback(data);
    }

    //// The following functions are the helper functions for `unlockCallback`. They abstract much
    //// of the complexity of tracking which tokens need to be zeroed out at the end of the
    //// callback.
    ////
    //// The two major pieces of state that are maintained through the callback are `Note[] memory
    //// notes` and `State state`
    ////
    //// `notes` keeps track of the list of the tokens that have been touched throughout the
    //// callback that have nonzero credit. At the end of the fills, all tokens with credit will be
    //// swept back to Settler. These are the global buy token (against which slippage is checked)
    //// and any other multiplex-out tokens. Only the global sell token is allowed to have debt, but
    //// it is accounted slightly differently from the other tokens. The function `_take` is
    //// responsible for iterating over the list of tokens and withdrawing any credit to the
    //// appropriate recipient.
    ////
    //// `state` exists to reduce stack pressure and to simplify/gas-optimize the process of
    //// swapping. By keeping track of the sell and buy token on each hop, we're able to compress
    //// the representation of the fills required to satisfy the swap. Most often in a swap, the
    //// tokens in adjacent fills are somewhat in common. By caching, we avoid having them appear
    //// multiple times in the calldata.

    // the mandatory fields are
    // 2 - sell bps
    // 20 - sqrtPriceLimitX96
    // 1 - pool key tokens case
    // 3 - pool fee
    // 3 - pool tick spacing
    // 20 - pool hooks
    // 3 - hook data length
    uint256 private constant _HOP_DATA_LENGTH = 52;

    /// Decode a `PoolKey` from its packed representation in `bytes` and the token information in
    /// `state`. Returns the `zeroForOne` flag and the suffix of the bytes that are not consumed in
    /// the decoding process.
    function _setPoolKey(IPoolManager.PoolKey memory key, State state, bytes calldata data)
        private
        pure
        returns (bool, bytes calldata)
    {
        (IERC20 sellToken, IERC20 buyToken) = (state.sell().token(), state.buy().token());
        bool zeroForOne;
        assembly ("memory-safe") {
            let sellTokenShifted := shl(0x60, sellToken)
            let buyTokenShifted := shl(0x60, buyToken)
            zeroForOne :=
                or(
                    eq(0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee000000000000000000000000, sellTokenShifted),
                    and(
                        iszero(eq(0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee000000000000000000000000, buyTokenShifted)),
                        lt(sellTokenShifted, buyTokenShifted)
                    )
                )
        }
        (key.token0, key.token1) = zeroForOne.maybeSwap(buyToken, sellToken);

        uint256 packed;
        assembly ("memory-safe") {
            packed := shr(0x30, calldataload(data.offset))

            data.offset := add(0x1a, data.offset)
            data.length := sub(data.length, 0x1a)
            // we don't check for array out-of-bounds here; we will check it later in `Decoder.overflowCheck`
        }

        key.fee = uint24(packed >> 184);
        key.tickSpacing = int24(uint24(packed >> 160));
        key.hooks = IHooks.wrap(address(uint160(packed)));

        return (zeroForOne, data);
    }

    function _pay(
        IERC20 sellToken,
        address payer,
        uint256 sellAmount,
        ISignatureTransfer.PermitTransferFrom calldata permit,
        bool isForwarded,
        bytes calldata sig
    ) private returns (uint256) {
        IPoolManager(msg.sender).unsafeSync(sellToken);
        if (payer == address(this)) {
            sellToken.safeTransfer(msg.sender, sellAmount);
        } else {
            // assert(payer == address(0));
            ISignatureTransfer.SignatureTransferDetails memory transferDetails =
                ISignatureTransfer.SignatureTransferDetails({to: msg.sender, requestedAmount: sellAmount});
            _transferFrom(permit, transferDetails, sig, isForwarded);
        }
        return IPoolManager(msg.sender).unsafeSettle();
    }

    function unlockCallback(bytes calldata data) private returns (bytes memory) {
        address recipient;
        uint256 minBuyAmount;
        uint256 hashMul;
        uint256 hashMod;
        bool feeOnTransfer;
        address payer;
        (data, recipient, minBuyAmount, hashMul, hashMod, feeOnTransfer, payer) = Decoder.decodeHeader(data);

        // Set up `state` and `notes`. The other values are ancillary and might be used when we need
        // to settle global sell token debt at the end of swapping.
        (
            bytes calldata newData,
            State state,
            NotesLib.Note[] memory notes,
            ISignatureTransfer.PermitTransferFrom calldata permit,
            bool isForwarded,
            bytes calldata sig
        ) = Decoder.initialize(data, hashMul, hashMod, payer);
        {
            NotePtr globalSell = state.globalSell();
            if (payer != address(this)) {
                globalSell.setAmount(_permitToSellAmountCalldata(permit));
            }
            if (feeOnTransfer) {
                globalSell.setAmount(_pay(globalSell.token(), payer, globalSell.amount(), permit, isForwarded, sig));
            }
            state.setGlobalSellAmount(globalSell.amount());
        }
        state.checkZeroSellAmount();
        data = newData;

        // Now that we've unpacked and decoded the header, we can begin decoding the array of swaps
        // and executing them.
        IPoolManager.PoolKey memory key;
        IPoolManager.SwapParams memory params;
        while (data.length >= _HOP_DATA_LENGTH) {
            uint256 bps;
            {
                uint160 sqrtPriceLimitX96;
                assembly ("memory-safe") {
                    bps := shr(0xf0, calldataload(data.offset))
                    data.offset := add(0x02, data.offset)

                    sqrtPriceLimitX96 := shr(0x60, calldataload(data.offset))
                    data.offset := add(0x14, data.offset)

                    data.length := sub(data.length, 0x16)
                    // we don't check for array out-of-bounds here; we will check it later in `Decoder.overflowCheck`
                }
                params.sqrtPriceLimitX96 = sqrtPriceLimitX96;
            }

            data = Decoder.updateState(state, notes, data);
            bool zeroForOne;
            (zeroForOne, data) = _setPoolKey(key, state, data);
            bytes calldata hookData;
            (data, hookData) = Decoder.decodeBytes(data);
            Decoder.overflowCheck(data);

            params.zeroForOne = zeroForOne;
            unchecked {
                params.amountSpecified = int256((state.sell().amount() * bps).unsafeDiv(BASIS)).unsafeNeg();
            }

            BalanceDelta delta = IPoolManager(msg.sender).unsafeSwap(key, params, hookData);
            {
                (int256 settledSellAmount, int256 settledBuyAmount) =
                    zeroForOne.maybeSwap(delta.amount1(), delta.amount0());
                // Some insane hooks may increase the sell amount; obviously this may result in
                // unavoidable reverts in some cases. But we still need to make sure that we don't
                // underflow to avoid wildly unexpected behavior. The pool manager enforces that the
                // settled sell amount cannot be positive
                NotePtr sell = state.sell();
                sell.setAmount(sell.amount() - uint256(settledSellAmount.unsafeNeg()));
                // If `state.buy.amount()` overflows an `int128`, we'll get a revert inside the pool
                // manager later. We cannot overflow a `uint256`.
                unchecked {
                    NotePtr buy = state.buy();
                    buy.setAmount(buy.amount() + settledBuyAmount.asCredit(buy));
                }
            }
        }

        // `data` has been consumed. All that remains is to settle out the net result of all the
        // swaps. Any credit in any token other than `state.buy.token` will be swept to
        // Settler. `state.buy.token` will be sent to `recipient`.
        {
            NotePtr globalSell = state.globalSell();
            (IERC20 globalSellToken, uint256 globalSellAmount) = (globalSell.token(), globalSell.amount());
            uint256 globalBuyAmount =
                Take.take(state, notes, uint32(IPoolManager.take.selector), recipient, minBuyAmount);
            if (feeOnTransfer) {
                // We've already transferred the sell token to the pool manager and
                // `settle`'d. `globalSellAmount` is the verbatim credit in that token stored by the
                // pool manager. We only need to handle the case of incomplete filling.
                if (globalSellAmount != 0) {
                    Take._callSelector(
                        uint32(IPoolManager.take.selector),
                        globalSellToken,
                        payer == address(this) ? address(this) : _msgSender(),
                        globalSellAmount
                    );
                }
            } else {
                // While `notes` records a credit value, the pool manager actually records a debt
                // for the global sell token. We recover the exact amount of that debt and then pay
                // it.
                // `globalSellAmount` is _usually_ zero, but if it isn't it represents a partial
                // fill. This subtraction recovers the actual debt recorded in the pool manager.
                uint256 debt;
                unchecked {
                    debt = state.globalSellAmount() - globalSellAmount;
                }
                if (debt == 0) {
                    assembly ("memory-safe") {
                        mstore(0x14, globalSellToken)
                        mstore(0x00, 0xfb772a88000000000000000000000000) // selector for `ZeroSellAmount(address)` with `globalSellToken`'s padding
                        revert(0x10, 0x24)
                    }
                }
                if (globalSellToken == ETH_ADDRESS) {
                    IPoolManager(msg.sender).unsafeSync(IERC20(address(0)));
                    IPoolManager(msg.sender).unsafeSettle(debt);
                } else {
                    _pay(globalSellToken, payer, debt, permit, isForwarded, sig);
                }
            }

            // return abi.encode(globalBuyAmount);
            bytes memory returndata;
            assembly ("memory-safe") {
                returndata := mload(0x40)
                mstore(returndata, 0x60)
                mstore(add(0x20, returndata), 0x20)
                mstore(add(0x40, returndata), 0x20)
                mstore(add(0x60, returndata), globalBuyAmount)
                mstore(0x40, add(0x80, returndata))
            }
            return returndata;
        }
    }

    address public constant rebateClaimer = 0x352650Ac2653508d946c4912B07895B22edd84CD; // an EOA owned by Scott
}
