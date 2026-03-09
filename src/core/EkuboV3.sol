// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";
import {FastLogic} from "../utils/FastLogic.sol";
import {Ternary} from "../utils/Ternary.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {Panic} from "../utils/Panic.sol";
import {TooMuchSlippage, ZeroSellAmount} from "./SettlerErrors.sol";
import {CreditDebt, Encoder, NotePtr, NotesLib, State, Decoder, CompactTake} from "./FlashAccountingCommon.sol";

type Config is bytes32;

type SqrtRatio is uint96;

// Each pool has its own state associated with this key
struct PoolKey {
    address token0;
    address token1;
    Config config;
}

interface IEkuboCore {
    // The entrypoint for all operations on the core contract
    function lock() external;

    // Swap tokens
    function swap_6269342730() external payable;

    function forward(address to) external;

    function startPayments() external;

    function completePayments() external;

    // Get swapped tokens
    function withdraw() external;
}

IEkuboCore constant CORE = IEkuboCore(0x00000000000014aA86C5d3c41765bb24e11bd701);

/// @notice Interface for the callback executed when an address locks core
interface IEkuboCallbacks {
    /// @notice Called by Core on `msg.sender` when a lock is acquired
    /// @param id The id assigned to the action
    /// @return Any data that you want to be returned from the lock call
    function locked_6416899205(uint256 id) external returns (bytes memory);
}

library UnsafeEkuboCore {
    /// The `amount` as well as both `delta`'s are `int256` for contract size savings.  The
    /// `delta`'s are guaranteed clean by the returndata encoding of `CORE`, but we keep them as
    /// `int256` so as not to duplicate any work. If `amount` overflows a `int128`, we will throw.
    ///
    /// The `skipAhead` argument of the underlying `swap` function is hardcoded to zero.
    function unsafeSwap(IEkuboCore core, PoolKey memory poolKey, int256 amount, bool isToken1, SqrtRatio sqrtRatioLimit)
        internal
        returns (int256 delta0, int256 delta1)
    {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            // Compact params (uint96 sqrtRatioLimit, int128 amount, bool isToken1, uint32 skipAhead)
            // skipAhead is encoded as 31 bits
            // mstore(add(0x80, ptr), 0x00) // skipAhead harcoded to zero
            mstore(add(0x80, ptr), shl(0x1f, isToken1)) // sets skipAhead to zero
            mstore(add(0x7c, ptr), amount)
            mstore(add(0x6c, ptr), sqrtRatioLimit)
            mcopy(add(0x20, ptr), poolKey, 0x60)
            mstore(ptr, 0x00000000) // selector for `swap_6269342730()`

            if iszero(call(gas(), core, 0x00, add(0x1c, ptr), 0x84, 0x00, 0x20)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
            let poolBalanceUpdate := mload(0x00)
            delta1 := signextend(0x0f, poolBalanceUpdate)
            delta0 := sar(0x80, poolBalanceUpdate)
            // let poolState := mload(0x20) // unused
            // Ekubo is well behaved no need to check returndatasize
            // if gt(0x40, returndatasize()) { revert(0x00, 0x00) }
            if or(xor(signextend(0x0f, amount), amount), shr(0x60, sqrtRatioLimit)) {
                revert(0x00, 0x00)
            }
        }
    }

    function unsafeForward(
        IEkuboCore core,
        PoolKey memory poolKey,
        int256 amount,
        bool isToken1,
        SqrtRatio sqrtRatioLimit
    ) internal returns (int256 delta0, int256 delta1) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            /// Compact params (uint96 sqrtRatioLimit, int128 amount, bool isToken1, uint32 skipAhead)
            // skipAhead is encoded as 31 bits
            // mstore(add(0x94, ptr), 0x00) // skipAhead harcoded to zero
            mstore(add(0x94, ptr), shl(0x1f, isToken1)) // sets skipAhead to zero
            mstore(add(0x90, ptr), amount)
            mstore(add(0x80, ptr), sqrtRatioLimit)
            mcopy(add(0x34, ptr), poolKey, 0x60)
            mcopy(add(0x20, ptr), add(0x40, poolKey), 0x14) // copy the `extension` from `poolKey.config` as the `to` argument
            mstore(ptr, 0x101e8952000000000000000000000000) // selector for `forward(address)` with `to`'s padding

            if iszero(call(gas(), core, 0x00, add(0x10, ptr), 0x104, 0x00, 0x20)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
            let poolBalanceUpdate := mload(0x00)
            delta1 := signextend(0x0f, poolBalanceUpdate)
            delta0 := sar(0x80, poolBalanceUpdate)
            // `forward` function returned data depends on the extension implementation
            // supported extensions are supposed to return same data as `swap_6269342730`
            // which is (bytes32 balanceUpdate, bytes32 stateAfter), 0x40 bytes long
            if or(or(gt(0x40, returndatasize()), xor(signextend(0x0f, amount), amount)), shr(0x60, sqrtRatioLimit)) {
                revert(0x00, 0x00)
            }
        }
    }

    function unsafeStartPayments(IEkuboCore core, IERC20 sellToken) internal {
        assembly ("memory-safe") {
            mstore(0x14, sellToken)
            mstore(0x00, 0xf9b6a796000000000000000000000000) // selector for `startPayments()` with `sellToken`'s padding
            if iszero(call(gas(), core, 0x00, 0x10, 0x24, 0x00, 0x00)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
            // Ekubo is well behaved no need to check returndatasize
            // if gt(0x20, returndatasize()) { revert(0x00, 0x00) }
            // Ekubo returns its own balance of the token
            // but the value is unused
        }
    }

    function unsafeCompletePayments(IEkuboCore core, IERC20 sellToken) internal returns (uint256 payment) {
        assembly ("memory-safe") {
            mstore(0x14, sellToken)
            mstore(0x00, 0x12e103f1000000000000000000000000) // selector for `completePayments()` with `sellToken`'s padding
            if iszero(call(gas(), core, 0x00, 0x10, 0x24, 0x00, 0x10)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
            // Ekubo is well behaved no need to check returndatasize
            // if gt(0x10, returndatasize()) { revert(0x00, 0x00) }
            payment := shr(0x80, mload(0x00))
        }
    }
}

abstract contract EkuboV3 is SettlerAbstract {
    using UnsafeMath for uint256;
    using UnsafeMath for int256;
    using CreditDebt for int256;
    using FastLogic for bool;
    using Ternary for bool;
    using SafeTransferLib for IERC20;
    using NotesLib for NotesLib.Note[];
    using UnsafeEkuboCore for IEkuboCore;

    constructor() {
        assert(BASIS == Encoder.BASIS);
        assert(BASIS == Decoder.BASIS);
        assert(address(ETH_ADDRESS) == NotesLib.ETH_ADDRESS);
    }

    //// How to generate `fills` for Ekubo
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
    //// Take care to note that while Ekubo represents the native asset of the chain as
    //// the address of all zeroes, Settler represents this as the address of all `e`s. You must use
    //// Settler's representation. The conversion is performed by Settler before making calls to Ekubo
    ////
    //// Now that you have a list of fills, encode each fill as follows.
    //// First encode the `bps` for the fill as 2 bytes. Remember that this `bps` is relative to the
    //// running balance at the moment that the fill is settled. If the uppermost bit of `bps` is
    //// set, then the swap is treated as a swap through an extension that requires forwarding. Only
    //// the lower 15 bits of `bps` are used for the amount calculation.
    //// Second, encode the price caps sqrtRatio as 12 bytes.
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
    //// Fourth, encode the config of the pool as 32 bytes. Should be done as described in Ekubo implementation
    //// https://github.com/EkuboProtocol/evm-contracts/blob/81c2c2642afe321e7f5d7de70f8b3be18f6f80b3/src/types/poolConfig.sol#L6-#L12
    ////
    //// Repeat the process for each fill and concatenate the results without padding.

    function sellToEkuboV3(
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
            uint32(IEkuboCore.lock.selector),
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
            address(CORE), data, uint32(IEkuboCallbacks.locked_6416899205.selector), _ekuboLockCallbackV3
        );
        // buyAmount = abi.decode(abi.decode(encodedBuyAmount, (bytes)), (uint256));
        assembly ("memory-safe") {
            // We can skip all the checks performed by `abi.decode` because we know that this is the
            // verbatim result from `locked_6416899205` and that `locked_6416899205` encoded the buy amount
            // correctly.
            buyAmount := mload(add(0x60, encodedBuyAmount))
        }
    }

    function sellToEkuboV3VIP(
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
            uint32(IEkuboCore.lock.selector),
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
            address(CORE), data, uint32(IEkuboCallbacks.locked_6416899205.selector), _ekuboLockCallbackV3
        );
        // buyAmount = abi.decode(abi.decode(encodedBuyAmount, (bytes)), (uint256));
        assembly ("memory-safe") {
            // We can skip all the checks performed by `abi.decode` because we know that this is the
            // verbatim result from `locked_6416899205` and that `locked_6416899205` encoded the buy amount
            // correctly.
            buyAmount := mload(add(0x60, encodedBuyAmount))
        }
    }

    function _ekuboLockCallbackV3(bytes calldata data) private returns (bytes memory) {
        // We know that our calldata is well-formed. Therefore, the first slot is ekubo lock id,
        // second slot is 0x20 and third is the length of the strict ABIEncoded payload
        assembly ("memory-safe") {
            data.length := calldataload(add(0x40, data.offset))
            data.offset := add(0x60, data.offset)
        }
        return locked_6416899205(data);
    }

    function _ekuboPayV3(
        IERC20 sellToken,
        address payer,
        uint256 sellAmount,
        ISignatureTransfer.PermitTransferFrom calldata permit,
        bool isForwarded,
        bytes calldata sig
    ) private returns (uint256 payment) {
        if (sellToken == ETH_ADDRESS) {
            SafeTransferLib.safeTransferETH(payable(msg.sender), sellAmount);
            return sellAmount;
        } else {
            // Initiate the payment
            IEkuboCore(msg.sender).unsafeStartPayments(sellToken);

            if (payer == address(this)) {
                sellToken.safeTransfer(msg.sender, sellAmount);
            } else {
                ISignatureTransfer.SignatureTransferDetails memory transferDetails =
                    ISignatureTransfer.SignatureTransferDetails({to: msg.sender, requestedAmount: sellAmount});
                _transferFrom(permit, transferDetails, sig, isForwarded);
            }

            payment = IEkuboCore(msg.sender).unsafeCompletePayments(sellToken);
        }
    }

    // the mandatory fields are
    // 2 - sell bps
    // 12 - sqrtRatio
    // 1 - pool key tokens case
    // 32 - config (20 extension, 8 fee, 4 tickSpacing)
    uint256 private constant _HOP_DATA_LENGTH = 47;

    function locked_6416899205(bytes calldata data) private returns (bytes memory) {
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
                globalSell.setAmount(
                    _ekuboPayV3(globalSell.token(), payer, globalSell.amount(), permit, isForwarded, sig)
                );
            }
            if (globalSell.amount() >> 127 != 0) {
                Panic.panic(Panic.ARITHMETIC_OVERFLOW);
            }
            state.setGlobalSellAmount(globalSell.amount());
        }
        state.checkZeroSellAmount();
        data = newData;

        PoolKey memory poolKey;

        while (data.length >= _HOP_DATA_LENGTH) {
            uint256 bps;
            SqrtRatio sqrtRatio;
            assembly ("memory-safe") {
                bps := shr(0xf0, calldataload(data.offset))
                data.offset := add(0x02, data.offset)

                sqrtRatio := shr(0xa0, calldataload(data.offset))
                data.offset := add(0x0c, data.offset)

                data.length := sub(data.length, 0x0e)
                // we don't check for array out-of-bounds here; we will check it later in `Decoder.overflowCheck`
            }

            data = Decoder.updateState(state, notes, data);
            // It's not possible for `state.sell.amount` to even *approach* overflowing an `int256`,
            // given that deltas are `int128`. If it overflows an `int128`, `unsafeSwap` will throw.
            int256 amountSpecified;
            unchecked {
                amountSpecified = int256((state.sell().amount() * (bps & 0x7fff)).unsafeDiv(BASIS));
            }

            bool isToken1; // opposite of regular zeroForOne
            {
                (IERC20 sellToken, IERC20 buyToken) = (state.sell().token(), state.buy().token());
                assembly ("memory-safe") {
                    let sellTokenShifted := shl(0x60, sellToken)
                    let buyTokenShifted := shl(0x60, buyToken)
                    isToken1 := or(
                        eq(0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee000000000000000000000000, buyTokenShifted),
                        and(
                            iszero(
                                eq(0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee000000000000000000000000, sellTokenShifted)
                            ),
                            lt(buyTokenShifted, sellTokenShifted)
                        )
                    )
                }
                (poolKey.token0, poolKey.token1) = isToken1.maybeSwap(address(sellToken), address(buyToken));
                assembly ("memory-safe") {
                    let token0 := mload(poolKey)
                    // set poolKey to address(0) if it is the native token
                    mstore(poolKey, mul(token0, iszero(eq(0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, token0))))
                }
                // poolKey.token0 is not represented according to ERC-7528 to match the format expected by Ekubo
            }

            {
                bytes32 config;
                assembly ("memory-safe") {
                    config := calldataload(data.offset)
                    data.offset := add(0x20, data.offset)
                    data.length := sub(data.length, 0x20)
                    // we don't check for array out-of-bounds here; we will check it later in `Decoder.overflowCheck`
                }
                poolKey.config = Config.wrap(config);
            }

            Decoder.overflowCheck(data);

            {
                int256 delta0;
                int256 delta1;
                if (bps & 0x8000 == 0) {
                    (delta0, delta1) = IEkuboCore(msg.sender).unsafeSwap(poolKey, amountSpecified, isToken1, sqrtRatio);
                } else {
                    (delta0, delta1) =
                        IEkuboCore(msg.sender).unsafeForward(poolKey, amountSpecified, isToken1, sqrtRatio);
                }

                // Ekubo's sign convention here is backwards compared to UniV4/BalV3/PancakeInfinity
                // `settledSellAmount` is positive, `settledBuyAmount` is negative. So the use of
                // `asCredit` and `asDebt` below is misleading as they are actually debt and credit,
                // respectively, in this context.
                (int256 settledSellAmount, int256 settledBuyAmount) = isToken1.maybeSwap(delta0, delta1);

                // We have to check for underflow in the sell amount (could create more debt than
                // we're able to pay)
                unchecked {
                    NotePtr sell = state.sell();
                    uint256 sellAmountActual = settledSellAmount.asCredit(sell);
                    uint256 sellCreditBefore = sell.amount();
                    sell.setAmount(sellCreditBefore - sellAmountActual);
                    if ((sellAmountActual > uint256(amountSpecified)).or(sellAmountActual > sellCreditBefore)) {
                        Panic.panic(Panic.ARITHMETIC_OVERFLOW);
                    }
                }

                // We *DON'T* have to check for overflow in the buy amount because adding an
                // `int128` to a `uint256`, even repeatedly cannot practically overflow.
                unchecked {
                    NotePtr buy = state.buy();
                    buy.setAmount(buy.amount() + settledBuyAmount.asDebt(buy));
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
                CompactTake.take(state, notes, uint32(IEkuboCore.withdraw.selector), recipient, minBuyAmount);
            if (feeOnTransfer) {
                // We've already transferred the sell token to the vault and
                // `settle`'d. `globalSellAmount` is the verbatim credit in that token stored by the
                // vault. We only need to handle the case of incomplete filling.
                if (globalSellAmount != 0) {
                    CompactTake._callSelector(
                        uint32(IEkuboCore.withdraw.selector),
                        globalSellToken,
                        (payer == address(this)) ? address(this) : _msgSender(),
                        globalSellAmount
                    );
                }
            } else {
                // While `notes` records a credit value, the vault actually records a debt for the
                // global sell token. We recover the exact amount of that debt and then pay it.
                // `globalSellAmount` is _usually_ zero, but if it isn't it represents a partial
                // fill. This subtraction recovers the actual debt recorded in the vault.
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
                _ekuboPayV3(globalSellToken, payer, debt, permit, isForwarded, sig);
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
}
