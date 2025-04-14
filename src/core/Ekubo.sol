// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";
import {Ternary} from "../utils/Ternary.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {FullMath} from "../vendor/FullMath.sol";
import {Panic} from "../utils/Panic.sol";
import {TooMuchSlippage, ZeroSellAmount} from "./SettlerErrors.sol";
import {CreditDebt, Encoder, NotesLib, StateLib, Decoder, Take} from "./FlashAccountingCommon.sol";

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
    function swap_611415377(
        PoolKey memory poolKey,
        int128 amount,
        bool isToken1,
        SqrtRatio sqrtRatioLimit,
        uint256 skipAhead
    ) external payable returns (int128 delta0, int128 delta1);

    // Pay for swapped tokens
    function pay(address token) external returns (uint128 payment);

    // Get swapped tokens
    function withdraw(address token, address recipient, uint128 amount) external;
}

IEkuboCore constant CORE = IEkuboCore(0xe0e0e08A6A4b9Dc7bD67BCB7aadE5cF48157d444);

/// @notice Interface for the callback executed when an address locks core
interface IEkuboCallbacks {
    /// @notice Called by Core on `msg.sender` when a lock is acquired
    /// @param id The id assigned to the action
    /// @return Any data that you want to be returned from the lock call
    function locked(uint256 id) external returns (bytes memory);

    /// @notice Called by Core on `msg.sender` to collect assets
    /// @param id The id assigned to the action
    /// @param token The token to pay on
    function payCallback(uint256 id, address token) external;
}

library UnsafeEkuboCore {
    function unsafeSwap(
        IEkuboCore core,
        PoolKey memory poolKey,
        int256 amount,
        bool isToken1,
        SqrtRatio sqrtRatioLimit,
        uint256 skipAhead
    ) internal returns (int128 delta0, int128 delta1) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            mstore(ptr, 0x00000000) // selector for `swap_611415377((address,address,bytes32),int128,bool,uint96,uint256)`
            let poolKeyPtr := add(0x20, ptr)
            mcopy(poolKeyPtr, poolKey, 0x60)
            let token0 := mload(poolKeyPtr)
            mstore(poolKeyPtr, mul(iszero(eq(0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, token0)), token0))
            // ABI decoding in Ekubo will check if amount fits in int128
            mstore(add(0x80, ptr), amount)
            mstore(add(0xa0, ptr), isToken1)
            mstore(add(0xc0, ptr), and(0xffffffffffffffffffffffff, sqrtRatioLimit))
            mstore(add(0xe0, ptr), skipAhead)

            if iszero(call(gas(), core, 0x00, add(0x1c, ptr), 0xe4, 0x00, 0x40)) {
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            // Ekubo CORE returns data properly no need to mask
            delta0 := mload(0x00)
            delta1 := mload(0x20)
        }
    }
}

abstract contract Ekubo is SettlerAbstract {
    using UnsafeMath for uint256;
    using FullMath for uint256;
    using UnsafeMath for int256;
    using CreditDebt for int256;
    using Ternary for bool;
    using SafeTransferLib for IERC20;
    using NotesLib for NotesLib.Note;
    using NotesLib for NotesLib.Note[];
    using StateLib for StateLib.State;
    using UnsafeEkuboCore for IEkuboCore;

    constructor() {
        assert(BASIS == Encoder.BASIS);
        assert(BASIS == Decoder.BASIS);
        assert(ETH_ADDRESS == Decoder.ETH_ADDRESS);
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
    //// Take care to note that while Ekube represents the native asset of the chain as
    //// the address of all zeroes, Settler represents this as the address of all `e`s. You must use
    //// Settler's representation. The conversion is performed by Settler before making calls to Ekubo
    ////
    //// Now that you have a list of fills, encode each fill as follows.
    //// First encode the `bps` for the fill as 2 bytes. Remember that this `bps` is relative to the
    //// running balance at the moment that the fill is settled.
    //// Second, encode the packing key for that fill as 1 byte. The packing key byte depends on the
    //// tokens involved in the previous fill. The packing key for the first fill must be 1;
    //// i.e. encode only the buy token for the first fill.
    ////   0 -> sell and buy tokens remain unchanged from the previous fill (pure multiplex)
    ////   1 -> sell token remains unchanged from the previous fill, buy token is encoded (diamond multiplex)
    ////   2 -> sell token becomes the buy token from the previous fill, new buy token is encoded (multihop)
    ////   3 -> both sell and buy token are encoded
    //// Obviously, after encoding the packing key, you encode 0, 1, or 2 tokens (each as 20 bytes),
    //// as appropriate.
    //// The remaining fields of the fill are mandatory.
    //// Third, encode the config of the pool as 32 bytes. It contains pool parameters which are
    //// 20 bytes extension address, 8 bytes fee, and 4 bytes tickSpacing.
    //// Fourth, encode the skipAhead to use in the swap as 32 bytes. It specifies how many steps to
    //// do when looking for the next/prev initialized tick in the pool.
    ////
    //// Repeat the process for each fill and concatenate the results without padding.

    function sellToEkubo(
        address recipient,
        IERC20 sellToken,
        uint256 bps,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        uint256 amountOutMin
    ) internal returns (uint256 buyAmount) {
        if (bps > BASIS) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
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
        bytes memory encodedBuyAmount =
            _setOperatorAndCall(address(CORE), data, uint32(IEkuboCallbacks.locked.selector), _ekuboLockCallback);
        // buyAmount = abi.decode(abi.decode(encodedBuyAmount, (bytes)), (uint256));
        assembly ("memory-safe") {
            // We can skip all the checks performed by `abi.decode` because we know that this is the
            // verbatim result from `locked` and that `locked` encoded the buy amount
            // correctly.
            buyAmount := mload(add(0x60, encodedBuyAmount))
        }
    }

    function sellToEkuboVIP(
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
        bytes memory encodedBuyAmount =
            _setOperatorAndCall(address(CORE), data, uint32(IEkuboCallbacks.locked.selector), _ekuboLockCallback);
        // buyAmount = abi.decode(abi.decode(encodedBuyAmount, (bytes)), (uint256));
        assembly ("memory-safe") {
            // We can skip all the checks performed by `abi.decode` because we know that this is the
            // verbatim result from `locked` and that `locked` encoded the buy amount
            // correctly.
            buyAmount := mload(add(0x60, encodedBuyAmount))
        }
    }

    function _ekuboLockCallback(bytes calldata data) private returns (bytes memory) {
        // We know that our calldata is well-formed. Therefore, the first slot is ekubo lock id,
        // second slot is 0x20 and third is the length of the strict ABIEncoded payload
        assembly ("memory-safe") {
            data.length := calldataload(add(0x40, data.offset))
            data.offset := add(0x60, data.offset)
        }
        return locked(data);
    }

    function _ekuboPay(
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
            // Encode the call plus the extra data that is going to be needed in the callback
            bytes memory data;
            assembly ("memory-safe") {
                data := mload(0x40)

                mstore(add(0x24, data), sellToken)
                mstore(add(0x10, data), 0x0c11dedd000000000000000000000000) // selector for pay(address) with padding for token

                mstore(add(0x44, data), sellAmount)
                let size := 0x44

                // if permit is needed add it to data
                if iszero(eq(payer, address())) {
                    // let's skip token and sell amount and reuse the values already in data
                    calldatacopy(add(0x64, data), add(0x40, permit), 0x40)
                    mstore(add(0xa4, data), isForwarded)
                    mstore(add(0xc4, data), sig.length)
                    calldatacopy(add(0xe4, data), sig.offset, sig.length)
                    size := add(size, add(0x80, sig.length))
                }

                // update data length
                mstore(data, size)

                // update free memory pointer
                mstore(0x40, add(data, add(0x20, size)))
            }
            bytes memory encodedPayedAmount =
                _setOperatorAndCall(msg.sender, data, uint32(IEkuboCallbacks.payCallback.selector), payCallback);
            assembly ("memory-safe") {
                // We can skip all the checks performed by `abi.decode` because we know that this is the
                // verbatim result from `payCallback` and that `payCallback` encoded the payment
                // correctly.
                payment := mload(add(0x60, encodedPayedAmount))
            }
        }
    }

    // the mandatory fields are
    // 2 - sell bps
    // 1 - pool key tokens case
    // 32 - config (20 extension, 8 fee, 4 tickSpacing)
    // 32 - skipAhead
    uint256 private constant _HOP_DATA_LENGTH = 67;

    uint256 private constant _ADDRESS_MASK = 0x00ffffffffffffffffffffffffffffffffffffffff;

    function locked(bytes calldata data) private returns (bytes memory) {
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
            StateLib.State memory state,
            NotesLib.Note[] memory notes,
            ISignatureTransfer.PermitTransferFrom calldata permit,
            bool isForwarded,
            bytes calldata sig
        ) = Decoder.initialize(data, hashMul, hashMod, payer);
        if (state.sell.amount >> 127 != 0) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        if (payer != address(this)) {
            state.globalSell.amount = _permitToSellAmountCalldata(permit);
        }
        if (feeOnTransfer) {
            state.globalSell.amount =
                _ekuboPay(state.globalSell.token, payer, state.globalSell.amount, permit, isForwarded, sig);
        }
        state.checkZeroSellAmount();
        state.globalSellAmount = state.globalSell.amount;
        data = newData;

        PoolKey memory poolKey;

        while (data.length >= _HOP_DATA_LENGTH) {
            uint16 bps;
            assembly ("memory-safe") {
                bps := shr(0xf0, calldataload(data.offset))

                data.offset := add(0x02, data.offset)
                data.length := sub(data.length, 0x02)
                // we don't check for array out-of-bounds here; we will check it later in `Decoder.overflowCheck`
            }

            data = Decoder.updateState(state, notes, data);
            // It's not possible for `state.sell.amount` to even *approach* overflowing an `int256`,
            // given that deltas are `int128`. If it overflows an `int128`, the ABI decoding in
            // `CORE` will throw.
            int256 amountSpecified;
            unchecked {
                amountSpecified = int256((state.sell.amount * bps).unsafeDiv(BASIS));
            }

            bool isToken1;
            {
                (IERC20 sellToken, IERC20 buyToken) = (state.sell.token, state.buy.token);
                assembly ("memory-safe") {
                    sellToken := and(_ADDRESS_MASK, sellToken)
                    buyToken := and(_ADDRESS_MASK, buyToken)
                    isToken1 :=
                        or(
                            eq(buyToken, 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee),
                            and(iszero(eq(sellToken, 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee)), lt(buyToken, sellToken))
                        )
                }
                (poolKey.token0, poolKey.token1) = isToken1.maybeSwap(address(sellToken), address(buyToken));
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

            uint256 skipAhead;
            assembly ("memory-safe") {
                skipAhead := calldataload(data.offset)
                data.offset := add(0x20, data.offset)
                data.length := sub(data.length, 0x20)
                // we don't check for array out-of-bounds here; we will check it later in `Decoder.overflowCheck`
            }

            Decoder.overflowCheck(data);

            {
                SqrtRatio sqrtRatio = SqrtRatio.wrap(
                    uint96(isToken1.ternary(uint256(79227682466138141934206691491), uint256(4611797791050542631)))
                );
                (int256 delta0, int256 delta1) = IEkuboCore(msg.sender).unsafeSwap(
                    poolKey, int128(amountSpecified), isToken1, sqrtRatio, skipAhead
                );
                // Ekubo's sign convention here is backwards compared to UniV4/BalV3/PancakeInfinity
                // `settledSellAmount` is positive, `settledBuyAmount` is negative. So the use of
                // `asCredit` and `asDebt` below is misleading as they are actually debt and credit,
                // respectively, in this context.
                (int256 settledSellAmount, int256 settledBuyAmount) = isToken1.maybeSwap(delta0, delta1);

                // We have to check for underflow in the sell amount (could create more debt than
                // we're able to pay)
                state.sell.amount -= settledSellAmount.asCredit(state.sell);

                // We *DON'T* have to check for overflow in the buy amount because adding an
                // `int128` to a `uint256`, even repeatedly cannot practically overflow.
                unchecked {
                    state.buy.amount += settledBuyAmount.asDebt(state.buy);
                }
            }
        }

        // `data` has been consumed. All that remains is to settle out the net result of all the
        // swaps. Any credit in any token other than `state.buy.token` will be swept to
        // Settler. `state.buy.token` will be sent to `recipient`.
        {
            (IERC20 globalSellToken, uint256 globalSellAmount) = (state.globalSell.token, state.globalSell.amount);
            uint256 globalBuyAmount =
                Take.take(state, notes, uint32(IEkuboCore.withdraw.selector), recipient, minBuyAmount);
            if (feeOnTransfer) {
                // We've already transferred the sell token to the vault and
                // `settle`'d. `globalSellAmount` is the verbatim credit in that token stored by the
                // vault. We only need to handle the case of incomplete filling.
                if (globalSellAmount != 0) {
                    Take._callSelector(
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
                    debt = state.globalSellAmount - globalSellAmount;
                }
                if (debt == 0) {
                    assembly ("memory-safe") {
                        mstore(0x14, globalSellToken)
                        mstore(0x00, 0xfb772a88000000000000000000000000) // selector for `ZeroSellAmount(address)` with `globalSellToken`'s padding
                        revert(0x10, 0x24)
                    }
                }
                _ekuboPay(globalSellToken, payer, debt, permit, isForwarded, sig);
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

    function payCallback(bytes calldata data) private returns (bytes memory) {
        IERC20 sellToken;
        uint256 sellAmount;

        ISignatureTransfer.PermitTransferFrom calldata permit;
        bool isForwarded;
        bytes calldata sig;

        assembly ("memory-safe") {
            // Initialize permit and sig to appease the compiler
            permit := calldatasize()
            sig.offset := calldatasize()
            sig.length := 0x00

            // first 2 slots in calldata are id and token
            // id is not being used so can be skipped
            sellToken := calldataload(add(0x20, data.offset))
            // then extra data added in _ekuboPay
            sellAmount := calldataload(add(0x40, data.offset))

            if lt(0x60, data.length) {
                // starts at the beginning of sellToken
                permit := add(0x20, data.offset)
                isForwarded := calldataload(add(0xa0, data.offset))

                sig.offset := add(0xc0, data.offset)
                sig.length := calldataload(sig.offset)
                sig.offset := add(0x20, sig.offset)
            }
        }
        if (0x60 < data.length) {
            ISignatureTransfer.SignatureTransferDetails memory transferDetails =
                ISignatureTransfer.SignatureTransferDetails({to: msg.sender, requestedAmount: sellAmount});
            _transferFrom(permit, transferDetails, sig, isForwarded);
        } else {
            sellToken.safeTransfer(msg.sender, sellAmount);
        }
        // return abi.encode(sellAmount);
        bytes memory returndata;
        assembly ("memory-safe") {
            returndata := mload(0x40)
            mstore(returndata, 0x60)
            mstore(add(0x20, returndata), 0x20)
            mstore(add(0x40, returndata), 0x20)
            mstore(add(0x60, returndata), sellAmount)
            mstore(0x40, add(0x80, returndata))
        }
        return returndata;
    }
}
