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
import {CreditDebt, Encoder, NotePtr, NotesLib, State, Decoder, Take} from "./FlashAccountingCommon.sol";

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

    function forward(address to) external;

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
    /// The `amountSpecified` as well as both `delta`'s are `int256` for contract size savings. If
    /// `amountSpecified` is not a clean, signed, 128-bit value, the call will revert inside the ABI
    /// decoding in `CORE`. The `delta`'s are guaranteed clean by the returndata encoding of `CORE`,
    /// but we keep them as `int256` so as not to duplicate any work.
    ///
    /// The `skipAhead` argument of the underlying `swap` function is hardcoded to zero.
    function unsafeSwap(IEkuboCore core, PoolKey memory poolKey, int256 amount, bool isToken1, SqrtRatio sqrtRatioLimit)
        internal
        returns (int256 delta0, int256 delta1)
    {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            mstore(ptr, 0x00000000) // selector for `swap_611415377((address,address,bytes32),int128,bool,uint96,uint256)`
            let poolKeyPtr := add(0x20, ptr)
            mcopy(poolKeyPtr, poolKey, 0x60)
            // ABI decoding in Ekubo will check if amount fits in int128
            mstore(add(0x80, ptr), amount)
            mstore(add(0xa0, ptr), isToken1)
            mstore(add(0xc0, ptr), and(0xffffffffffffffffffffffff, sqrtRatioLimit))
            mstore(add(0xe0, ptr), 0x00)

            if iszero(call(gas(), core, 0x00, add(0x1c, ptr), 0xe4, 0x00, 0x40)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
            // Ekubo CORE returns data properly no need to mask
            delta0 := mload(0x00)
            delta1 := mload(0x20)
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

            mstore(ptr, 0x101e8952000000000000000000000000) // selector for `forward(address)` with `to`'s padding
            mcopy(add(0x20, ptr), add(0x40, poolKey), 0x14) // copy the `extension` from `poolKey.config` as the `to` argument

            let poolKeyPtr := add(0x34, ptr)
            mcopy(poolKeyPtr, poolKey, 0x60)
            mstore(add(0x94, ptr), amount)
            mstore(add(0xb4, ptr), isToken1)
            mstore(add(0xd4, ptr), and(0xffffffffffffffffffffffff, sqrtRatioLimit))
            mstore(add(0xf4, ptr), 0x00)

            if iszero(call(gas(), core, 0x00, add(0x10, ptr), 0x104, 0x00, 0x40)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
            delta0 := mload(0x00)
            delta1 := mload(0x20)
            if or(
                or(gt(0x40, returndatasize()), xor(signextend(0x0f, amount), amount)),
                or(xor(signextend(0x0f, delta0), delta0), xor(signextend(0x0f, delta1), delta1))
            ) { revert(0x00, 0x00) }
        }
    }
}

abstract contract EkuboV2 is SettlerAbstract {
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
    //// Fourth, encode the config of the pool as 32 bytes. It contains pool parameters which are
    //// 20 bytes extension address, 8 bytes fee, and 4 bytes tickSpacing.
    ////
    //// Repeat the process for each fill and concatenate the results without padding.

    function sellToEkuboV2(
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
        bytes memory encodedBuyAmount =
            _setOperatorAndCall(address(CORE), data, uint32(IEkuboCallbacks.locked.selector), _ekuboLockCallbackV2);
        // buyAmount = abi.decode(abi.decode(encodedBuyAmount, (bytes)), (uint256));
        assembly ("memory-safe") {
            // We can skip all the checks performed by `abi.decode` because we know that this is the
            // verbatim result from `locked` and that `locked` encoded the buy amount
            // correctly.
            buyAmount := mload(add(0x60, encodedBuyAmount))
        }
    }

    function sellToEkuboV2VIP(
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
            _setOperatorAndCall(address(CORE), data, uint32(IEkuboCallbacks.locked.selector), _ekuboLockCallbackV2);
        // buyAmount = abi.decode(abi.decode(encodedBuyAmount, (bytes)), (uint256));
        assembly ("memory-safe") {
            // We can skip all the checks performed by `abi.decode` because we know that this is the
            // verbatim result from `locked` and that `locked` encoded the buy amount
            // correctly.
            buyAmount := mload(add(0x60, encodedBuyAmount))
        }
    }

    function _ekuboLockCallbackV2(bytes calldata data) private returns (bytes memory) {
        // We know that our calldata is well-formed. Therefore, the first slot is ekubo lock id,
        // second slot is 0x20 and third is the length of the strict ABIEncoded payload
        assembly ("memory-safe") {
            data.length := calldataload(add(0x40, data.offset))
            data.offset := add(0x60, data.offset)
        }
        return locked(data);
    }

    function _ekuboPayV2(
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
    // 12 - sqrtRatio
    // 1 - pool key tokens case
    // 32 - config (20 extension, 8 fee, 4 tickSpacing)
    uint256 private constant _HOP_DATA_LENGTH = 47;

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
                    _ekuboPayV2(globalSell.token(), payer, globalSell.amount(), permit, isForwarded, sig)
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
            // given that deltas are `int128`. If it overflows an `int128`, the ABI decoding in
            // `CORE` will throw.
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
                    isToken1 :=
                        or(
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
                    debt = state.globalSellAmount() - globalSellAmount;
                }
                if (debt == 0) {
                    assembly ("memory-safe") {
                        mstore(0x14, globalSellToken)
                        mstore(0x00, 0xfb772a88000000000000000000000000) // selector for `ZeroSellAmount(address)` with `globalSellToken`'s padding
                        revert(0x10, 0x24)
                    }
                }
                _ekuboPayV2(globalSellToken, payer, debt, permit, isForwarded, sig);
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

    function payCallback(bytes calldata data) private returns (bytes memory returndata) {
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
            // then extra data added in _ekuboPayV2
            sellAmount := calldataload(add(0x40, data.offset))
        }
        if (0x60 < data.length) {
            assembly ("memory-safe") {
                // starts at the beginning of sellToken
                permit := add(0x20, data.offset)
                isForwarded := calldataload(add(0xa0, data.offset))

                sig.offset := add(0xc0, data.offset)
                sig.length := calldataload(sig.offset)
                sig.offset := add(0x20, sig.offset)
            }
            ISignatureTransfer.SignatureTransferDetails memory transferDetails =
                ISignatureTransfer.SignatureTransferDetails({to: msg.sender, requestedAmount: sellAmount});
            _transferFrom(permit, transferDetails, sig, isForwarded);
        } else {
            sellToken.safeTransfer(msg.sender, sellAmount);
        }
        // return abi.encode(sellAmount);
        assembly ("memory-safe") {
            returndata := mload(0x40)
            mstore(returndata, 0x60)
            mstore(add(0x20, returndata), 0x20)
            mstore(add(0x40, returndata), 0x20)
            mstore(add(0x60, returndata), sellAmount)
            mstore(0x40, add(0x80, returndata))
        }
    }
}
