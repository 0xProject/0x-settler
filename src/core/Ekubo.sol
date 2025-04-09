// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";
import {Ternary} from "../utils/Ternary.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {Panic} from "../utils/Panic.sol";

import {TooMuchSlippage, ZeroSellAmount} from "./SettlerErrors.sol";

import {CreditDebt, Encoder, NotesLib, StateLib, Decoder, Take} from "./FlashAccountingCommon.sol";

type Config is bytes32;

type SqrtRatio is uint96;

error AmountSpecifiedTooLarge(int256 amount);

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

abstract contract Ekubo is SettlerAbstract {
    using UnsafeMath for uint256;
    using UnsafeMath for int256;
    using CreditDebt for int256;
    using Ternary for bool;
    using SafeTransferLib for IERC20;
    using NotesLib for NotesLib.Note;
    using NotesLib for NotesLib.Note[];
    using StateLib for StateLib.State;

    constructor() {
        assert(BASIS == Encoder.BASIS);
        assert(BASIS == Decoder.BASIS);
        assert(ETH_ADDRESS == Decoder.ETH_ADDRESS);
    }

    // fill encoding musings:
    //     bps (2 bytes)
    //     packing key (1 byte)
    //     sell/buy tokens (0, 20, or 40 bytes)
    //     config (32 bytes) - (8 bytes fee, 4 bytes tickSpacing, 20 bytes extension)
    //     skipAhead (32 bytes)

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
            // verbatim result from `lockAcquired` and that `lockAcquired` encoded the buy amount
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
            // verbatim result from `lockAcquired` and that `lockAcquired` encoded the buy amount
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
    ) private returns (uint256) {
        if (sellToken == ETH_ADDRESS) {
            SafeTransferLib.safeTransferETH(payable(msg.sender), sellAmount);
            return sellAmount;
        } else {
            // Encode the call plus the extra data that is going to be needed in the callback
            bytes memory data = abi.encodePacked(
                abi.encodeCall(IEkuboCore.pay, address(sellToken)), abi.encode(payer, sellAmount, permit, isForwarded, sig)
            );
            bytes memory encodedPayedAmount = _setOperatorAndCall(
                msg.sender, data, uint32(IEkuboCallbacks.payCallback.selector), payCallback
            );
            return abi.decode(encodedPayedAmount, (uint256));
        }
    }

    // the mandatory fields are
    // 2 - sell bps
    // 1 - pool key tokens case
    // 32 - config (8 fee, 4 tickSpacing, 20 extension)
    // 32 - skipAhead
    uint256 private constant _HOP_DATA_LENGTH = 62;

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
        if (payer != address(this)) {
            state.globalSell.amount = _permitToSellAmountCalldata(permit);
        }
        if (feeOnTransfer) {
            state.globalSell.amount =
                _ekuboPay(state.globalSell.token, payer, state.globalSell.amount, permit, isForwarded, sig);
        }
        if (state.globalSell.amount == 0) {
            revert ZeroSellAmount(state.globalSell.token);
        }
        state.globalSellAmount = state.globalSell.amount;
        data = newData;

        PoolKey memory poolKey;

        while (data.length >= _HOP_DATA_LENGTH) {
            // TODO: Check if BPS is needed
            uint16 bps;
            assembly ("memory-safe") {
                bps := shr(0xf0, calldataload(data.offset))

                data.offset := add(0x02, data.offset)
                data.length := sub(data.length, 0x02)
                // we don't check for array out-of-bounds here; we will check it later in `Decoder.overflowCheck`
            }

            data = Decoder.updateState(state, notes, data);
            // TODO: check the sign convention
            int256 amountSpecified = int256((state.sell.amount * bps).unsafeDiv(BASIS)).unsafeNeg();
            if (amountSpecified > type(int128).max) {
                revert AmountSpecifiedTooLarge(amountSpecified);
            }
            bool zeroForOne;
            {
                (IERC20 sellToken, IERC20 buyToken) = (state.sell.token, state.buy.token);
                assembly ("memory-safe") {
                    sellToken := and(_ADDRESS_MASK, sellToken)
                    buyToken := and(_ADDRESS_MASK, buyToken)
                    zeroForOne :=
                        or(
                            eq(sellToken, 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee),
                            and(iszero(eq(buyToken, 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee)), lt(sellToken, buyToken))
                        )
                }
                (poolKey.token0, poolKey.token1) = zeroForOne.maybeSwap(address(buyToken), address(sellToken));
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
                SqrtRatio sqrtRatio =
                    SqrtRatio.wrap(uint96(zeroForOne.ternary(uint256(4611797791050542631), uint256(79227682466138141934206691491))));
                (int256 delta0, int256 delta1) =
                    IEkuboCore(msg.sender).swap_611415377(poolKey, int128(amountSpecified), zeroForOne, sqrtRatio, skipAhead);
                (int256 settledSellAmount, int256 settledBuyAmount) = zeroForOne.maybeSwap(delta1, delta0);

                // TODO: Check if this comment applies to Ekubo but for extensions
                // Some insane hooks may increase the sell amount; obviously this may result in
                // unavoidable reverts in some cases. But we still need to make sure that we don't
                // underflow to avoid wildly unexpected behavior.

                // TODO: verify that the vault enforces that the settled sell amount cannot be
                // positive
                state.sell.amount -= uint256(settledSellAmount.unsafeNeg());
                // If `state.buy.amount()` overflows an `int128`, we'll get a revert inside the
                // vault later. We cannot overflow a `uint256`.
                unchecked {
                    state.buy.amount += settledBuyAmount.asCredit(state.buy.token);
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
                        (payer == address(this))? address(this) : _msgSender(),
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
                    revert ZeroSellAmount(globalSellToken);
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
        (
            IERC20 sellToken,
            uint256 requestedAmount,
            address payer,
            uint256 sellAmount,
            ISignatureTransfer.PermitTransferFrom memory permit,
            bool isForwarded,
            bytes memory sig
        ) = abi.decode(data, (IERC20, uint256, address, uint256, ISignatureTransfer.PermitTransferFrom, bool, bytes));
        // TODO: Check if  assert(requestedAmount == sellAmount) should be true
        if (payer == address(this)) {
            sellToken.safeTransfer(msg.sender, sellAmount);
        } else {
            // assert(payer == address(0));
            ISignatureTransfer.SignatureTransferDetails memory transferDetails =
                ISignatureTransfer.SignatureTransferDetails({to: msg.sender, requestedAmount: sellAmount});
            _transferFrom(permit, transferDetails, sig, isForwarded);
        }
    }
}
