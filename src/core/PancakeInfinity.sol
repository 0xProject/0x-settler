// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";

import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {Panic} from "../utils/Panic.sol";
import {Ternary} from "../utils/Ternary.sol";
import {ZeroSellAmount, UnknownPoolManagerId} from "./SettlerErrors.sol";

import {CreditDebt, Encoder, NotePtr, NotesLib, State, Decoder, Take} from "./FlashAccountingCommon.sol";
import {BalanceDelta} from "./UniswapV4Types.sol";

interface IPancakeInfinityVault {
    /// @notice Called by the user to net out some value owed to the user
    /// @dev Will revert if the requested amount is not available, consider using `mint` instead
    /// @dev Can also be used as a mechanism for free flash loans
    function take(IERC20 currency, address to, uint256 amount) external;

    /// @notice Writes the current ERC20 balance of the specified currency to transient storage
    /// This is used to checkpoint balances for the manager and derive deltas for the caller.
    /// @dev This MUST be called before any ERC20 tokens are sent into the contract, but can be skipped
    /// for native tokens because the amount to settle is determined by the sent value.
    /// However, if an ERC20 token has been synced and not settled, and the caller instead wants to settle
    /// native funds, this function can be called with the native currency to then be able to settle the native currency
    function sync(IERC20 token0) external;

    /// @notice Called by the user to pay what is owed
    function settle() external payable returns (uint256 paid);

    /// @notice All operations go through this function
    /// @param data Any data to pass to the callback, via `ILockCallback(msg.sender).lockCallback(data)`
    /// @return The data returned by the call to `ILockCallback(msg.sender).lockCallback(data)`
    function lock(bytes calldata data) external returns (bytes memory);
}

IPancakeInfinityVault constant VAULT = IPancakeInfinityVault(0x238a358808379702088667322f80aC48bAd5e6c4);

/// @notice Interface for the callback executed when an address locks the vault
interface IPancakeInfinityLockCallback {
    /// @notice Called by the pool manager on `msg.sender` when a lock is acquired
    /// @param data The data that was passed to the call to lock
    /// @return Any data that you want to be returned from the lock call
    function lockAcquired(bytes calldata data) external returns (bytes memory);
}

type PoolId is bytes32;

type IHooks is address;

interface IPancakeInfinityPoolManager {
    /// @notice Return PoolKey for a given PoolId
    function poolIdToPoolKey(PoolId id) external view returns (PoolKey memory);
}

/// @notice Returns the key for identifying a pool
struct PoolKey {
    /// @notice The lower currency of the pool, sorted numerically
    IERC20 currency0;
    /// @notice The higher currency of the pool, sorted numerically
    IERC20 currency1;
    /// @notice The hooks of the pool, won't have a general interface because hooks interface vary on pool type
    IHooks hooks;
    /// @notice The pool manager of the pool
    IPancakeInfinityPoolManager poolManager;
    /// @notice The pool lp fee, capped at 1_000_000. If the pool has a dynamic fee then it must be exactly equal to 0x800000
    uint24 fee;
    /// @notice Hooks callback and pool specific parameters, i.e. tickSpacing for CL, binStep for bin
    bytes32 parameters;
}

interface IPancakeInfinityCLPoolManager is IPancakeInfinityPoolManager {
    struct SwapParams {
        bool zeroForOne;
        int256 amountSpecified;
        uint160 sqrtPriceLimitX96;
    }

    /// @notice Swap against the given pool
    /// @param key The pool to swap in
    /// @param params The parameters for swapping
    /// @param hookData Any data to pass to the callback
    /// @return delta The balance delta of the address swapping
    /// @dev Swapping on low liquidity pools may cause unexpected swap amounts when liquidity available is less than amountSpecified.
    /// Additionally note that if interacting with hooks that have the BEFORE_SWAP_RETURNS_DELTA_FLAG or AFTER_SWAP_RETURNS_DELTA_FLAG
    /// the hook may alter the swap input/output. Integrators should perform checks on the returned swapDelta.
    function swap(PoolKey memory key, SwapParams memory params, bytes calldata hookData)
        external
        returns (BalanceDelta delta);
}

IPancakeInfinityCLPoolManager constant CL_MANAGER =
    IPancakeInfinityCLPoolManager(0xa0FfB9c1CE1Fe56963B0321B32E7A0302114058b);

interface IPancakeInfinityBinPoolManager is IPancakeInfinityPoolManager {
    /// @notice Peform a swap to a pool
    /// @param key The pool key
    /// @param swapForY If true, swap token X for Y, if false, swap token Y for X
    /// @param amountSpecified If negative, imply exactInput, if positive, imply exactOutput.
    function swap(PoolKey memory key, bool swapForY, int128 amountSpecified, bytes calldata hookData)
        external
        returns (BalanceDelta delta);
}

library UnsafePancakeInfinityVault {
    function unsafeSync(IPancakeInfinityVault vault, IERC20 token) internal {
        assembly ("memory-safe") {
            mstore(0x14, token)
            mstore(0x00, 0xa5841194000000000000000000000000) // selector for `sync(address)` with `token`'s padding
            if iszero(call(gas(), vault, 0x00, 0x10, 0x24, 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
        }
    }

    function unsafeSettle(IPancakeInfinityVault vault, uint256 value) internal returns (uint256 r) {
        assembly ("memory-safe") {
            mstore(0x00, 0x11da60b4) // selector for `settle()`
            if iszero(call(gas(), vault, value, 0x1c, 0x04, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            // No checks on returndata as Pancake Infinity vault is trusted and not arbitrary
            r := mload(0x00)
        }
    }

    function unsafeSettle(IPancakeInfinityVault vault) internal returns (uint256) {
        return unsafeSettle(vault, 0);
    }
}

library UnsafePancakeInfinityPoolManager {
    function unsafeSwap(
        IPancakeInfinityCLPoolManager poolManager,
        PoolKey memory key,
        bool zeroForOne,
        int256 amountSpecified,
        uint256 sqrtPriceLimitX96,
        bytes calldata hookData
    ) internal returns (BalanceDelta r) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, 0xcd0cc1ce) // selector for `swap((address,address,address,address,uint24,bytes32),(bool,int256,uint160),bytes)`
            mcopy(add(0x20, ptr), key, 0xc0)
            mstore(add(0xe0, ptr), zeroForOne)
            mstore(add(0x100, ptr), amountSpecified)
            mstore(add(0x120, ptr), sqrtPriceLimitX96)
            mstore(add(0x140, ptr), 0x140)
            mstore(add(0x160, ptr), hookData.length)
            calldatacopy(add(0x180, ptr), hookData.offset, hookData.length)
            if iszero(call(gas(), poolManager, 0x00, add(0x1c, ptr), add(0x164, hookData.length), 0x00, 0x20)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
            // No checks on returndata as Pancake Infinity cl pool manager is trusted and not arbitrary
            r := mload(0x00)
        }
    }
}

library UnsafePancakeInfinityBinPoolManager {
    function unsafeSwap(
        IPancakeInfinityBinPoolManager poolManager,
        PoolKey memory key,
        bool swapForY,
        int128 amountSpecified,
        bytes calldata hookData
    ) internal returns (BalanceDelta r) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, 0x911a63b7) // selector for `swap((address,address,address,address,uint24,bytes32),bool,int128,bytes)`
            mcopy(add(0x20, ptr), key, 0xc0)
            mstore(add(0xe0, ptr), swapForY)
            mstore(add(0x100, ptr), signextend(0x0f, amountSpecified))
            mstore(add(0x120, ptr), 0x120)
            mstore(add(0x140, ptr), hookData.length)
            calldatacopy(add(0x160, ptr), hookData.offset, hookData.length)
            if iszero(call(gas(), poolManager, 0x00, add(0x1c, ptr), add(0x164, hookData.length), 0x00, 0x20)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
            // No checks on returndata as Pancake Infinity bin pool manager is trusted and not arbitrary
            r := mload(0x00)
        }
    }
}

IPancakeInfinityBinPoolManager constant BIN_MANAGER =
    IPancakeInfinityBinPoolManager(0xC697d2898e0D09264376196696c51D7aBbbAA4a9);

abstract contract PancakeInfinity is SettlerAbstract {
    using UnsafeMath for uint256;
    using UnsafeMath for int256;
    using Ternary for bool;
    using CreditDebt for int256;
    using SafeTransferLib for IERC20;
    using NotesLib for NotesLib.Note[];
    using UnsafePancakeInfinityVault for IPancakeInfinityVault;
    using UnsafePancakeInfinityPoolManager for IPancakeInfinityCLPoolManager;
    using UnsafePancakeInfinityBinPoolManager for IPancakeInfinityBinPoolManager;

    constructor() {
        assert(BASIS == Encoder.BASIS);
        assert(BASIS == Decoder.BASIS);
        assert(address(ETH_ADDRESS) == NotesLib.ETH_ADDRESS);
    }

    //// How to generate `fills` for Pancake Infinity:
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
    //// Take care to note that while Pancake Infinity represents the native asset of the chain as
    //// the address of all zeroes, Settler represents this as the address of all `e`s. You must use
    //// Settler's representation. The conversion is performed by Settler before making calls to
    //// Pancake Infinity.
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
    //// Fourth, encode the hook address as 20 bytes
    //// Fifth, encode the identity of the pool manager for this fill as 1 byte
    ////   0 -> discontinuous-liquidity constant-product (UniV3-like) AKA CL
    ////   1 -> constant-sum (LFJ Liquidity Book -like) AKA Bin
    //// Sixth, encode the pool fee as 3 bytes
    //// Seventh, encode the pool parameters according to the semantics of the selected pool manager,
    //// as 32 bytes
    //// Eighth, encode the hook data for the fill. Encode the length of the hook data as 3 bytes,
    //// then append the hook data itself.
    ////
    //// Repeat the process for each fill and concatenate the results without padding.

    function sellToPancakeInfinity(
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
            uint32(IPancakeInfinityVault.lock.selector),
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
            address(VAULT), data, uint32(IPancakeInfinityLockCallback.lockAcquired.selector), _pancakeInfinityCallback
        );
        // buyAmount = abi.decode(abi.decode(encodedBuyAmount, (bytes)), (uint256));
        assembly ("memory-safe") {
            // We can skip all the checks performed by `abi.decode` because we know that this is the
            // verbatim result from `lockAcquired` and that `lockAcquired` encoded the buy amount
            // correctly.
            buyAmount := mload(add(0x60, encodedBuyAmount))
        }
    }

    function sellToPancakeInfinityVIP(
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
            uint32(IPancakeInfinityVault.lock.selector),
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
            address(VAULT), data, uint32(IPancakeInfinityLockCallback.lockAcquired.selector), _pancakeInfinityCallback
        );
        // buyAmount = abi.decode(abi.decode(encodedBuyAmount, (bytes)), (uint256));
        assembly ("memory-safe") {
            // We can skip all the checks performed by `abi.decode` because we know that this is the
            // verbatim result from `lockAcquired` and that `lockAcquired` encoded the buy amount
            // correctly.
            buyAmount := mload(add(0x60, encodedBuyAmount))
        }
    }

    function _pancakeInfinityPay(
        IERC20 sellToken,
        address payer,
        uint256 sellAmount,
        ISignatureTransfer.PermitTransferFrom calldata permit,
        bool isForwarded,
        bytes calldata sig
    ) private returns (uint256) {
        IPancakeInfinityVault(msg.sender).unsafeSync(sellToken);
        if (payer == address(this)) {
            sellToken.safeTransfer(msg.sender, sellAmount);
        } else {
            // assert(payer == address(0));
            ISignatureTransfer.SignatureTransferDetails memory transferDetails =
                ISignatureTransfer.SignatureTransferDetails({to: msg.sender, requestedAmount: sellAmount});
            _transferFrom(permit, transferDetails, sig, isForwarded);
        }
        return IPancakeInfinityVault(msg.sender).unsafeSettle();
    }

    function _pancakeInfinityCallback(bytes calldata data) private returns (bytes memory) {
        // We know that our calldata is well-formed. Therefore, the first slot is 0x20 and the
        // second slot is the length of the strict ABIEncoded payload
        assembly ("memory-safe") {
            data.length := calldataload(add(0x20, data.offset))
            data.offset := add(0x40, data.offset)
        }
        return lockAcquired(data);
    }

    // the mandatory fields are
    // 2 - sell bps
    // 20 - sqrtPriceLimitX96
    // 1 - pool key tokens case
    // 20 - hook
    // 1 - pool manager ID
    // 3 - pool fee
    // 32 - parameters
    // 3 - hook data length
    uint256 private constant _HOP_DATA_LENGTH = 82;

    uint256 private constant _ADDRESS_MASK = 0x00ffffffffffffffffffffffffffffffffffffffff;

    function lockAcquired(bytes calldata data) private returns (bytes memory) {
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
                    _pancakeInfinityPay(globalSell.token(), payer, globalSell.amount(), permit, isForwarded, sig)
                );
            }
            state.setGlobalSellAmount(globalSell.amount());
        }
        state.checkZeroSellAmount();
        data = newData;

        PoolKey memory poolKey;

        while (data.length >= _HOP_DATA_LENGTH) {
            int256 amountSpecified;
            uint160 sqrtPriceLimitX96;
            {
                uint16 bps;
                assembly ("memory-safe") {
                    bps := shr(0xf0, calldataload(data.offset))
                    data.offset := add(0x02, data.offset)

                    sqrtPriceLimitX96 := shr(0x60, calldataload(data.offset))
                    data.offset := add(0x14, data.offset)

                    data.length := sub(data.length, 0x16)
                    // we don't check for array out-of-bounds here; we will check it later in `Decoder.overflowCheck`
                }

                data = Decoder.updateState(state, notes, data);
                amountSpecified = int256((state.sell().amount() * bps).unsafeDiv(BASIS)).unsafeNeg();
            }
            bool zeroForOne;
            {
                (IERC20 sellToken, IERC20 buyToken) = (state.sell().token(), state.buy().token());
                assembly ("memory-safe") {
                    let sellTokenShifted := shl(0x60, sellToken)
                    let buyTokenShifted := shl(0x60, buyToken)
                    zeroForOne :=
                        or(
                            eq(0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee000000000000000000000000, sellTokenShifted),
                            and(
                                iszero(
                                    eq(0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee000000000000000000000000, buyTokenShifted)
                                ),
                                lt(sellTokenShifted, buyTokenShifted)
                            )
                        )
                }
                (poolKey.currency0, poolKey.currency1) = zeroForOne.maybeSwap(buyToken, sellToken);
                assembly ("memory-safe") {
                    let currency0 := mload(poolKey)
                    // set poolKey to address(0) if it is the native token
                    mstore(poolKey, mul(currency0, iszero(eq(0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, currency0))))
                }
                // poolKey.currency0 is not represented according to ERC-7528 to match the format expected by Pancake Infinity
            }

            {
                IHooks hooks;
                assembly ("memory-safe") {
                    hooks := shr(0x60, calldataload(data.offset))
                    data.offset := add(0x14, data.offset)
                    data.length := sub(data.length, 0x14)
                    // we don't check for array out-of-bounds here; we will check it later in `Decoder.overflowCheck`
                }
                poolKey.hooks = hooks;
            }

            uint8 poolManagerId;
            assembly ("memory-safe") {
                poolManagerId := shr(0xf8, calldataload(data.offset))
                data.offset := add(0x01, data.offset)
                data.length := sub(data.length, 0x01)
                // we don't check for array out-of-bounds here; we will check it later in `Decoder.overflowCheck`
            }

            {
                uint24 fee;
                assembly ("memory-safe") {
                    fee := shr(0xe8, calldataload(data.offset))
                    data.offset := add(0x03, data.offset)
                    data.length := sub(data.length, 0x03)
                    // we don't check for array out-of-bounds here; we will check it later in `Decoder.overflowCheck`
                }
                poolKey.fee = fee;
            }

            {
                bytes32 parameters;
                assembly ("memory-safe") {
                    parameters := calldataload(data.offset)
                    data.offset := add(0x20, data.offset)
                    data.length := sub(data.length, 0x20)
                    // we don't check for array out-of-bounds here; we will check it later in `Decoder.overflowCheck`
                }
                poolKey.parameters = parameters;
            }

            bytes calldata hookData;
            (data, hookData) = Decoder.decodeBytes(data);

            Decoder.overflowCheck(data);

            {
                BalanceDelta delta;
                if (uint256(poolManagerId) == 0) {
                    poolKey.poolManager = CL_MANAGER;

                    delta = IPancakeInfinityCLPoolManager(address(poolKey.poolManager)).unsafeSwap(
                        poolKey,
                        zeroForOne,
                        amountSpecified,
                        sqrtPriceLimitX96,
                        hookData
                    );
                } else if (uint256(poolManagerId) == 1) {
                    poolKey.poolManager = BIN_MANAGER;
                    if (amountSpecified >> 127 != amountSpecified >> 128) {
                        Panic.panic(Panic.ARITHMETIC_OVERFLOW);
                    }
                    delta = IPancakeInfinityBinPoolManager(address(poolKey.poolManager)).unsafeSwap(
                        poolKey, zeroForOne, int128(amountSpecified), hookData
                    );
                } else {
                    assembly ("memory-safe") {
                        mstore(0x00, 0x0a9a7da6) // selector for `UnknownPoolManagerId(uint8)`
                        mstore(0x20, and(0xff, poolManagerId))
                        revert(0x1c, 0x24)
                    }
                }
                (int256 settledSellAmount, int256 settledBuyAmount) =
                    zeroForOne.maybeSwap(delta.amount1(), delta.amount0());
                // Some insane hooks may increase the sell amount, cause the sell amount to be
                // credit, or cause the buy amount to be debt. We need to handle all these cases by
                // reverting.

                NotePtr sell = state.sell();
                sell.setAmount(sell.amount() - settledSellAmount.asDebt(sell));
                // Since `settledBuyAmount` came from an `int128`, this addition cannot overflow a
                // `uint256`. We still need to make sure it doesn't record a debt, though.
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
                Take.take(state, notes, uint32(IPancakeInfinityVault.take.selector), recipient, minBuyAmount);
            if (feeOnTransfer) {
                // We've already transferred the sell token to the vault and
                // `settle`'d. `globalSellAmount` is the verbatim credit in that token stored by the
                // vault. We only need to handle the case of incomplete filling.
                if (globalSellAmount != 0) {
                    Take._callSelector(
                        uint32(IPancakeInfinityVault.take.selector),
                        globalSellToken,
                        payer == address(this) ? address(this) : _msgSender(),
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
                if (globalSellToken == ETH_ADDRESS) {
                    IPancakeInfinityVault(msg.sender).unsafeSync(IERC20(address(0)));
                    IPancakeInfinityVault(msg.sender).unsafeSettle(debt);
                } else {
                    _pancakeInfinityPay(globalSellToken, payer, debt, permit, isForwarded, sig);
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
}
