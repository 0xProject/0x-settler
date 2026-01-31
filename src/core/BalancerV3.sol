// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC4626} from "@forge-std/interfaces/IERC4626.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";

import {UnsafeMath} from "../utils/UnsafeMath.sol";

import {ZeroSellAmount} from "./SettlerErrors.sol";

import {Encoder, NotePtr, NotesLib, State, Decoder, Take} from "./FlashAccountingCommon.sol";

import {FreeMemory} from "../utils/FreeMemory.sol";

import {Ternary} from "../utils/Ternary.sol";

interface IBalancerV3Vault {
    /**
     * @notice Creates a context for a sequence of operations (i.e., "unlocks" the Vault).
     * @dev Performs a callback on msg.sender with arguments provided in `data`. The Callback is `transient`,
     * meaning all balances for the caller have to be settled at the end.
     *
     * @param data Contains function signature and args to be passed to the msg.sender
     * @return result Resulting data from the call
     */
    function unlock(bytes calldata data) external returns (bytes memory);

    /**
     * @notice Settles deltas for a token; must be successful for the current lock to be released.
     * @dev Protects the caller against leftover dust in the Vault for the token being settled. The caller
     * should know in advance how many tokens were paid to the Vault, so it can provide it as a hint to discard any
     * excess in the Vault balance.
     *
     * If the given hint is equal to or higher than the difference in reserves, the difference in reserves is given as
     * credit to the caller. If it's higher, the caller sent fewer tokens than expected, so settlement would fail.
     *
     * If the given hint is lower than the difference in reserves, the hint is given as credit to the caller.
     * In this case, the excess would be absorbed by the Vault (and reflected correctly in the reserves), but would
     * not affect settlement.
     *
     * The credit supplied by the Vault can be calculated as `min(reserveDifference, amountHint)`, where the reserve
     * difference equals current balance of the token minus existing reserves of the token when the function is called.
     *
     * @param token Address of the token
     * @param amountHint Amount paid as reported by the caller
     * @return credit Credit received in return of the payment
     */
    function settle(IERC20 token, uint256 amountHint) external returns (uint256 credit);

    /**
     * @notice Sends tokens to a recipient.
     * @dev There is no inverse operation for this function. Transfer funds to the Vault and call `settle` to cancel
     * debts.
     *
     * @param token Address of the token
     * @param to Recipient address
     * @param amount Amount of tokens to send
     */
    function sendTo(IERC20 token, address to, uint256 amount) external;

    enum SwapKind {
        EXACT_IN,
        EXACT_OUT
    }

    /**
     * @notice Data passed into primary Vault `swap` operations.
     * @param kind Type of swap (Exact In or Exact Out)
     * @param pool The pool with the tokens being swapped
     * @param tokenIn The token entering the Vault (balance increases)
     * @param tokenOut The token leaving the Vault (balance decreases)
     * @param amountGiven Amount specified for tokenIn or tokenOut (depending on the type of swap)
     * @param limit Minimum or maximum value of the calculated amount (depending on the type of swap)
     * @param userData Additional (optional) user data
     */
    struct VaultSwapParams {
        SwapKind kind;
        address pool;
        IERC20 tokenIn;
        IERC20 tokenOut;
        uint256 amountGiven;
        uint256 limit;
        bytes userData;
    }

    /**
     * @notice Swaps tokens based on provided parameters.
     * @dev All parameters are given in raw token decimal encoding.
     * @param vaultSwapParams Parameters for the swap (see above for struct definition)
     * @return amountCalculated Calculated swap amount
     * @return amountIn Amount of input tokens for the swap
     * @return amountOut Amount of output tokens from the swap
     */
    function swap(VaultSwapParams memory vaultSwapParams)
        external
        returns (uint256 amountCalculated, uint256 amountIn, uint256 amountOut);

    enum WrappingDirection {
        WRAP,
        UNWRAP
    }

    /**
     * @notice Data for a wrap/unwrap operation.
     * @param kind Type of swap (Exact In or Exact Out)
     * @param direction Direction of the wrapping operation (Wrap or Unwrap)
     * @param wrappedToken Wrapped token, compatible with interface ERC4626
     * @param amountGiven Amount specified for tokenIn or tokenOut (depends on the type of swap and wrapping direction)
     * @param limit Minimum or maximum amount specified for the other token (depends on the type of swap and wrapping
     * direction)
     */
    struct BufferWrapOrUnwrapParams {
        SwapKind kind;
        WrappingDirection direction;
        IERC4626 wrappedToken;
        uint256 amountGiven;
        uint256 limit;
    }

    /**
     * @notice Wraps/unwraps tokens based on the parameters provided.
     * @dev All parameters are given in raw token decimal encoding. It requires the buffer to be initialized,
     * and uses the internal wrapped token buffer when it has enough liquidity to avoid external calls.
     *
     * @param params Parameters for the wrap/unwrap operation (see struct definition)
     * @return amountCalculated Calculated swap amount
     * @return amountIn Amount of input tokens for the swap
     * @return amountOut Amount of output tokens from the swap
     */
    function erc4626BufferWrapOrUnwrap(BufferWrapOrUnwrapParams memory params)
        external
        returns (uint256 amountCalculated, uint256 amountIn, uint256 amountOut);
}

library UnsafeVault {
    function unsafeSettle(IBalancerV3Vault vault, IERC20 token, uint256 amount) internal returns (uint256 credit) {
        assembly ("memory-safe") {
            mstore(0x34, amount) // clobbers the upper (always zero) bits of the free memory pointer
            mstore(0x14, token)
            mstore(0x00, 0x15afd409000000000000000000000000) // selector for `settle(address,uint256)` with `token`'s padding

            if iszero(call(gas(), vault, 0x00, 0x10, 0x44, 0x00, 0x20)) {
                let ptr := and(0xffffff, mload(0x40))
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            credit := mload(0x00)

            mstore(0x34, 0x00)
        }
    }

    function unsafeSwap(IBalancerV3Vault vault, IBalancerV3Vault.VaultSwapParams memory params)
        internal
        returns (uint256 amountIn, uint256 amountOut)
    {
        assembly ("memory-safe") {
            // `VaultSwapParams` is a dynamic type with exactly 1 sub-object, and that sub-object is
            // dynamic (all the other members are value types). Therefore, the layout in calldata is
            // nearly identical to the layout in memory, but there's an extra indirection offset
            // that needs to be prepended. Also the pointer to `params.userData` needs to be
            // transformed into an offset relative to the start of `params`.
            // We know that it's safe to (temporarily) clobber the two words in memory immediately
            // before `params` because they are user-allocated (they're part of `wrapParams`). If
            // they were not user-allocated, this would be illegal as it could clobber a word that
            // `solc` spilled from the stack into memory.

            let ptr := mload(0x40)
            let clobberedPtr0 := sub(params, 0x40)
            let clobberedVal0 := mload(clobberedPtr0)
            let clobberedPtr1 := sub(params, 0x20)
            let clobberedVal1 := mload(clobberedPtr1)

            mstore(clobberedPtr0, 0x2bfb780c) // selector for `swap((uint8,address,address,address,uint256,uint256,bytes))`
            mstore(clobberedPtr1, 0x20) // indirection offset to the dynamic type `VaultSwapParams`

            // Because we laid out `swapParams` as the last object in memory before
            // `swapParam.userData`, the two objects are contiguous. Their encoding in calldata is
            // exactly the same as their encoding in memory, but with pointers changed to offsets.
            let userDataPtr := add(0xc0, params)
            let userData := mload(userDataPtr)
            let userDataLen := mload(userData)
            // Convert the pointer `userData` into an offset relative to the start of its parent
            // object (`params`), and replace it in memory to transform it to the calldata encoding
            let len := sub(userData, params)
            mstore(userDataPtr, len)
            // Compute the length of the entire encoded object
            len := add(0x20, add(userDataLen, len))
            // The padding is a little wonky (we're not creating the Solidity-strict ABI encoding),
            // but the Solidity ABIDecoder is relaxed enough that this doesn't matter.

            // The length of the whole call's calldata is 36 bytes longer than the encoding of
            // `params` in memory to account for the prepending of the selector (4 bytes) and the
            // indirection offset (32 bytes)
            if iszero(call(gas(), vault, 0x00, add(0x1c, clobberedPtr0), add(0x24, len), 0x00, 0x60)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
            amountIn := mload(0x20)
            amountOut := mload(0x40)

            // mstore(userDataPtr, userData) // we don't need this because we're immediately going to deallocate
            mstore(clobberedPtr0, clobberedVal0)
            mstore(clobberedPtr1, clobberedVal1)
            mstore(0x40, ptr)
        }
    }

    function unsafeErc4626BufferWrapOrUnwrap(
        IBalancerV3Vault vault,
        IBalancerV3Vault.BufferWrapOrUnwrapParams memory params
    ) internal returns (uint256 amountIn, uint256 amountOut) {
        assembly ("memory-safe") {
            // `BufferWrapOrUnwrapParams` is a static type and contains no sub-objects (all its
            // members are value types), so the layout in calldata is just the layout in memory,
            // without any indirection.
            // We know that it's safe to (temporarily) clobber the word in memory immediately before
            // `params` because it is user-allocated (it's part of the `Notes` heap). If it were not
            // user-allocated, this would be illegal as it could clobber a word that `solc` spilled
            // from the stack into memory.

            let ptr := mload(0x40)
            let clobberedPtr := sub(params, 0x20)
            let clobberedVal := mload(clobberedPtr)
            mstore(clobberedPtr, 0x43583be5) // selector for `erc4626BufferWrapOrUnwrap((uint8,uint8,address,uint256,uint256))`

            if iszero(call(gas(), vault, 0x00, add(0x1c, clobberedPtr), 0xa4, 0x00, 0x60)) {
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            amountIn := mload(0x20)
            amountOut := mload(0x40)

            mstore(clobberedPtr, clobberedVal)
            mstore(0x40, ptr)
        }
    }
}

IBalancerV3Vault constant VAULT = IBalancerV3Vault(0xbA1333333333a1BA1108E8412f11850A5C319bA9);

abstract contract BalancerV3 is SettlerAbstract, FreeMemory {
    using SafeTransferLib for IERC20;
    using UnsafeMath for uint256;
    using NotesLib for NotesLib.Note[];
    using Ternary for bool;

    using UnsafeVault for IBalancerV3Vault;

    constructor() {
        assert(BASIS == Encoder.BASIS);
        assert(BASIS == Decoder.BASIS);
        assert(address(ETH_ADDRESS) == NotesLib.ETH_ADDRESS);
    }

    //// How to generate `fills` for BalancerV3:
    ////
    //// Linearize your DAG of fills by doing a topological sort on the tokens involved. Swapping
    //// against a boosted pool (usually) creates 3 fills: wrap, swap, unwrap. The tokens involved
    //// includes each ERC4626 tokenized vault token for any boosted pools. In the topological sort
    //// of tokens, when there is a choice of the next token, break ties by preferring a token if it
    //// is the lexicographically largest token that is bought among fills with sell token equal to
    //// the previous token in the topological sort. Then sort the fills belonging to each sell
    //// token by their buy token. This technique isn't *quite* optimal, but it's pretty close. The
    //// buy token of the final fill is special-cased. It is the token that will be transferred to
    //// `recipient` and have its slippage checked against `amountOutMin`. In the event that you are
    //// encoding a series of fills with more than one output token, ensure that at least one of the
    //// global buy token's fills is positioned appropriately.
    ////
    //// Now that you have a list of fills, encode each fill as follows.
    //// First, decide if the fill is a swap or an ERC4626 wrap/unwrap.
    //// Second, encode the `bps` for the fill as 2 bytes. Remember that this `bps` is relative to
    //// the running balance at the moment that the fill is settled. If the fill is a wrap, set the
    //// most significant bit of `bps`. If the fill is an unwrap, set the second most significant
    //// bit of `bps`
    //// Third, encode the packing key for that fill as 1 byte. The packing key byte depends on the
    //// tokens involved in the previous fill. If the fill is a wrap, the buy token must be the
    //// ERC4626 vault. If the fill is an unwrap, the sell token must be the ERC4626 vault. If the
    //// fill is a swap against a boosted pool, both sell and buy tokens must be ERC4626 vaults. God
    //// help you if you're dealing with a boosted pool where only some of the tokens involved are
    //// ERC4626. The packing key for the first fill must be 1; i.e. encode only the buy token for
    //// the first fill.
    ////   0 -> sell and buy tokens remain unchanged from the previous fill (pure multiplex)
    ////   1 -> sell token remains unchanged from the previous fill, buy token is encoded (diamond multiplex)
    ////   2 -> sell token becomes the buy token from the previous fill, new buy token is encoded (multihop)
    ////   3 -> both sell and buy token are encoded
    //// Obviously, after encoding the packing key, you encode 0, 1, or 2 tokens (each as 20 bytes),
    //// as appropriate.
    //// If the fill is a wrap/unwrap, you're done. Move on to the next fill. If the fill is a swap,
    //// the following fields are mandatory:
    //// Fourth, encode the pool address as 20 bytes.
    //// Fifth, encode the hook data for the fill. Encode the length of the hook data as 3 bytes,
    //// then append the hook data itself.
    ////
    //// Repeat the process for each fill and concatenate the results without padding.

    function sellToBalancerV3(
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
            uint32(IBalancerV3Vault.unlock.selector),
            recipient,
            sellToken,
            bps,
            feeOnTransfer,
            hashMul,
            hashMod,
            fills,
            amountOutMin
        );
        // If, for some insane reason, the first 4 bytes of `recipient` alias the selector for the
        // only mutative function of Settler (`execute` or `executeMetaTxn`, as appropriate), then
        // this call will revert. We will encounter a revert in the nested call to
        // `execute`/`executeMetaTxn` because Settler is reentrancy-locked (this revert is
        // bubbled). If, instead, it aliases a non-mutative function of Settler, we would encounter
        // a revert inside `TransientStorage.checkSpentOperatorAndCallback` because the transient
        // storage slot was not zeroed. This would happen by accident with negligible probability,
        // and is merely annoying if it does happen.
        bytes memory encodedBuyAmount =
            _setOperatorAndCall(address(VAULT), data, uint32(uint256(uint160(recipient)) >> 128), _balV3Callback);
        // buyAmount = abi.decode(abi.decode(encodedBuyAmount, (bytes)), (uint256));
        assembly ("memory-safe") {
            // We can skip all the checks performed by `abi.decode` because we know that this is the
            // verbatim result from `balV3UnlockCallback` and that `balV3UnlockCallback` encoded the
            // buy amount correctly.
            buyAmount := mload(add(0x60, encodedBuyAmount))
        }
    }

    function sellToBalancerV3VIP(
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
            uint32(IBalancerV3Vault.unlock.selector),
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
        // See comment in `sellToBalancerV3` about why `recipient` aliasing a valid selector is
        // ultimately harmless.
        bytes memory encodedBuyAmount =
            _setOperatorAndCall(address(VAULT), data, uint32(uint256(uint160(recipient)) >> 128), _balV3Callback);
        // buyAmount = abi.decode(abi.decode(encodedBuyAmount, (bytes)), (uint256));
        assembly ("memory-safe") {
            // We can skip all the checks performed by `abi.decode` because we know that this is the
            // verbatim result from `balV3UnlockCallback` and that `balV3UnlockCallback` encoded the
            // buy amount correctly.
            buyAmount := mload(add(0x60, encodedBuyAmount))
        }
    }

    function _balV3Callback(bytes calldata) private returns (bytes memory) {
        // `VAULT` doesn't prepend a selector and ABIEncode the payload. It just echoes the decoded
        // payload verbatim back to us. Therefore, we use `_msgData()` instead of the argument to
        // this function because `_msgData()` still has the first 4 bytes of the payload attached.
        return balV3UnlockCallback(_msgData());
    }

    function _setSwapParams(IBalancerV3Vault.VaultSwapParams memory swapParams, State state, bytes calldata data)
        private
        pure
        returns (bytes calldata)
    {
        assembly ("memory-safe") {
            mstore(add(0x20, swapParams), shr(0x60, calldataload(data.offset)))
            data.offset := add(0x14, data.offset)
            data.length := sub(data.length, 0x14)
            // we don't check for array out-of-bounds here; we will check it later in `Decoder.overflowCheck`
        }
        swapParams.tokenIn = state.sell().token();
        swapParams.tokenOut = state.buy().token();
        return data;
    }

    function _decodeUserdataAndSwap(
        IBalancerV3Vault.VaultSwapParams memory swapParams,
        State state,
        bytes calldata data
    ) private DANGEROUS_freeMemory returns (bytes calldata) {
        (data, swapParams.userData) = Decoder.decodeBytes(data);
        Decoder.overflowCheck(data);

        (uint256 amountIn, uint256 amountOut) = IBalancerV3Vault(msg.sender).unsafeSwap(swapParams);
        unchecked {
            // `amountIn` is always exactly `swapParams.amountGiven`
            NotePtr sell = state.sell();
            sell.setAmount(sell.amount() - amountIn);
        }
        // `amountOut` can never get super close to `type(uint256).max` because `VAULT` does its
        // internal calculations in fixnum with a basis of `1 ether`, giving us a headroom of ~60
        // bits. However, `state.buy.amount` may be an agglomeration of values returned by ERC4626
        // vaults, and there is no implicit restriction on those values.
        NotePtr buy = state.buy();
        buy.setAmount(buy.amount() + amountOut);
        assembly ("memory-safe") {
            mstore(add(0xc0, swapParams), 0x60)
        }

        return data;
    }

    function _erc4626WrapUnwrap(IBalancerV3Vault.BufferWrapOrUnwrapParams memory wrapParams, State state) private {
        (uint256 amountIn, uint256 amountOut) = IBalancerV3Vault(msg.sender).unsafeErc4626BufferWrapOrUnwrap(wrapParams);
        unchecked {
            // `amountIn` is always exactly `wrapParams.amountGiven`
            NotePtr sell = state.sell();
            sell.setAmount(sell.amount() - amountIn);
        }
        // `amountOut` may depend on the behavior of the ERC4626 vault. We can make no assumptions
        // about the reasonableness of the range of values that may be returned.
        NotePtr buy = state.buy();
        buy.setAmount(buy.amount() + amountOut);
    }

    function _balV3Pay(
        IERC20 sellToken,
        address payer,
        uint256 sellAmount,
        ISignatureTransfer.PermitTransferFrom calldata permit,
        bool isForwarded,
        bytes calldata sig
    ) private returns (uint256) {
        if (payer == address(this)) {
            if (sellAmount != 0) {
                sellToken.safeTransfer(msg.sender, sellAmount);
            }
        } else {
            // assert(payer == address(0));
            ISignatureTransfer.SignatureTransferDetails memory transferDetails =
                ISignatureTransfer.SignatureTransferDetails({to: msg.sender, requestedAmount: sellAmount});
            _transferFrom(permit, transferDetails, sig, isForwarded);
        }
        return IBalancerV3Vault(msg.sender).unsafeSettle(sellToken, sellAmount);
    }

    // the mandatory fields are
    // 2 - sell bps
    // 1 - pool key tokens case
    uint256 private constant _HOP_DATA_LENGTH = 3;

    function balV3UnlockCallback(bytes calldata data) private returns (bytes memory) {
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
                    _balV3Pay(globalSell.token(), payer, globalSell.amount(), permit, isForwarded, sig)
                );
            }
            state.setGlobalSellAmount(globalSell.amount());
        }
        state.checkZeroSellAmount();
        data = newData;

        IBalancerV3Vault.BufferWrapOrUnwrapParams memory wrapParams;
        /*
        wrapParams.kind = IBalancerV3Vault.SwapKind.EXACT_IN;
        wrapParams.limit = 0; // TODO: price limits for partial filling to prevent slippage/bad pricing during partial fills
        */

        // We position `swapParams` at the end of allocated memory so that when we `calldatacopy`
        // the `userData`, it ends up contiguous
        IBalancerV3Vault.VaultSwapParams memory swapParams;
        /*
        swapParams.kind = IBalancerV3Vault.SwapKind.EXACT_IN;
        swapParams.limit = 0; // TODO: price limits for partial filling
        */

        while (data.length >= _HOP_DATA_LENGTH) {
            uint256 bps;
            assembly ("memory-safe") {
                bps := shr(0xf0, calldataload(data.offset))

                data.offset := add(0x02, data.offset)
                data.length := sub(data.length, 0x02)
                // we don't check for array out-of-bounds here; we will check it later in `Decoder.overflowCheck`
            }

            data = Decoder.updateState(state, notes, data);

            if (bps & 0xc000 == 0) {
                data = _setSwapParams(swapParams, state, data);
                unchecked {
                    swapParams.amountGiven = (state.sell().amount() * bps).unsafeDiv(BASIS);
                }
                data = _decodeUserdataAndSwap(swapParams, state, data);
            } else {
                Decoder.overflowCheck(data);

                if (bps & 0x4000 == 0) {
                    wrapParams.direction = IBalancerV3Vault.WrappingDirection.WRAP;
                    wrapParams.wrappedToken = IERC4626(address(state.buy().token()));
                } else {
                    wrapParams.direction = IBalancerV3Vault.WrappingDirection.UNWRAP;
                    wrapParams.wrappedToken = IERC4626(address(state.sell().token()));
                }
                bps &= 0x3fff;
                unchecked {
                    wrapParams.amountGiven = (state.sell().amount() * bps).unsafeDiv(BASIS);
                }

                _erc4626WrapUnwrap(wrapParams, state);
            }
        }

        // `data` has been consumed. All that remains is to settle out the net result of all the
        // swaps. Any credit in any token other than `state.buy.token` will be swept to
        // Settler. `state.buy.token` will be sent to `recipient`.
        {
            NotePtr globalSell = state.globalSell();
            (IERC20 globalSellToken, uint256 globalSellAmount) = (globalSell.token(), globalSell.amount());
            uint256 globalBuyAmount =
                Take.take(state, notes, uint32(IBalancerV3Vault.sendTo.selector), recipient, minBuyAmount);
            if (feeOnTransfer) {
                // We've already transferred the sell token to the vault and
                // `settle`'d. `globalSellAmount` is the verbatim credit in that token stored by the
                // vault. We only need to handle the case of incomplete filling.
                if (globalSellAmount != 0) {
                    Take._callSelector(
                        uint32(IBalancerV3Vault.sendTo.selector),
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
                _balV3Pay(globalSellToken, payer, debt, permit, isForwarded, sig);
            }

            bytes memory returndata;
            assembly ("memory-safe") {
                returndata := mload(0x40)
                mstore(returndata, 0x20)
                mstore(add(0x20, returndata), globalBuyAmount)
                mstore(0x40, add(0x40, returndata))
            }
            return returndata;
        }
    }
}
