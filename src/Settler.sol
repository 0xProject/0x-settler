// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IERC20, IERC20Meta} from "./IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {Permit2Payment} from "./core/Permit2Payment.sol";
import {Basic} from "./core/Basic.sol";
import {OtcOrderSettlement} from "./core/OtcOrderSettlement.sol";
import {UniswapV3} from "./core/UniswapV3.sol";
import {UniswapV2} from "./core/UniswapV2.sol";
import {IPSM, MakerPSM} from "./core/MakerPSM.sol";

import {SafeTransferLib} from "./vendor/SafeTransferLib.sol";
import {UnsafeMath} from "./utils/UnsafeMath.sol";
import {FullMath} from "./utils/FullMath.sol";
import {FreeMemory} from "./utils/FreeMemory.sol";

import {ISettlerActions} from "./ISettlerActions.sol";

/// @dev This library omits index bounds/overflow checking when accessing calldata arrays for gas efficiency, but still includes checks against `calldatasize()` for safety.
library CalldataDecoder {
    function decodeCall(bytes[] calldata data, uint256 i)
        internal
        pure
        returns (bytes4 selector, bytes calldata args)
    {
        assembly ("memory-safe") {
            // helper functions
            function panic(code) {
                mstore(0x00, 0x4e487b71) // keccak256("Panic(uint256)")[:4]
                mstore(0x20, code)
                revert(0x1c, 0x24)
            }
            function overflow() {
                panic(0x11) // 0x11 -> arithmetic under-/over- flow
            }
            function bad_calldata() {
                revert(0x00, 0x00) // empty reason for malformed calldata
            }

            // initially, we set `args.offset` to the pointer to the length. this is 32 bytes before the actual start of data
            args.offset :=
                add(
                    data.offset,
                    calldataload(
                        add(shl(5, i), data.offset) // can't overflow; we assume `i` is in-bounds
                    )
                )
            // because the offset to `args` stored in `data` is arbitrary, we have to check it
            if lt(args.offset, add(shl(5, data.length), data.offset)) { overflow() }
            if iszero(lt(args.offset, calldatasize())) { bad_calldata() }
            // now we load `args.length` and set `args.offset` to the start of data
            args.length := calldataload(args.offset)
            args.offset := add(args.offset, 0x20) // can't overflow; calldata can't be that long
            {
                // check that the end of `args` is in-bounds
                let end := add(args.offset, args.length)
                if lt(end, args.offset) { overflow() }
                if gt(end, calldatasize()) { bad_calldata() }
            }
            // slice off the first 4 bytes of `args` as the selector
            if lt(args.length, 4) {
                // loading selector results in out-of-bounds read
                panic(0x32) // 0x32 -> out-of-bounds array access
            }
            selector := calldataload(args.offset) // solidity cleans dirty bits automatically
            args.length := sub(args.length, 4) // can't underflow; checked above
            args.offset := add(args.offset, 4) // can't overflow/oob; we already checked `end`
        }
    }
}

contract Settler is Permit2Payment, Basic, OtcOrderSettlement, UniswapV3, UniswapV2, MakerPSM, FreeMemory {
    using SafeTransferLib for IERC20;
    using SafeTransferLib for address payable;
    using UnsafeMath for uint256;
    using FullMath for uint256;
    using CalldataDecoder for bytes[];

    error ActionInvalid(uint256 i, bytes4 action, bytes data);

    receive() external payable {}

    constructor(address permit2, address uniFactory, bytes32 poolInitCodeHash, address dai, address trustedForwarder)
        Permit2Payment(permit2, trustedForwarder)
        Basic()
        OtcOrderSettlement()
        UniswapV3(uniFactory, poolInitCodeHash)
        UniswapV2()
        MakerPSM(dai)
    {}

    struct AllowedSlippage {
        address buyToken;
        address recipient;
        uint256 minAmountOut;
    }

    function _checkSlippageAndTransfer(AllowedSlippage calldata slippage) internal {
        // This final slippage check effectively prohibits custody optimization on the
        // final hop of every swap. This is gas-inefficient. This is on purpose. Because
        // ISettlerActions.BASIC_SELL could interaction with an intents-based settlement
        // mechanism, we must ensure that the user's want token increase is coming
        // directly from us instead of from some other form of exchange of value.
        (address buyToken, address recipient, uint256 minAmountOut) =
            (slippage.buyToken, slippage.recipient, slippage.minAmountOut);
        if (minAmountOut != 0 || buyToken != address(0)) {
            if (buyToken == ETH_ADDRESS) {
                uint256 amountOut = address(this).balance;
                if (amountOut < minAmountOut) {
                    revert TooMuchSlippage(buyToken, minAmountOut, amountOut);
                }
                payable(recipient).safeTransferETH(amountOut);
            } else {
                uint256 amountOut = IERC20(buyToken).balanceOf(address(this));
                if (amountOut < minAmountOut) {
                    revert TooMuchSlippage(buyToken, minAmountOut, amountOut);
                }
                IERC20(buyToken).safeTransfer(recipient, amountOut);
            }
        }
    }

    function _otcVIP(bytes calldata data) internal DANGEROUS_freeMemory {
        (
            address recipient,
            ISignatureTransfer.PermitTransferFrom memory makerPermit,
            address maker,
            bytes memory makerSig,
            ISignatureTransfer.PermitTransferFrom memory takerPermit,
            bytes memory takerSig
        ) = abi.decode(
            data,
            (
                address,
                ISignatureTransfer.PermitTransferFrom,
                address,
                bytes,
                ISignatureTransfer.PermitTransferFrom,
                bytes
            )
        );

        fillOtcOrder(recipient, makerPermit, maker, makerSig, takerPermit, takerSig);
    }

    function _uniV3VIP(bytes calldata data) internal DANGEROUS_freeMemory {
        (
            address recipient,
            uint256 amountIn,
            uint256 amountOutMin,
            bytes memory path,
            ISignatureTransfer.PermitTransferFrom memory permit,
            bytes memory sig
        ) = abi.decode(data, (address, uint256, uint256, bytes, ISignatureTransfer.PermitTransferFrom, bytes));

        sellTokenForTokenToUniswapV3(recipient, path, amountIn, amountOutMin, _msgSender(), permit, sig);
    }

    function execute(bytes[] calldata actions, AllowedSlippage calldata slippage) public payable {
        if (actions.length != 0) {
            (bytes4 action, bytes calldata data) = actions.decodeCall(0);
            if (action == ISettlerActions.SETTLER_OTC_PERMIT2.selector) {
                _otcVIP(data);
            } else if (action == ISettlerActions.UNISWAPV3_PERMIT2_SWAP_EXACT_IN.selector) {
                _uniV3VIP(data);
            } else {
                _dispatch(0, action, data, _msgSender());
            }
        }

        for (uint256 i = 1; i < actions.length; i = i.unsafeInc()) {
            (bytes4 action, bytes calldata data) = actions.decodeCall(i);
            _dispatch(i, action, data, _msgSender());
        }

        _checkSlippageAndTransfer(slippage);
    }

    function _hashArrayOfBytes(bytes[] calldata actions) internal pure returns (bytes32 result) {
        // This function deliberately does no bounds checking on `actions` for
        // gas efficiency. We assume that `actions` will get used elsewhere in
        // this context and any OOB or other malformed calldata will result in a
        // revert later.
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            let hashesLength := shl(5, actions.length)
            for {
                let i := actions.offset
                let dst := ptr
                let end := add(i, hashesLength)
            } lt(i, end) {
                i := add(i, 0x20)
                dst := add(dst, 0x20)
            } {
                let src := add(actions.offset, calldataload(i))
                let length := calldataload(src)
                calldatacopy(dst, add(src, 0x20), length)
                mstore(dst, keccak256(dst, length))
            }
            result := keccak256(ptr, hashesLength)
        }
    }

    function _hashActionsAndSlippage(bytes[] calldata actions, AllowedSlippage calldata slippage)
        internal
        pure
        returns (bytes32 result)
    {
        // This function does not check for or clean any dirty bits that might
        // exist in `slippage`. We assume that `slippage` will be used elsewhere
        // in this context and that if there are dirty bits it will result in a
        // revert later.
        bytes32 arrayOfBytesHash = _hashArrayOfBytes(actions);
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, ACTIONS_AND_SLIPPAGE_TYPEHASH)
            calldatacopy(add(ptr, 0x20), slippage, 0x60)
            mstore(add(ptr, 0x80), arrayOfBytesHash)
            result := keccak256(ptr, 0xa0)
        }
    }

    function _metaTxnOtcVIP(bytes calldata data, bytes32 witness, address msgSender, bytes calldata sig)
        internal
        DANGEROUS_freeMemory
    {
        // An optimized path involving a maker/taker in a single trade
        // The OTC order is signed by both maker and taker, validation is
        // performed inside the OtcOrderSettlement so there is no need to
        // validate `sig` against `actions` here
        (
            address recipient,
            ISignatureTransfer.PermitTransferFrom memory makerPermit,
            address maker,
            bytes memory makerSig,
            ISignatureTransfer.PermitTransferFrom memory takerPermit
        ) = abi.decode(
            data,
            (address, ISignatureTransfer.PermitTransferFrom, address, bytes, ISignatureTransfer.PermitTransferFrom)
        );
        fillOtcOrderMetaTxn(recipient, makerPermit, maker, makerSig, takerPermit, msgSender, sig, witness);
    }

    function _metaTxnTransferFrom(bytes calldata data, bytes32 witness, address msgSender, bytes calldata sig)
        internal
        DANGEROUS_freeMemory
    {
        (address recipient, ISignatureTransfer.PermitTransferFrom memory permit) =
            abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom));
        (ISignatureTransfer.SignatureTransferDetails memory transferDetails,,) =
            _permitToTransferDetails(permit, recipient);

        // We simultaneously transfer-in the taker's tokens and authenticate the
        // metatransaction.
        _transferFrom(permit, transferDetails, msgSender, witness, ACTIONS_AND_SLIPPAGE_WITNESS, sig);
    }

    function _metaTxnUniV3VIP(bytes calldata data, bytes32 witness, address msgSender, bytes calldata sig)
        internal
        DANGEROUS_freeMemory
    {
        (
            address recipient,
            uint256 amountIn,
            uint256 amountOutMin,
            bytes memory path,
            ISignatureTransfer.PermitTransferFrom memory permit
        ) = abi.decode(data, (address, uint256, uint256, bytes, ISignatureTransfer.PermitTransferFrom));
        sellTokenForTokenToUniswapV3(recipient, path, amountIn, amountOutMin, msgSender, permit, sig, witness);
    }

    function executeMetaTxn(
        bytes[] calldata actions,
        AllowedSlippage calldata slippage,
        address msgSender,
        bytes calldata sig
    ) public {
        if (actions.length != 0) {
            (bytes4 action, bytes calldata data) = actions.decodeCall(0);

            // By forcing the first action to be one of the witness-aware
            // actions, we ensure that the entire sequence of actions is
            // authorized. `msgSender` is the signer of the metatransaction.
            bytes32 witness = _hashActionsAndSlippage(actions, slippage);

            if (action == ISettlerActions.METATXN_SETTLER_OTC_PERMIT2.selector) {
                _metaTxnOtcVIP(data, witness, msgSender, sig);
            } else if (action == ISettlerActions.METATXN_PERMIT2_TRANSFER_FROM.selector) {
                _metaTxnTransferFrom(data, witness, msgSender, sig);
            } else if (action == ISettlerActions.METATXN_UNISWAPV3_PERMIT2_SWAP_EXACT_IN.selector) {
                _metaTxnUniV3VIP(data, witness, msgSender, sig);
            } else {
                revert ActionInvalid({i: 0, action: action, data: data});
            }
        }

        for (uint256 i = 1; i < actions.length; i = i.unsafeInc()) {
            (bytes4 action, bytes calldata data) = actions.decodeCall(i);
            _dispatch(i, action, data, msgSender);
        }

        _checkSlippageAndTransfer(slippage);
    }

    function _dispatch(uint256 i, bytes4 action, bytes calldata data, address msgSender)
        internal
        DANGEROUS_freeMemory
    {
        if (action == ISettlerActions.PERMIT2_TRANSFER_FROM.selector) {
            (address recipient, ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) =
                abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom, bytes));
            (ISignatureTransfer.SignatureTransferDetails memory transferDetails,,) =
                _permitToTransferDetails(permit, recipient);
            _transferFrom(permit, transferDetails, msgSender, sig);
        } else if (action == ISettlerActions.SETTLER_OTC_SELF_FUNDED.selector) {
            (
                address recipient,
                ISignatureTransfer.PermitTransferFrom memory permit,
                address maker,
                bytes memory makerSig,
                IERC20 takerToken,
                uint256 maxTakerAmount
            ) = abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom, address, bytes, IERC20, uint256));

            fillOtcOrderSelfFunded(recipient, permit, maker, makerSig, takerToken, maxTakerAmount, msgSender);
        } else if (action == ISettlerActions.UNISWAPV3_SWAP_EXACT_IN.selector) {
            (address recipient, uint256 bips, uint256 amountOutMin, bytes memory path) =
                abi.decode(data, (address, uint256, uint256, bytes));

            sellTokenForTokenToUniswapV3(recipient, path, bips, amountOutMin);
        } else if (action == ISettlerActions.UNISWAPV2_SWAP.selector) {
            (address recipient, address sellToken, address pool, uint8 swapInfo, uint256 bips, uint256 amountOutMin) =
                abi.decode(data, (address, address, address, uint8, uint256, uint256));

            sellToUniswapV2(recipient, sellToken, pool, swapInfo, bips, amountOutMin);
        } else if (action == ISettlerActions.MAKER_PSM_SELL_GEM.selector) {
            (address recipient, uint256 bips, IPSM psm, IERC20Meta gemToken) =
                abi.decode(data, (address, uint256, IPSM, IERC20Meta));

            makerPsmSellGem(recipient, bips, psm, gemToken);
        } else if (action == ISettlerActions.MAKER_PSM_BUY_GEM.selector) {
            (address recipient, uint256 bips, IPSM psm, IERC20Meta gemToken) =
                abi.decode(data, (address, uint256, IPSM, IERC20Meta));

            makerPsmBuyGem(recipient, bips, psm, gemToken);
        } else if (action == ISettlerActions.BASIC_SELL.selector) {
            (address pool, IERC20 sellToken, uint256 proportion, uint256 offset, bytes memory _data) =
                abi.decode(data, (address, IERC20, uint256, uint256, bytes));

            basicSellToPool(pool, sellToken, proportion, offset, _data);
        } else if (action == ISettlerActions.POSITIVE_SLIPPAGE.selector) {
            (address recipient, IERC20 token, uint256 expectedAmount) = abi.decode(data, (address, IERC20, uint256));
            if (token == IERC20(ETH_ADDRESS)) {
                uint256 balance = address(this).balance;
                if (balance > expectedAmount) {
                    unchecked {
                        payable(recipient).safeTransferETH(balance - expectedAmount);
                    }
                }
            } else {
                uint256 balance = token.balanceOf(address(this));
                if (balance > expectedAmount) {
                    unchecked {
                        token.safeTransfer(recipient, balance - expectedAmount);
                    }
                }
            }
        } else {
            revert ActionInvalid({i: i, action: action, data: data});
        }
    }
}
