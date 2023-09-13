// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ERC20} from "solmate/src/tokens/ERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {Basic} from "./core/Basic.sol";
import {CurveV2} from "./core/CurveV2.sol";
import {OtcOrderSettlement} from "./core/OtcOrderSettlement.sol";
import {UniswapV3} from "./core/UniswapV3.sol";
import {IZeroEx, ZeroEx} from "./core/ZeroEx.sol";

import {SafeTransferLib} from "./utils/SafeTransferLib.sol";
import {UnsafeMath} from "./utils/UnsafeMath.sol";
import {FullMath} from "./utils/FullMath.sol";

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

contract Settler is Basic, OtcOrderSettlement, UniswapV3, CurveV2, ZeroEx {
    using SafeTransferLib for ERC20;
    using UnsafeMath for uint256;
    using FullMath for uint256;
    using CalldataDecoder for bytes[];

    error ActionInvalid(uint256 i, bytes4 action, bytes data);
    error TooMuchSlippage(address token, uint256 expected, uint256 actual);

    // Permit2 Witness for meta transactions
    string internal constant ACTIONS_AND_SLIPPAGE_TYPE =
        "ActionsAndSlippage(bytes[] actions,address wantToken,address recipient,uint256 minAmountOut)";
    // `string.concat` isn't recognized by solc as compile-time constant, but `abi.encodePacked` is
    string internal constant ACTIONS_AND_SLIPPAGE_WITNESS = string(
        abi.encodePacked("ActionsAndSlippage actionsAndSlippage)", ACTIONS_AND_SLIPPAGE_TYPE, TOKEN_PERMISSIONS_TYPE)
    );
    bytes32 internal constant ACTIONS_AND_SLIPPAGE_TYPEHASH =
        0x4ab0563587faa1f2e86ede76cfacd8c39103aeb94829021cb7a790cc1776fa37;

    bytes4 internal constant SLIPPAGE_ACTION = bytes4(keccak256("SLIPPAGE(address,uint256)"));

    constructor(address permit2, address zeroEx, address uniFactory, bytes32 poolInitCodeHash, address feeRecipient)
        Basic(permit2)
        CurveV2()
        OtcOrderSettlement(permit2, feeRecipient)
        UniswapV3(uniFactory, poolInitCodeHash, permit2)
        ZeroEx(zeroEx)
    {
        assert(ACTIONS_AND_SLIPPAGE_TYPEHASH == keccak256(bytes(ACTIONS_AND_SLIPPAGE_TYPE)));
    }

    function _checkSlippageAndTransfer(address wantToken, address recipient, uint256 minAmountOut) internal {
        // This final slippage check effectively prohibits custody optimization on the
        // final hop of every swap. This is gas-inefficient. This is on purpose. Because
        // ISettlerActions.BASIC_SELL could interaction with an intents-based settlement
        // mechanism, we must ensure that the user's want token increase is coming
        // directly from us instead of from some other form of exchange of value.
        if (wantToken != address(0) || minAmountOut != 0) {
            uint256 amountOut = ERC20(wantToken).balanceOf(address(this));
            if (amountOut < minAmountOut) {
                revert TooMuchSlippage(wantToken, minAmountOut, amountOut);
            }
            ERC20(wantToken).safeTransfer(recipient, amountOut);
        }
    }

    function execute(bytes[] calldata actions, address wantToken, address recipient, uint256 minAmountOut)
        public
        payable
    {
        if (actions.length != 0) {
            (bytes4 action, bytes calldata data) = actions.decodeCall(0);
            if (action == ISettlerActions.SETTLER_OTC_PERMIT2.selector) {
                if (actions.length != 1) {
                    (action, data) = actions.decodeCall(1);
                    revert ActionInvalid({i: 1, action: action, data: data});
                }
                (
                    ISignatureTransfer.PermitBatchTransferFrom memory makerPermit,
                    address maker,
                    bytes memory makerSig,
                    ISignatureTransfer.PermitBatchTransferFrom memory takerPermit,
                    bytes memory takerSig
                ) = abi.decode(
                    data,
                    (
                        ISignatureTransfer.PermitBatchTransferFrom,
                        address,
                        bytes,
                        ISignatureTransfer.PermitBatchTransferFrom,
                        bytes
                    )
                );
                fillOtcOrder(makerPermit, maker, makerSig, takerPermit, takerSig, recipient);
                return;
            } else {
                _dispatch(0, action, data, msg.sender);
            }
        }

        for (uint256 i = 1; i < actions.length; i = i.unsafeInc()) {
            (bytes4 action, bytes calldata data) = actions.decodeCall(i);
            _dispatch(i, action, data, msg.sender);
        }

        _checkSlippageAndTransfer(wantToken, recipient, minAmountOut);
    }

    function _hashArrayOfBytes(bytes[] calldata actions) internal pure returns (bytes32 result) {
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

    function _hashActionsAndSlippage(
        bytes[] calldata actions,
        address wantToken,
        address recipient,
        uint256 minAmountOut
    ) internal pure returns (bytes32 result) {
        bytes32 arrayOfBytesHash = _hashArrayOfBytes(actions);
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, ACTIONS_AND_SLIPPAGE_TYPEHASH)
            mstore(add(ptr, 0x20), arrayOfBytesHash)
            mstore(add(ptr, 0x40), wantToken)
            mstore(add(ptr, 0x60), recipient)
            mstore(add(ptr, 0x80), minAmountOut)
            result := keccak256(ptr, 0xa0)
        }
    }

    function executeMetaTxn(
        bytes[] calldata actions,
        address wantToken,
        address recipient,
        uint256 minAmountOut,
        bytes memory sig
    ) public {
        address msgSender = msg.sender;

        if (actions.length != 0) {
            (bytes4 action, bytes calldata data) = actions.decodeCall(0);

            // We force the first action to be a Permit2 witness transfer and validate the actions
            // against the signature

            if (action == ISettlerActions.METATXN_SETTLER_OTC_PERMIT2.selector) {
                if (actions.length != 1) {
                    (action, data) = actions.decodeCall(1);
                    revert ActionInvalid({i: 1, action: action, data: data});
                }
                // An optimized path involving a maker/taker in a single trade
                // The OTC order is signed by both maker and taker, validation is performed inside the OtcOrderSettlement
                // so there is no need to validate `sig` against `actions` here
                (
                    ISignatureTransfer.PermitBatchTransferFrom memory makerPermit,
                    address maker,
                    bytes memory makerSig,
                    ISignatureTransfer.PermitBatchTransferFrom memory takerPermit,
                    address taker,
                    bytes memory takerSig
                ) = abi.decode(
                    data,
                    (
                        ISignatureTransfer.PermitBatchTransferFrom,
                        address,
                        bytes,
                        ISignatureTransfer.PermitBatchTransferFrom,
                        address,
                        bytes
                    )
                );
                fillOtcOrderMetaTxn(makerPermit, maker, makerSig, takerPermit, taker, takerSig, recipient);
                return;
            } else if (action == ISettlerActions.METATXN_PERMIT2_TRANSFER_FROM.selector) {
                (ISignatureTransfer.PermitBatchTransferFrom memory permit, address from) =
                    abi.decode(data, (ISignatureTransfer.PermitBatchTransferFrom, address));
                (ISignatureTransfer.SignatureTransferDetails[] memory transferDetails,,) =
                    _permitToTransferDetails(permit, address(this));

                // Checking this witness ensures that the entire sequence of actions is
                // authorized.
                bytes32 witness = _hashActionsAndSlippage(actions, wantToken, recipient, minAmountOut);
                // `msgSender` becomes the metatransaction requestor (the taker of the
                // sequence of actions).
                msgSender = from;
                // We simultaneously transfer-in the taker's tokens and authenticate the
                // metatransaction.
                _permit2WitnessTransferFrom(
                    permit, transferDetails, msgSender, witness, ACTIONS_AND_SLIPPAGE_WITNESS, sig
                );
            } else {
                revert ActionInvalid({i: 0, action: action, data: data});
            }
        }

        for (uint256 i = 1; i < actions.length; i = i.unsafeInc()) {
            (bytes4 action, bytes calldata data) = actions.decodeCall(i);
            _dispatch(i, action, data, msgSender);
        }

        _checkSlippageAndTransfer(wantToken, recipient, minAmountOut);
    }

    function _dispatch(uint256 i, bytes4 action, bytes calldata data, address msgSender) internal {
        if (action == ISettlerActions.PERMIT2_TRANSFER_FROM.selector) {
            (ISignatureTransfer.PermitBatchTransferFrom memory permit, bytes memory sig) =
                abi.decode(data, (ISignatureTransfer.PermitBatchTransferFrom, bytes));
            (ISignatureTransfer.SignatureTransferDetails[] memory transferDetails,,) =
                _permitToTransferDetails(permit, address(this));
            _permit2TransferFrom(permit, transferDetails, msgSender, sig);
        } else if (action == ISettlerActions.SETTLER_OTC_SELF_FUNDED.selector) {
            (
                ISignatureTransfer.PermitTransferFrom memory permit,
                address maker,
                bytes memory sig,
                ERC20 takerToken,
                uint256 maxTakerAmount
            ) = abi.decode(data, (ISignatureTransfer.PermitTransferFrom, address, bytes, ERC20, uint256));

            fillOtcOrderSelfFunded(permit, maker, sig, takerToken, maxTakerAmount, msgSender);
        } else if (action == ISettlerActions.ZERO_EX_OTC.selector) {
            (IZeroEx.OtcOrder memory order, IZeroEx.Signature memory signature, uint256 sellAmount) =
                abi.decode(data, (IZeroEx.OtcOrder, IZeroEx.Signature, uint256));

            sellTokenForTokenToZeroExOTC(order, signature, sellAmount);
        } else if (action == ISettlerActions.UNISWAPV3_SWAP_EXACT_IN.selector) {
            (address recipient, uint256 amountIn, uint256 amountOutMin, bytes memory path) =
                abi.decode(data, (address, uint256, uint256, bytes));

            sellTokenForTokenToUniswapV3(path, amountIn, amountOutMin, recipient);
        } else if (action == ISettlerActions.UNISWAPV3_PERMIT2_SWAP_EXACT_IN.selector) {
            (address recipient, uint256 amountIn, uint256 amountOutMin, bytes memory path, bytes memory permit2Data) =
                abi.decode(data, (address, uint256, uint256, bytes, bytes));

            sellTokenForTokenToUniswapV3(path, amountIn, amountOutMin, recipient, permit2Data);
        } else if (action == ISettlerActions.CURVE_UINT256_EXCHANGE.selector) {
            (
                address pool,
                ERC20 sellToken,
                uint256 fromTokenIndex,
                uint256 toTokenIndex,
                uint256 sellAmount,
                uint256 minBuyAmount
            ) = abi.decode(data, (address, ERC20, uint256, uint256, uint256, uint256));

            sellTokenForTokenToCurve(pool, sellToken, fromTokenIndex, toTokenIndex, sellAmount, minBuyAmount);
        } else if (action == ISettlerActions.BASIC_SELL.selector) {
            (address pool, ERC20 sellToken, uint256 proportion, uint256 offset, bytes memory _data) =
                abi.decode(data, (address, ERC20, uint256, uint256, bytes));

            basicSellToPool(pool, sellToken, proportion, offset, _data);
        } else if (action == ISettlerActions.TRANSFER_OUT_FIXED.selector) {
            (ERC20 token, address recipient, uint256 amount) = abi.decode(data, (ERC20, address, uint256));
            token.safeTransfer(recipient, amount);
        } else if (action == ISettlerActions.TRANSFER_OUT_PROPORTIONAL.selector) {
            (ERC20 token, address recipient, uint256 bips) = abi.decode(data, (ERC20, address, uint256));
            require(bips <= 10_000, "Settler: can't transfer more than 10,000 bips");

            uint256 balance = token.balanceOf(address(this));
            uint256 amount = balance.unsafeMulDiv(bips, 10_000);
            token.safeTransfer(recipient, amount);
        } else if (action == ISettlerActions.TRANSFER_OUT_POSITIVE_SLIPPAGE.selector) {
            (ERC20 token, address recipient, uint256 expectedAmount) = abi.decode(data, (ERC20, address, uint256));
            uint256 balance = token.balanceOf(address(this));
            if (balance > expectedAmount) {
                unchecked {
                    token.safeTransfer(recipient, balance - expectedAmount);
                }
            }
        } else {
            revert ActionInvalid({i: i, action: action, data: data});
        }
    }
}
