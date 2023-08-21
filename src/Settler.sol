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

import {ISettlerActions} from "./ISettlerActions.sol";

library UnsafeMath {
    function unsafeInc(uint256 i) internal pure returns (uint256) {
        unchecked {
            return i + 1;
        }
    }
}

contract Settler is Basic, OtcOrderSettlement, UniswapV3, CurveV2, ZeroEx {
    using SafeTransferLib for ERC20;
    using UnsafeMath for uint256;

    error ActionInvalid(uint256 i, bytes4 action, bytes data);
    error ActionFailed(uint256 i, bytes4 action, bytes data, bytes output);

    // Permit2 Witness for meta transactions
    string internal constant ACTIONS_AND_SLIPPAGE_TYPE =
        "ActionsAndSlippage(bytes[] actions,address wantToken,uint256 minAmountOut)";
    // `string.concat` isn't recognized by solc as compile-time constant, but `abi.encodePacked` is
    string internal constant ACTIONS_AND_SLIPPAGE_WITNESS = string(
        abi.encodePacked("ActionsAndSlippage actionsAndSlippage)", ACTIONS_AND_SLIPPAGE_TYPE, TOKEN_PERMISSIONS_TYPE)
    );
    bytes32 internal constant ACTIONS_AND_SLIPPAGE_TYPEHASH =
        0x740ff4b4bedfa7438eba5fd36b723b10e5b2d4781deb32a7c62bfa2c00dd9034;

    bytes4 internal constant SLIPPAGE_ACTION = bytes4(keccak256("SLIPPAGE(address,uint256)"));

    /// @dev The highest bit of a uint256 value.
    uint256 private constant HIGH_BIT = 2 ** 255;
    /// @dev Mask of the lower 255 bits of a uint256 value.
    uint256 private constant LOWER_255_BITS = HIGH_BIT - 1;

    constructor(address permit2, address zeroEx, address uniFactory, bytes32 poolInitCodeHash)
        Basic(permit2)
        CurveV2()
        OtcOrderSettlement(permit2)
        UniswapV3(uniFactory, poolInitCodeHash, permit2)
        ZeroEx(zeroEx)
    {
        assert(ACTIONS_AND_SLIPPAGE_TYPEHASH == keccak256(bytes(ACTIONS_AND_SLIPPAGE_TYPE)));
    }

    function execute(bytes[] calldata actions, address wantToken, uint256 minAmountOut) public payable {
        {
            bytes4 action = bytes4(actions[0][0:4]);
            bytes calldata data = actions[0][4:];
            if (action == ISettlerActions.SETTLER_OTC_PERMIT2.selector) {
                if (actions.length > 1) {
                    revert ActionInvalid({i: 1, action: bytes4(actions[1][0:4]), data: actions[1][4:]});
                }
                (
                    ISignatureTransfer.PermitBatchTransferFrom memory makerPermit,
                    address maker,
                    bytes memory makerSig,
                    ISignatureTransfer.PermitBatchTransferFrom memory takerPermit,
                    bytes memory takerSig,
                    uint128 takerTokenFillAmount,
                    address recipient
                ) = abi.decode(
                    data,
                    (
                        ISignatureTransfer.PermitBatchTransferFrom,
                        address,
                        bytes,
                        ISignatureTransfer.PermitBatchTransferFrom,
                        bytes,
                        uint128,
                        address
                    )
                );
                fillOtcOrder(makerPermit, maker, makerSig, takerPermit, takerSig, takerTokenFillAmount, recipient);
                return;
            } else {
                (bool success, bytes memory output) = _dispatch(0, action, data, msg.sender);
                if (!success) {
                    revert ActionFailed({i: 0, action: action, data: data, output: output});
                }
            }
        }

        for (uint256 i = 1; i < actions.length; i = i.unsafeInc()) {
            bytes4 action = bytes4(actions[i][0:4]);
            bytes calldata data = actions[i][4:];

            (bool success, bytes memory output) = _dispatch(i, action, data, msg.sender);
            if (!success) {
                revert ActionFailed({i: i, action: action, data: data, output: output});
            }
        }

        // This final slippage check effectively prohibits custody optimization on the
        // final hop of every swap. This is gas-inefficient. This is on purpose. Because
        // ISettlerActions.BASIC_SELL could interaction with an intents-based settlement
        // mechanism, we must ensure that the user's want token increase is coming
        // directly from us instead of from some other form of exchange of value.
        if (wantToken != address(0) || minAmountOut != 0) {
            uint256 amountOut = ERC20(wantToken).balanceOf(address(this));
            if (amountOut < minAmountOut) {
                revert ActionFailed({
                    i: type(uint256).max,
                    action: SLIPPAGE_ACTION,
                    data: abi.encode(wantToken, minAmountOut),
                    output: abi.encode(amountOut)
                });
            }
            ERC20(wantToken).safeTransfer(msg.sender, amountOut);
        }
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

    function _hashActionsAndSlippage(bytes[] calldata actions, address wantToken, uint256 minAmountOut)
        internal
        pure
        returns (bytes32 result)
    {
        bytes32 arrayOfBytesHash = _hashArrayOfBytes(actions);
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, ACTIONS_AND_SLIPPAGE_TYPEHASH)
            mstore(add(ptr, 0x20), arrayOfBytesHash)
            mstore(add(ptr, 0x40), wantToken)
            mstore(add(ptr, 0x60), minAmountOut)
            result := keccak256(ptr, 0x80)
        }
    }

    function executeMetaTxn(bytes[] calldata actions, address wantToken, uint256 minAmountOut, bytes memory sig)
        public
    {
        address msgSender = msg.sender;

        {
            bytes4 action = bytes4(actions[0][0:4]);
            bytes calldata data = actions[0][4:];

            // We force the first action to be a Permit2 witness transfer and validate the actions
            // against the signature

            if (action == ISettlerActions.METATXN_SETTLER_OTC_PERMIT2.selector) {
                if (actions.length > 1) {
                    revert ActionInvalid({i: 1, action: bytes4(actions[1][0:4]), data: actions[1][4:]});
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
                    bytes memory takerSig,
                    address recipient
                ) = abi.decode(
                    data,
                    (
                        ISignatureTransfer.PermitBatchTransferFrom,
                        address,
                        bytes,
                        ISignatureTransfer.PermitBatchTransferFrom,
                        address,
                        bytes,
                        address
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
                bytes32 witness = _hashActionsAndSlippage(actions, wantToken, minAmountOut);
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
            bytes4 action = bytes4(actions[i][0:4]);
            bytes calldata data = actions[i][4:];

            (bool success, bytes memory output) = _dispatch(i, action, data, msgSender);
            if (!success) {
                revert ActionFailed({i: i, action: action, data: data, output: output});
            }
        }

        if (wantToken != address(0) || minAmountOut != 0) {
            uint256 amountOut = ERC20(wantToken).balanceOf(address(this));
            if (amountOut < minAmountOut) {
                revert ActionFailed({
                    i: type(uint256).max,
                    action: SLIPPAGE_ACTION,
                    data: abi.encode(wantToken, minAmountOut),
                    output: abi.encode(amountOut)
                });
            }
            ERC20(wantToken).safeTransfer(msgSender, amountOut);
        }
    }

    function _dispatch(uint256 i, bytes4 action, bytes calldata data, address msgSender)
        internal
        returns (bool success, bytes memory output)
    {
        success = true;

        if (action == ISettlerActions.PERMIT2_TRANSFER_FROM.selector) {
            (ISignatureTransfer.PermitBatchTransferFrom memory permit, bytes memory sig) =
                abi.decode(data, (ISignatureTransfer.PermitBatchTransferFrom, bytes));
            (ISignatureTransfer.SignatureTransferDetails[] memory transferDetails,,) =
                _permitToTransferDetails(permit, address(this));
            _permit2TransferFrom(permit, transferDetails, msgSender, sig);
        } else if (action == ISettlerActions.SETTLER_OTC_SELF_FUNDED.selector) {
            (
                ISignatureTransfer.PermitBatchTransferFrom memory permit,
                address maker,
                bytes memory sig,
                address takerToken,
                uint256 maxTakerAmount
            ) = abi.decode(data, (ISignatureTransfer.PermitBatchTransferFrom, address, bytes, address, uint256));
            fillOtcOrderSelfFunded(
                permit, maker, sig, takerToken, maxTakerAmount, ERC20(takerToken).balanceOf(address(this)), msgSender
            );
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
                address sellToken,
                uint256 fromTokenIndex,
                uint256 toTokenIndex,
                uint256 sellAmount,
                uint256 minBuyAmount
            ) = abi.decode(data, (address, address, uint256, uint256, uint256, uint256));

            sellTokenForTokenToCurve(pool, ERC20(sellToken), fromTokenIndex, toTokenIndex, sellAmount, minBuyAmount);
        } else if (action == ISettlerActions.BASIC_SELL.selector) {
            (address pool, ERC20 sellToken, ERC20 buyToken, uint256 proportion, uint256 offset, bytes memory data) =
                abi.decode(data, (address, ERC20, ERC20, uint256, uint256, bytes));
            basicSellToPool(pool, sellToken, buyToken, proportion, offset, data);
        } else if (action == ISettlerActions.TRANSFER_OUT.selector) {
            (address token, address recipient, uint256 bips) = abi.decode(data, (address, address, uint256));
            uint256 balance = ERC20(token).balanceOf(address(this));
            uint256 amount = (balance * bips) / 10_000;
            ERC20(token).safeTransfer(recipient, amount);
        } else {
            revert ActionInvalid({i: i, action: action, data: data});
        }
    }
}
