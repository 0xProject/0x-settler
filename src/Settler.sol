// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ERC20} from "solmate/src/tokens/ERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {Basic} from "./core/Basic.sol";
import {CurveV2} from "./core/CurveV2.sol";
import {OtcOrderSettlement} from "./core/OtcOrderSettlement.sol";
import {UniswapV3} from "./core/UniswapV3.sol";
import {IZeroEx, ZeroEx} from "./core/ZeroEx.sol";

import {Permit2Payment} from "./core/Permit2Payment.sol";
import {SafeTransferLib} from "./utils/SafeTransferLib.sol";

import {ISettlerActions} from "./ISettlerActions.sol";

contract Settler is Basic, OtcOrderSettlement, UniswapV3, Permit2Payment, CurveV2, ZeroEx {
    using SafeTransferLib for ERC20;

    error ActionInvalid(bytes4 action, bytes data);
    error ActionFailed(bytes4 action, bytes data, bytes output);
    error LengthMismatch();

    // Permit2 Witness for meta transactions
    string internal constant ACTIONS_AND_SLIPPAGE_TYPE_STRING =
        "ActionsAndSlippage(bytes[] actions,address wantToken,uint256 minAmountOut)";
    // `string.concat` isn't recognized by solc as compile-time constant, but `abi.encodePacked` is
    string internal constant METATXN_TYPE_STRING = string(
        abi.encodePacked(
            "ActionsAndSlippage actionsAndSlippage)", ACTIONS_AND_SLIPPAGE_TYPE_STRING, TOKEN_PERMISSIONS_TYPE_STRING
        )
    );
    bytes32 internal constant ACTIONS_AND_SLIPPAGE_TYPEHASH =
        0x740ff4b4bedfa7438eba5fd36b723b10e5b2d4781deb32a7c62bfa2c00dd9034;

    bytes4 internal constant SLIPPAGE_ACTION = bytes4(keccak256("SLIPPAGE(address,uint256)"));

    /// @dev The highest bit of a uint256 value.
    uint256 private constant HIGH_BIT = 2 ** 255;
    /// @dev Mask of the lower 255 bits of a uint256 value.
    uint256 private constant LOWER_255_BITS = HIGH_BIT - 1;

    constructor(address permit2, address zeroEx, address uniFactory, bytes32 poolInitCodeHash, address trustedForwarder)
        Basic(permit2)
        CurveV2()
        OtcOrderSettlement(permit2, trustedForwarder)
        Permit2Payment(permit2)
        UniswapV3(uniFactory, poolInitCodeHash, permit2)
        ZeroEx(zeroEx)
    {
        assert(ACTIONS_AND_SLIPPAGE_TYPEHASH == keccak256(bytes(ACTIONS_AND_SLIPPAGE_TYPE_STRING)));
    }

    function execute(bytes[] calldata actions, address wantToken, uint256 minAmountOut) public payable {
        for (uint256 i = 0; i < actions.length;) {
            bytes4 action = bytes4(actions[i][0:4]);
            bytes calldata data = actions[i][4:];

            (bool success, bytes memory output) = _dispatch(action, data, _msgSender());
            if (!success) {
                revert ActionFailed({action: action, data: data, output: output});
            }
            unchecked {
                i++;
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
                    action: SLIPPAGE_ACTION,
                    data: abi.encode(wantToken, minAmountOut),
                    output: abi.encode(amountOut)
                });
            }
            ERC20(wantToken).safeTransfer(_msgSender(), amountOut);
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
            mstore(add(ptr, 0x40), and(ADDRESS_MASK, wantToken))
            mstore(add(ptr, 0x60), minAmountOut)
            result := keccak256(ptr, 0x80)
        }
    }

    function executeMetaTxn(bytes[] calldata actions, address wantToken, uint256 minAmountOut, bytes memory sig)
        public
    {
        address msgSender = _msgSender();

        for (uint256 i = 0; i < actions.length;) {
            bytes4 action = bytes4(actions[i][0:4]);
            bytes calldata data = actions[i][4:];

            if (i == 0) {
                // We force the first action to be a Permit2 witness transfer and validate the actions
                // against the signature
                if (
                    action != ISettlerActions.METATXN_PERMIT2_WITNESS_TRANSFER_FROM.selector
                        && action != ISettlerActions.METATXN_SETTLER_OTC.selector
                ) {
                    revert ActionInvalid({action: action, data: data});
                }

                if (action == ISettlerActions.METATXN_SETTLER_OTC.selector) {
                    // An optimized path involving a maker/taker in a single trade
                    // The OTC order is signed by both maker and taker, validation is performed inside the OtcOrderSettlement
                    // so there is no need to validate `sig` against `actions` here
                    (
                        OtcOrder memory order,
                        ISignatureTransfer.PermitTransferFrom memory makerPermit,
                        bytes memory makerSig,
                        ISignatureTransfer.PermitTransferFrom memory takerPermit,
                        bytes memory takerSig
                    ) = abi.decode(
                        data,
                        (
                            OtcOrder,
                            ISignatureTransfer.PermitTransferFrom,
                            bytes,
                            ISignatureTransfer.PermitTransferFrom,
                            bytes
                        )
                    );
                    fillOtcOrderMetaTxn(order, makerPermit, makerSig, takerPermit, takerSig);
                    return;
                }

                // METATXN_PERMIT2_WITNESS_TRANSFER_FROM
                (ISignatureTransfer.PermitTransferFrom memory permit, address from) =
                    abi.decode(data, (ISignatureTransfer.PermitTransferFrom, address));
                ISignatureTransfer.SignatureTransferDetails memory transferDetails = ISignatureTransfer
                    .SignatureTransferDetails({to: address(this), requestedAmount: permit.permitted.amount});

                // Now that the actions have been validated and signed by `from` we can safely assign
                // msgSender
                permit2WitnessTransferFrom(
                    permit,
                    transferDetails,
                    msgSender = from,
                    sig,
                    _hashActionsAndSlippage(actions, wantToken, minAmountOut),
                    METATXN_TYPE_STRING
                );
            } else {
                (bool success, bytes memory output) = _dispatch(action, data, msgSender);
                if (!success) {
                    revert ActionFailed({action: action, data: data, output: output});
                }
            }

            unchecked {
                i++;
            }
        }

        if (wantToken != address(0) || minAmountOut != 0) {
            uint256 amountOut = ERC20(wantToken).balanceOf(address(this));
            if (amountOut < minAmountOut) {
                revert ActionFailed({
                    action: SLIPPAGE_ACTION,
                    data: abi.encode(wantToken, minAmountOut),
                    output: abi.encode(amountOut)
                });
            }
            ERC20(wantToken).safeTransfer(msgSender, amountOut);
        }
    }

    function _dispatch(bytes4 action, bytes calldata data, address msgSender)
        internal
        returns (bool success, bytes memory output)
    {
        success = true;

        // This can only be performed and validated in `executeMetaTxn`
        if (action == ISettlerActions.METATXN_PERMIT2_WITNESS_TRANSFER_FROM.selector) {
            revert ActionFailed({action: action, data: data, output: new bytes(0)});
        }

        if (action == ISettlerActions.PERMIT2_TRANSFER_FROM.selector) {
            (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) =
                abi.decode(data, (ISignatureTransfer.PermitTransferFrom, bytes));
            // Consume the entire Permit with the recipient of funds as this contract
            ISignatureTransfer.SignatureTransferDetails memory transferDetails = ISignatureTransfer
                .SignatureTransferDetails({to: address(this), requestedAmount: permit.permitted.amount});

            permit2TransferFrom(permit, transferDetails, msgSender, sig);
        } else if (action == ISettlerActions.PERMIT2_BATCH_TRANSFER_FROM.selector) {
            (ISignatureTransfer.PermitBatchTransferFrom memory permit, bytes memory sig) =
                abi.decode(data, (ISignatureTransfer.PermitBatchTransferFrom, bytes));
            require(permit.permitted.length <= 2, "Invalid Batch Permit2");
            // First item is this contract
            ISignatureTransfer.SignatureTransferDetails[] memory transferDetails =
                new ISignatureTransfer.SignatureTransferDetails[](permit.permitted.length);
            transferDetails[0] = ISignatureTransfer.SignatureTransferDetails({
                to: address(this),
                requestedAmount: permit.permitted[0].amount
            });
            if (permit.permitted.length > 1) {
                // TODO fee recipient
                transferDetails[1] = ISignatureTransfer.SignatureTransferDetails({
                    to: 0x2222222222222222222222222222222222222222,
                    requestedAmount: permit.permitted[1].amount
                });
            }
            permit2TransferFrom(permit, transferDetails, msgSender, sig);
        } else if (action == ISettlerActions.SETTLER_OTC.selector) {
            (
                OtcOrder memory order,
                ISignatureTransfer.PermitTransferFrom memory makerPermit,
                bytes memory makerSig,
                ISignatureTransfer.PermitTransferFrom memory takerPermit,
                bytes memory takerSig,
                uint128 takerTokenFillAmount,
                address recipient
            ) = abi.decode(
                data,
                (
                    OtcOrder,
                    ISignatureTransfer.PermitTransferFrom,
                    bytes,
                    ISignatureTransfer.PermitTransferFrom,
                    bytes,
                    uint128,
                    address
                )
            );

            /**
             * UNSAFE: recipient/spender mismatch and can be influenced
             *             Ensure the tx.origin is a counterparty to this order. This ensures Mallory cannot
             *             take an OTC order between Alice and Bob and send the funds to herself.
             */
            // TODO this can be handled in OtcOrderSettlement
            require(order.txOrigin == tx.origin || order.taker == msgSender, "Settler: txOrigin mismatch");
            fillOtcOrder(
                order, makerPermit, makerSig, takerPermit, takerSig, msgSender, takerTokenFillAmount, recipient
            );
        } else if (action == ISettlerActions.SETTLER_OTC_BATCH_PERMIT2.selector) {
            (
                OtcOrder memory order,
                ISignatureTransfer.PermitBatchTransferFrom memory makerPermit,
                bytes memory makerSig,
                ISignatureTransfer.PermitBatchTransferFrom memory takerPermit,
                bytes memory takerSig,
                uint128 takerTokenFillAmount,
                address recipient
            ) = abi.decode(
                data,
                (
                    OtcOrder,
                    ISignatureTransfer.PermitBatchTransferFrom,
                    bytes,
                    ISignatureTransfer.PermitBatchTransferFrom,
                    bytes,
                    uint128,
                    address
                )
            );

            /**
             * UNSAFE: recipient/spender mismatch and can be influenced
             *             Ensure the tx.origin is a counterparty to this order. This ensures Mallory cannot
             *             take an OTC order between Alice and Bob and send the funds to herself.
             */
            // TODO this can be handled in OtcOrderSettlement
            require(order.txOrigin == tx.origin || order.taker == msgSender, "Settler: txOrigin mismatch");
            fillOtcOrder(
                order, makerPermit, makerSig, takerPermit, takerSig, msgSender, takerTokenFillAmount, recipient
            );
        } else if (action == ISettlerActions.SETTLER_OTC_SELF_FUNDED.selector) {
            (
                OtcOrder memory order,
                ISignatureTransfer.PermitTransferFrom memory makerPermit,
                bytes memory makerSig,
                uint128 takerTokenFillAmount
            ) = abi.decode(data, (OtcOrder, ISignatureTransfer.PermitTransferFrom, bytes, uint128));
            fillOtcOrderSelfFunded(order, makerPermit, makerSig, takerTokenFillAmount);
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
            revert ActionInvalid({action: action, data: data});
        }
    }
}
