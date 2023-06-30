// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

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
    string internal constant METATXN_TYPE_STRING = "bytes[] actions)TokenPermissions(address token,uint256 amount)";

    /// @dev The highest bit of a uint256 value.
    uint256 private constant HIGH_BIT = 2 ** 255;
    /// @dev Mask of the lower 255 bits of a uint256 value.
    uint256 private constant LOWER_255_BITS = HIGH_BIT - 1;

    constructor(address permit2, address zeroEx, address uniFactory, bytes32 poolInitCodeHash)
        CurveV2()
        OtcOrderSettlement(permit2)
        Permit2Payment(permit2)
        UniswapV3(uniFactory, poolInitCodeHash, permit2)
        ZeroEx(zeroEx)
    {}

    function execute(bytes[] calldata actions) public payable {
        bool success;
        bytes memory output;

        for (uint256 i = 0; i < actions.length;) {
            bytes4 action = bytes4(actions[i][0:4]);
            bytes calldata data = actions[i][4:];

            (success, output) = dispatch(action, data, msg.sender);
            if (!success) {
                revert ActionFailed({action: action, data: data, output: output});
            }
            unchecked {
                i++;
            }
        }
    }

    function executeMetaTxn(bytes[] calldata actions, bytes memory sig) public {
        bool success;
        bytes memory output;

        address msgSender = msg.sender;

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
                bytes32 witness = keccak256(abi.encode(actions));

                // Now that the actions have been validated and signed by `from` we can safely assign
                // msgSender
                msgSender = from;
                permit2WitnessTransferFrom(permit, transferDetails, from, sig, witness, METATXN_TYPE_STRING);
            } else {
                (success, output) = dispatch(action, data, msgSender);
                if (!success) {
                    revert ActionFailed({action: action, data: data, output: output});
                }
            }

            unchecked {
                i++;
            }
        }
    }

    function dispatch(bytes4 action, bytes calldata data, address msgSender)
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
