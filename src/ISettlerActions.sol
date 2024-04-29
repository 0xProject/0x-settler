// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

interface ISettlerActions {
    /// @dev Transfer funds from msg.sender Permit2.
    function TRANSFER_FROM(address recipient, ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig)
        external;

    /// @dev Transfer funds from metatransaction requestor into the Settler contract using Permit2. Only for use in `Settler.executeMetaTxn` where the signature is provided as calldata
    function METATXN_TRANSFER_FROM(address recipient, ISignatureTransfer.PermitTransferFrom memory permit) external;

    /// @dev Settle an OtcOrder between maker and taker transfering funds directly between the parties
    // Post-req: Payout if recipient != taker
    function OTC_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        address maker,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        bytes memory takerSig
    ) external;

    /// @dev Settle an OtcOrder between maker and taker transfering funds directly between the parties for the entire amount
    function METATXN_OTC_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        address maker,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit
    ) external;

    /// @dev Settle an OtcOrder between Maker and Settler. Transfering funds from the Settler contract to maker.
    /// Retaining funds in the settler contract.
    // Pre-req: Funded
    // Post-req: Payout
    function OTC(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        address maker,
        bytes memory makerSig,
        address takerToken,
        uint256 maxTakerAmount
    ) external;

    /// @dev Trades against UniswapV3 using the contracts balance for funding
    // Pre-req: Funded
    // Post-req: Payout
    function UNISWAPV3(address recipient, uint256 bps, uint256 amountOutMin, bytes memory path) external;

    /// @dev Trades against UniswapV3 using user funds via Permit2 for funding
    function UNISWAPV3_VIP(
        address recipient,
        uint256 amountOutMin,
        bytes memory path,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) external;

    function MAKERPSM_SELL(address recipient, uint256 bps, address psm, address gemToken) external;
    function MAKERPSM_BUY(address recipient, uint256 bps, address psm, address gemToken) external;

    function CURVE_TRICRYPTO(address recipient, address sellToken, uint80 poolInfo, uint256 bps, uint256 minBuyAmount)
        external;
    function CURVE_TRICRYPTO_VIP(
        address recipient,
        uint80 poolInfo,
        uint256 minBuyAmount,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) external;
    function METATXN_CURVE_TRICRYPTO_VIP(
        address recipient,
        uint80 poolInfo,
        uint256 minBuyAmount,
        ISignatureTransfer.PermitTransferFrom memory permit
    ) external;

    function SOLIDLYV3(address recipient, uint256 bps, uint256 amountOutMin, bytes memory path) external;
    function SOLIDLYV3_VIP(
        address recipient,
        uint256 amountOutMin,
        bytes memory path,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) external;
    function METATXN_SOLIDLYV3_VIP(
        address recipient,
        uint256 amountOutMin,
        bytes memory path,
        ISignatureTransfer.PermitTransferFrom memory permit
    ) external;

    function PANCAKESWAPV3(address recipient, uint256 bps, uint256 amountOutMin, bytes memory path) external;
    function PANCAKESWAPV3_VIP(
        address recipient,
        uint256 amountOutMin,
        bytes memory path,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) external;
    function METATXN_PANCAKESWAPV3_VIP(
        address recipient,
        uint256 amountOutMin,
        bytes memory path,
        ISignatureTransfer.PermitTransferFrom memory permit
    ) external;

    /// @dev Trades against UniswapV3 using user funds via Permit2 for funding. Metatransaction variant. Signature is over all actions.
    function METATXN_UNISWAPV3_VIP(
        address recipient,
        uint256 amountOutMin,
        bytes memory path,
        ISignatureTransfer.PermitTransferFrom memory permit
    ) external;

    /// @dev Trades against UniswapV2 using the contracts balance for funding
    function UNISWAPV2(
        address recipient,
        address sellToken,
        address pool,
        uint8 swapInfo,
        uint256 bps,
        uint256 amountOutMin
    ) external;

    function POSITIVE_SLIPPAGE(address recipient, address token, uint256 expectedAmount) external;

    /// @dev Trades against a basic AMM which follows the approval, transferFrom(msg.sender) interaction
    // Pre-req: Funded
    // Post-req: Payout
    function BASIC(address pool, address sellToken, uint256 bps, uint256 offset, bytes calldata data) external;
}
