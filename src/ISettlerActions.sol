// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

interface ISettlerActions {
    /// @dev Transfer funds from msg.sender Permit2.
    function TRANSFER_FROM(address recipient, ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig)
        external;

    /// @dev Transfer funds from metatransaction requestor into the Settler contract using Permit2. Only for use in `Settler.executeMetaTxn` where the signature is provided as calldata
    function METATXN_TRANSFER_FROM(address recipient, ISignatureTransfer.PermitTransferFrom memory permit) external;

    /// @dev Settle an RfqOrder between maker and taker transfering funds directly between the parties
    // Post-req: Payout if recipient != taker
    function RFQ_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        address maker,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        bytes memory takerSig
    ) external;

    /// @dev Settle an RfqOrder between maker and taker transfering funds directly between the parties for the entire amount
    function METATXN_RFQ_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        address maker,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit
    ) external;

    /// @dev Settle an RfqOrder between Maker and Settler. Transfering funds from the Settler contract to maker.
    /// Retaining funds in the settler contract.
    // Pre-req: Funded
    // Post-req: Payout
    function RFQ(
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
    function UNISWAPV3(address recipient, uint256 bps, bytes memory path, uint256 amountOutMin) external;

    /// @dev Trades against UniswapV3 using user funds via Permit2 for funding
    function UNISWAPV3_VIP(
        address recipient,
        bytes memory path,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig,
        uint256 amountOutMin
    ) external;

    function MAKERPSM_SELL(address recipient, address gemToken, uint256 bps, address psm) external;
    function MAKERPSM_BUY(address recipient, address gemToken, uint256 bps, address psm) external;

    function CURVE_TRICRYPTO_VIP(
        address recipient,
        uint80 poolInfo,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig,
        uint256 minBuyAmount
    ) external;
    function METATXN_CURVE_TRICRYPTO_VIP(
        address recipient,
        uint80 poolInfo,
        ISignatureTransfer.PermitTransferFrom memory permit,
        uint256 minBuyAmount
    ) external;

    function DODOV1(address sellToken, uint256 bps, address pool, bool baseNotQuote, uint256 minBuyAmount) external;
    function DODOV1_VIP(
        uint64 deployerNonce,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig,
        bool baseNotQuote,
        uint256 minBuyAmount
    ) external;
    function METATXN_DODOV1_VIP(
        uint64 deployerNonce,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bool baseNotQuote,
        uint256 minBuyAmount
    ) external;

    /// @dev Trades against UniswapV3 using user funds via Permit2 for funding. Metatransaction variant. Signature is over all actions.
    function METATXN_UNISWAPV3_VIP(
        address recipient,
        bytes memory path,
        ISignatureTransfer.PermitTransferFrom memory permit,
        uint256 amountOutMin
    ) external;

    /// @dev Trades against UniswapV2 using the contracts balance for funding
    function UNISWAPV2(
        address recipient,
        address sellToken,
        uint256 bps,
        address pool,
        uint8 swapInfo,
        uint256 amountOutMin
    ) external;

    function POSITIVE_SLIPPAGE(address recipient, address token, uint256 expectedAmount) external;

    /// @dev Trades against a basic AMM which follows the approval, transferFrom(msg.sender) interaction
    // Pre-req: Funded
    // Post-req: Payout
    function BASIC(address sellToken, uint256 bps, address pool, uint256 offset, bytes calldata data) external;
}
