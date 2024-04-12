// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

interface ISettlerActions {
    /// @dev Transfer funds from msg.sender Permit2.
    function PERMIT2_TRANSFER_FROM(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) external;

    /// @dev Transfer funds from metatransaction requestor into the Settler contract using Permit2. Only for use in `Settler.executeMetaTxn` where the signature is provided as calldata
    function METATXN_PERMIT2_TRANSFER_FROM(address recipient, ISignatureTransfer.PermitTransferFrom memory) external;

    /// @dev Settle an OtcOrder between maker and taker transfering funds directly between the parties
    // Post-req: Payout if recipient != taker
    function SETTLER_OTC_PERMIT2(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        address maker,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        bytes memory takerSig
    ) external;

    /// @dev Settle an OtcOrder between maker and taker transfering funds directly between the parties for the entire amount
    function METATXN_SETTLER_OTC_PERMIT2(
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
    function SETTLER_OTC_SELF_FUNDED(
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
    function UNISWAPV3_SWAP_EXACT_IN(address recipient, uint256 bips, uint256 amountOutMin, bytes memory path)
        external;

    /// @dev Trades against UniswapV3 using user funds via Permit2 for funding
    function UNISWAPV3_PERMIT2_SWAP_EXACT_IN(
        address recipient,
        uint256 amountIn,
        uint256 amountOutMin,
        bytes memory path,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) external;

    function MAKER_PSM_SELL_GEM(address recipient, uint256 bips, address psm, address gemToken) external;
    function MAKER_PSM_BUY_GEM(address recipient, uint256 bips, address psm, address gemToken) external;

    /// @dev Trades against UniswapV3 using user funds via Permit2 for funding. Metatransaction variant. Signature is over all actions.
    function METATXN_UNISWAPV3_PERMIT2_SWAP_EXACT_IN(
        address recipient,
        uint256 amountIn,
        uint256 amountOutMin,
        bytes memory path,
        ISignatureTransfer.PermitTransferFrom memory permit
    ) external;

    /// @dev Trades against UniswapV2 using the contracts balance for funding
    function UNISWAPV2_SWAP(
        address recipient,
        address sellToken,
        address pool,
        uint8 swapInfo,
        uint256 bips,
        uint256 amountOutMin
    ) external;

    function POSITIVE_SLIPPAGE(address recipient, address token, uint256 expectedAmount) external;

    /// @dev Trades against a basic AMM which follows the approval, transferFrom(msg.sender) interaction
    // Pre-req: Funded
    // Post-req: Payout
    function BASIC_SELL(address pool, address sellToken, uint256 bips, uint256 offset, bytes calldata data) external;
}
