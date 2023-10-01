// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {IZeroEx} from "./core/ZeroEx.sol";

interface ISettlerActions {
    // TODO: PERMIT2_TRANSFER_FROM and METATXN_PERMIT2_TRANSFER_FROM need custody optimization

    /// @dev Transfer funds from msg.sender to multiple destinations using Permit2.
    /// First element is the amount to transfer into Settler. Second element is the amount to transfer to fee recipient.
    function PERMIT2_TRANSFER_FROM(ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) external;

    /// @dev Transfer funds from `from` into the Settler contract using Permit2. Only for use in `Settler.executeMetaTxn`
    /// where the signature is provided as calldata
    function METATXN_PERMIT2_TRANSFER_FROM(ISignatureTransfer.PermitTransferFrom memory, address from) external;

    /// @dev Settle an OtcOrder between maker and taker transfering funds directly between the parties
    // Post-req: Payout if recipient != taker
    function SETTLER_OTC_PERMIT2(
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        address maker,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        bytes memory takerSig
    ) external;

    /// @dev Settle an OtcOrder between maker and taker transfering funds directly between the parties for the entire amount
    function METATXN_SETTLER_OTC_PERMIT2(
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        address maker,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        address taker,
        bytes memory takerSig
    ) external;

    // TODO: SETTLER_OTC_SELF_FUNDED needs custody optimization

    /// @dev Settle an OtcOrder between Maker and Settler. Transfering funds from the Settler contract to maker.
    /// Retaining funds in the settler contract.
    // Pre-req: Funded
    // Post-req: Payout
    function SETTLER_OTC_SELF_FUNDED(
        ISignatureTransfer.PermitTransferFrom memory permit,
        address maker,
        bytes memory sig,
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
        bytes memory permit2Data
    ) external;

    /// @dev Trades against UniswapV2 using the contracts balance for funding
    function UNISWAPV2_SWAP(address recipient, uint256 bips, bytes memory path) external;

    function POSITIVE_SLIPPAGE(address token, address recipient, uint256 expectedAmount) external;

    // @dev Fill a 0x V4 OTC order using the 0x Exchange Proxy contract
    // Pre-req: Funded
    // Post-req: Payout
    function ZERO_EX_OTC(IZeroEx.OtcOrder memory order, IZeroEx.Signature memory signature, uint256 sellAmount)
        external;

    /// @dev Trades against a basic AMM which follows the approval, transferFrom(msg.sender) interaction
    // Pre-req: Funded
    // Post-req: Payout
    function BASIC_SELL(address pool, address sellToken, uint256 bips, uint256 offset, bytes calldata data) external;
}
