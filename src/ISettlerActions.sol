// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {OtcOrderSettlement} from "./core/OtcOrderSettlement.sol";
import {IZeroEx} from "./core/ZeroEx.sol";

interface ISettlerActions {
    // TODO: PERMIT2_TRANSFER_FROM and METATXN_PERMIT2_TRANSFER_FROM need custody optimization

    /// @dev Transfer funds from msg.sender to multiple destinations using Permit2.
    /// First element is the amount to transfer into Settler. Second element is the amount to transfer to fee recipient.
    function PERMIT2_TRANSFER_FROM(ISignatureTransfer.PermitBatchTransferFrom memory permit, bytes memory sig)
        external;

    /// @dev Transfer funds from `from` into the Settler contract using Permit2. Only for use in `Settler.executeMetaTxn`
    /// where the signature is provided as calldata
    function METATXN_PERMIT2_TRANSFER_FROM(ISignatureTransfer.PermitBatchTransferFrom memory, address from) external;

    /// @dev Settle an OtcOrder between maker and taker transfering funds directly between the parties
    // Post-req: Payout if recipient != taker
    function SETTLER_OTC_PERMIT2(
        OtcOrderSettlement.OtcOrder memory order,
        ISignatureTransfer.PermitBatchTransferFrom memory makerPermit,
        bytes memory makerSig,
        ISignatureTransfer.PermitBatchTransferFrom memory takerPermit,
        bytes memory takerSig,
        uint128 takerTokenFillAmount,
        address recipient
    ) external;

    /// @dev Settle an OtcOrder between maker and taker transfering funds directly between the parties for the entire amount
    function METATXN_SETTLER_OTC_PERMIT2(
        OtcOrderSettlement.OtcOrder memory order,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        bytes memory takerSig,
        address recipient
    ) external;

    /// @dev Settle an OtcOrder between Maker and Settler. Transfering funds from the Settler contract to maker.
    /// Retaining funds in the settler contract.
    // Pre-req: Funded
    // Post-req: Payout
    function SETTLER_OTC_SELF_FUNDED(
        OtcOrderSettlement.OtcOrder memory order,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        bytes memory makerSig,
        uint128 takerTokenFillAmount
    ) external;

    /// @dev Trades against UniswapV3 using the contracts balance for funding
    // Pre-req: Funded
    // Post-req: Payout
    function UNISWAPV3_SWAP_EXACT_IN(address recipient, uint256 amountIn, uint256 amountOutMin, bytes memory path)
        external;

    /// @dev Trades against UniswapV3 using user funds via Permit2 for funding
    function UNISWAPV3_PERMIT2_SWAP_EXACT_IN(
        address recipient,
        uint256 amountIn,
        uint256 amountOutMin,
        bytes memory path,
        bytes memory permit2Data
    ) external;

    /// @dev Trades against Curve (uint256 variants) using the contracts balance for funding
    // Pre-req: Funded
    // Post-req: Payout
    function CURVE_UINT256_EXCHANGE(
        address pool,
        address sellToken,
        uint256 fromTokenIndex,
        uint256 toTokenIndex,
        uint256 sellAmount,
        uint256 minBuyAmount
    ) external;

    /// @dev Transfers out an amount of the token to recipient. This amount amount can be partial
    /// and the divisor is 10_000. E.g 10_000 represents 100%, 5_000 represents 50%.
    function TRANSFER_OUT(address token, address recipient, uint256 bips) external;

    // @dev Fill a 0x V4 OTC order using the 0x Exchange Proxy contract
    // Pre-req: Funded
    // Post-req: Payout
    function ZERO_EX_OTC(IZeroEx.OtcOrder memory order, IZeroEx.Signature memory signature, uint256 sellAmount)
        external;

    /// @dev Trades against a basic AMM which follows the approval, transferFrom(msg.sender) interaction
    // Pre-req: Funded
    // Post-req: Payout
    function BASIC_SELL(
        address pool,
        address sellToken,
        address buyToken,
        uint256 proportion,
        uint256 offset,
        bytes calldata data
    ) external;
}
