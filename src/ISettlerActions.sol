// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {OtcOrderSettlement} from "./core/OtcOrderSettlement.sol";
import {IZeroEx} from "./core/ZeroEx.sol";

interface ISettlerActions {
    /// @dev Uses Permit2 with a signed payload from msg.sender to transfer funds from the user into the Settler contract
    function PERMIT2_TRANSFER_FROM(ISignatureTransfer.PermitTransferFrom memory, bytes memory) external;
    function PERMIT2_WITNESS_TRANSFER_FROM(ISignatureTransfer.PermitTransferFrom memory, address) external;
    /// @dev Settle an OtcOrder between maker and taker transfering funds directly between the parties
    function SETTLER_OTC(
        OtcOrderSettlement.OtcOrder memory order,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        bytes memory takerSig,
        uint128 takerTokenFillAmount
    ) external;
    /// @dev Trades against UniswapV3 using the contracts balance for funding
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
    function ZERO_EX_OTC(IZeroEx.OtcOrder memory order, IZeroEx.Signature memory signature, uint256 sellAmount)
        external;
}
