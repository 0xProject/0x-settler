// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {UniswapV3ForkBase} from "./UniswapV3ForkBase.sol";

interface IPancakeSwapV3Callback {
    function pancakeV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external;
}

abstract contract PancakeSwapV3 is UniswapV3ForkBase {
    address private constant _PANCAKESWAPV3_FACTORY = 0x41ff9AA7e16B8B1a8a8dc4f0eFacd93D02d071c9;
    bytes32 private constant _PANCAKESWAPV3_INITHASH =
        0x6ce8eb472fa82df5469c6ab6d485f17c3ad13c8cd7af59b3d4a8026c5ce0f7e2;

    /// see sellToUniswapV3Fork
    function sellToPancakeSwapV3(address recipient, bytes memory encodedPath, uint256 bps, uint256 minBuyAmount)
        internal
        returns (uint256 buyAmount)
    {
        return sellToUniswapV3Fork(
            _PANCAKESWAPV3_FACTORY,
            _PANCAKESWAPV3_INITHASH,
            recipient,
            encodedPath,
            bps,
            minBuyAmount,
            IPancakeSwapV3Callback.pancakeV3SwapCallback.selector
        );
    }

    /// see sellToUniswapV3ForkVIP
    function sellToPancakeSwapV3VIP(
        address recipient,
        bytes memory encodedPath,
        uint256 minBuyAmount,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) internal returns (uint256 buyAmount) {
        return sellToUniswapV3ForkVIP(
            _PANCAKESWAPV3_FACTORY,
            _PANCAKESWAPV3_INITHASH,
            recipient,
            encodedPath,
            minBuyAmount,
            permit,
            sig,
            IPancakeSwapV3Callback.pancakeV3SwapCallback.selector
        );
    }

    /// see sellToUniswapV3ForkMetaTxn
    function sellToPancakeSwapV3MetaTxn(
        address recipient,
        bytes memory encodedPath,
        uint256 minBuyAmount,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) internal returns (uint256 buyAmount) {
        return sellToUniswapV3ForkMetaTxn(
            _PANCAKESWAPV3_FACTORY,
            _PANCAKESWAPV3_INITHASH,
            recipient,
            encodedPath,
            minBuyAmount,
            permit,
            sig,
            IPancakeSwapV3Callback.pancakeV3SwapCallback.selector
        );
    }
}
