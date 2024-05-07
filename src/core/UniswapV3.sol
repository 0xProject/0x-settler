// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {UniswapV3ForkBase} from "./UniswapV3ForkBase.sol";

interface IUniswapV3Callback {
    function uniswapV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external;
}

abstract contract UniswapV3 is UniswapV3ForkBase {
    /// @dev UniswapV3 Factory contract address
    address private immutable _UNISWAPV3_FACTORY;
    /// @dev UniswapV3 pool init code hash.
    bytes32 private constant _UNISWAPV3_INITHASH = 0xe34f199b19b2b4f47f68442619d555527d244f78a3297ea89325f843f87b8b54;

    constructor(address uniFactory) {
        _UNISWAPV3_FACTORY = uniFactory;
    }

    /// see sellToUniswapV3Fork
    function sellToUniswapV3(address recipient, bytes memory encodedPath, uint256 bps, uint256 minBuyAmount)
        internal
        returns (uint256 buyAmount)
    {
        return sellToUniswapV3Fork(
            _UNISWAPV3_FACTORY,
            _UNISWAPV3_INITHASH,
            recipient,
            encodedPath,
            bps,
            minBuyAmount,
            IUniswapV3Callback.uniswapV3SwapCallback.selector
        );
    }

    /// see sellToUniswapV3ForkVIP
    function sellToUniswapV3VIP(
        address recipient,
        bytes memory encodedPath,
        uint256 minBuyAmount,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) internal returns (uint256 buyAmount) {
        return sellToUniswapV3ForkVIP(
            _UNISWAPV3_FACTORY,
            _UNISWAPV3_INITHASH,
            recipient,
            encodedPath,
            minBuyAmount,
            permit,
            sig,
            IUniswapV3Callback.uniswapV3SwapCallback.selector
        );
    }

    /// see sellToUniswapV3ForkMetaTxn
    function sellToUniswapV3MetaTxn(
        address recipient,
        bytes memory encodedPath,
        uint256 minBuyAmount,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) internal returns (uint256 buyAmount) {
        return sellToUniswapV3ForkMetaTxn(
            _UNISWAPV3_FACTORY,
            _UNISWAPV3_INITHASH,
            recipient,
            encodedPath,
            minBuyAmount,
            permit,
            sig,
            IUniswapV3Callback.uniswapV3SwapCallback.selector
        );
    }
}
