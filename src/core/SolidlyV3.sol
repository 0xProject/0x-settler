// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {UniswapV3ForkBase} from "./UniswapV3ForkBase.sol";

interface ISolidlyV3Callback {
    function solidlyV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external;
}

abstract contract SolidlyV3 is UniswapV3ForkBase {
    address private constant _SOLIDLYV3_FACTORY = 0x70Fe4a44EA505cFa3A57b95cF2862D4fd5F0f687;
    bytes32 private constant _SOLIDLYV3_INITHASH = 0xe9b68c5f77858eecac2e651646e208175e9b1359d68d0e14fc69f8c54e5010bf;

    /// see sellToUniswapV3Fork
    function sellToSolidlyV3(address recipient, bytes memory encodedPath, uint256 bips, uint256 minBuyAmount)
        internal
        returns (uint256 buyAmount)
    {
        return sellToUniswapV3Fork(
            _SOLIDLYV3_FACTORY,
            _SOLIDLYV3_INITHASH,
            recipient,
            encodedPath,
            bips,
            minBuyAmount,
            ISolidlyV3Callback.solidlyV3SwapCallback.selector
        );
    }

    /// see sellToUniswapV3ForkVIP
    function sellToSolidlyV3VIP(
        address recipient,
        bytes memory encodedPath,
        uint256 minBuyAmount,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) internal returns (uint256 buyAmount) {
        return sellToUniswapV3ForkVIP(
            _SOLIDLYV3_FACTORY,
            _SOLIDLYV3_INITHASH,
            recipient,
            encodedPath,
            minBuyAmount,
            permit,
            sig,
            ISolidlyV3Callback.solidlyV3SwapCallback.selector
        );
    }

    /// see sellToUniswapV3ForkMetaTxn
    function sellToSolidlyV3MetaTxn(
        address recipient,
        bytes memory encodedPath,
        uint256 minBuyAmount,
        address payer,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) internal returns (uint256 buyAmount) {
        return sellToUniswapV3ForkMetaTxn(
            _SOLIDLYV3_FACTORY,
            _SOLIDLYV3_INITHASH,
            recipient,
            encodedPath,
            minBuyAmount,
            payer,
            permit,
            sig,
            ISolidlyV3Callback.solidlyV3SwapCallback.selector
        );
    }
}
