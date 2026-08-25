// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SettlerSwapAbstract} from "../SettlerAbstract.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {revertConfusedDeputy, revertTooMuchSlippage} from "./SettlerErrors.sol";

interface IFluxSwap {
    function swapWithCallback(
        bytes32 poolId,
        bool zeroForOne,
        uint256 amountIn,
        uint256 amountOutMinimum,
        address swapReceiver,
        bytes calldata callbackData
    ) external returns (uint256 amountOut);
}

interface IFluxSwapCallback {
    function fluxSwapCallback(IERC20 tokenToPay, uint256 amountToPay, bytes calldata data) external;
}

address constant FLUX_SWAP = 0xff7fe6b6951Afd81Bc5eF9d205c28e5117012FD8;
address constant FLUX_VAULT = 0x0F8E0136f09e8b188d21EdDF17f65522f81f7151;

abstract contract FluxPool is SettlerSwapAbstract {
    using SafeTransferLib for IERC20;

    constructor() {
        assert(block.chainid == 31337 || (FLUX_SWAP.code.length > 0 && FLUX_VAULT.code.length > 0));
    }

    function sellToFluxPool(
        IERC20 sellToken,
        uint256 ppm,
        bytes32 poolId,
        bool zeroForOne,
        IERC20 buyToken,
        uint256 minBuyAmount
    ) internal {
        uint256 sellAmount;
        unchecked {
            sellAmount = sellToken.fastBalanceOf(address(this)) * ppm / BASIS;
        }

        uint256 balanceBefore = buyToken.fastBalanceOf(address(this));
        _setOperatorAndCall(
            FLUX_SWAP,
            abi.encodeCall(
                IFluxSwap.swapWithCallback,
                (poolId, zeroForOne, sellAmount, minBuyAmount, address(this), abi.encodePacked(sellToken, sellAmount))
            ),
            uint32(IFluxSwapCallback.fluxSwapCallback.selector),
            _fluxSwapCallback
        );
        uint256 buyAmount = buyToken.fastBalanceOf(address(this)) - balanceBefore;
        if (buyAmount < minBuyAmount) revertTooMuchSlippage(buyToken, minBuyAmount, buyAmount);
    }

    function _fluxSwapCallback(bytes calldata data) private returns (bytes memory) {
        if (data.length != 0xc0) revertConfusedDeputy();
        IERC20 tokenToPay;
        uint256 amountToPay;
        IERC20 sellToken;
        uint256 sellAmount;
        // Decode the callback and packed token/amount without allocating memory.
        assembly ("memory-safe") {
            tokenToPay := calldataload(data.offset)
            amountToPay := calldataload(add(0x20, data.offset))
            sellToken := shr(0x60, calldataload(add(0x80, data.offset)))
            sellAmount := calldataload(add(0x94, data.offset))
        }
        if (tokenToPay != sellToken || amountToPay != sellAmount) revertConfusedDeputy();

        sellToken.safeTransfer(FLUX_VAULT, sellAmount);
        return new bytes(0);
    }
}
