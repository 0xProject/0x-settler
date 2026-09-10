// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SettlerSwapAbstract} from "../SettlerAbstract.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {revertExcessiveSellAmount} from "./SettlerErrors.sol";
import "./Constants.sol" as Constants;

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

    function sellToFluxPool(IERC20 sellToken, uint256 ppm, bytes32 poolId, bool zeroForOne, uint256 minBuyAmount)
        internal
    {
        uint256 sellAmount;
        unchecked {
            sellAmount = sellToken.fastBalanceOf(address(this)) * ppm / Constants.BASIS;
        }

        // Equivalent to `abi.encodeCall(IFluxSwap.swapWithCallback, (poolId, zeroForOne, sellAmount, minBuyAmount,
        // address(this), abi.encodePacked(sellToken, sellAmount)))`, but tightly packed and canonicalizing `zeroForOne`.
        bytes memory data;
        assembly ("memory-safe") {
            data := mload(0x40)
            mstore(add(0x104, data), shl(0x60, sellToken))
            mstore(add(0x118, data), sellAmount)
            mstore(add(0xe4, data), 0x34)
            mstore(add(0xc4, data), 0xc0)
            mstore(add(0xa4, data), address())
            mstore(add(0x84, data), minBuyAmount)
            mstore(add(0x64, data), sellAmount)
            mstore(add(0x44, data), lt(0x00, zeroForOne))
            mstore(add(0x24, data), poolId)
            mstore(add(0x04, data), 0x3dd88329) // selector for `swapWithCallback(bytes32,bool,uint256,uint256,address,bytes)`
            mstore(data, 0x118)
            mstore(0x40, add(0x138, data))
        }
        _setOperatorAndCall(FLUX_SWAP, data, uint32(IFluxSwapCallback.fluxSwapCallback.selector), _fluxSwapCallback);
    }

    function _fluxSwapCallback(bytes calldata data) private returns (bytes memory) {
        uint256 amountToPay;
        IERC20 sellToken;
        uint256 sellAmount;
        // Read the callback amount and our packed token/amount without allocating memory.
        // (, amountToPay, bytes memory callbackData) = abi.decode(data, (IERC20, uint256, bytes));
        // sellToken = IERC20(address(bytes20(callbackData[:20]))); sellAmount = uint256(bytes32(callbackData[20:]));
        assembly ("memory-safe") {
            amountToPay := calldataload(add(0x20, data.offset))
            sellToken := shr(0x60, calldataload(add(0x80, data.offset)))
            sellAmount := calldataload(add(0x94, data.offset))
        }
        // The curve is unverified and swappable by the owner, so never pay more than we offered.
        if (amountToPay > sellAmount) revertExcessiveSellAmount(sellToken, sellAmount, amountToPay);

        sellToken.safeTransfer(FLUX_VAULT, amountToPay);
        return new bytes(0);
    }
}
