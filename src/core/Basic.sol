// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {SafeTransferLib} from "../utils/SafeTransferLib.sol";
import {FullMath} from "../utils/FullMath.sol";
import {Panic} from "../utils/Panic.sol";

abstract contract Basic {
    using SafeTransferLib for ERC20;
    using FullMath for uint256;

    address internal constant ETH_ADDRESS = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;

    /// @dev Permit2 address
    address private immutable PERMIT2;

    constructor(address permit2) {
        PERMIT2 = permit2;
    }

    error ConfusedDeputy();

    /// @dev Sell to a pool with a generic approval, transferFrom interaction.
    /// offset in the calldata is used to update the sellAmount given a proportion of the sellToken balance
    function basicSellToPool(address pool, ERC20 sellToken, uint256 bips, uint256 offset, bytes memory data) internal {
        if (pool == PERMIT2) {
            revert ConfusedDeputy();
        }

        if (sellToken == ERC20(ETH_ADDRESS)) {
            uint256 amount = address(this).balance.mulDiv(bips, 10_000);
            if (data.length == 0) {
                require(offset == 0);
                (bool success, bytes memory returnData) = payable(pool).call{value: amount}("");
                if (!success) {
                    assembly ("memory-safe") {
                        revert(add(0x20, returnData), mload(returnData))
                    }
                }
            } else {
                if ((offset += 32) > data.length) {
                    Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
                }
                assembly ("memory-safe") {
                    mstore(add(data, offset), amount)
                }
                (bool success, bytes memory returnData) = payable(pool).call{value: amount}(data);
                if (!success) {
                    assembly ("memory-safe") {
                        revert(add(0x20, returnData), mload(returnData))
                    }
                }
                require(returnData.length > 0 || pool.code.length > 0); // forbid sending data to EOAs
            }
        } else {
            uint256 amount;
            if (address(sellToken) == address(0)) {
                require(offset == 0);
            } else {
                amount = sellToken.balanceOf(address(this)).mulDiv(bips, 10_000);
                if ((offset += 32) > data.length) {
                    Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
                }
                assembly ("memory-safe") {
                    mstore(add(data, offset), amount)
                }
                if (address(sellToken) != pool) {
                    sellToken.safeApproveIfBelow(pool, amount);
                }
            }
            (bool success, bytes memory returnData) = pool.call(data);
            if (!success) {
                assembly ("memory-safe") {
                    revert(add(0x20, returnData), mload(returnData))
                }
            }
            require(returnData.length > 0 || pool.code.length > 0); // forbid EOAs
        }
    }
}
