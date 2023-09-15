// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {SafeTransferLib} from "../utils/SafeTransferLib.sol";
import {FullMath} from "../utils/FullMath.sol";
import {Panic} from "../utils/Panic.sol";

abstract contract Basic {
    using SafeTransferLib for ERC20;
    using FullMath for uint256;

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
        if ((offset += 32) > data.length) {
            Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
        }

        uint256 beforeBalanceSell = sellToken.balanceOf(address(this));
        uint256 proportionSellBalance = beforeBalanceSell.mulDiv(bips, 10_000);
        // Update the sellAmount given a proportion of the sellToken balance
        assembly ("memory-safe") {
            mstore(add(data, offset), proportionSellBalance)
        }
        sellToken.safeApproveIfBelow(pool, type(uint256).max);
        (bool success, bytes memory returnData) = address(pool).call(data);
        if (!success) {
            assembly ("memory-safe") {
                revert(add(0x20, returnData), mload(returnData))
            }
        }
    }
}
