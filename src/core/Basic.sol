// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {SafeTransferLib} from "../utils/SafeTransferLib.sol";

abstract contract Basic {
    using SafeTransferLib for ERC20;

    /// @dev Permit2 address
    address private immutable PERMIT2;

    constructor(address permit2) {
        PERMIT2 = permit2;
    }

    /// @dev Sell to a pool with a generic approval, transferFrom interaction.
    /// offset in the calldata is used to update the sellAmount given a proportion of the sellToken balance
    /// @return buyAmount Amount of tokens bought
    function basicSellToPool(
        address pool,
        ERC20 sellToken,
        ERC20 buyToken,
        uint256 bips,
        uint256 offset,
        bytes memory data
    ) internal returns (uint256 buyAmount) {
        require(pool != PERMIT2, "Basic: Pool address invalid");
        require((offset += 32) <= data.length, "Basic: out of bounds");

        uint256 beforeBalanceSell = sellToken.balanceOf(address(this));
        uint256 proportionSellBalance = (beforeBalanceSell * bips) / 10_000;
        // Update the sellAmount given a proportion of the sellToken balance
        assembly ("memory-safe") {
            mstore(add(data, offset), proportionSellBalance)
        }
        sellToken.safeApproveIfBelow(pool, type(uint256).max);
        uint256 beforeBalance = buyToken.balanceOf(address(this));
        (bool success, bytes memory returnData) = address(pool).call(data);
        return buyToken.balanceOf(address(this)) - beforeBalance;
    }
}
