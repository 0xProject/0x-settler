// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {SafeTransferLib} from "../utils/SafeTransferLib.sol";

abstract contract Basic {
    using SafeTransferLib for ERC20;

    /// @dev Sell to a pool with a generic approval, transferFrom interaction.
    /// offset in the calldata is used to update the sellAmount given a proportion of the sellToken balance
    /// @return buyAmount Amount of tokens bought
    function basicSellToPool(
        address pool,
        ERC20 sellToken,
        ERC20 buyToken,
        uint256 proportion,
        uint256 offset,
        bytes memory data
    ) internal returns (uint256 buyAmount) {
        sellToken.safeApproveIfBelow(pool, type(uint256).max);
        uint256 beforeBalance = buyToken.balanceOf(address(this));
        // TODO update proportion into data at offset
        (bool success, bytes memory returnData) = address(pool).call(data);
        return buyToken.balanceOf(address(this)) - beforeBalance;
    }
}
