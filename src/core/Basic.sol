// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {IERC20} from "../IERC20.sol";

import {Permit2PaymentAbstract} from "./Permit2Payment.sol";

import {SafeTransferLib} from "../utils/SafeTransferLib.sol";
import {FullMath} from "../utils/FullMath.sol";
import {Panic} from "../utils/Panic.sol";

library Revert {
    function _revert(bytes memory reason) internal pure {
        assembly ("memory-safe") {
            revert(add(reason, 0x20), mload(reason))
        }
    }

    function maybeRevert(bool success, bytes memory reason) internal pure {
        if (!success) {
            _revert(reason);
        }
    }
}

abstract contract Basic is Permit2PaymentAbstract {
    using SafeTransferLib for IERC20;
    using FullMath for uint256;
    using Revert for bool;

    address internal constant ETH_ADDRESS = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;

    error ConfusedDeputy();

    /// @dev Sell to a pool with a generic approval, transferFrom interaction.
    /// offset in the calldata is used to update the sellAmount given a proportion of the sellToken balance
    function basicSellToPool(address pool, IERC20 sellToken, uint256 bips, uint256 offset, bytes memory data)
        internal
    {
        if (pool == address(PERMIT2())) {
            revert ConfusedDeputy();
        }

        uint256 value;
        if (sellToken == IERC20(ETH_ADDRESS)) {
            value = address(this).balance.mulDiv(bips, 10_000);
            if (data.length == 0) {
                require(offset == 0);
                (bool success, bytes memory returnData) = payable(pool).call{value: value}("");
                success.maybeRevert(returnData);
                return;
            } else {
                if ((offset += 32) > data.length) {
                    Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
                }
                assembly ("memory-safe") {
                    mstore(add(data, offset), value)
                }
            }
        } else {
            if (address(sellToken) == address(0)) {
                require(offset == 0);
            } else {
                uint256 amount = sellToken.balanceOf(address(this)).mulDiv(bips, 10_000);
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
        }
        (bool success, bytes memory returnData) = payable(pool).call{value: value}(data);
        success.maybeRevert(returnData);
        require(returnData.length > 0 || pool.code.length > 0); // forbid sending data to EOAs
    }
}
