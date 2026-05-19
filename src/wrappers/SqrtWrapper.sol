// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Sqrt} from "src/vendor/Sqrt.sol";

/// @dev Thin wrapper exposing Sqrt's internal functions for `forge inspect ... ir`.
/// Function names are prefixed with `wrap_` to avoid Yul name collisions with the
/// library functions, keeping the IR unambiguous for the formal-proof code generator.
contract SqrtWrapper {
    function wrap_sqrt(uint256 x) external pure returns (uint256) {
        return Sqrt.sqrt(x);
    }
    function wrap_sqrtUp(uint256 x) external pure returns (uint256) {
        return Sqrt.sqrtUp(x);
    }
}
