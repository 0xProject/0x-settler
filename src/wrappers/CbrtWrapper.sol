// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Cbrt} from "src/vendor/Cbrt.sol";

/// @dev Thin wrapper exposing Cbrt's internal functions for `forge inspect ... ir`.
/// Function names are prefixed with `wrap_` to avoid Yul name collisions with the
/// library functions, keeping the IR unambiguous for the formal-proof code generator.
contract CbrtWrapper {
    function wrap_cbrt(uint256 x) external pure returns (uint256) {
        return Cbrt.cbrt(x);
    }
    function wrap_cbrtUp(uint256 x) external pure returns (uint256) {
        return Cbrt.cbrtUp(x);
    }
}
