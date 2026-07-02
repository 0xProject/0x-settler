// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {Exp} from "src/vendor/Exp.sol";

/// @dev Thin wrapper exposing Exp's internal function for `forge inspect ... ir`.
/// Function names are prefixed with `wrap_` to avoid Yul name collisions with the
/// library functions, keeping the IR unambiguous for the formal-proof code generator.
contract ExpWrapper {
    function wrap_expRayToWad(int256 x) external pure returns (int256) {
        return Exp.expRayToWad(x);
    }
}
