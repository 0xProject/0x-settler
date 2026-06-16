// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

import {Ln} from "src/vendor/Ln.sol";

/// @dev Thin wrapper exposing Ln's internal function for `forge inspect ... ir`.
/// Function names are prefixed with `wrap_` to avoid Yul name collisions with the
/// library functions, keeping the IR unambiguous for the formal-proof code generator.
contract LnWrapper {
    function wrap_lnWadToRay(int256 x) external pure returns (int256) {
        return Ln.lnWadToRay(x);
    }

    function wrap_lnWad(int256 x) external pure returns (int256) {
        return Ln.lnWad(x);
    }
}
