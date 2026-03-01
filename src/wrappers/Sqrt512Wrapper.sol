// SPDX-License-Identifier: MIT
pragma solidity =0.8.33;

import {uint512, alloc, tmp} from "src/utils/512Math.sol";

/// @dev Thin wrapper exposing 512Math's sqrt functions for `forge inspect ... ir`.
/// The public `sqrt(uint512)` calls `_sqrt(x_hi, x_lo)` internally, so both
/// appear in the Yul IR. The driver script disambiguates by parameter count.
///
/// The `wrap_sqrt512` and `wrap_sqrt512Up` functions use `alloc()` for their
/// own testing purposes. For model generation, `flat_sqrt512` and
/// `flat_osqrtUp` use `tmp()` (fixed address 0) so that the Yul IR's
/// mstore/mload pairs can be folded to direct parameter references by the
/// model generator.
contract Sqrt512Wrapper {
    function flat_sqrt512(uint256 x_hi, uint256 x_lo) external pure returns (uint256) {
        return tmp().from(x_hi, x_lo).sqrt();
    }

    function flat_osqrtUp(uint256 x_hi, uint256 x_lo) external pure returns (uint256, uint256) {
        uint512 x;
        assembly { // not "memory-safe"
            x := 0x1080
        }
        return tmp().osqrtUp(x.from(x_hi, x_lo)).into();
    }
}
