// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {uint512, tmp} from "src/utils/512Math.sol";

/// @dev Thin wrapper exposing 512Math's cbrt functions for `forge inspect ... ir`.
/// The public `cbrt(uint512)` calls `_cbrt(x_hi, x_lo)` internally, so both
/// appear in the Yul IR. The driver script disambiguates by parameter count.
///
/// Uses `tmp()` (fixed address 0) so that the Yul IR's mstore/mload pairs can
/// be folded to direct parameter references by the model generator.
contract Cbrt512Wrapper {
    function wrap_cbrt512(uint256 x_hi, uint256 x_lo) external pure returns (uint256) {
        return tmp().from(x_hi, x_lo).cbrt();
    }

    function wrap_cbrtUp512(uint256 x_hi, uint256 x_lo) external pure returns (uint256) {
        return tmp().from(x_hi, x_lo).cbrtUp();
    }
}
