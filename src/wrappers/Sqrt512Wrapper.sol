// SPDX-License-Identifier: MIT
pragma solidity =0.8.33;

import {uint512, alloc} from "src/utils/512Math.sol";

/// @dev Thin wrapper exposing 512Math's `_sqrt` for `forge inspect ... ir`.
/// The public `sqrt(uint512)` calls `_sqrt(x_hi, x_lo)` internally, so both
/// appear in the Yul IR. The driver script disambiguates by parameter count.
contract Sqrt512Wrapper {
    function wrap_sqrt512(uint256 x_hi, uint256 x_lo) external pure returns (uint256) {
        uint512 x = alloc();
        assembly ("memory-safe") {
            mstore(x, x_hi)
            mstore(add(0x20, x), x_lo)
        }
        return x.sqrt();
    }
}
