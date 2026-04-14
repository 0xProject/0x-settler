// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {uint512, alloc, tmp} from "src/utils/512Math.sol";

/// @dev Thin wrapper exposing 512Math's sqrt functions for `forge inspect ... ir`.
/// The public `sqrt(uint512)` calls `_sqrt(x_hi, x_lo)` internally, so both
/// appear in the Yul IR. The driver script disambiguates by parameter count.
///
/// `wrap_sqrt512` uses `tmp()` as its scratch cell. `wrap_osqrtUp` uses
/// `alloc()` for the input `uint512` and `tmp()` for the output `uint512`.
contract Sqrt512Wrapper {
    function wrap_sqrt512(uint256 x_hi, uint256 x_lo) external pure returns (uint256) {
        return tmp().from(x_hi, x_lo).sqrt();
    }

    function wrap_osqrtUp(uint256 x_hi, uint256 x_lo)
        external
        pure
        returns (uint256, uint256)
    {
        uint512 x = alloc();
        x.from(x_hi, x_lo);
        return tmp().osqrtUp(x).into();
    }
}
