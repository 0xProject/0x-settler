// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

abstract contract VIPBase {
    error TooMuchSlippage(address token, uint256 expected, uint256 actual);
}
