// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

interface IFeeCollector {
    function feeCollector() external view returns (address);
}
