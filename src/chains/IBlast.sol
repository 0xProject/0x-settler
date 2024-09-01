// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

enum BlastYieldMode {
    AUTOMATIC,
    VOID,
    CLAIMABLE
}

enum BlastGasMode {
    VOID,
    CLAIMABLE
}

interface IBlast {
    function configure(BlastYieldMode _yield, BlastGasMode gasMode, address governor) external;
}

interface IBlastYieldERC20 {
    function configure(BlastYieldMode) external returns (uint256);
}

IBlast constant BLAST = IBlast(0x4300000000000000000000000000000000000002);
IBlastYieldERC20 constant BLAST_USDB = IBlastYieldERC20(0x4300000000000000000000000000000000000003);
IBlastYieldERC20 constant BLAST_WETH = IBlastYieldERC20(0x4300000000000000000000000000000000000004);
