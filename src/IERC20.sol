// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

interface IERC20 {
    function totalSupply() external view returns (uint256);
    function balanceOf(address) external view returns (uint256);
    function transfer(address, uint256) external returns (bool);
    function transferFrom(address, address, uint256) external returns (bool);
    function approve(address, uint256) external returns (bool);
    function allowance(address, address) external view returns (uint256);

    event Transfer(address indexed, address indexed, uint256);
    event Approval(address indexed, address indexed, uint256);
}

interface IERC20Meta is IERC20 {
    function name() external view returns (string memory);
    function symbol() external view returns (string memory);
    function decimals() external view returns (uint8);
}
