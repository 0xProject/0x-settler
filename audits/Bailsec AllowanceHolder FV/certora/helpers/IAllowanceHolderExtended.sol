// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

interface IAllowanceHolderExtended {
    function exec(address operator, address token, uint256 amount, address payable target, bytes calldata data)
        external
        payable
        returns (bytes memory result);

    function transferFrom(address token, address owner, address recipient, uint256 amount) external returns (bool);

    function balanceOf(address owner) external view returns (uint256);
}
