// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

interface IERC1967Proxy {
    event Upgraded(address indexed implementation);

    function implementation() external view returns (address);

    function version() external view returns (string memory);

    function upgrade(address newImplementation) external payable returns (bool);

    function upgradeAndCall(address newImplementation, bytes calldata data) external payable returns (bool);
}
