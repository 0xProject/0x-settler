// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC165} from "@forge-std/interfaces/IERC165.sol";

interface IOwnable is IERC165 {
    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    function owner() external view returns (address);

    function transferOwnership(address) external returns (bool);

    error PermissionDenied();
    error ZeroAddress();
}
