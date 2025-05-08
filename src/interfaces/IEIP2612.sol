// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

bytes32 constant PERMIT_TYPEHASH =
    keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)");

interface IEIP2612 is IERC20 {
    function permit(address owner, address spender, uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s)
        external;
    function nonces(address owner) external view returns (uint256);
    function DOMAIN_SEPARATOR() external view returns (bytes32);
}
