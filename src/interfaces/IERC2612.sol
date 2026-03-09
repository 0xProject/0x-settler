// SPDX-License-Identifier: CC0-1.0
pragma solidity ^0.8.19;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

interface IERC20PermitCommon is IERC20 {
    function nonces(address owner) external view returns (uint256);
    function DOMAIN_SEPARATOR() external view returns (bytes32);
}

interface IERC2612 is IERC20PermitCommon {
    function permit(address owner, address spender, uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s)
        external;
}

interface IDAIStylePermit is IERC20PermitCommon {
    function permit(
        address holder,
        address spender,
        uint256 nonce,
        uint256 expiry,
        bool allowed,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external;
}
