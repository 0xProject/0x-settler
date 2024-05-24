// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

interface IERC721Owner {
    function ownerOf(uint256) external view returns (address);
}
