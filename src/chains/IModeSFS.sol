// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

interface IModeSFS {
    function getTokenId(address _smartContract) external view returns (uint256);
    function register(address _recipient) external returns (uint256 tokenId);
    function assign(uint256 _tokenId) external returns (uint256);
}

IModeSFS constant MODE_SFS = IModeSFS(0x8680CEaBcb9b56913c519c069Add6Bc3494B7020);
