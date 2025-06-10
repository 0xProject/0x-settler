// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

abstract contract BridgeSettlerAbstract {
    // Do we need this? Is it going to be registered in the Registry?
    // maybe take out logic related to this from Settler into a different contract
    // and inherit from that everywhere
    function _tokenId() internal pure virtual returns (uint256);

    function _dispatch(uint256 i, uint256 action, bytes calldata data) internal virtual returns (bool);
}