// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

abstract contract AbstractContext {
    function _msgSender() internal view virtual returns (address);

    function _msgData() internal view virtual returns (bytes calldata);

    function _isForwarded() internal view virtual returns (bool);

    // This hook exists for schemes that append authenticated metadata to
    // calldata (e.g. ERC2771). If msg.sender during the outer call is the
    // authenticator, the metadata must be copied from the outer calldata into
    // the inner delegatecall calldata to ensure that any logic that inspects
    // msg.sender and decodes the authenticated metadata gets the correct
    // result.
    function _encodeDelegateCall(bytes memory) internal view virtual returns (bytes memory);
}

abstract contract Context is AbstractContext {
    function _msgSender() internal view virtual override returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual override returns (bytes calldata) {
        return msg.data;
    }

    function _isForwarded() internal view virtual override returns (bool) {
        return false;
    }

    function _encodeDelegateCall(bytes memory callData) internal view virtual override returns (bytes memory) {
        return callData;
    }
}
