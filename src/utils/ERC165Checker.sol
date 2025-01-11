// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC165} from "@forge-std/interfaces/IERC165.sol";
import {CallWithGas} from "./CallWithGas.sol";

library ERC165Checker {
    using CallWithGas for address;

    /**
     * @notice Query if a contract implements an interface, does not check ERC165
     *         support
     * @param account The address of the contract to query for support of an interface
     * @param interfaceId The interface identifier, as specified in ERC165
     * @return true if the contract at account indicates support of the interface with
     *         identifier interfaceId, false otherwise
     * @dev Assumes that account contains a contract that supports ERC165, otherwise the
     *      behavior of this method is undefined. This precondition can be checked with
     *      `supportsERC165`.
     */
    function _supportsERC165Interface(address account, bytes4 interfaceId) private view returns (bool) {
        bytes memory data = abi.encodeCall(IERC165(account).supportsInterface, (interfaceId));
        (bool success, bytes memory result) = account.functionStaticCallWithGas(data, 30_000, 32);
        return success && result.length >= 32 && bytes32(result) == bytes32(uint256(1));
    }

    function supportsERC165(address account) internal view returns (bool) {
        return _supportsERC165Interface(account, type(IERC165).interfaceId)
            && !_supportsERC165Interface(account, bytes4(0xffffffff));
    }

    function supportsInterface(address account, bytes4 interfaceId) internal view returns (bool) {
        return supportsERC165(account) && _supportsERC165Interface(account, interfaceId);
    }
}
