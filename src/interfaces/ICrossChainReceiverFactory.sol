// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC1271} from "./IERC1271.sol";
import {IERC5267} from "./IERC5267.sol";
import {IOwnable} from "./IOwnable.sol";

interface ICrossChainReceiverFactory is IERC1271, IERC5267, IOwnable {
    function name() external view returns (string memory);

    /// Only available on the factory
    function deploy(bytes32 root, bool setOwnerNotCleanup, address initialOwner)
        external
        returns (ICrossChainReceiverFactory);

    /// Only available on proxies
    function setOwner(address owner) external;

    /// Only available on proxies
    function approvePermit2(IERC20 token, uint256 amount) external returns (bool);

    /// Only available on proxies
    function call(address payable target, uint256 value, bytes calldata data) external returns (bytes memory);

    /// Only available on proxies
    function cleanup(address payable beneficiary) external;

    /// Only available on proxies
    receive() external payable;
}
