// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC1271} from "./IERC1271.sol";
import {IERC5267} from "./IERC5267.sol";
import {IOwnable} from "./IOwnable.sol";
import {IMultiCall} from "../multicall/MultiCallContext.sol";

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

    /// Utility function for getting stuck native/tokens out of the ERC2771-forwarding multicall contract
    /// @dev This function DOES NOT WORK if the token implements ERC2771 with the multicall as its forwarder
    function getFromMulticall(IERC20 token, address payable recipient) external returns (bool);

    /// Only available on proxies
    function call(address payable target, uint256 value, bytes calldata data) external returns (bytes memory);

    /// Only available on proxies
    function call(address payable target, IERC20 token, uint256 ppm, uint256 patchOffset, bytes calldata data)
        external
        payable
        returns (bytes memory);

    /// Only available on proxies
    function metaTx(
        IMultiCall.Call[] calldata calls,
        uint256 contextdepth,
        uint256 nonce,
        uint256 deadline,
        bytes calldata signature
    ) external returns (IMultiCall.Result[] memory);

    /// Only available on proxies
    function cleanup(address payable beneficiary) external;

    /// Only available on proxies
    receive() external payable;
}
