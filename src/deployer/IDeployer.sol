// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC165} from "@forge-std/interfaces/IERC165.sol";
import {IOwnable} from "../interfaces/IOwnable.sol";
import {IERC1967Proxy} from "../interfaces/IERC1967Proxy.sol";
import {IMultiCall} from "../interfaces/IMultiCall.sol";
import {Feature} from "./Feature.sol";
import {Nonce} from "./Nonce.sol";

interface IERC721View is IERC165 {
    event Transfer(address indexed from, address indexed to, uint256 indexed tokenId);
    event PermanentURI(string, uint256 indexed); // not technically part of the standard

    function balanceOf(address) external view returns (uint256);
    function ownerOf(uint256 tokenId) external view returns (address);
    function getApproved(uint256 tokenId) external view returns (address);
    function isApprovedForAll(address owner, address operator) external view returns (bool);
}

interface IERC721ViewMetadata is IERC721View {
    function name() external view returns (string memory);
    function symbol() external view returns (string memory);
    function tokenURI(uint256) external view returns (string memory);
}

interface IDeployerRemove {
    function remove(Feature, Nonce) external returns (bool);
    function remove(address) external returns (bool);
    function removeAll(Feature) external returns (bool);
}

interface IDeployer is IOwnable, IERC721ViewMetadata, IMultiCall, IDeployerRemove {
    function authorized(Feature) external view returns (address, uint40);
    function descriptionHash(Feature) external view returns (bytes32);
    function prev(Feature) external view returns (address);
    function next(Feature) external view returns (address);
    function deployInfo(address) external view returns (Feature, Nonce);
    function authorize(Feature, address, uint40) external returns (bool);
    function setDescription(Feature, string calldata) external returns (string memory);
    function deploy(Feature, bytes calldata) external payable returns (address, Nonce);

    // ERC-6093 errors
    error ERC721InvalidOwner(address owner);
    error ERC721NonexistentToken(uint256 tokenId);

    error FeatureNotInitialized(Feature);
    error FeatureInitialized(Feature);
    error DeployFailed(Feature, Nonce, address);
    error FutureNonce(Nonce);
    error NoInstance();

    event Authorized(Feature indexed, address indexed, uint40);
    event Deployed(Feature indexed, Nonce indexed, address indexed);
    event Removed(Feature indexed, Nonce indexed, address indexed);
    event RemovedAll(Feature indexed);
}
