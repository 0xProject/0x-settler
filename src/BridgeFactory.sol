// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC1271} from "./interfaces/IERC1271.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {TwoStepOwnable} from "./deployer/TwoStepOwnable.sol";
import {SafeTransferLib} from "./vendor/SafeTransferLib.sol";
import {MerkleProofLib} from "./vendor/MerkleProofLib.sol";
import {Context} from "./Context.sol";

contract BridgeFactory is IERC1271, Context, TwoStepOwnable {
    using SafeTransferLib for IERC20;

    address private immutable _cachedThis;

    constructor() {
        require(
            (msg.sender == 0x4e59b44847b379578588920cA78FbF26c0B4956C && uint160(address(this)) >> 104 == 0)
                || block.chainid == 31337
        );
        _cachedThis = address(this);
    }

    modifier onlyProxy() {
        require(address(this) != _cachedThis);
        _;
    }

    modifier noDelegateCall() {
        require(address(this) == _cachedThis);
        _;
    }

    modifier onlyFactory() {
        require(_msgSender() == _cachedThis);
        _;
    }

    function isValidSignature(bytes32 _hash, bytes calldata _signature)
        external
        view
        override
        onlyProxy
        returns (bytes4)
    {
        return _isValidSignature(_hash, _signature);
    }

    function _isValidSignature(bytes32 _leaf, bytes calldata _proof) private view returns (bytes4) {
        bytes32[] calldata proof;
        assembly ("memory-safe") {
            // _signature is just going to be the proof, then we can read it as so
            proof.offset := add(0x20, _proof.offset)
            proof.length := calldataload(proof.offset)
            proof.offset := add(0x20, proof.offset)
        }
        bytes32 salt = keccak256(abi.encodePacked(MerkleProofLib.getRoot(proof, _leaf), block.chainid));

        address factory = _cachedThis;
        assembly ("memory-safe") {
            mstore(0x1d, 0x5af43d5f5f3e6022573d5ffd5b3d5ff3)
            mstore(0x0d, factory)
            mstore(0x00, 0x60265f8160095f39f35f5f365f5f37365f6c)
            let initCodeHash := keccak256(0x0e, 0x2f)

            // 0xff + factory + salt + hash(initCode)
            mstore(0x00, 0xff00000000000000)
            mstore(0x2d, salt)
            mstore(0x4d, initCodeHash)
            let computedAddress := keccak256(0x18, 0x55)

            if shl(0x60, xor(computedAddress, address())) {
                mstore(0x00, 0x00)
                return(0x00, 0x20)
            }
            // Return ERC1271 magic value (isValidSignature selector)
            mstore(0x00, 0x1626ba7e00000000000000000000000000000000000000000000000000000000)
            return(0x00, 0x20)
        }
    }

    function deploy(bytes32 salt, address owner, bytes32 r, bytes32 vs) external noDelegateCall returns (address proxy) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            mstore(0x00, salt)
            mstore(0x20, add(0x1b, shr(0xff, vs)))
            mstore(0x40, r)
            mstore(0x60, and(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, vs))
            pop(staticcall(gas(), 0x01, 0x00, 0x80, 0x20, 0x20))

            // reset clobbered memory
            mstore(0x40, ptr)
            mstore(0x60, 0x00)

            if xor(owner, mul(mload(0x20), eq(returndatasize(), 0x20))) {
                mstore(0x00, 0x8baa579f) // selector for `InvalidSignature()`
                revert(0x1c, 0x04)
            }
        
            mstore(0x20, chainid())
            salt := keccak256(0x00, 0x40)

            // create a minimal proxy targeting this contract
            mstore(0x1d, 0x5af43d5f5f3e6022573d5ffd5b3d5ff3)
            mstore(0x0d, address())
            mstore(0x00, 0x60265f8160095f39f35f5f365f5f37365f6c)
            proxy := create2(0x00, 0x0e, 0x2f, salt)
            if iszero(proxy) {
                mstore(0x00, 0x30116425) // selector for `DeploymentFailed()`.
                revert(0x1c, 0x04)
            }
        }
        BridgeFactory(proxy).setPendingOwner(owner);
    }

    function setPendingOwner(address owner) external onlyFactory {
        _setPendingOwner(owner);
    }

    function approvePermit2(IERC20 token) external onlyProxy returns (bool) {
        token.safeApprove(0x000000000022D473030F116dDEE9F6B43aC78BA3, type(uint256).max);
        return true;
    }

    function call(address target, uint256 value, bytes calldata data) external onlyOwner returns (bytes memory) {
        (bool success, bytes memory result) = target.call{value: value}(data);
        require(success);
        return result;
    }

    function cleanup() external onlyOwner {
        selfdestruct(payable(_msgSender()));
    }
}
