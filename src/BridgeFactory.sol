// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC1271} from "./interfaces/IERC1271.sol";

import {TwoStepOwnable} from "./deployer/TwoStepOwnable.sol";
import {MultiCallContext} from "./multicall/MultiCallContext.sol";

import {Revert} from "./utils/Revert.sol";
import {SafeTransferLib} from "./vendor/SafeTransferLib.sol";
import {MerkleProofLib} from "./vendor/MerkleProofLib.sol";

contract BridgeFactory is IERC1271, MultiCallContext, TwoStepOwnable {
    using SafeTransferLib for IERC20;
    using Revert for bool;

    address private immutable _cachedThis;
    bytes32 private immutable _proxyInitHash;

    constructor() {
        require(
            (msg.sender == 0x4e59b44847b379578588920cA78FbF26c0B4956C && uint160(address(this)) >> 104 == 0)
                || block.chainid == 31337
        );
        _cachedThis = address(this);
        _proxyInitHash = keccak256(
            bytes.concat(
                hex"60265f8160095f39f35f5f365f5f37365f6c",
                bytes13(uint104(uint160(address(this)))),
                hex"5af43d5f5f3e6022573d5ffd5b3d5ff3"
            )
        );
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

    function _verifyRoot(bytes32 root, address pendingOwner_) internal view {
        bytes32 initHash = _proxyInitHash;
        address factory = _cachedThis;
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            // derive creation salt
            mstore(0x00, root)
            mstore(0x14, pendingOwner_)
            mstore(0x34, chainid())
            let salt := keccak256(0x00, 0x54)

            // 0xff + factory + salt + hash(initCode)
            mstore(0x0d, factory)
            mstore(0x00, 0xff00000000000000)
            mstore(0x2d, salt)
            mstore(0x4d, initHash)
            let computedAddress := keccak256(0x18, 0x55)

            // verify that `salt` was used to deploy `address(this)`
            if shl(0x60, xor(address(), computedAddress)) {
                mstore(0x00, 0x1e092104) // selector for `PermissionDenied()`
                revert(0x1c, 0x04)
            }

            // restore clobbered memory
            mstore(0x60, 0x00)
            mstore(0x40, ptr)
        }
    }

    function isValidSignature(bytes32 hash, bytes calldata signature)
        external
        view
        override
        onlyProxy
        returns (bytes4)
    {
        bytes32[] calldata proof;
        assembly ("memory-safe") {
            // signature is just the proof, then we can read it as so
            proof.offset := add(signature.offset, calldataload(signature.offset))
            proof.length := calldataload(proof.offset)
            proof.offset := add(0x20, proof.offset)
        }

        _verifyRoot(MerkleProofLib.getRoot(proof, hash), pendingOwner());
        return IERC1271.isValidSignature.selector;
    }

    error DeploymentFailed();

    function deploy(bytes32 salt, address owner) external noDelegateCall returns (address proxy) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            // derive the deployment salt from the owner and chainid
            mstore(0x00, salt)
            mstore(0x14, owner)
            mstore(0x34, chainid())
            salt := keccak256(0x00, 0x54)

            // create a minimal proxy targeting this contract
            mstore(0x1d, 0x5af43d5f5f3e6022573d5ffd5b3d5ff3)
            mstore(0x0d, address())
            mstore(0x00, 0x60265f8160095f39f35f5f365f5f37365f6c)
            proxy := create2(0x00, 0x0e, 0x2f, salt)
            if iszero(proxy) {
                mstore(0x00, 0x30116425) // selector for `DeploymentFailed()`.
                revert(0x1c, 0x04)
            }

            // set the pending owner in the proxy
            mstore(0x14, owner)
            mstore(0x00, 0xc42069ec000000000000000000000000) // selector for `setPendingOwner(address)` with padding for owner
            if iszero(call(gas(), proxy, 0x00, 0x10, 0x24, 0x00, 0x00)) {
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }

            // restore clobbered memory
            mstore(0x40, ptr)
        }
    }

    function setPendingOwner(address owner) external onlyFactory {
        _setPendingOwner(owner);
    }

    function approvePermit2(IERC20 token, uint256 amount) external onlyProxy returns (bool) {
        token.safeApprove(0x000000000022D473030F116dDEE9F6B43aC78BA3, amount);
        return true;
    }

    function call(address payable target, uint256 value, bytes calldata data)
        external
        onlyOwner
        returns (bytes memory)
    {
        (bool success, bytes memory result) = target.call{value: value}(data);
        success.maybeRevert(result);
        assembly ("memory-safe") {
            let start := sub(result, 0x20) // TODO: examine bytecode to ensure this does not clobber reserved memory
            mstore(start, 0x20)
            return(start, add(0x40, mload(result)))
        }
    }

    function cleanup(address payable beneficiary) external onlyProxy {
        address owner_ = owner();
        if (_msgSender() != owner_) {
            if (owner_ != address(0)) {
                assembly ("memory-safe") {
                    mstore(0x00, 0x1e092104) // selector for `PermissionDenied()`
                    revert(0x1c, 0x04)
                }
            }
            address pendingOwner_ = pendingOwner();
            if (pendingOwner_ == address(0)) {
                selfdestruct(beneficiary);
            }
            selfdestruct(payable(pendingOwner_));
        }
        selfdestruct(beneficiary);
    }
}
