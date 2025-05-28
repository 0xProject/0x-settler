// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC1271} from "./interfaces/IERC1271.sol";

import {TwoStepOwnable} from "./deployer/TwoStepOwnable.sol";
import {MultiCallContext} from "./multicall/MultiCallContext.sol";

import {FastLogic} from "./utils/FastLogic.sol";
import {MerkleProofLib} from "./vendor/MerkleProofLib.sol";
import {Recover, PackedSignature} from "./utils/Recover.sol";

contract CrossChainReceiverFactory is IERC1271, MultiCallContext, TwoStepOwnable {
    using FastLogic for bool;
    using Recover for bytes32;

    struct Storage {
        uint256 nonce;
    }
    
    CrossChainReceiverFactory private immutable _cachedThis;
    bytes32 private immutable _proxyInitHash;
    uint256 private immutable _cachedChainId;
    bytes32 private immutable _cachedDomainSeparator;
    string public constant name = "ZeroExCrossChainReceiver";
    bytes32 private constant _DOMAIN_TYPEHASH = 0x8cad95687ba82c2ce50e74f7b754645e5117c3a5bec8151c0726d5857980a866;
    bytes32 private constant _NAMEHASH = 0x819c7f86c24229cd5fed5a41696eb0cd8b3f84cc632df73cfd985e8b100980e8;
    bytes32 private constant _CALL_TYPEHASH = 0x50f2ab2eac871c8aaa2eb987a8627469f3938419add9936462b32bca29e53ed3;

    error DeploymentFailed();
    error ApproveFailed();

    constructor() {
        require(
            (msg.sender == 0x4e59b44847b379578588920cA78FbF26c0B4956C && uint160(address(this)) >> 104 == 0)
                || block.chainid == 31337
        );
        require(_DOMAIN_TYPEHASH == keccak256("EIP712Domain(string name,uint256 chainId,address verifyingContract)"));
        require(_NAMEHASH == keccak256(bytes(name)));
        require(
            _CALL_TYPEHASH
                == keccak256(
                    "CALL(uint256 nonce,address crossChainReceiver,address target,uint256 value,bytes data)"
                )
        );

        uint256 $int;
        Storage storage $ = _$();
        assembly ("memory-safe") {
            $int := $.slot
        }
        require($int == (uint256(_NAMEHASH) - 1) & 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00);

        _cachedThis = this;
        _proxyInitHash = keccak256(
            bytes.concat(
                hex"60265f8160095f39f35f5f365f5f37365f6c",
                bytes13(uint104(uint160(address(this)))),
                hex"5af43d5f5f3e6022573d5ffd5b3d5ff3"
            )
        );
        _cachedChainId = block.chainid;
        _cachedDomainSeparator = _computeDomainSeparator();
    }

    modifier onlyProxy() {
        require(this != _cachedThis);
        _;
    }

    modifier noDelegateCall() {
        require(this == _cachedThis);
        _;
    }

    modifier onlyFactory() {
        require(msg.sender == address(_cachedThis));
        _;
    }

    function _$() internal pure returns (Storage storage $) {
        assembly ("memory-safe") {
            $.slot := 0x819c7f86c24229cd5fed5a41696eb0cd8b3f84cc632df73cfd985e8b10098000
        }
    }

    function _computeDomainSeparator() private view returns (bytes32 r) {
        address cachedThis = address(_cachedThis);
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(0x00, _DOMAIN_TYPEHASH)
            mstore(0x20, _NAMEHASH)
            mstore(0x40, chainid())
            mstore(0x60, and(0xffffffffffffffffffffffffff, cachedThis))
            r := keccak256(0x00, 0x80)
            mstore(0x40, ptr)
            mstore(0x60, 0x00)
        }
    }

    function _DOMAIN_SEPARATOR() internal view returns (bytes32) {
        return block.chainid == _cachedChainId ? _cachedDomainSeparator : _computeDomainSeparator();
    }

    function DOMAIN_SEPARATOR() external view noDelegateCall returns (bytes32) {
        return _DOMAIN_SEPARATOR();
    }

    function _verifyRoot(bytes32 root, address originalOwner) internal view {
        bytes32 initHash = _proxyInitHash;
        CrossChainReceiverFactory factory = _cachedThis;
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            // derive creation salt
            mstore(0x14, originalOwner)
            mstore(0x00, root)
            let salt := keccak256(0x00, 0x34)

            // 0xff + factory + salt + hash(initCode)
            mstore(0x4d, initHash)
            mstore(0x2d, salt)
            mstore(0x0d, factory)
            mstore(0x00, 0xff00000000000000)
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
        /* `_verifyRoot` hashes `_cachedThis`, making this function implicitly `onlyProxy` */
        returns (bytes4)
    {
        address owner;
        bytes32[] calldata proof;

        // This assembly block is equivalent to:
        //     hash = keccak256(abi.encode(hash, block.chainid));
        // except that it's cheaper and doesn't allocate memory. We make the assumption here that
        // `block.chainid` cannot alias a valid tree node or signing hash. Realistically,
        // `block.chainid` cannot exceed 2**53 or it would cause significant issues elsewhere in the
        // ecosystem. This also means that the sort order of the hash and the chainid backwards from
        // what `MerkleProofLib` produces, again protecting us against extension attacks.
        assembly ("memory-safe") {
            mstore(0x00, hash)
            mstore(0x20, chainid())
            hash := keccak256(0x00, 0x40)
        }

        // This assembly block is equivalent to:
        //     (owner, proof) = abi.decode(signature, (address, bytes32[]));
        // except we omit all the range and overflow checking.
        assembly ("memory-safe") {
            owner := calldataload(signature.offset)
            if shr(0xa0, owner) { revert(0x00, 0x00) }
            proof.offset := add(signature.offset, calldataload(add(0x20, signature.offset)))
            proof.length := calldataload(proof.offset)
            proof.offset := add(0x20, proof.offset)
        }

        _verifyRoot(MerkleProofLib.getRoot(proof, hash), owner);
        return IERC1271.isValidSignature.selector;
    }

    function eip712Domain()
        external
        view
        returns (
            bytes1 fields,
            string memory name_,
            string memory,
            uint256 chainId,
            address verifyingContract,
            bytes32,
            uint256[] memory
        )
    {
        fields = bytes1(0x0d);
        name_ = name;
        chainId = block.chainid;
        verifyingContract = address(_cachedThis);
    }

    function _consumeNonce() internal returns (uint256) {
        return _$().nonce++;
    }

    function nonce() external view returns (uint256) {
        return _$().nonce;
    }

    function deploy(bytes32 root, address owner, bool setOwner) external noDelegateCall returns (address proxy) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            // derive the deployment salt from the owner and chainid
            mstore(0x14, owner)
            mstore(0x00, root)
            let salt := keccak256(0x00, 0x34)

            // create a minimal proxy targeting this contract
            mstore(0x1d, 0x5af43d5f5f3e6022573d5ffd5b3d5ff3)
            mstore(0x0d, address())
            mstore(0x00, 0x60265f8160095f39f35f5f365f5f37365f6c)
            proxy := create2(0x00, 0x0e, 0x2f, salt)
            if iszero(proxy) {
                mstore(0x00, 0x30116425) // selector for `DeploymentFailed()`.
                revert(0x1c, 0x04)
            }

            // restore clobbered memory
            mstore(0x40, ptr)

            // If `setOwner == true`, this gets the selector for `setPendingOwner(address)`,
            // otherwise you get the selector for `cleanup(address)`. In both cases, the selector is
            // appended with `owner`'s padding
            let selector := xor(0xfbacefce000000000000000000000000, mul(0x3f8c8622000000000000000000000000, setOwner))

            // set the pending owner, or `selfdestruct` to the owner
            mstore(0x14, owner)
            mstore(0x00, selector)
            if iszero(call(gas(), proxy, 0x00, 0x10, 0x24, 0x00, 0x00)) {
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
        }
    }

    function setPendingOwner(address owner) external onlyFactory {
        _setPendingOwner(owner);
    }

    function approvePermit2(IERC20 token, uint256 amount) external onlyProxy returns (bool) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            mstore(0x00, 0x095ea7b3) // selector for `approve(address,uint256)`
            mstore(0x20, 0x000000000022D473030F116dDEE9F6B43aC78BA3) // Permit2
            mstore(0x40, amount)

            if iszero(call(gas(), token, 0x00, 0x1c, 0x44, 0x00, 0x20)) {
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if iszero(or(and(eq(mload(0x00), 0x01), lt(0x1f, returndatasize())), iszero(returndatasize()))) {
                mstore(0x00, 0x3e3f8f73) // selector for `ApproveFailed()`
                revert(0x1c, 0x04)
            }

            mstore(0x00, 0x01)
            return(0x00, 0x20)
        }
    }

    function call(address payable target, uint256 value, bytes calldata data)
        external
        onlyOwner
        returns (bytes memory)
    {
        _call(target, value, data);
    }

    function call(bytes32 root, address payable target, uint256 value, bytes calldata data, PackedSignature calldata sig) external returns (bytes memory) {
        _verifyRoot(root, _hashCall(target, value, data, _consumeNonce()).recover(sig));
        _call(target, value, data);
    }

    function _call(address payable target, uint256 value, bytes calldata data) internal returns (bytes memory) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            calldatacopy(ptr, data.offset, data.length)
            let success := call(gas(), target, value, ptr, data.length, 0x00, 0x00)

            returndatacopy(add(0x40, ptr), 0x00, returndatasize())

            if iszero(success) {
                revert(add(0x40, ptr), returndatasize())
            }

            mstore(add(0x20, ptr), returndatasize())
            mstore(ptr, 0x20)
            return(ptr, add(0x40, returndatasize()))
        }
    }

    function _hashCall(address payable target, uint256 value, bytes calldata data, uint256 nonce_) internal view returns (bytes32 signingHash) {
        bytes32 domainSep = _DOMAIN_SEPARATOR();
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            calldatacopy(ptr, data.offset, data.length)
            let dataHash := keccak256(ptr, data.length)

            mstore(ptr, _CALL_TYPEHASH)
            mstore(add(0x20, ptr), nonce_)
            mstore(add(0x40, ptr), address())
            mstore(add(0x60, ptr), target)
            mstore(add(0x80, ptr), value)
            mstore(add(0xa0, ptr), dataHash)
            let structHash := keccak256(ptr, 0xc0)

            mstore(0x00, 0x1901)
            mstore(0x20, domainSep)
            mstore(0x40, structHash)

            signingHash := keccak256(0x1e, 0x42)

            mstore(0x40, ptr)
        }
    }

    function cleanup(address payable beneficiary) external {
        if (msg.sender == address(_cachedThis)) {
            selfdestruct(beneficiary);
        }

        address owner_ = owner();
        if (_msgSender() != owner_) {
            if (owner_ != address(0)) {
                _permissionDenied();
            }
            address pendingOwner_ = pendingOwner();
            if ((pendingOwner_ == address(0)).or(beneficiary != pendingOwner_)) {
                _permissionDenied();
            }
        }
        selfdestruct(beneficiary);
    }
}
