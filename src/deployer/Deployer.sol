// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {IERC165, TwoStepOwnable, Ownable} from "./TwoStepOwnable.sol";
import {Panic} from "../utils/Panic.sol";
import {AddressDerivation} from "../utils/AddressDerivation.sol";
import {IPFS} from "../utils/IPFS.sol";
import {ItoA} from "../utils/ItoA.sol";
import {IFeeCollector} from "../core/IFeeCollector.sol";
import {Revert} from "../utils/Revert.sol";

library UnsafeArray {
    function unsafeGet(bytes[] calldata datas, uint256 i) internal pure returns (bytes calldata data) {
        assembly ("memory-safe") {
            // helper functions
            function overflow() {
                mstore(0x00, 0x4e487b71) // keccak256("Panic(uint256)")[:4]
                mstore(0x20, 0x11) // 0x11 -> arithmetic under-/over- flow
                revert(0x1c, 0x24)
            }
            function bad_calldata() {
                revert(0x00, 0x00) // empty reason for malformed calldata
            }

            // initially, we set `data.offset` to the pointer to the length. this is 32 bytes before the actual start of data
            data.offset :=
                add(
                    datas.offset,
                    calldataload(
                        add(shl(5, i), datas.offset) // can't overflow; we assume `i` is in-bounds
                    )
                )
            // because the offset to `data` stored in `datas` is arbitrary, we have to check it
            if lt(data.offset, add(shl(5, datas.length), datas.offset)) { overflow() }
            if iszero(lt(data.offset, calldatasize())) { bad_calldata() }
            // now we load `data.length` and set `data.offset` to the start of datas
            data.length := calldataload(data.offset)
            data.offset := add(data.offset, 0x20) // can't overflow; calldata can't be that long
            {
                // check that the end of `data` is in-bounds
                let end := add(data.offset, data.length)
                if lt(end, data.offset) { overflow() }
                if gt(end, calldatasize()) { bad_calldata() }
            }
        }
    }
}

interface IERC721View is IERC165 {
    event Transfer(address indexed from, address indexed to, uint256 indexed tokenId);

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

contract Deployer is TwoStepOwnable, IERC721ViewMetadata {
    using UnsafeArray for bytes[];

    struct DoublyLinkedList {
        uint64 prev;
        uint64 next;
        uint128 feature;
    }

    struct ListHead {
        uint64 head;
        uint64 highWater;
    }

    struct ExpiringAuthorization {
        address who;
        uint96 deadline;
    }

    bytes32 private _pad; // ensure that `nextNonce` starts in its own slot

    uint64 public nextNonce = 1;
    mapping(uint64 => DoublyLinkedList) private _deploymentLists;
    mapping(uint128 => ListHead) private _featureNonce;
    mapping(address => uint64) private _deploymentNonce;

    mapping(uint128 => address) public feeCollector;
    mapping(uint128 => ExpiringAuthorization) public authorized;
    mapping(uint128 => bytes32) public descriptionHash;

    constructor(address initialOwner) {
        emit OwnershipPending(initialOwner);
        pendingOwner = initialOwner;
    }

    event Authorized(uint128 indexed, address indexed, uint256);

    error FeatureNotInitialized(uint128);

    function authorize(uint128 feature, address who, uint96 deadline) public onlyOwner returns (bool) {
        require((who == address(0)) == (block.timestamp > deadline));
        if (feature == 0) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        if (descriptionHash[feature] == 0) {
            revert FeatureNotInitialized(feature);
        }
        emit Authorized(feature, who, deadline);
        authorized[feature] = ExpiringAuthorization({who: who, deadline: deadline});
        return true;
    }

    function _requireAuthorized(uint128 feature) private view {
        ExpiringAuthorization storage authorization = authorized[feature];
        (address who, uint96 deadline) = (authorization.who, authorization.deadline);
        if (msg.sender != who || (deadline != type(uint96).max && block.timestamp > deadline)) {
            revert PermissionDenied();
        }
    }

    modifier onlyAuthorized(uint128 feature) {
        _requireAuthorized(feature);
        _;
    }

    event FeeCollectorChanged(uint128 indexed, address indexed);

    function setFeeCollector(uint128 feature, address newFeeCollector) public onlyOwner returns (bool) {
        emit FeeCollectorChanged(feature, newFeeCollector);
        feeCollector[feature] = newFeeCollector;
        return true;
    }

    event PermanentURI(string, uint256 indexed);

    error FeatureInitialized(uint128);

    function setDescription(uint128 feature, string calldata description)
        public
        onlyOwner
        returns (string memory content)
    {
        if (descriptionHash[feature] != 0) {
            revert FeatureInitialized(feature);
        }
        content = string.concat(
            "{\"description\": \"", description, "\", \"name\": \"0xV5 feature ", ItoA.itoa(feature), "\"}\n"
        );
        bytes32 contentHash = IPFS.dagPbUnixFsHash(content);
        descriptionHash[feature] = contentHash;
        emit PermanentURI(IPFS.CIDv0(contentHash), feature);
    }

    event Deployed(uint128 indexed, uint64 indexed, address indexed);

    error DeployFailed(uint64);

    uint256 private constant _ADDRESS_MASK = 0x00ffffffffffffffffffffffffffffffffffffffff;

    function deploy(uint128 feature, bytes calldata initCode)
        public
        payable
        onlyAuthorized(feature)
        returns (address predicted)
    {
        uint64 thisNonce = nextNonce++;
        predicted = AddressDerivation.deriveContract(address(this), thisNonce);
        _deploymentNonce[predicted] = thisNonce;
        emit Deployed(feature, thisNonce, predicted);

        uint64 prevNonce = _featureNonce[feature].head;
        _featureNonce[feature].head = thisNonce;
        _deploymentLists[thisNonce] = DoublyLinkedList({prev: prevNonce, next: 0, feature: feature});
        if (prevNonce == 0) {
            emit Transfer(address(0), predicted, feature);
        } else {
            emit Transfer(AddressDerivation.deriveContract(address(this), prevNonce), predicted, feature);
            _deploymentLists[prevNonce].next = thisNonce;
        }

        address thisFeeCollector = feeCollector[feature];
        bool success;
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            calldatacopy(ptr, initCode.offset, initCode.length)
            mstore(add(ptr, initCode.length), and(_ADDRESS_MASK, thisFeeCollector))
            mstore(0x00, 0xc415b95c) // selector for `feeCollector()`
            // Yul evaluation order is right-to-left
            success :=
                and(
                    // check that the call to `feeCollector()` returned nonempty and returned the expected address
                    and(gt(returndatasize(), 0x1f), eq(mload(0x00), and(_ADDRESS_MASK, thisFeeCollector))),
                    and(
                        // call `feeCollector()` on the predicted address and check for success (succeeds with empty
                        // returnData if deployment failed, deployed to the wrong address, or produced empty bytecode)
                        staticcall(gas(), predicted, 0x1c, 0x04, 0x00, 0x20),
                        // CREATE the new instance and check that it returns the predicted address
                        eq(and(_ADDRESS_MASK, predicted), create(callvalue(), ptr, add(initCode.length, 0x20)))
                    )
                )
        }
        if (!success) {
            revert DeployFailed(thisNonce);
        }
    }

    event Removed(uint128 indexed, uint64 indexed, address indexed);

    function remove(uint128 feature, uint64 nonce) public onlyAuthorized(feature) returns (bool) {
        DoublyLinkedList storage entry = _deploymentLists[nonce];
        if (entry.feature != feature) {
            revert PermissionDenied();
        }
        (uint64 prev, uint64 next) = (entry.prev, entry.next);
        address deployment = AddressDerivation.deriveContract(address(this), nonce);
        if (next == 0) {
            ListHead storage headEntry = _featureNonce[feature];
            if (nonce > headEntry.highWater) {
                // assert(headEntry.head == nonce);
                headEntry.head = prev;
                emit Transfer(
                    deployment, prev == 0 ? address(0) : AddressDerivation.deriveContract(address(this), prev), feature
                );
            }
        } else {
            _deploymentLists[next].prev = prev;
        }
        if (prev != 0) {
            _deploymentLists[prev].next = next;
        }
        delete entry.prev;
        delete entry.next;
        delete entry.feature;

        emit Removed(feature, nonce, deployment);
        return true;
    }

    event RemovedAll(uint256 indexed);

    function removeAll(uint128 feature) public onlyAuthorized(feature) returns (bool) {
        ListHead storage entry = _featureNonce[feature];
        uint64 nonce = entry.head;
        if (nonce != 0) {
            // assert(nonce > entry.highWater);
            (entry.head, entry.highWater) = (0, nonce);
            emit Transfer(AddressDerivation.deriveContract(address(this), nonce), address(0), feature);
        }
        emit RemovedAll(feature);
        return true;
    }

    // in spite of the fact that `deploy` is payable, `multicall` cannot be
    // payable for security. therefore, there are some use cases where it is
    // necessary to make multiple calls to this contract.
    function multicall(bytes[] calldata datas) public {
        uint256 freeMemPtr;
        assembly ("memory-safe") {
            freeMemPtr := mload(0x40)
        }
        unchecked {
            for (uint256 i; i < datas.length; i++) {
                (bool success, bytes memory reason) = address(this).delegatecall(datas.unsafeGet(i));
                Revert.maybeRevert(success, reason);
                assembly ("memory-safe") {
                    mstore(0x40, freeMemPtr)
                }
            }
        }
    }

    string public constant override name = "0xV5";
    string public constant override symbol = "0xV5";

    function supportsInterface(bytes4 interfaceId) public view override(IERC165, Ownable) returns (bool) {
        return super.supportsInterface(interfaceId) || interfaceId == 0x80ac58cd // regular IERC721
            || interfaceId == type(IERC721ViewMetadata).interfaceId;
    }

    function balanceOf(address owner) external view override returns (uint256) {
        if (owner == address(0)) {
            revert ZeroAddress();
        }
        DoublyLinkedList storage entry = _deploymentLists[_deploymentNonce[owner]];
        (uint64 next, uint128 feature) = (entry.next, entry.feature);
        if (feature != 0 && next == 0) {
            return 1;
        }
        return 0;
    }

    error NoToken(uint256);

    function _requireTokenExists(uint256 tokenId) private view returns (uint64 nonce) {
        if (tokenId > type(uint128).max) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        if ((nonce = _featureNonce[uint128(tokenId)].head) == 0) {
            revert NoToken(tokenId);
        }
    }

    function ownerOf(uint256 tokenId) external view override returns (address) {
        return AddressDerivation.deriveContract(address(this), _requireTokenExists(tokenId));
    }

    modifier tokenExists(uint256 tokenId) {
        _requireTokenExists(tokenId);
        _;
    }

    function getApproved(uint256 tokenId) external view override tokenExists(tokenId) returns (address) {
        return address(0);
    }

    function isApprovedForAll(address, address) external pure override returns (bool) {
        return false;
    }

    function tokenURI(uint256 tokenId) external view override tokenExists(tokenId) returns (string memory) {
        return IPFS.CIDv0(descriptionHash[uint128(tokenId)]);
    }
}
