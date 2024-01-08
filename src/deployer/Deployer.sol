// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {IERC165, TwoStepOwnable, Ownable} from "./TwoStepOwnable.sol";
import {Panic} from "../utils/Panic.sol";
import {AddressDerivation} from "../utils/AddressDerivation.sol";
import {verifyIPFS} from "../vendor/verifyIPFS.sol";

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

    uint64 public nextNonce = 1;
    mapping(uint64 => DoublyLinkedList) private _deploymentLists;
    mapping(uint128 => uint64) private _featureNonce;
    mapping(address => uint64) private _deploymentNonce;

    mapping(uint128 => address) public feeCollector;
    mapping(uint128 => mapping(address => uint256)) public authorizedUntil;
    mapping(uint128 => bytes32) public descriptionHash;

    constructor(address initialOwner) {
        emit OwnershipPending(initialOwner);
        pendingOwner = initialOwner;
    }

    error FeatureInitialized(uint128);

    event Authorized(uint128 indexed, address indexed, uint256);

    function authorize(uint128 feature, address who, uint256 expiry) public onlyOwner returns (bool) {
        if (feature == 0) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        if (descriptionHash[feature] == 0) {
            revert FeatureInitialized(feature);
        }
        emit Authorized(feature, who, expiry);
        authorizedUntil[feature][who] = expiry;
        return true;
    }

    function _requireAuthorized(uint128 feature) private view {
        if (block.timestamp >= authorizedUntil[feature][msg.sender]) {
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

    function setDescription(uint128 feature, string calldata description) public onlyOwner returns (string memory) {
        if (descriptionHash[feature] != 0) {
            revert FeatureInitialized(feature);
        }
        // TODO: put something better in the `"name"` field
        string memory content =
            string(abi.encodePacked("{\"description\": \"", description, "\", \"name\": \"0xV5\"}\n"));
        bytes32 contentHash = verifyIPFS.ipfsHash(content);
        descriptionHash[feature] = contentHash;
        string memory ipfsURI = string(abi.encodePacked("ipfs://", verifyIPFS.base58sha256multihash(contentHash)));
        emit PermanentURI(ipfsURI, feature);
        return ipfsURI;
    }

    event Deployed(uint128 indexed, address indexed);

    error DeployFailed();

    function deploy(uint128 feature, bytes calldata initCode)
        public
        payable
        onlyAuthorized(feature)
        returns (address predicted)
    {
        uint64 thisNonce = nextNonce++;
        predicted = AddressDerivation.deriveContract(address(this), thisNonce);
        _deploymentNonce[predicted] = thisNonce;
        emit Deployed(feature, predicted);

        uint64 prevNonce = _featureNonce[feature];
        _featureNonce[feature] = thisNonce;
        _deploymentLists[thisNonce] = DoublyLinkedList({prev: prevNonce, next: 0, feature: feature});
        if (prevNonce == 0) {
            emit Transfer(address(0), predicted, feature);
        } else {
            emit Transfer(AddressDerivation.deriveContract(address(this), prevNonce), predicted, feature);
            _deploymentLists[prevNonce].next = thisNonce;
        }

        address thisFeeCollector = feeCollector[feature];
        address deployed;
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            calldatacopy(ptr, initCode.offset, initCode.length)
            mstore(add(ptr, initCode.length), and(0xffffffffffffffffffffffffffffffffffffffff, thisFeeCollector))
            deployed := create(callvalue(), ptr, add(initCode.length, 0x20))
        }
        if (deployed != predicted || deployed.code.length == 0) {
            revert DeployFailed();
        }
    }

    event Unsafe(uint128 indexed, uint64 indexed);

    function setUnsafe(uint128 feature, uint64 nonce) public onlyAuthorized(feature) returns (bool) {
        DoublyLinkedList storage entry = _deploymentLists[nonce];
        if (entry.feature != feature) {
            revert PermissionDenied();
        }
        (uint64 prev, uint64 next) = (entry.prev, entry.next);
        if (next == 0) {
            // assert(_featureNonce[feature] == nonce);
            _featureNonce[feature] = prev;
            emit Transfer(
                AddressDerivation.deriveContract(address(this), nonce),
                prev == 0 ? address(0) : AddressDerivation.deriveContract(address(this), prev),
                feature
            );
        } else {
            _deploymentLists[next].prev = prev;
        }
        if (prev != 0) {
            _deploymentLists[prev].next = next;
        }
        delete entry.prev;
        delete entry.next;
        delete entry.feature;

        emit Unsafe(feature, nonce);
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
                if (!success) {
                    assembly ("memory-safe") {
                        revert(add(reason, 0x20), mload(reason))
                    }
                }
                assembly ("memory-safe") {
                    mstore(0x40, freeMemPtr)
                }
            }
        }
    }

    string public constant override name = "0xV5";
    string public constant override symbol = "0xV5";

    function supportsInterface(bytes4 interfaceId) public view override(IERC165, Ownable) returns (bool) {
        return super.supportsInterface(interfaceId) || interfaceId == 0x80ac58cd || interfaceId == 0x5b5e139f;
    }

    function balanceOf(address owner) external view override returns (uint256) {
        DoublyLinkedList storage entry = _deploymentLists[_deploymentNonce[owner]];
        (uint64 next, uint128 feature) = (entry.next, entry.feature);
        if (feature != 0 && next == 0) {
            return 1;
        }
        return 0;
    }

    function ownerOf(uint256 tokenId) external view returns (address) {
        if (tokenId > type(uint128).max) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        uint64 nonce = _featureNonce[uint128(tokenId)];
        if (nonce == 0) {
            return address(0);
        } else {
            return AddressDerivation.deriveContract(address(this), nonce);
        }
    }

    function getApproved(uint256) external pure override returns (address) {
        return address(0);
    }

    function isApprovedForAll(address, address) external pure override returns (bool) {
        return false;
    }

    error NoToken(uint256);

    function tokenURI(uint256 tokenId) external view returns (string memory) {
        if (tokenId > type(uint128).max) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        if (_featureNonce[uint128(tokenId)] == 0) {
            revert NoToken(tokenId);
        }
        return string(abi.encodePacked("ipfs://", verifyIPFS.base58sha256multihash(descriptionHash[uint128(tokenId)])));
    }
}
