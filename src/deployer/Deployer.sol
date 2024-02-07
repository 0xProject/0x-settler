// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IERC165, AbstractOwnable} from "./TwoStepOwnable.sol";
import {ERC1967UUPSUpgradeable, ERC1967TwoStepOwnable} from "../proxy/ERC1967UUPSUpgradeable.sol";
import {Panic} from "../utils/Panic.sol";
import {Create3} from "../utils/Create3.sol";
import {IPFS} from "../utils/IPFS.sol";
import {ItoA} from "../utils/ItoA.sol";
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

contract Deployer is ERC1967UUPSUpgradeable, ERC1967TwoStepOwnable, IERC721ViewMetadata {
    using UnsafeArray for bytes[];

    struct DoublyLinkedList {
        uint64 prev;
        uint64 next;
        uint128 feature;
    }

    struct ListHead {
        uint64 head;
        uint64 highWater;
        uint64 prevNonce;
    }

    struct ExpiringAuthorization {
        address who;
        uint96 deadline;
    }

    // @custom:storage-location erc7201:0xV5Deployer.1
    struct ZeroExV5DeployerStorage {
        mapping(uint64 => DoublyLinkedList) deploymentLists;
        mapping(uint128 => ListHead) featureNonce;
        mapping(address => uint64) deploymentNonce;
        mapping(uint128 => ExpiringAuthorization) authorized;
        mapping(uint128 => bytes32) descriptionHash;
    }

    function _stor() private pure returns (ZeroExV5DeployerStorage storage r) {
        assembly ("memory-safe") {
            r.slot := 0x6fc90c2fe4d07a554a5baba07c2807f581f77bd906c5068b416617fdd1427800
        }
    }

    function authorized(uint128 feature) external view returns (address who, uint96 deadline) {
        ExpiringAuthorization storage result = _stor().authorized[feature];
        (who, deadline) = (result.who, result.deadline);
    }

    function descriptionHash(uint128 feature) external view returns (bytes32) {
        return _stor().descriptionHash[feature];
    }

    constructor() ERC1967UUPSUpgradeable(1) {
        ZeroExV5DeployerStorage storage stor = _stor();
        bytes32 slot;
        assembly ("memory-safe") {
            slot := stor.slot
        }
        assert(slot == keccak256(abi.encodePacked(uint256(keccak256("0xV5Deployer.1")) - 1)) & ~bytes32(uint256(0xff)));
    }

    function initialize(address initialOwner) external {
        _setPendingOwner(initialOwner);
        super._initialize();
    }

    function _salt(uint128 feature, uint64 nonce) internal pure returns (bytes32) {
        return bytes32(uint256(feature) << 128 | uint256(nonce));
    }

    function next(uint128 feature) external view returns (address) {
        return Create3.predict(_salt(feature, _stor().featureNonce[feature].prevNonce + 1));
    }

    event Authorized(uint128 indexed, address indexed, uint256);

    error FeatureNotInitialized(uint128);

    function authorize(uint128 feature, address who, uint96 deadline) public onlyOwner returns (bool) {
        require((who == address(0)) == (block.timestamp > deadline));
        if (feature == 0) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        ZeroExV5DeployerStorage storage stor = _stor();
        if (stor.descriptionHash[feature] == 0) {
            revert FeatureNotInitialized(feature);
        }
        emit Authorized(feature, who, deadline);
        stor.authorized[feature] = ExpiringAuthorization({who: who, deadline: deadline});
        return true;
    }

    function _requireAuthorized(uint128 feature) private view {
        ExpiringAuthorization storage authorization = _stor().authorized[feature];
        (address who, uint96 deadline) = (authorization.who, authorization.deadline);
        if (msg.sender != who || (deadline != type(uint96).max && block.timestamp > deadline)) {
            revert PermissionDenied();
        }
    }

    modifier onlyAuthorized(uint128 feature) {
        _requireAuthorized(feature);
        _;
    }

    event PermanentURI(string, uint256 indexed);

    error FeatureInitialized(uint128);

    function setDescription(uint128 feature, string calldata description)
        public
        onlyOwner
        returns (string memory content)
    {
        ZeroExV5DeployerStorage storage stor = _stor();
        if (stor.descriptionHash[feature] != 0) {
            revert FeatureInitialized(feature);
        }
        content = string.concat(
            "{\"description\": \"", description, "\", \"name\": \"0xV5 feature ", ItoA.itoa(feature), "\"}\n"
        );
        bytes32 contentHash = IPFS.dagPbUnixFsHash(content);
        stor.descriptionHash[feature] = contentHash;
        emit PermanentURI(IPFS.CIDv0(contentHash), feature);
    }

    event Deployed(uint128 indexed, uint64 indexed, address indexed);

    error DeployFailed(uint64);

    uint256 private constant _ADDRESS_MASK = 0x00ffffffffffffffffffffffffffffffffffffffff;

    function deploy(uint128 feature, bytes calldata initCode)
        public
        payable
        onlyAuthorized(feature)
        returns (address predicted, uint64 thisNonce)
    {
        ZeroExV5DeployerStorage storage stor = _stor();
        uint64 prevNonce;
        {
            ListHead storage head = stor.featureNonce[feature];
            (prevNonce, thisNonce) = (head.head, head.prevNonce);
            thisNonce++;
            (head.head, head.prevNonce) = (thisNonce, thisNonce);
        }
        bytes32 salt = _salt(feature, thisNonce);
        predicted = Create3.predict(salt);
        stor.deploymentNonce[predicted] = thisNonce;
        emit Deployed(feature, thisNonce, predicted);

        stor.deploymentLists[thisNonce] = DoublyLinkedList({prev: prevNonce, next: 0, feature: feature});
        if (prevNonce == 0) {
            emit Transfer(address(0), predicted, feature);
        } else {
            emit Transfer(Create3.predict(_salt(feature, prevNonce)), predicted, feature);
            stor.deploymentLists[prevNonce].next = thisNonce;
        }

        if (Create3.createFromCalldata(salt, initCode) != predicted || predicted.code.length == 0) {
            revert DeployFailed(thisNonce);
        }
    }

    event Removed(uint128 indexed, uint64 indexed, address indexed);

    function remove(uint128 feature, uint64 nonce) public onlyAuthorized(feature) returns (bool) {
        ZeroExV5DeployerStorage storage stor = _stor();
        DoublyLinkedList storage entry = stor.deploymentLists[nonce];
        if (entry.feature != feature) {
            revert PermissionDenied();
        }
        (uint64 prevNonce, uint64 nextNonce) = (entry.prev, entry.next);
        address deployment = Create3.predict(_salt(feature, nonce));
        if (nextNonce == 0) {
            ListHead storage headEntry = stor.featureNonce[feature];
            if (nonce > headEntry.highWater) {
                // assert(headEntry.head == nonce);
                headEntry.head = prevNonce;
                emit Transfer(
                    deployment, prevNonce == 0 ? address(0) : Create3.predict(_salt(feature, prevNonce)), feature
                );
            }
        } else {
            stor.deploymentLists[nextNonce].prev = prevNonce;
        }
        if (prevNonce != 0) {
            stor.deploymentLists[prevNonce].next = nextNonce;
        }
        delete entry.prev;
        delete entry.next;
        delete entry.feature;

        emit Removed(feature, nonce, deployment);
        return true;
    }

    event RemovedAll(uint256 indexed);

    function removeAll(uint128 feature) public onlyAuthorized(feature) returns (bool) {
        ListHead storage entry = _stor().featureNonce[feature];
        uint64 nonce = entry.head;
        if (nonce != 0) {
            // assert(nonce > entry.highWater);
            (entry.head, entry.highWater) = (0, nonce);
            emit Transfer(Create3.predict(_salt(feature, nonce)), address(0), feature);
        }
        emit RemovedAll(feature);
        return true;
    }

    // in spite of the fact that `deploy` is payable, `multicall` cannot be
    // payable for security. therefore, there are some use cases where it is
    // necessary to make multiple calls to this contract.
    function multicall(bytes[] calldata datas) public {
        uint256 freeMemPtr;
        address target = _implementation;
        assembly ("memory-safe") {
            freeMemPtr := mload(0x40)
        }
        unchecked {
            for (uint256 i; i < datas.length; i++) {
                (bool success, bytes memory reason) = target.delegatecall(datas.unsafeGet(i));
                Revert.maybeRevert(success, reason);
                assembly ("memory-safe") {
                    mstore(0x40, freeMemPtr)
                }
            }
        }
    }

    string public constant override name = "0xV5";
    string public constant override symbol = "0xV5";

    function supportsInterface(bytes4 interfaceId)
        public
        view
        override(IERC165, AbstractOwnable, ERC1967UUPSUpgradeable)
        returns (bool)
    {
        return super.supportsInterface(interfaceId) || interfaceId == 0x80ac58cd // regular IERC721
            || interfaceId == type(IERC721ViewMetadata).interfaceId;
    }

    function balanceOf(address instance) external view override returns (uint256) {
        if (instance == address(0)) {
            revert ZeroAddress();
        }
        ZeroExV5DeployerStorage storage stor = _stor();
        DoublyLinkedList storage entry = stor.deploymentLists[stor.deploymentNonce[instance]];
        (uint64 nextNonce, uint128 feature) = (entry.next, entry.feature);
        if (feature != 0 && nextNonce == 0) {
            return 1;
        }
        return 0;
    }

    error NoToken(uint256);

    function _requireTokenExists(uint256 tokenId) private view returns (uint64 nonce) {
        if (tokenId > type(uint128).max) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        if ((nonce = _stor().featureNonce[uint128(tokenId)].head) == 0) {
            revert NoToken(tokenId);
        }
    }

    function ownerOf(uint256 tokenId) external view override returns (address) {
        return Create3.predict(_salt(uint128(tokenId), _requireTokenExists(tokenId)));
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
        return IPFS.CIDv0(_stor().descriptionHash[uint128(tokenId)]);
    }

    // solc is dumb

    function owner() public view override(ERC1967UUPSUpgradeable, AbstractOwnable) returns (address) {
        return super.owner();
    }
}
