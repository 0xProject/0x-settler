// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IERC165, AbstractOwnable} from "./TwoStepOwnable.sol";
import {ERC1967UUPSUpgradeable, ERC1967TwoStepOwnable} from "../proxy/ERC1967UUPSUpgradeable.sol";
import {Context} from "../Context.sol";
import {Panic} from "../utils/Panic.sol";
import {Create3} from "../utils/Create3.sol";
import {IPFS} from "../utils/IPFS.sol";
import {ItoA} from "../utils/ItoA.sol";
import {MultiCall} from "../utils/MultiCall.sol";

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

contract Deployer is ERC1967UUPSUpgradeable, Context, ERC1967TwoStepOwnable, IERC721ViewMetadata, MultiCall {
    struct DoublyLinkedListElem {
        uint64 prev;
        uint64 next;
    }

    struct DoublyLinkedList {
        mapping(uint64 => DoublyLinkedListElem) links;
        uint64 head;
        uint64 highWater;
        uint64 lastNonce;
    }

    struct DeployInfo {
        uint128 feature;
        uint64 nonce;
    }

    struct ExpiringAuthorization {
        address who;
        uint40 deadline;
    }

    /// @custom:storage-location erc7201:0xV5Deployer.1
    struct ZeroExV5DeployerStorage1 {
        mapping(uint128 => DoublyLinkedList) featureLists;
        mapping(address => DeployInfo) deployInfo;
        mapping(uint128 => ExpiringAuthorization) authorized;
        mapping(uint128 => bytes32) descriptionHash;
    }

    uint256 private constant _BASE_SLOT = 0x6fc90c2fe4d07a554a5baba07c2807f581f77bd906c5068b416617fdd1427800;

    function _stor1() private pure returns (ZeroExV5DeployerStorage1 storage r) {
        assembly ("memory-safe") {
            r.slot := _BASE_SLOT
        }
    }

    function authorized(uint128 feature) external view returns (address who, uint40 deadline) {
        ExpiringAuthorization storage result = _stor1().authorized[feature];
        (who, deadline) = (result.who, result.deadline);
    }

    function descriptionHash(uint128 feature) external view returns (bytes32) {
        return _stor1().descriptionHash[feature];
    }

    constructor() ERC1967UUPSUpgradeable(1) {
        ZeroExV5DeployerStorage1 storage stor1 = _stor1();
        bytes32 slot;
        assembly ("memory-safe") {
            slot := stor1.slot
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
        return Create3.predict(_salt(feature, _stor1().featureLists[feature].lastNonce + 1));
    }

    error FeatureNotInitialized(uint128);

    event Authorized(uint128 indexed, address indexed, uint40);

    function authorize(uint128 feature, address who, uint40 deadline) public onlyOwner returns (bool) {
        require((who == address(0)) == (block.timestamp > deadline));
        if (feature == 0) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        ZeroExV5DeployerStorage1 storage stor1 = _stor1();
        if (stor1.descriptionHash[feature] == 0) {
            revert FeatureNotInitialized(feature);
        }
        emit Authorized(feature, who, deadline);
        stor1.authorized[feature] = ExpiringAuthorization({who: who, deadline: deadline});
        return true;
    }

    function _requireAuthorized(uint128 feature) private view {
        ExpiringAuthorization storage authorization = _stor1().authorized[feature];
        (address who, uint40 deadline) = (authorization.who, authorization.deadline);
        if (_msgSender() != who || (deadline != type(uint40).max && block.timestamp > deadline)) {
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
        ZeroExV5DeployerStorage1 storage stor1 = _stor1();
        if (stor1.descriptionHash[feature] != 0) {
            revert FeatureInitialized(feature);
        }
        content = string.concat(
            "{\"description\": \"", description, "\", \"name\": \"0xV5 feature ", ItoA.itoa(feature), "\"}\n"
        );
        bytes32 contentHash = IPFS.dagPbUnixFsHash(content);
        stor1.descriptionHash[feature] = contentHash;
        emit PermanentURI(IPFS.CIDv0(contentHash), feature);
    }

    event Deployed(uint128 indexed, uint64 indexed, address indexed);

    error DeployFailed(uint64);

    function deploy(uint128 feature, bytes calldata initCode)
        public
        payable
        onlyAuthorized(feature)
        returns (address predicted, uint64 thisNonce)
    {
        ZeroExV5DeployerStorage1 storage stor1 = _stor1();
        DoublyLinkedList storage featureList = stor1.featureLists[feature];
        uint64 prevNonce;
        (prevNonce, thisNonce) = (featureList.head, featureList.lastNonce);
        thisNonce++;
        (featureList.head, featureList.lastNonce) = (thisNonce, thisNonce);

        bytes32 salt = _salt(feature, thisNonce);
        predicted = Create3.predict(salt);
        stor1.deployInfo[predicted] = DeployInfo({feature: feature, nonce: thisNonce});
        emit Deployed(feature, thisNonce, predicted);

        featureList.links[thisNonce] = DoublyLinkedListElem({prev: prevNonce, next: 0});
        if (prevNonce == 0) {
            emit Transfer(address(0), predicted, feature);
        } else {
            emit Transfer(Create3.predict(_salt(feature, prevNonce)), predicted, feature);
            featureList.links[prevNonce].next = thisNonce;
        }

        if (Create3.createFromCalldata(salt, initCode, msg.value) != predicted || predicted.code.length == 0) {
            revert DeployFailed(thisNonce);
        }
    }

    error FutureDeployment(uint64);

    event Removed(uint128 indexed, uint64 indexed, address indexed);

    function remove(uint128 feature, uint64 nonce) public onlyAuthorized(feature) returns (bool) {
        ZeroExV5DeployerStorage1 storage stor1 = _stor1();
        DoublyLinkedList storage featureList = stor1.featureLists[feature];
        if (nonce > featureList.lastNonce) {
            revert FutureDeployment(nonce);
        }
        DoublyLinkedListElem storage entry = featureList.links[nonce];

        (uint64 prevNonce, uint64 nextNonce) = (entry.prev, entry.next);
        address deployment = Create3.predict(_salt(feature, nonce));
        if (nextNonce == 0) {
            if (nonce > featureList.highWater) {
                // assert(head.head == nonce);
                featureList.head = prevNonce;
                emit Transfer(
                    deployment, prevNonce == 0 ? address(0) : Create3.predict(_salt(feature, prevNonce)), feature
                );
            }
        } else {
            featureList.links[nextNonce].prev = prevNonce;
        }
        if (prevNonce != 0) {
            featureList.links[prevNonce].next = nextNonce;
        }
        delete entry.prev;
        delete entry.next;

        emit Removed(feature, nonce, deployment);
        return true;
    }

    event RemovedAll(uint128 indexed);

    function removeAll(uint128 feature) public onlyAuthorized(feature) returns (bool) {
        DoublyLinkedList storage featureList = _stor1().featureLists[feature];
        uint64 nonce;
        (nonce, featureList.head, featureList.highWater) = (featureList.head, 0, featureList.lastNonce);
        if (nonce != 0) {
            emit Transfer(Create3.predict(_salt(feature, nonce)), address(0), feature);
        }
        emit RemovedAll(feature);
        return true;
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
        ZeroExV5DeployerStorage1 storage stor1 = _stor1();
        DeployInfo storage info = stor1.deployInfo[instance];
        (uint128 feature, uint64 nonce) = (info.feature, info.nonce);
        if (feature == 0) {
            return 0;
        }
        DoublyLinkedList storage featureList = stor1.featureLists[feature];
        if (nonce > featureList.highWater && featureList.links[nonce].next == 0) {
            return 1;
        }
        return 0;
    }

    error NoToken(uint256);

    function _requireTokenExists(uint256 tokenId) private view returns (uint64 nonce) {
        if (tokenId > type(uint128).max) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        if ((nonce = _stor1().featureLists[uint128(tokenId)].head) == 0) {
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
        return IPFS.CIDv0(_stor1().descriptionHash[uint128(tokenId)]);
    }

    // solc is dumb

    function owner() public view override(ERC1967UUPSUpgradeable, AbstractOwnable) returns (address) {
        return super.owner();
    }
}
