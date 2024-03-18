// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IERC165, AbstractOwnable} from "./TwoStepOwnable.sol";
import {
    ERC1967UUPSUpgradeable, ERC1967TwoStepOwnable, AbstractUUPSUpgradeable
} from "../proxy/ERC1967UUPSUpgradeable.sol";
import {Context} from "../Context.sol";
import {Panic} from "../utils/Panic.sol";
import {Create3} from "../utils/Create3.sol";
import {IPFS} from "../utils/IPFS.sol";
import {ItoA} from "../utils/ItoA.sol";
import {ProxyMultiCall} from "../utils/ProxyMultiCall.sol";
import {Feature, wrap, isNull} from "./Feature.sol";
import {Nonce, zero, isNull} from "./Nonce.sol";

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

library NonceList {
    struct ListElem {
        Nonce prev;
        Nonce next;
    }

    struct List {
        Nonce head;
        Nonce highWater;
        Nonce lastNonce;
        /// @dev if you update this, you also have to update the size of `Nonce` in Nonce.sol
        ListElem[4294967296] links;
    }

    function _idx(ListElem[4294967296] storage links, Nonce i) private pure returns (ListElem storage r) {
        assembly ("memory-safe") {
            r.slot := add(links.slot, and(0xffffffff, i))
        }
    }

    function push(List storage list) internal returns (Nonce prevNonce, Nonce thisNonce) {
        (prevNonce, thisNonce) = (list.head, list.lastNonce.incr());
        // update the head
        (list.head, list.lastNonce) = (thisNonce, thisNonce);
        // update the links
        _idx(list.links, thisNonce).prev = prevNonce;
        if (!prevNonce.isNull()) {
            _idx(list.links, prevNonce).next = thisNonce;
        }
    }

    error FutureNonce(Nonce);

    function remove(List storage list, Nonce thisNonce) internal returns (Nonce newHead, bool updatedHead) {
        if (thisNonce > list.lastNonce) {
            revert FutureNonce(thisNonce);
        }

        ListElem storage entry = _idx(list.links, thisNonce);
        Nonce nextNonce;
        (newHead, nextNonce) = (entry.prev, entry.next);
        if (nextNonce.isNull()) {
            if (thisNonce > list.highWater) {
                updatedHead = true;
                list.head = newHead;
            }
        } else {
            _idx(list.links, nextNonce).prev = newHead;
        }
        if (!newHead.isNull()) {
            _idx(list.links, newHead).next = nextNonce;
        }
        (entry.prev, entry.next) = (zero, zero);
    }

    function clear(List storage list) internal returns (Nonce oldHead) {
        (oldHead, list.head, list.highWater) = (list.head, zero, list.lastNonce);
    }
}

contract Deployer is ERC1967UUPSUpgradeable, Context, ERC1967TwoStepOwnable, IERC721ViewMetadata, ProxyMultiCall {
    using NonceList for NonceList.List;

    struct FeatureInfo {
        bytes32 descriptionHash;
        address auth;
        uint40 deadline;
        NonceList.List list;
    }

    struct DeployInfo {
        Feature feature;
        Nonce nonce;
    }

    /// @custom:storage-location erc7201:0xV5Deployer.1
    struct ZeroExV5DeployerStorage1 {
        mapping(Feature => FeatureInfo) featureInfo;
        mapping(address => DeployInfo) deployInfo;
    }

    uint256 private constant _BASE_SLOT = 0x6fc90c2fe4d07a554a5baba07c2807f581f77bd906c5068b416617fdd1427800;

    function _stor1() private pure returns (ZeroExV5DeployerStorage1 storage r) {
        assembly ("memory-safe") {
            r.slot := _BASE_SLOT
        }
    }

    function authorized(Feature feature) external view returns (address auth, uint40 deadline) {
        FeatureInfo storage result = _stor1().featureInfo[feature];
        (auth, deadline) = (result.auth, result.deadline);
    }

    function descriptionHash(Feature feature) external view returns (bytes32) {
        return _stor1().featureInfo[feature].descriptionHash;
    }

    constructor() ERC1967UUPSUpgradeable(1) {
        ZeroExV5DeployerStorage1 storage stor1 = _stor1();
        // storage starts at the slot defined by ERC7201
        {
            bytes32 slot;
            assembly ("memory-safe") {
                slot := stor1.slot
            }
            assert(
                slot == keccak256(abi.encodePacked(uint256(keccak256("0xV5Deployer.1")) - 1)) & ~bytes32(uint256(0xff))
            );
        }

        // `ListElem` does not pack because it is a struct
        {
            NonceList.ListElem storage linkZero = stor1.featureInfo[wrap(1)].list.links[0];
            NonceList.ListElem storage linkOne = stor1.featureInfo[wrap(1)].list.links[1];
            uint256 slotZero;
            uint256 slotOne;
            assembly ("memory-safe") {
                slotZero := linkZero.slot
                slotOne := linkOne.slot
            }
            assert(slotZero + 1 == slotOne);
        }
    }

    function initialize(address initialOwner) external {
        require(address(this) == 0x00000000000004533Fe15556B1E086BB1A72cEae || block.chainid == 31337);
        _setPendingOwner(initialOwner);
        super._initialize();
    }

    uint8 private constant _FEATURE_SHIFT = 128;
    uint8 private constant _CHAIN_SHIFT = 64;

    function _salt(Feature feature, Nonce nonce) internal view returns (bytes32) {
        return bytes32(
            uint256(Feature.unwrap(feature)) << _FEATURE_SHIFT | uint256(block.chainid) << _CHAIN_SHIFT
                | uint256(Nonce.unwrap(nonce))
        );
    }

    function next(Feature feature) external view returns (address) {
        return Create3.predict(_salt(feature, _stor1().featureInfo[feature].list.lastNonce.incr()));
    }

    error NotDeployed(address);

    function deployInfo(address instance) public view returns (Feature feature, Nonce nonce) {
        DeployInfo storage info = _stor1().deployInfo[instance];
        (feature, nonce) = (info.feature, info.nonce);
        if (feature.isNull()) {
            revert NotDeployed(instance);
        }
    }

    error FeatureNotInitialized(Feature);

    event Authorized(Feature indexed, address indexed, uint40);

    function authorize(Feature feature, address auth, uint40 deadline) external onlyOwner returns (bool) {
        require((auth == address(0)) == (block.timestamp > deadline));
        if (feature.isNull()) {
            Panic.panic(Panic.ENUM_CAST);
        }
        FeatureInfo storage featureInfo = _stor1().featureInfo[feature];
        if (featureInfo.descriptionHash == 0) {
            revert FeatureNotInitialized(feature);
        }
        emit Authorized(feature, auth, deadline);
        (featureInfo.auth, featureInfo.deadline) = (auth, deadline);
        return true;
    }

    function _requireAuthorized(Feature feature) private view returns (FeatureInfo storage featureInfo) {
        featureInfo = _stor1().featureInfo[feature];
        (address auth, uint40 deadline) = (featureInfo.auth, featureInfo.deadline);
        if (_msgSender() != auth || (deadline != type(uint40).max && block.timestamp > deadline)) {
            revert PermissionDenied();
        }
    }

    event PermanentURI(string, uint256 indexed);

    error FeatureInitialized(Feature);

    function setDescription(Feature feature, string calldata description)
        external
        onlyOwner
        returns (string memory content)
    {
        FeatureInfo storage featureInfo = _stor1().featureInfo[feature];
        if (featureInfo.descriptionHash != 0) {
            revert FeatureInitialized(feature);
        }
        content = string.concat(
            "{\"description\": \"",
            description,
            "\", \"name\": \"0xV5 feature ",
            ItoA.itoa(Feature.unwrap(feature)),
            "\"}\n"
        );
        bytes32 contentHash = IPFS.dagPbUnixFsHash(content);
        featureInfo.descriptionHash = contentHash;
        emit PermanentURI(IPFS.CIDv0(contentHash), Feature.unwrap(feature));
    }

    error DeployFailed(Feature, Nonce, address);

    event Deployed(Feature indexed, Nonce indexed, address indexed);

    function deploy(Feature feature, bytes calldata initCode)
        external
        payable
        returns (address predicted, Nonce thisNonce)
    {
        Nonce prevNonce;
        (prevNonce, thisNonce) = _requireAuthorized(feature).list.push();

        bytes32 salt = _salt(feature, thisNonce);
        predicted = Create3.predict(salt);
        emit Transfer(
            prevNonce.isNull() ? address(0) : Create3.predict(_salt(feature, prevNonce)),
            predicted,
            Feature.unwrap(feature)
        );

        _stor1().deployInfo[predicted] = DeployInfo({feature: feature, nonce: thisNonce});
        emit Deployed(feature, thisNonce, predicted);

        if (Create3.createFromCalldata(salt, initCode, msg.value) != predicted || predicted.code.length == 0) {
            revert DeployFailed(feature, thisNonce, predicted);
        }
    }

    event Removed(Feature indexed, Nonce indexed, address indexed);

    function remove(Feature feature, Nonce nonce) public returns (bool) {
        (Nonce newHead, bool updatedHead) = _requireAuthorized(feature).list.remove(nonce);
        address deployment = Create3.predict(_salt(feature, nonce));
        if (updatedHead) {
            emit Transfer(
                deployment,
                newHead.isNull() ? address(0) : Create3.predict(_salt(feature, newHead)),
                Feature.unwrap(feature)
            );
        }
        emit Removed(feature, nonce, deployment);
        return true;
    }

    function remove(address instance) external returns (bool) {
        (Feature feature, Nonce nonce) = deployInfo(instance);
        return remove(feature, nonce);
    }

    event RemovedAll(Feature indexed);

    function removeAll(Feature feature) external returns (bool) {
        Nonce nonce = _requireAuthorized(feature).list.clear();
        if (!nonce.isNull()) {
            emit Transfer(Create3.predict(_salt(feature, nonce)), address(0), Feature.unwrap(feature));
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
        (Feature feature, Nonce nonce) = (info.feature, info.nonce);
        if (feature.isNull()) {
            return 0;
        }
        if (nonce == stor1.featureInfo[feature].list.head) {
            return 1;
        }
        return 0;
    }

    error NoToken(uint256);

    function _requireTokenExists(Feature feature) private view returns (Nonce nonce) {
        if ((nonce = _stor1().featureInfo[feature].list.head).isNull()) {
            revert NoToken(Feature.unwrap(feature));
        }
    }

    function _requireTokenExists(uint256 tokenId) private view returns (Nonce) {
        return _requireTokenExists(wrap(tokenId));
    }

    function ownerOf(uint256 tokenId) external view override returns (address) {
        Feature feature = wrap(tokenId);
        return Create3.predict(_salt(feature, _requireTokenExists(feature)));
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

    function tokenURI(uint256 tokenId) external view override returns (string memory) {
        Feature feature = wrap(tokenId);
        _requireTokenExists(feature);
        return IPFS.CIDv0(_stor1().featureInfo[feature].descriptionHash);
    }

    // solc is dumb

    function owner() public view override(ERC1967UUPSUpgradeable, AbstractOwnable) returns (address) {
        return super.owner();
    }

    function implementation() public view override(AbstractUUPSUpgradeable, ERC1967UUPSUpgradeable) returns (address) {
        return super.implementation();
    }
}
