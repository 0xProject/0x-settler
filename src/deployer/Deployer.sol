// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {IERC165} from "@forge-std/interfaces/IERC165.sol";
import {IOwnable} from "../interfaces/IOwnable.sol";
import {AbstractOwnable} from "../utils/TwoStepOwnable.sol";
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
import {IDeployer, IERC721ViewMetadata} from "./IDeployer.sol";
import {DEPLOYER} from "./DeployerAddress.sol";

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

    function get(List storage list, Nonce i) internal view returns (Nonce prev, Nonce next) {
        ListElem storage x = _idx(list.links, i);
        (prev, next) = (x.prev, x.next);
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

    function remove(List storage list, Nonce thisNonce) internal returns (Nonce newHead, bool updatedHead) {
        if (thisNonce > list.lastNonce) {
            revert IDeployer.FutureNonce(thisNonce);
        }

        ListElem storage entry = _idx(list.links, thisNonce);
        Nonce nextNonce;
        (newHead, nextNonce) = (entry.prev, entry.next);
        if (nextNonce.isNull()) {
            (Nonce head, Nonce highWater) = (list.head, list.highWater);
            if (thisNonce == head && thisNonce > highWater) {
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

function salt(Feature feature, Nonce nonce) view returns (bytes32) {
    return
        bytes32(uint256(Feature.unwrap(feature)) << 128 | uint256(block.chainid) << 64 | uint256(Nonce.unwrap(nonce)));
}

/// @custom:security-contact security@0x.org
contract Deployer is IDeployer, ERC1967UUPSUpgradeable, Context, ERC1967TwoStepOwnable, ProxyMultiCall {
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

    /// @custom:storage-location erc7201:ZeroExSettlerDeployer.1
    struct ZeroExSettlerDeployerStorage1 {
        mapping(Feature => FeatureInfo) featureInfo;
        mapping(address => DeployInfo) deployInfo;
    }

    uint256 private constant _BASE_SLOT = 0xb48ce68a610ebca40b9e7586fb84b5d8b0b030b71733a8d4a75a983d5f78e800;

    function _stor1() private pure returns (ZeroExSettlerDeployerStorage1 storage r) {
        assembly ("memory-safe") {
            r.slot := _BASE_SLOT
        }
    }

    function authorized(Feature feature) external view override returns (address auth, uint40 deadline) {
        FeatureInfo storage result = _stor1().featureInfo[feature];
        (auth, deadline) = (result.auth, result.deadline);
    }

    function descriptionHash(Feature feature) external view override returns (bytes32) {
        return _stor1().featureInfo[feature].descriptionHash;
    }

    constructor(uint256 version) ERC1967UUPSUpgradeable(version) {
        ZeroExSettlerDeployerStorage1 storage stor1 = _stor1();
        // storage starts at the slot defined by ERC7201
        {
            bytes32 slot;
            assembly ("memory-safe") {
                slot := stor1.slot
            }
            assert(
                slot
                    == keccak256(abi.encodePacked(uint256(keccak256("ZeroExSettlerDeployer.1")) - 1))
                        & ~bytes32(uint256(0xff))
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

    function initialize(address initialOwner) public virtual {
        require(address(this) == DEPLOYER || block.chainid == 31337);
        if (_implVersion == 1) {
            _setPendingOwner(initialOwner);
        } else {
            assert(initialOwner == address(0));
        }
        super._initialize();
    }

    function next(Feature feature) external view override returns (address) {
        FeatureInfo storage featureInfo = _stor1().featureInfo[feature];
        if (featureInfo.descriptionHash == 0) {
            revert ERC721NonexistentToken(Feature.unwrap(feature));
        }
        return Create3.predict(salt(feature, featureInfo.list.lastNonce.incr()));
    }

    function prev(Feature feature) external view override returns (address) {
        (Nonce prevNonce,) = _stor1().featureInfo[feature].list.get(_requireTokenExists(feature));
        if (prevNonce.isNull()) {
            revert NoInstance();
        }
        return Create3.predict(salt(feature, prevNonce));
    }

    function deployInfo(address instance) public view override returns (Feature feature, Nonce nonce) {
        DeployInfo storage info = _stor1().deployInfo[instance];
        (feature, nonce) = (info.feature, info.nonce);
        if (feature.isNull()) {
            revert ERC721InvalidOwner(instance);
        }
    }

    function authorize(Feature feature, address auth, uint40 deadline) external override onlyOwner returns (bool) {
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
        if (_msgSender() != auth) {
            revert PermissionDenied();
        }
        if (deadline != type(uint40).max && block.timestamp > deadline) {
            revert PermissionDenied();
        }
    }

    function setDescription(Feature feature, string calldata description)
        external
        override
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
            "\", \"name\": \"0x Settler feature ",
            ItoA.itoa(Feature.unwrap(feature)),
            "\"}\n"
        );
        bytes32 contentHash = IPFS.dagPbUnixFsHash(content);
        featureInfo.descriptionHash = contentHash;
        emit PermanentURI(IPFS.CIDv0(contentHash), Feature.unwrap(feature));
    }

    function deploy(Feature feature, bytes calldata initCode)
        external
        payable
        override
        returns (address predicted, Nonce thisNonce)
    {
        Nonce prevNonce;
        (prevNonce, thisNonce) = _requireAuthorized(feature).list.push();

        bytes32 salt_ = salt(feature, thisNonce);
        predicted = Create3.predict(salt_);
        emit Transfer(
            prevNonce.isNull() ? address(0) : Create3.predict(salt(feature, prevNonce)),
            predicted,
            Feature.unwrap(feature)
        );

        _stor1().deployInfo[predicted] = DeployInfo({feature: feature, nonce: thisNonce});
        emit Deployed(feature, thisNonce, predicted);

        if (Create3.createFromCalldata(salt_, initCode, msg.value) != predicted) {
            revert DeployFailed(feature, thisNonce, predicted);
        }
        if (predicted.code.length == 0) {
            revert DeployFailed(feature, thisNonce, predicted);
        }
    }

    function remove(Feature feature, Nonce nonce) public override returns (bool) {
        (Nonce newHead, bool updatedHead) = _requireAuthorized(feature).list.remove(nonce);
        address deployment = Create3.predict(salt(feature, nonce));
        if (updatedHead) {
            emit Transfer(
                deployment,
                newHead.isNull() ? address(0) : Create3.predict(salt(feature, newHead)),
                Feature.unwrap(feature)
            );
        }
        emit Removed(feature, nonce, deployment);
        return true;
    }

    function remove(address instance) external override returns (bool) {
        (Feature feature, Nonce nonce) = deployInfo(instance);
        return remove(feature, nonce);
    }

    function removeAll(Feature feature) external override returns (bool) {
        Nonce nonce = _requireAuthorized(feature).list.clear();
        if (!nonce.isNull()) {
            emit Transfer(Create3.predict(salt(feature, nonce)), address(0), Feature.unwrap(feature));
        }
        emit RemovedAll(feature);
        return true;
    }

    string public constant override name = "0x Settler";
    string public constant override symbol = "0x Settler";

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
        ZeroExSettlerDeployerStorage1 storage stor1 = _stor1();
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

    function _requireTokenExists(Feature feature) private view returns (Nonce nonce) {
        if ((nonce = _stor1().featureInfo[feature].list.head).isNull()) {
            revert ERC721NonexistentToken(Feature.unwrap(feature));
        }
    }

    function _requireTokenExists(uint256 tokenId) private view returns (Nonce) {
        return _requireTokenExists(wrap(tokenId));
    }

    function ownerOf(uint256 tokenId) external view override returns (address) {
        Feature feature = wrap(tokenId);
        return Create3.predict(salt(feature, _requireTokenExists(feature)));
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

    function owner() public view override(IOwnable, AbstractOwnable, ERC1967UUPSUpgradeable) returns (address) {
        return super.owner();
    }

    function implementation() public view override(AbstractUUPSUpgradeable, ERC1967UUPSUpgradeable) returns (address) {
        return super.implementation();
    }
}
