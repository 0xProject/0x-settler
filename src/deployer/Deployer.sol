// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {TwoStepOwnable} from "./TwoStepOwnable.sol";
import {AddressDerivation} from "../utils/AddressDerivation.sol";

contract Deployer is TwoStepOwnable {
    uint64 public nonce;
    address public feeCollector;
    mapping(address => bool) isAuthorized;
    mapping(address => bool) isUnsafe;

    constructor(address initialOwner) {
        emit OwnershipPending(initialOwner);
        pendingOwner = initialOwner;

        // contracts can't deploy at nonce zero. blacklist it to avoid foot guns.
        address zeroInstance = AddressDerivation.deriveContract(address(this), 0);
        isUnsafe[zeroInstance] = true;
        emit Unsafe(0, zeroInstance);
    }

    event Authorized(address indexed, bool);

    function authorize(address who, bool auth) public onlyOwner returns (bool) {
        emit Authorized(who, auth);
        isAuthorized[who] = auth;
        return true;
    }

    function _requireAuthorized() private view {
        if (!isAuthorized[msg.sender]) {
            revert PermissionDenied();
        }
    }

    modifier onlyAuthorized() {
        _requireAuthorized();
        _;
    }

    event FeeCollectorChanged(address indexed);

    function setFeeCollector(address newFeeCollector) public onlyOwner returns (bool) {
        emit FeeCollectorChanged(newFeeCollector);
        feeCollector = newFeeCollector;
        return true;
    }

    event Deployed(uint64 indexed, address indexed);

    function deploy(bytes calldata initCode)
        public
        payable
        onlyAuthorized
        returns (uint64 newNonce, address deployed)
    {
        newNonce = ++nonce;
        address _feeCollector = feeCollector;
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            calldatacopy(ptr, initCode.offset, initCode.length)
            mstore(add(ptr, initCode.length), _feeCollector)
            deployed := create(callvalue(), ptr, add(initCode.length, 0x20))
        }
        emit Deployed(newNonce, deployed);
    }

    function deployment(uint64 _nonce) public view returns (address) {
        return AddressDerivation.deriveContract(address(this), _nonce);
    }

    function deployment() public view returns (address) {
        return AddressDerivation.deriveContract(address(this), nonce);
    }

    event Unsafe(uint64 indexed, address indexed);

    function setUnsafe(uint64 _nonce) public onlyAuthorized returns (bool) {
        address instance = AddressDerivation.deriveContract(address(this), _nonce);
        require(_nonce <= nonce);
        isUnsafe[instance] = true;
        emit Unsafe(_nonce, instance);
        return true;
    }

    function safeDeployment() public view returns (address) {
        unchecked {
            for (uint64 i = nonce; i > 0; --i) {
                address instance = AddressDerivation.deriveContract(address(this), i);
                if (!isUnsafe[instance] && instance.code.length > 0) {
                    return instance;
                }
            }
        }
        revert();
    }

    // in spite of the fact that `deploy` is payable, `multicall` cannot be
    // payable for security. therefore, there are some instances where it is
    // necessary to make multiple calls to this contract.
    function multicall(bytes[] calldata datas) public {
        uint256 freeMemPtr;
        assembly ("memory-safe") {
            freeMemPtr := mload(0x40)
        }
        unchecked {
            for (uint256 i; i < datas.length; i++) {
                (bool success, bytes memory reason) = address(this).delegatecall(datas[i]);
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
}
