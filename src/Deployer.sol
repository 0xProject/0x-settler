// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {TwoStepOwnable} from "./TwoStepOwnable.sol";
import {AddressDerivation} from "./AddressDerivation.sol";

contract Deployer is TwoStepOwnable {
    uint64 public nonce;
    address public feeCollector;
    mapping(address => bool) isAuthorized;

    constructor(address initialOwner) {
        emit OwnershipPending(initialOwner);
        pendingOwner = initialOwner;
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
}
