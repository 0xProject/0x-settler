// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {TwoStepOwnable} from "./TwoStepOwnable.sol";
import {AddressDerivation} from "../utils/AddressDerivation.sol";

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

contract Deployer is TwoStepOwnable {
    using UnsafeArray for bytes[];

    bytes32 private constant _EMPTYHASH = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;

    bytes32 private _pad;
    uint64 public nonce;
    address public feeCollector;
    mapping(address => bool) public isAuthorized;
    mapping(address => bool) public isUnsafe;

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

    error DeployFailed();

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
            mstore(add(ptr, initCode.length), and(0xffffffffffffffffffffffffffffffffffffffff, _feeCollector))
            deployed := create(callvalue(), ptr, add(initCode.length, 0x20))
        }
        if (deployed != AddressDerivation.deriveContract(address(this), newNonce) || deployed.codehash == _EMPTYHASH) {
            revert DeployFailed();
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
            for (uint64 i = nonce; i != 0; --i) {
                address instance = AddressDerivation.deriveContract(address(this), i);
                if (!isUnsafe[instance] && instance.codehash != _EMPTYHASH) {
                    return instance;
                }
            }
        }
        revert();
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
}
