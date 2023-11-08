// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {TwoStepOwnable} from "./TwoStepOwnable.sol";
import {Panic} from "../utils/Panic.sol";

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

    struct DoublyLinkedList {
        address prev;
        address next;
        uint256 feature;
    }

    mapping(address => DoublyLinkedList) private _deploymentLists;
    mapping(uint256 => address) public deployments;

    address public feeCollector;
    mapping(uint256 => mapping(address => uint256)) public authorizedUntil;

    uint256 private constant _ADDRESS_MASK = 0x00ffffffffffffffffffffffffffffffffffffffff;

    constructor(address initialOwner) {
        emit OwnershipPending(initialOwner);
        pendingOwner = initialOwner;
    }

    event Authorized(uint256 indexed, address indexed, uint256);

    function authorize(uint256 feature, address who, uint256 expiry) public onlyOwner returns (bool) {
        if (feature == 0) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        emit Authorized(feature, who, expiry);
        authorizedUntil[feature][who] = expiry;
        return true;
    }

    function _requireAuthorized(uint256 feature) private view {
        if (block.timestamp >= authorizedUntil[feature][msg.sender]) {
            revert PermissionDenied();
        }
    }

    modifier onlyAuthorized(uint256 feature) {
        _requireAuthorized(feature);
        _;
    }

    event FeeCollectorChanged(address indexed);

    function setFeeCollector(address newFeeCollector) public onlyOwner returns (bool) {
        emit FeeCollectorChanged(newFeeCollector);
        feeCollector = newFeeCollector;
        return true;
    }

    event Deployed(uint256 indexed, address indexed);

    error DeployFailed();

    function deploy(uint256 feature, bytes calldata initCode, bytes32 salt)
        public
        payable
        onlyAuthorized(feature)
        returns (address predicted)
    {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            let initLength := add(initCode.length, 0x20)
            let initEnd := add(ptr, initLength)

            // this is for computing the CREATE2 address. doing this here avoids having to
            // manipulate any padding later
            mstore(sub(initEnd, 0x0b), address())

            // store the initcode in memory, with the fee collector appended to the constructor
            calldatacopy(ptr, initCode.offset, initCode.length)
            mstore(add(ptr, initCode.length), and(_ADDRESS_MASK, sload(feeCollector.slot)))

            // compute the CREATE2 address
            mstore8(initEnd, 0xff)
            mstore(add(initEnd, 0x15), salt)
            mstore(add(initEnd, 0x35), keccak256(ptr, initLength))
            predicted := and(_ADDRESS_MASK, keccak256(initEnd, 0x55))

            // push the predicted address into the doubly-linked list
            // we do this here in assembly to strictly follow checks-effects-interactions before deploying
            {
                // set the predicted value as the head of the list
                mstore(0x00, feature)
                mstore(0x20, deployments.slot)
                let headSlot := keccak256(0x00, 0x40)
                // address oldHead = deployments[feature];
                let oldHead := and(_ADDRESS_MASK, sload(headSlot))
                // deployments[feature] = predicted;
                sstore(headSlot, predicted)

                mstore(0x20, _deploymentLists.slot)
                if oldHead {
                    // _deploymentLists[oldHead].next = predicted;
                    mstore(0x00, oldHead)
                    sstore(add(1, keccak256(0x00, 0x40)), predicted)
                }
                // _deploymentLists[predicted].prev = oldHead;
                mstore(0x00, predicted)
                let predictedSlot := keccak256(0x00, 0x40)
                sstore(predictedSlot, oldHead) // don't bother checking if oldHead is zero
                // _deploymentLists[predicted].feature = feature;
                sstore(add(2, predictedSlot), feature)
            }

            // do the deployment and check for success
            predicted :=
                and(
                    // this `sub` produces a mask that is zero iff the deployment failed
                    sub(
                        or(
                            // order of evaluation is right-to-left. `extcodesize` must come after `create2`
                            iszero(extcodesize(predicted)),
                            iszero(
                                eq(
                                    // this is the interaction; no more state updates past this point
                                    create2(callvalue(), ptr, initLength, salt),
                                    predicted
                                )
                            )
                        ),
                        1
                    ),
                    // the failure mask passes `predicted` unchanged if the deployment suceeded
                    predicted
                )
        }
        if (predicted == address(0)) {
            revert DeployFailed();
        }
        emit Deployed(feature, predicted);
    }

    event Unsafe(uint256 indexed, address indexed);

    function setUnsafe(uint256 feature, address addr) public onlyAuthorized(feature) returns (bool) {
        DoublyLinkedList storage entry = _deploymentLists[addr];
        if (entry.feature != feature) {
            revert PermissionDenied();
        }
        address prev = entry.prev;
        address next = entry.next;
        if (next == address(0)) {
            // assert(deployments[feature] == addr);
            deployments[feature] = prev;
        } else {
            _deploymentLists[next].prev = prev;
        }
        if (prev != address(0)) {
            _deploymentLists[prev].next = next;
        }
        delete entry.prev;
        delete entry.next;
        delete entry.feature;

        emit Unsafe(feature, addr);
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
}
