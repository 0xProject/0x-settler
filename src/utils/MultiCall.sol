// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Revert} from "./Revert.sol";
import {IMultiCall} from "../interfaces/IMultiCall.sol";

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

abstract contract MultiCallBase is IMultiCall {
    using UnsafeArray for bytes[];

    function _multicall(address target, bytes[] calldata datas) internal {
        uint256 freeMemPtr;
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
}

abstract contract MultiCall is MultiCallBase {
    function multicall(bytes[] calldata datas) external override {
        _multicall(address(this), datas);
    }
}
