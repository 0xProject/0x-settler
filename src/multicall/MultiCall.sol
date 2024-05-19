// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

enum RevertPolicy {
    REVERT,
    STOP,
    CONTINUE
}

struct Call {
    address target;
    RevertPolicy revertPolicy;
    bytes data;
}

struct Result {
    bool success;
    bytes data;
}

interface IMultiCall {
    function multicall(Call[] calldata, uint256 contextdepth) external returns (Result[] memory);
}

///////////////////// ABANDON ALL HOPE, YE WHO ENTER HERE //////////////////////
// But seriously, everything that comes after this is a pile of gas golfing. All
// you need to know is the interface above.

library SafeCall {
    function safeCall(address target, bytes calldata data, uint256 contextdepth)
        internal
        returns (bool success, bytes memory returndata)
    {
        assembly ("memory-safe") {
            returndata := mload(0x40)
            calldatacopy(returndata, data.offset, data.length)
            let beforeGas := gas()
            success := call(gas(), target, 0x00, returndata, data.length, 0x00, 0x00)
            // `verbatim` can't work in inline assembly. Assignment of a value to a variable costs
            // gas (although how much is unpredictable because it depends on the Yul/IR optimizer),
            // as does the `GAS` opcode itself. Therefore, the `gas()` below returns less than the
            // actual amount of gas available for computation at the end of the call. Also
            // `beforeGas` above is exclusive of the preparing of the stack for `staticcall` as well
            // as the gas costs of the `staticcall` paid by the caller (e.g. cold account
            // access). All this makes the check below slightly too conservative. However, we do not
            // correct this because the correction would become outdated (possibly too permissive)
            // if the opcodes are repriced.
            let afterGas := gas()

            if iszero(returndatasize()) {
                // The absence of returndata means that it's possible that either we called an
                // address without code or that the call reverted due to out-of-gas. We must check.
                switch success
                case 0 {
                    // Apply the "all but one 64th" rule `contextdepth + 1` times.
                    let remainingGas := shr(0x06, beforeGas)
                    for {} contextdepth { contextdepth := sub(contextdepth, 1) } {
                        remainingGas := add(remainingGas, shr(0x06, sub(beforeGas, remainingGas)))
                    }
                    // Check that the revert was not due to OOG.
                    if iszero(lt(remainingGas, afterGas)) { invalid() }
                }
                default {
                    // Success with no returndata could indicate calling an address with no code
                    // (potentially an EOA). Check for that.
                    if iszero(extcodesize(target)) { revert(0x00, 0x00) }
                }
            }

            // Copy returndata into memory, ignoring whether it's a result or a revert reason.
            mstore(returndata, returndatasize())
            returndatacopy(add(0x20, returndata), 0x00, returndatasize())
            mstore(0x40, add(0x20, add(returndatasize(), returndata)))
        }
    }

    /// This version of `safeCall` omits the OOG check because it bubbles the revert if the call
    /// reverts. Therefore, `success` is always `true`.
    function safeCall(address target, bytes calldata data) internal returns (bool success, bytes memory returndata) {
        assembly ("memory-safe") {
            returndata := mload(0x40)
            calldatacopy(returndata, data.offset, data.length)
            success := call(gas(), target, 0x00, returndata, data.length, 0x00, 0x00)
            let dst := add(0x20, returndata)
            returndatacopy(dst, 0x00, returndatasize())
            if iszero(success) { revert(dst, returndatasize()) }
            if iszero(returndatasize()) { if iszero(extcodesize(target)) { revert(0x00, 0x00) } }
            mstore(returndata, returndatasize())
            mstore(0x40, add(returndatasize(), dst))
        }
    }
}

library UnsafeArray {
    /// This is equivalent to:
    /// ```
    /// Call calldata call_ = calls[i];
    /// (target, data, revertPolicy) = (call_.target, call_.data, call_.revertPolicy);
    /// ```
    function unsafeGet(Call[] calldata calls, uint256 i)
        internal
        pure
        returns (address target, bytes calldata data, RevertPolicy revertPolicy)
    {
        assembly ("memory-safe") {
            // Initially, we set `data.offset` to point at the `Call` struct. This is 64 bytes
            // before the offset to the actual `data` array length.
            data.offset :=
                add(
                    calls.offset,
                    // We allow the indirection/offset to `calls[i]` to be negative
                    calldataload(
                        add(shl(0x05, i), calls.offset) // Can't overflow; we assume `i` is in-bounds.
                    )
                )

            // `data.offset` now points to `target`; load it.
            target := calldataload(data.offset)
            // Check for dirty bits in `target`.
            let err := shr(0xa0, target)

            // And load `revertPolicy`.
            revertPolicy := calldataload(add(0x20, data.offset))
            // And check it for dirty bits too.
            err := or(err, gt(revertPolicy, 0x02))

            // revert if calldata is unclean
            if err { revert(0x00, 0x00) }

            // Indirect `data.offset` again to get the `bytes` payload.
            data.offset :=
                add(
                    data.offset,
                    // We allow the offset stored in the `Call` struct to be negative.
                    calldataload(
                        // Can't overflow; `data.offset` is in-bounds of `calldata`.
                        add(0x40, data.offset)
                    )
                )
            // `data.offset` now points to the length field 32 bytes before the start of the actual array.

            // Now we load `data.length` and set `data.offset` to the start of the actual array.
            data.length := calldataload(data.offset)
            data.offset := add(0x20, data.offset)
        }
    }

    /// This is equivalent to `(a[i].success, a[i].data) = (success, data)`
    function unsafeSet(Result[] memory a, uint256 i, bool success, bytes memory data) internal pure {
        assembly ("memory-safe") {
            let dst := mload(add(add(0x20, shl(0x05, i)), a))
            mstore(dst, and(0x01, success))
            mstore(add(0x20, dst), data)
        }
    }

    function unsafeTruncate(Result[] memory a, uint256 newLength) internal pure {
        assembly ("memory-safe") {
            mstore(a, newLength)
        }
    }
}

library UnsafeMath {
    function unsafeInc(uint256 x) internal pure returns (uint256) {
        unchecked {
            return x + 1;
        }
    }
}

library UnsafeReturn {
    /// @notice This is *ROUGHLY* equivalent to `return(abi.encode(r))`.
    /// @dev This *DOES NOT* produce the so-called "Strict Encoding Mode" specified by the formal
    ///      ABI encoding specification
    ///      https://docs.soliditylang.org/en/v0.8.25/abi-spec.html#strict-encoding-mode . However,
    ///      it is compatible with the non-strict ABI *decoder* employed by Solidity. In particular,
    ///      it does not pad the encoding of each value to a multiple of 32 bytes, and it does not
    ///      contiguously encode all values reachable from some tuple/struct before moving on to
    ///      another tuple/struct. (e.g. the encoding of an array of 2 `Result`s first encodes each
    ///      `Result` then encodes each `bytes data`)
    function unsafeReturn(Result[] memory r) internal pure {
        // We assume (and our use in this file obeys) that all these objects in memory are laid out
        // contiguously and in a sensible order.
        assembly ("memory-safe") {
            // This is not technically memory safe, but manual verification of the emitted bytecode
            // demonstrates that this does not clobber any compiler-generated temporaries.
            let returndatastart := sub(r, 0x20)
            mstore(returndatastart, 0x20)

            // Because *all* the structs/tuples involved here are dynamic types according to the ABI
            // specification, the layout in memory is identical to the layout in returndata except
            // that memory uses pointers and returndata uses offsets. Convert pointers to offsets.
            for {
                let base := add(0x20, r)
                let i := base
                let end := add(base, shl(0x05, mload(r)))
            } lt(i, end) { i := add(0x20, i) } {
                let ri := mload(i) // Load the pointer to the `Result` object.
                mstore(i, sub(ri, base)) // Replace the pointer with an offset.
                let j := add(0x20, ri) // Point at the pointer the pointer to the `bytes data`.
                let rj := mload(j) // Load the pointer to the `bytes data`.
                mstore(j, sub(rj, ri)) // Replace the pointer with an offset.
            }

            // We assume (and our use in this file obeys) that there aren't any other objects in
            // memory after the end of `r` (and all the objects it references, recursively)
            return(returndatastart, sub(mload(0x40), returndatastart))
        }
    }
}

contract MultiCall {
    using SafeCall for address;
    using UnsafeArray for Call[];
    using UnsafeArray for Result[];
    using UnsafeMath for uint256;
    using UnsafeReturn for Result[];

    constructor() {
        assert(address(this) == 0x000000000000175a8b9bC6d539B3708EEd92EA6c || block.chainid == 31337);
    }

    function multicall(Call[] calldata calls, uint256 contextdepth) internal returns (Result[] memory result) {
        result = new Result[](calls.length);
        for (uint256 i; i < calls.length; i = i.unsafeInc()) {
            (address target, bytes calldata data, RevertPolicy revertPolicy) = calls.unsafeGet(i);
            bool success;
            bytes memory returndata;
            if (revertPolicy == RevertPolicy.REVERT) {
                // We don't need to use the OOG-protected `safeCall` here because an OOG will result
                // in a bubbled revert anyways.
                (success, returndata) = target.safeCall(data);
            } else {
                (success, returndata) = target.safeCall(data, contextdepth);
                // This could be implemented in assembly as (equivalently) `(revertPolicy ==
                // RevertPolicy.STOP) > success`, but that only optimizes the `success == false`
                // condition and significantly compromises readability.
                if (!success && revertPolicy == RevertPolicy.STOP) {
                    result.unsafeSet(i, success, returndata);
                    result.unsafeTruncate(i.unsafeInc()); // This results in `returndata` with gaps.
                    break;
                }
            }
            result.unsafeSet(i, success, returndata);
        }
    }

    fallback() external payable {
        bytes32 selector = bytes32(IMultiCall.multicall.selector);
        Call[] calldata calls;
        uint256 contextdepth;
        assembly ("memory-safe") {
            // check the selector and for `nonpayable`
            // this implicitly prohibits a `calls.offset` greater than 4GiB
            if or(callvalue(), xor(selector, calldataload(0x00))) { revert(0x00, 0x00) }

            calls.offset := add(0x04, calldataload(0x04)) // Can't overflow without clobbering selector.
            calls.length := calldataload(calls.offset)
            calls.offset := add(0x20, calls.offset) // Can't overflow without clobbering selector.

            contextdepth := calldataload(0x24)
        }

        multicall(calls, contextdepth).unsafeReturn();
    }
}
