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
    function safeCall(address target, bytes calldata data, address sender, uint256 contextdepth)
        internal
        returns (bool success, bytes memory returndata)
    {
        assembly ("memory-safe") {
            returndata := mload(0x40)
            calldatacopy(returndata, data.offset, data.length)
            mstore(add(returndata, data.length), shl(0x60, sender))
            let beforeGas := gas()
            success := call(gas(), target, 0x00, returndata, add(0x14, data.length), 0x00, 0x00)
            // `verbatim` can't work in inline assembly. Assignment of a value to a variable costs
            // gas (although how much is unpredictable because it depends on the Yul/IR optimizer),
            // as does the `GAS` opcode itself. Therefore, the `gas()` below returns less than the
            // actual amount of gas available for computation at the end of the call. Also
            // `beforeGas` above is exclusive of the preparing of the stack for `call` as well as
            // the gas costs of the `call` paid by the caller (e.g. cold account access). All this
            // makes the check below slightly too conservative. However, we do not correct this
            // because the correction would become outdated (possibly too permissive) if the opcodes
            // are repriced.
            let afterGas := gas()

            if iszero(returndatasize()) {
                // The absence of returndata means that it's possible that either we called an
                // address without code or that the call reverted due to out-of-gas. We must check.
                switch success
                case 0 {
                    // Apply the "all but one 64th" rule `contextdepth + 1` times.
                    let remainingGas := shr(0x06, beforeGas)
                    for {} contextdepth { contextdepth := sub(contextdepth, 0x01) } {
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
            let dst := add(0x20, returndata)
            returndatacopy(dst, 0x00, returndatasize())
            mstore(0x40, add(returndatasize(), dst))
        }
    }

    /// This version of `safeCall` omits the OOG check because it bubbles the revert if the call
    /// reverts. Therefore, `success` is always `true`.
    function safeCall(address target, bytes calldata data, address sender)
        internal
        returns (bool success, bytes memory returndata)
    {
        assembly ("memory-safe") {
            returndata := mload(0x40)
            calldatacopy(returndata, data.offset, data.length)
            mstore(add(returndata, data.length), shl(0x60, sender))
            success := call(gas(), target, 0x00, returndata, add(0x14, data.length), 0x00, 0x00)
            let dst := add(0x20, returndata)
            returndatacopy(dst, 0x00, returndatasize())
            if iszero(success) { revert(dst, returndatasize()) }
            if iszero(returndatasize()) { if iszero(extcodesize(target)) { revert(0x00, 0x00) } }
            mstore(returndata, returndatasize())
            mstore(0x40, add(returndatasize(), dst))
        }
    }
}

type CallArrayIterator is uint256;

library LibCallArrayIterator {
    function next(CallArrayIterator i) internal pure returns (CallArrayIterator) {
        unchecked {
            return CallArrayIterator.wrap(32 + CallArrayIterator.unwrap(i));
        }
    }
}

using LibCallArrayIterator for CallArrayIterator global;

function __eq(CallArrayIterator a, CallArrayIterator b) pure returns (bool) {
    return CallArrayIterator.unwrap(a) == CallArrayIterator.unwrap(b);
}

function __ne(CallArrayIterator a, CallArrayIterator b) pure returns (bool) {
    return CallArrayIterator.unwrap(a) != CallArrayIterator.unwrap(b);
}

using {__eq as ==, __ne as !=} for CallArrayIterator global;

library UnsafeCallArray {
    function iter(Call[] calldata calls) internal pure returns (CallArrayIterator r) {
        assembly ("memory-safe") {
            r := calls.offset
        }
    }

    function end(Call[] calldata calls) internal pure returns (CallArrayIterator r) {
        unchecked {
            return CallArrayIterator.wrap((calls.length << 5) + CallArrayIterator.unwrap(iter(calls)));
        }
    }

    function get(Call[] calldata calls, CallArrayIterator i)
        internal
        pure
        returns (address target, bytes calldata data, RevertPolicy revertPolicy)
    {
        assembly ("memory-safe") {
            // `s` points at the `Call` struct. This is 64 bytes before the offset to the `data`
            // array length. We allow the indirection/offset relative to `calls` to be negative.
            let s := add(calls.offset, calldataload(i))

            // `s` points to `target`; load it.
            target := calldataload(s)
            // Check for dirty bits in `target`.
            let err := shr(0xa0, target)

            // Load `revertPolicy`
            revertPolicy := calldataload(add(0x20, s))
            // and check it for dirty bits too.
            err := or(err, gt(revertPolicy, 0x02))

            // Revert if any calldata is unclean.
            if err { revert(0x00, 0x00) }

            // Indirect `data.offset` to get the `bytes` payload.
            data.offset :=
                add(
                    s,
                    // We allow the offset stored in the `Call` struct to be negative.
                    calldataload(
                        // Can't overflow; `s` is in-bounds of `calldata`.
                        add(0x40, s)
                    )
                )
            // `data.offset` now points to the length field 32 bytes before the start of the actual array.

            // Now we load `data.length` and set `data.offset` to the start of the actual array.
            data.length := calldataload(data.offset)
            data.offset := add(0x20, data.offset)
        }
    }
}

type ResultArrayIterator is uint256;

library LibResultArrayIterator {
    function next(ResultArrayIterator i) internal pure returns (ResultArrayIterator r) {
        unchecked {
            return ResultArrayIterator.wrap(32 + ResultArrayIterator.unwrap(i));
        }
    }
}

using LibResultArrayIterator for ResultArrayIterator global;

library UnsafeResultArray {
    function iter(Result[] memory results) internal pure returns (ResultArrayIterator r) {
        assembly ("memory-safe") {
            r := add(0x20, results)
        }
    }

    function set(Result[] memory, ResultArrayIterator i, bool success, bytes memory data) internal pure {
        assembly ("memory-safe") {
            let dst := mload(i)
            mstore(dst, success)
            mstore(add(0x20, dst), data)
        }
    }

    function unsafeTruncate(Result[] memory results, ResultArrayIterator i) internal pure {
        assembly ("memory-safe") {
            mstore(results, shr(0x05, sub(i, results)))
        }
    }

    // This is equivalent to `result = new Result[](length)`
    function unsafeAlloc(uint256 length) internal pure returns (Result[] memory result) {
        assembly ("memory-safe") {
            result := mload(0x40)
            mstore(result, length)
            mstore(0x40, add(0x20, add(mul(0x60, length), result)))
            for {
                let baseArray := add(0x20, result)
                let lenArrayBytes := shl(0x05, length)
                let baseResults := add(baseArray, lenArrayBytes)
                let i
            } lt(i, lenArrayBytes) { i := add(0x20, i) } { mstore(add(baseArray, i), add(baseResults, add(i, i))) }
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
    using UnsafeCallArray for Call[];
    using UnsafeResultArray for Result[];
    using UnsafeReturn for Result[];

    constructor() {
        assert(
            (msg.sender == 0x4e59b44847b379578588920cA78FbF26c0B4956C && uint160(address(this)) >> 112 == 0)
                || block.chainid == 31337
        );
    }

    function _msgSender() private view returns (address sender) {
        if ((sender = msg.sender) == address(this)) {
            assembly ("memory-safe") {
                sender := shr(0x60, calldataload(sub(calldatasize(), 0x14)))
            }
        }
    }

    function multicall(Call[] calldata calls, uint256 contextdepth) internal returns (Result[] memory result) {
        result = UnsafeResultArray.unsafeAlloc(calls.length);
        address sender = _msgSender();

        for (
            (CallArrayIterator i, CallArrayIterator end, ResultArrayIterator j) =
                (calls.iter(), calls.end(), result.iter());
            i != end;
            (i, j) = (i.next(), j.next())
        ) {
            (address target, bytes calldata data, RevertPolicy revertPolicy) = calls.get(i);
            if (revertPolicy == RevertPolicy.REVERT) {
                // We don't need to use the OOG-protected `safeCall` here because an OOG will result
                // in a bubbled revert anyways.
                (bool success, bytes memory returndata) = target.safeCall(data, sender);
                result.set(j, success, returndata);
            } else {
                (bool success, bytes memory returndata) = target.safeCall(data, sender, contextdepth);
                result.set(j, success, returndata);
                if (!success) {
                    if (revertPolicy == RevertPolicy.STOP) {
                        result.unsafeTruncate(j); // This results in `returndata` with gaps.
                        break;
                    }
                }
            }
        }
    }

    fallback() external payable {
        bytes32 selector = bytes32(IMultiCall.multicall.selector);
        Call[] calldata calls;
        uint256 contextdepth;
        assembly ("memory-safe") {
            // Check the selector and for `nonpayable`. This implicitly prohibits a `calls.offset`
            // greater than 4GiB.
            if or(callvalue(), xor(selector, calldataload(0x00))) { revert(0x00, 0x00) }

            calls.offset := add(0x04, calldataload(0x04)) // Can't overflow without clobbering selector.
            calls.length := calldataload(calls.offset)
            calls.offset := add(0x20, calls.offset) // Can't overflow without clobbering selector.

            contextdepth := calldataload(0x24)
        }

        multicall(calls, contextdepth).unsafeReturn();
    }
}
