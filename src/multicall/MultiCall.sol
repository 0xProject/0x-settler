// SPDX-License-Identifier: MIT
pragma solidity =0.8.28;

/// Each call issued has a revert policy. This controls the behavior of the batch if the call
/// reverts.
enum RevertPolicy {
    REVERT,  // Bubble the revert, undoing the entire multicall/batch. `contextdepth` is ignored
    HALT,    // Don't revert, but end the multicall/batch immediately. Subsequent calls are not
             // executed. An OOG revert is always bubbled
    CONTINUE // Ignore the revert and continue with the batch. The corresponding `Result` will have
             // `success = false`. An OOG revert is always bubbled
}

struct Call {
    address payable target;
    RevertPolicy revertPolicy;
    uint256 value;
    bytes data;
}

struct Result {
    bool success;
    bytes data;
}

interface IMultiCall {
    /// @param contextdepth determines the depth of the context stack that we inspect (the number of
    ///                     all-but-one-64th iterations applied) when determining whether a call
    ///                     reverted due to OOG. Setting this too high is gas-wasteful during revert
    ///                     handling. OOG checking only works when the revert reason is empty. If an
    ///                     intervening context applies its own revert reason, OOG checking will not
    ///                     be applied.
    /// Mismatches between `msg.value` and each `calls[i].value` is not checked or handled
    /// specially. If this contract has nonzero `address(this).balance`, you can get some free ETH
    /// by setting `value` to nonzero. If you set `msg.value` lower than the sum of
    /// `calls[i].value`, then the creation of one of the call contexts may fail and you'll get a
    /// failure (possibly a bubbled revert, depending on the value of `revertPolicy`) with no
    /// reason. If you set `revertPolicy` to something other than `REVERT` and a call with nonzero
    /// value reverts, the extra ETH is kept in this contract. You must make other arrangements for
    /// value refund.
    function multicall(Call[] calldata calls, uint256 contextdepth) external payable returns (Result[] memory);

    receive() external payable;
}

///////////////////// ABANDON ALL HOPE, YE WHO ENTER HERE //////////////////////
// But seriously, everything that comes after this is a pile of gas golfing. All
// you need to know is the interface above.

library SafeCall {
    /// Call `target` with `data` sending `value` ETH. `sender` (as 20 bytes) is appeneded to the
    /// end of `data`. Returns the `success` of the call as well as any `returndata`/revert
    /// data. *HOWEVER*, if an out-of-gas occurs at `contextdepth` frames away from `target`, we
    /// will instead revert with an OOG (`invalid()`). We will also revert when calling a `target`
    /// without code.
    /// @dev Out-of-gas is detected by the absence of returndata as well as a `gasleft()` at or
    ///      below what the `contextdepth + 1` times iterated all-but-one-64th rule would
    ///      indicate. The all-but-one-64th rule is applied naïvely, not accounting for the gas
    ///      costs of setting up the stack or the caller-paid costs of `call`ing. This means that in
    ///      order to avoid a false-positive OOG detection, gas must be slightly overprovisioned.
    /// @dev This does not align the free memory pointer to a slot/word boundary.
    /// @dev Calling a precompile will not result in a revert, even though it contains no code.
    /// @dev Sending ETH and no data to an EOA will not result in a revert.
    function safeCall(address target, uint256 value, bytes calldata data, address sender, uint256 contextdepth)
        internal
        returns (bool success, bytes memory returndata)
    {
        assembly ("memory-safe") {
            returndata := mload(0x40)
            calldatacopy(returndata, data.offset, data.length)
            // Append the ERC-2771 forwarded caller
            mstore(add(returndata, data.length), shl(0x60, sender))
            // Only append the ERC-2771 forwarded caller if the selector is also present
            let length := add(mul(0x14, lt(0x03, data.length)), data.length)
            let beforeGas := gas()
            success := call(gas(), target, value, returndata, length, codesize(), 0x00)
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
                for {} true {} {
                    if success {
                        // Success with no returndata could indicate calling an address with no code
                        // (potentially an EOA). Disallow calling an EOA unless sending no data and some
                        // ETH.
                        if or(iszero(value), data.length) {
                            if iszero(extcodesize(target)) { revert(codesize(), 0x00) }
                        }
                        break
                    }
                    // Apply the "all but one 64th" rule `contextdepth + 1` times.
                    let remainingGas := shr(0x06, beforeGas)
                    for {} contextdepth { contextdepth := sub(contextdepth, 0x01) } {
                        remainingGas := add(remainingGas, shr(0x06, sub(beforeGas, remainingGas)))
                    }
                    // Check that the revert was not due to OOG.
                    if iszero(lt(remainingGas, afterGas)) { invalid() }
                    break
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
    /// @dev This does not align the free memory pointer to a slot boundary.
    function safeCall(address target, uint256 value, bytes calldata data, address sender)
        internal
        returns (bool success, bytes memory returndata)
    {
        assembly ("memory-safe") {
            returndata := mload(0x40)
            calldatacopy(returndata, data.offset, data.length)
            // Append the ERC-2771 forwarded caller
            mstore(add(returndata, data.length), shl(0x60, sender))
            // Only append the ERC-2771 forwarded caller if the selector is also present
            success :=
                call(gas(), target, value, returndata, add(mul(0x14, lt(0x03, data.length)), data.length), codesize(), 0x00)
            let dst := add(0x20, returndata)
            returndatacopy(dst, 0x00, returndatasize())
            if iszero(success) { revert(dst, returndatasize()) }
            if iszero(returndatasize()) {
                if or(iszero(value), data.length) { if iszero(extcodesize(target)) { revert(codesize(), 0x00) } }
            }
            mstore(returndata, returndatasize())
            mstore(0x40, add(returndatasize(), dst))
        }
    }
}

type CallArrayIterator is uint256;

library LibCallArrayIterator {
    /// Advance the iterator one position down the array. Out-of-bounds is not checked.
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
    /// Create an iterator pointing to the first element of the `calls` array. Out-of-bounds is not
    /// checked.
    function iter(Call[] calldata calls) internal pure returns (CallArrayIterator r) {
        assembly ("memory-safe") {
            r := calls.offset
        }
    }

    /// Create an iterator pointing to the one-past-the-end element of the `calls`
    /// array. Dereferencing this iterator will result in out-of-bounds access.
    function end(Call[] calldata calls) internal pure returns (CallArrayIterator r) {
        unchecked {
            return CallArrayIterator.wrap((calls.length << 5) + CallArrayIterator.unwrap(iter(calls)));
        }
    }

    /// Dereference the iterator `i` and return the values in the struct. This is *roughly*
    /// equivalent to:
    ///     Call calldata call = calls[i];
    ///     (target, data, revertPolicy) = (call.target, call.data, call.revertPolicy);
    /// Of course `i` isn't an integer, so the analogy is a bit loose. There are a lot of bounds
    /// checks that are omitted here. While we apply a relaxed ABI encoding (there are some
    /// encodings that we accept that Solidity would not), any valid ABI encoding accepted by
    /// Solidity is decoded identically.
    /// @dev `revertPolicy` is returned as `uint256` because it optimizes gas
    function get(Call[] calldata calls, CallArrayIterator i)
        internal
        pure
        returns (address target, uint256 value, bytes calldata data, uint256 revertPolicy)
    {
        assembly ("memory-safe") {
            // `s` points at the `Call` struct. This is 96 bytes before the offset to the `data`
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
            // 2 is the limit for the `RevertPolicy` enum. Violating this _should_ result in a
            // revert with a reason of `Panic(33)` for strict compatibility with Solidity, but we
            // gas-optimize this by lumping it in with the normal "malformed calldata" revert reason
            // (empty).

            // Revert if any calldata is unclean.
            if err { revert(codesize(), 0x00) }

            // Load `value`. No range checking is required.
            value := calldataload(add(0x40, s))

            // Indirect `data.offset` to get the `bytes` payload.
            data.offset :=
                add(
                    s,
                    // We allow the offset stored in the `Call` struct to be negative.
                    calldataload(
                        // Can't overflow; `s` is in-bounds of `calldata`.
                        add(0x60, s)
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
    /// Advance the iterator one position down the array. Out-of-bounds is not checked.
    function next(ResultArrayIterator i) internal pure returns (ResultArrayIterator r) {
        unchecked {
            return ResultArrayIterator.wrap(32 + ResultArrayIterator.unwrap(i));
        }
    }
}

using LibResultArrayIterator for ResultArrayIterator global;

library UnsafeResultArray {
    /// Create an iterator pointing to the first element of the `results` array. Out-of-bounds is
    /// not checked.
    function iter(Result[] memory results) internal pure returns (ResultArrayIterator r) {
        assembly ("memory-safe") {
            r := add(0x20, results)
        }
    }

    /// Dereference the iterator `i` and set the values in the returned struct (`Result
    /// memory`). This is *roughly* equivalent to:
    ///     Result memory result = results[i];
    ///     (result.success, result.data) = (success, data);
    /// Of course `i` isn't an integer, so the analogy is a bit loose. We omit bounds checking on
    /// `i`, so if it is out-of-bounds, memory will be corrupted.
    function set(Result[] memory, ResultArrayIterator i, bool success, bytes memory data) internal pure {
        assembly ("memory-safe") {
            let dst := mload(i)
            mstore(dst, success)
            mstore(add(0x20, dst), data)
        }
    }

    /// This is roughly equivalent to `results.length = i.next()`. Of course `i` is not an integer
    /// and settings `results.length` is illegal. Thus, it's written in Yul.
    function unsafeTruncate(Result[] memory results, ResultArrayIterator i) internal pure {
        assembly ("memory-safe") {
            mstore(results, shr(0x05, sub(i, results)))
        }
    }

    /// This is equivalent to `result = new Result[](length)`. While the array itself is populated
    /// correctly, the memory pointed *AT* by the slots of the array is not zeroed.
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
    /// This is *ROUGHLY* equivalent to `return(abi.encode(r))`.
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
            (msg.sender == 0x4e59b44847b379578588920cA78FbF26c0B4956C && uint160(address(this)) >> 104 == 0)
                || block.chainid == 31337
        );
    }

    /// Returns `msg.sender`, unless `msg.sender` is `address(this)`, in which case it returns the
    /// unpacked ERC-2771 forwarded caller (the next-outermost non-MultiCall context).
    function _msgSender() private view returns (address sender) {
        if ((sender = msg.sender) == address(this)) {
            // Unpack the ERC-2771-packed sender/caller.
            assembly ("memory-safe") {
                sender := shr(0x60, calldataload(sub(calldatasize(), 0x14)))
            }
        }
    }

    function multicall(Call[] calldata calls, uint256 contextdepth) internal returns (Result[] memory result) {
        // Allocate memory for our eventual return. This does not allocate memory for the returndata
        // from each of the calls of the multicall/batch.
        result = UnsafeResultArray.unsafeAlloc(calls.length);
        address sender = _msgSender();

        for (
            (CallArrayIterator i, CallArrayIterator end, ResultArrayIterator j) =
                (calls.iter(), calls.end(), result.iter());
            i != end;
            (i, j) = (i.next(), j.next())
        ) {
            // Decode and load the call.
            (address target, uint256 value, bytes calldata data, uint256 revertPolicy) = calls.get(i);
            // Each iteration of this loop allocates some memory for the returndata, but everything
            // ends up packed in memory because neither implementation of `safeCall` aligns the free
            // memory pointer to a word boundary.
            if (revertPolicy == uint8(RevertPolicy.REVERT)) {
                // We don't need to use the OOG-protected `safeCall` here because an OOG will result
                // in a bubbled revert anyways.
                (bool success, bytes memory returndata) = target.safeCall(value, data, sender);
                result.set(j, success, returndata);
            } else {
                (bool success, bytes memory returndata) = target.safeCall(value, data, sender, contextdepth);
                result.set(j, success, returndata);
                if (!success) {
                    if (revertPolicy == uint8(RevertPolicy.HALT)) {
                        result.unsafeTruncate(j); // This results in `returndata` with gaps.
                        break;
                    }
                }
            }
        }
    }

    fallback() external payable {
        bytes32 selector = IMultiCall.multicall.selector;
        Call[] calldata calls;
        uint256 contextdepth;
        assembly ("memory-safe") {
            // Check the selector. This implicitly prohibits a `calls.offset` greater than 4GiB.
            if xor(selector, calldataload(0x00)) {
                for {} true {} {
                    // Unrecognized selector
                    if calldatasize() { revert(codesize(), 0x00) }
                    // Receive ETH
                    return(codesize(), 0x00)
                }
            }

            calls.offset := add(0x04, calldataload(0x04)) // Can't overflow without clobbering selector.
            calls.length := calldataload(calls.offset)
            calls.offset := add(0x20, calls.offset) // Can't overflow without clobbering selector.

            contextdepth := calldataload(0x24)
        }

        multicall(calls, contextdepth).unsafeReturn();
    }
}
