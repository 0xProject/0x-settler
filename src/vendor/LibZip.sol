// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

/// @notice Library for compressing and decompressing bytes.
/// @author Solady (https://github.com/vectorized/solady/blob/main/src/utils/LibZip.sol)
/// @author Calldata compression by clabby (https://github.com/clabby/op-kompressor)
///
/// @dev Note:
/// The accompanying solady.js library includes implementations of calldata
/// operations for convenience.
library LibZip {
    // Calldata compression and decompression using selective run length encoding:
    // - Sequences of 0x00 (up to 128 consecutive).
    // - Sequences of 0xff (up to 32 consecutive).
    //
    // A run length encoded block consists of two bytes:
    // (0) 0x00
    // (1) A control byte with the following bit layout:
    //     - [7]     `0: 0x00, 1: 0xff`.
    //     - [0..6]  `runLength - 1`.
    //
    // The first 4 bytes are bitwise negated so that the compressed calldata
    // can be dispatched into the `fallback` and `receive` functions.

    /// @dev To be called in the `fallback` function.
    /// ```
    ///     fallback() external payable { LibZip.cdFallback(); }
    ///     receive() external payable {} // Silence compiler warning to add a `receive` function.
    /// ```
    /// For efficiency, this function will directly return the results, terminating the context.
    /// If called internally, it must be called at the end of the function.
    function cdFallback() internal {
        assembly ("memory-safe") {
            if iszero(calldatasize()) { return(0x00, 0x00) }
            let ptr := mload(0x40)
            let o := ptr
            let f := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc // For negating the first 4 bytes.
            for { let i := 0x00 } gt(calldatasize(), i) {} {
                let c := byte(0x00, xor(add(f, i), calldataload(i)))
                i := add(i, 1)
                if iszero(c) {
                    let d := byte(0x00, xor(add(f, i), calldataload(i)))
                    i := add(0x01, i)
                    // Fill with either 0xff or 0x00.
                    mstore(o, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
                    if iszero(lt(0x7f, d)) { codecopy(o, codesize(), add(0x01, d)) }
                    o := add(add(0x01, and(0x7f, d)), o)
                    continue
                }
                mstore8(o, c)
                o := add(0x01, o)
            }
            let success := delegatecall(gas(), address(), ptr, o, 0x00, 0x00)
            returndatacopy(ptr, 0x00, returndatasize())
            if iszero(success) { revert(ptr, returndatasize()) }
            return(ptr, returndatasize())
        }
    }
}
