// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

struct Call {
    address target;
    bytes data;
}

struct Result {
    bool success;
    bytes data;
}

interface IMultiCallAggregator {
    function multicall(Call[] calldata) external returns (Result[] memory);
}

library SafeCall {
    function safeCall(address target, bytes calldata data, uint256 calldepth)
        internal
        returns (bool success, bytes memory returndata)
    {
        assembly ("memory-safe") {
            returndata := mload(0x40)
            calldatacopy(returndata, data.offset, data.length)
            let beforeGas := gas()
            success := call(gas(), target, 0, returndata, data.length, 0, 0)
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
                    // Apply the "all but one 64th" rule `calldepth + 1` times.
                    let remainingGas := shr(6, beforeGas)
                    for {} calldepth { calldepth := sub(calldepth, 1) } {
                        remainingGas := add(remainingGas, shr(6, sub(beforeGas, remainingGas)))
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
}

library UnsafeArray {
    function unsafeGet(Call[] calldata calls, uint256 i) internal pure returns (address target, bytes calldata data) {
        assembly ("memory-safe") {
            // Initially, we set `data.offset` to the pointer to the length. This is 32 bytes before
            // the actual start of data.
            data.offset :=
                add(
                    calls.offset,
                    calldataload(
                        add(shl(5, i), calls.offset) // Can't overflow; we assume `i` is in-bounds.
                    )
                )
            // Because the offset to `data` stored in `calls` is arbitrary, we have to check it.
            let err := lt(data.offset, add(calls.offset, shl(5, calls.length)))
            err := or(err, iszero(lt(data.offset, calldatasize())))
            // `data.offset` now points to `target`; load it.
            target := calldataload(data.offset)

            {
                // Indirect `data.offset` again to get the `bytes` payload.
                let tmp :=
                    add(
                        data.offset,
                        calldataload(
                            // Can't overflow; `data.offset` is in-bounds of `calldata`.
                            add(0x20, data.offset)
                        )
                    )
                // Check that `tmp` (the new `data.offset`) didn't overflow.
                err := or(err, lt(tmp, data.offset))
                data.offset := tmp
            }
            // Check that `data.offset` is in-bounds.
            err := or(err, iszero(lt(data.offset, calldatasize())))

            // Now we load `data.length` and set `data.offset` to the start of calls.
            data.length := calldataload(data.offset)
            data.offset := add(0x20, data.offset) // Can't overflow; calldata can't be that long.
            {
                // Check that the end of `data` is in-bounds.
                let end := add(data.offset, data.length)
                err := or(err, lt(end, data.offset))
                err := or(err, gt(end, calldatasize()))
            }

            if err { revert(0x00, 0x00) }
        }
    }

    function unsafeGet(Result[] memory a, uint256 i) internal pure returns (Result memory r) {
        assembly ("memory-safe") {
            r := mload(add(add(0x20, shl(5, i)), a))
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
    /// This is equivalent to `return(abi.encode(r))`
    function unsafeReturn(Result[] memory r) internal pure {
        assembly ("memory-safe") {
            let returndatastart := sub(r, 0x20) // this is not technically memory safe
            mstore(returndatastart, 0x20)
            let returndataend

            {
                let end := add(r, shl(5, mload(r)))
                let base := add(0x20, r)
                for { let i := base } lt(i, end) { i := add(0x20, i) } {
                    let ri := mload(i)
                    mstore(i, sub(ri, base))
                    let j := add(0x20, ri)
                    let rj := mload(j)
                    mstore(j, sub(rj, ri))
                }

                {
                    let ri := mload(end)
                    mstore(end, sub(ri, base))
                    let j := add(0x20, ri)
                    let rj := mload(j)
                    mstore(j, sub(rj, ri))
                    returndataend := add(0x20, add(mload(rj), rj))
                }
            }

            return(returndatastart, sub(returndataend, returndatastart))
        }
    }
}

contract MultiCallAggregator {
    using SafeCall for address;
    using UnsafeArray for Call[];
    using UnsafeArray for Result[];
    using UnsafeMath for uint256;
    using UnsafeReturn for Result[];

    function multicall(Call[] calldata calls) internal returns (Result[] memory result) {
        result = new Result[](calls.length);
        for (uint256 i; i < calls.length; i = i.unsafeInc()) {
            (address target, bytes calldata data) = calls.unsafeGet(i);
            Result memory r = result.unsafeGet(i);
            (r.success, r.data) = target.safeCall(data, 4); // I chose 4 arbitrarily
        }
    }

    fallback() external payable {
        bytes32 selector = bytes32(IMultiCallAggregator.multicall.selector);
        Call[] calldata calls;
        assembly ("memory-safe") {
            // Check the selector.
            let err := xor(selector, calldataload(0x00))
            calls.offset := add(0x04, calldataload(0x04)) // can't overflow without clobbering selector
            calls.length := calldataload(calls.offset)
            calls.offset := add(0x20, calls.offset) // can't overflow without clobbering selector
            // Check that `calls.offset` is in-bounds.
            err := or(err, iszero(lt(calls.offset, calldatasize())))
            // Check that `calls.length` doesn't overflow.
            err := or(err, shr(0xfb, calls.length))
            let end := add(calls.offset, shl(0x05, calls.length))
            // Check that `end` doesn't overflow.
            err := or(err, lt(end, calls.offset))
            // Check that all of `calls` is in-bounds.
            err := or(err, gt(end, calldatasize()))

            if err { revert(0x00, 0x00) }
        }

        multicall(calls).unsafeReturn();
    }
}
