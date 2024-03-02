// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

library CheckCall {
    /**
     * @notice `staticcall` another contract. Check the length of the return
     *         without reading it.
     * @dev contains protections against EIP-150-induced insufficient gas
     *      griefing
     * @dev reverts iff the target is not a contract or we encounter an
     *      out-of-gas
     * @return success true iff the call succeded and returned at least `minReturnBytes` of return
     *                 data
     * @param target the contract (reverts if non-contract) on which to make the
     *               `staticcall`
     * @param data the calldata to pass
     * @param minReturnBytes `success` is false if the call doesn't return at
     *                       least this much return data
     */
    function checkCall(address target, bytes memory data, uint256 minReturnBytes)
        internal
        view
        returns (bool success)
    {
        assembly ("memory-safe") {
            let beforeGas
            {
                let offset := add(data, 0x20)
                let length := mload(data)
                beforeGas := gas()
                success := staticcall(gas(), target, offset, length, 0x00, 0x00)
            }

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

            if iszero(or(success, returndatasize())) {
                // https://eips.ethereum.org/EIPS/eip-150
                // https://ronan.eth.limo/blog/ethereum-gas-dangers/
                // We apply the "all but one 64th" rule twice because `target` could plausibly be a
                // proxy. We apply it only twice because we assume only a single level of
                // indirection.
                let remainingGas := shr(6, beforeGas)
                remainingGas := add(remainingGas, shr(6, sub(beforeGas, remainingGas)))
                if iszero(lt(remainingGas, afterGas)) {
                    // The call failed due to not enough gas left. We deliberately consume all
                    // remaining gas with `invalid` (instead of `revert`) to make this failure
                    // distinguishable to our caller.
                    invalid()
                }
            }

            if success {
                // addresses without code can't revert, so we only need this check in the
                // non-reverting path. the presence of returndata indicates that code was executed.
                if iszero(returndatasize()) { if iszero(extcodesize(target)) { revert(0x00, 0x00) } }
                // the actual core check of this function
                success := iszero(lt(returndatasize(), minReturnBytes))
            }
        }
    }
}
