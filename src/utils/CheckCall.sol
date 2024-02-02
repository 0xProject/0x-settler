// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

library CheckCall {
    /**
     * @notice `staticcall` another contract forwarding a precomputed amount of
     *         gas. Check the length of the return without reading it.
     * @dev contains protections against EIP-150-induced insufficient gas
     *      griefing
     * @dev reverts iff the target is not a contract or we encounter an
     *      out-of-gas
     * @return success true iff the call succeded and returned at least
     *                 `minReturnBytes` of return data
     * @param target the contract (reverts if non-contract) on which to make the
     *               `staticcall`
     * @param data the calldata to pass
     * @param callGas the gas to pass for the call. If the call requires more than
     *                the specified amount of gas and the caller didn't provide at
     *                least `callGas`, triggers an out-of-gas in the caller.
     * @param minReturnBytes `success` is false if the call doesn't return at
     *                       least this much return data
     */
    function checkCall(address target, bytes memory data, uint256 callGas, uint256 minReturnBytes)
        internal
        view
        returns (bool success)
    {
        assembly ("memory-safe") {
            target := and(0xffffffffffffffffffffffffffffffffffffffff, target)
            success := staticcall(callGas, target, add(data, 0x20), mload(data), 0x00, 0x00)

            // As of the time this contract was written, `verbatim` doesn't work in
            // inline assembly. Assignment of a value to a variable costs gas
            // (although how much is unpredictable because it depends on the Yul/IR
            // optimizer), as does the `GAS` opcode itself. Also solc tends to reorder
            // the call to `gas()` with preparing the arguments for `div`. Therefore,
            // the `gas()` below returns less than the actual amount of gas available
            // for computation at the end of the call. That makes this check slightly
            // too conservative. However, we do not correct for this because the
            // correction would become outdated (possibly too permissive) if the
            // opcodes are repriced.

            // https://eips.ethereum.org/EIPS/eip-150
            // https://ronan.eth.link/blog/ethereum-gas-dangers/
            if iszero(or(success, or(returndatasize(), lt(div(callGas, 63), gas())))) {
                // The call failed due to not enough gas left. We deliberately consume
                // all remaining gas with `invalid` (instead of `revert`) to make this
                // failure distinguishable to our caller.
                invalid()
            }

            if success {
                if iszero(returndatasize()) { if iszero(extcodesize(target)) { revert(0x00, 0x00) } }
                success := iszero(lt(returndatasize(), minReturnBytes))
            }
        }
    }
}
