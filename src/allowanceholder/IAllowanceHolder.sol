// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

IAllowanceHolder constant ALLOWANCE_HOLDER = IAllowanceHolder(0x0000000000001fF3684f28c67538d4D072C22734);

interface IAllowanceHolder {
    /// @notice Executes against `target` with the `data` payload. Prior to execution, token permits
    ///         are temporarily stored for the duration of the transaction. These permits can be
    ///         consumed by the `operator` during the execution
    /// @notice `operator` consumes the funds during its operations by calling back into
    ///         `AllowanceHolder` with `transferFrom`, consuming a token permit.
    /// @dev Neither `exec` nor `transferFrom` check that `token` contains code.
    /// @dev msg.sender is forwarded to target appended to the msg data (similar to ERC-2771)
    /// @param operator An address which is allowed to consume the token permits
    /// @param token The ERC20 token the caller has authorised to be consumed
    /// @param amount The quantity of `token` the caller has authorised to be consumed
    /// @param target A contract to execute operations with `data`
    /// @param data The data to forward to `target`
    /// @return result The returndata from calling `target` with `data`
    /// @notice If calling `target` with `data` reverts, the revert is propagated
    function exec(address operator, address token, uint256 amount, address payable target, bytes calldata data)
        external
        payable
        returns (bytes memory result);

    /// @notice The counterpart to `exec` which allows for the consumption of token permits later
    ///         during execution
    /// @dev *DOES NOT* check that `token` contains code. This function vacuously succeeds if
    ///      `token` is empty.
    /// @dev can only be called by the `operator` previously registered in `exec`
    /// @param token The ERC20 token to transfer
    /// @param owner The owner of tokens to transfer
    /// @param recipient The destination/beneficiary of the ERC20 `transferFrom`
    /// @param amount The quantity of `token` to transfer`
    /// @return true
    function transferFrom(address token, address owner, address recipient, uint256 amount) external returns (bool);
}
