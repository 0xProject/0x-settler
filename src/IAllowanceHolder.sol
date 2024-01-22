// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

interface IAllowanceHolder {
    /// @notice Executes against `target` with the `data` payload. Prior to execution, token permits are temporarily stored for the
    /// duration of the transaction. These permits can be consumed by the `operator` during the execution
    /// Operator consumes the funds during its operations by calling back into `AllowanceHolder` with `holderTransferFrom`, consuming
    /// a token permit
    /// @dev msg.sender is forwarded to target appended to the msg data (similar to ERC-2771)
    /// @param operator An address which is allowed to consume the token permits
    /// @param token The ERC20 token the caller has authorised to be consumed
    /// @param amount The quantity of `token` the caller has authorised to be consumed
    /// @param target A contract to execute operations with `data`
    /// @param data The data to forward to `target`
    function execute(address operator, address token, uint256 amount, address payable target, bytes calldata data)
        external
        payable
        returns (bytes memory result);

    /// @notice The counterpart to `execute` which allows for the consumption of token permits later during execution
    /// @dev can only be called by the `operator` previously registered in `execute`
    /// @param token The ERC20 token to transfer
    /// @param owner The owner of tokens to transfer
    /// @param recipient The destination/beneficiary of the ERC20 `transferFrom`
    /// @param amount The quantity of `token` to transfer`
    function holderTransferFrom(address token, address owner, address recipient, uint256 amount)
        external
        returns (bool);

    function ephemeralAllowance(address operator, address owner, address token) external view returns (uint256);
}
