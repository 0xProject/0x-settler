// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

interface IAllowanceHolder {
    struct TransferDetails {
        address token;
        address recipient;
        uint256 amount;
    }

    /// @notice Executes against `target` with the `data` payload. Prior to execution, token permits are temporarily stored for the
    /// duration of the transaction. These permits can be consumed by the `operator` during the execution
    /// Operator consumes the funds during its operations by calling back into `AllowanceHolder` with `holderTransferFrom`, consuming
    /// a token permit
    /// @dev tx.origin must be msg.sender in order to use `execute`
    /// @dev tx.origin / msg.sender is forwarded to target appended to the msg data (similar to EIP-2771)
    /// @param operator An address which is allowned to consume the token permits
    /// @param permits A list of tokens and amounts the caller has authorised to be consumed
    /// @param target A contract to execute operations with `data`
    /// @param data The data to forward to `target`
    function execute(
        address operator,
        ISignatureTransfer.TokenPermissions[] calldata permits,
        address payable target,
        bytes calldata data
    ) external payable returns (bytes memory result);

    /// @notice The counterpart to `execute` which allows for the consumption of token permits later during execution
    /// @dev can only be called by the `operator` previously registered in `execute`
    /// @dev can only spend funds from `tx.origin`
    /// @param owner The owner of tokens to transfer
    /// @param transferDetails The tokens, recipient and amounts which `operator` wants to spend during this interaction
    function holderTransferFrom(address owner, TransferDetails[] calldata transferDetails) external returns (bool);

    /// @notice Moves funds from msg.sender into target prior to execution.
    /// @dev Unlike `execute` no storage is used, all tokens are moved prior
    /// @dev msg.sender is forwarded to `target` by appending it to the msg data (similar to EIP-2771)
    /// @param permits A list of tokens and amounts the caller has authorised to be consumed
    /// @param target A contract to execute operations with `data`
    /// @param data The data to forward to `target`
    function moveExecute(
        ISignatureTransfer.TokenPermissions[] calldata permits,
        address payable target,
        bytes calldata data
    ) external payable returns (bytes memory result);
}
