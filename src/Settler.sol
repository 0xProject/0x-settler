// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {UniswapV3} from "./core/UniswapV3.sol";
import {Permit2Payment} from "./core/Permit2Payment.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

contract Settler is UniswapV3, Permit2Payment {
    error ActionInvalid(bytes4 action, bytes data);
    error ActionFailed(bytes4 action, bytes data, bytes output);
    error LengthMismatch();

    bytes4 internal constant ACTION_PERMIT2_TRANSFER_FROM = bytes4(keccak256("PERMIT2_TRANSFER_FROM"));
    bytes4 internal constant ACTION_UNISWAPV3_SWAP_EXACT_IN = bytes4(keccak256("UNISWAPV3_SWAP_EXACT_IN"));
    /// @dev Performs a UniswapV3 trade over pools with the initial funding coming from msg.sender Permit2.
    ///      Differs from ACTION_UNISWAPV3_SWAP_EXACT_IN  where the funding is expected to be address(this).
    bytes4 internal constant ACTION_UNISWAPV3_PERMIT2_SWAP_EXACT_IN =
        bytes4(keccak256("UNISWAPV3_PERMIT2_SWAP_EXACT_IN"));

    constructor(address permit2, address uniFactory, bytes32 poolInitCodeHash)
        Permit2Payment(permit2)
        UniswapV3(uniFactory, poolInitCodeHash, permit2)
    {}

    function execute(bytes calldata actions, bytes[] calldata datas) public payable {
        bool success;
        bytes memory output;
        uint256 numActions = actions.length / 4;

        if (datas.length != numActions) {
            revert LengthMismatch();
        }

        for (uint256 i = 0; i < numActions;) {
            bytes4 action = bytes4(actions[i * 4:i * 4 + 4]);

            bytes calldata data = datas[i];
            (success, output) = dispatch(action, data);
            if (!success) {
                revert ActionFailed({action: action, data: data, output: output});
            }
            unchecked {
                i++;
            }
        }
    }

    function dispatch(bytes4 action, bytes calldata data) internal returns (bool success, bytes memory output) {
        success = true;

        if (action == ACTION_PERMIT2_TRANSFER_FROM) {
            (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) =
                abi.decode(data, (ISignatureTransfer.PermitTransferFrom, bytes));
            // Consume the entire Permit with the recipient of funds as this contract
            ISignatureTransfer.SignatureTransferDetails memory transferDetails = ISignatureTransfer
                .SignatureTransferDetails({to: address(this), requestedAmount: permit.permitted.amount});

            permit2TransferFrom(permit, transferDetails, msg.sender, sig);
        } else if (action == ACTION_UNISWAPV3_SWAP_EXACT_IN) {
            (address recipient, uint256 amountIn, uint256 amountOutMin, bytes memory path) =
                abi.decode(data, (address, uint256, uint256, bytes));

            sellTokenForTokenToUniswapV3(path, amountIn, amountOutMin, recipient);
        } else if (action == ACTION_UNISWAPV3_PERMIT2_SWAP_EXACT_IN) {
            (address recipient, uint256 amountIn, uint256 amountOutMin, bytes memory path, bytes memory permit2Data) =
                abi.decode(data, (address, uint256, uint256, bytes, bytes));

            sellTokenForTokenToUniswapV3(path, amountIn, amountOutMin, recipient, permit2Data);
        } else {
            revert ActionInvalid({action: action, data: data});
        }
    }
}
