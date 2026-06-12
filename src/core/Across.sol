// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {tmp} from "../utils/512Math.sol";

interface ISpokePool {
    function deposit(
        bytes32 depositor,
        bytes32 recipient,
        bytes32 inputToken,
        bytes32 outputToken,
        uint256 inputAmount,
        uint256 outputAmount,
        uint256 destinationChainId,
        bytes32 exclusiveRelayer,
        uint32 quoteTimestamp,
        uint32 fillDeadline,
        uint32 exclusivityDeadline,
        bytes calldata message
    ) external payable;

    event FundsDeposited(
        bytes32 inputToken,
        bytes32 outputToken,
        uint256 inputAmount,
        uint256 outputAmount,
        uint256 indexed destinationChainId,
        uint256 indexed depositId,
        uint32 quoteTimestamp,
        uint32 fillDeadline,
        uint32 exclusivityDeadline,
        bytes32 indexed depositor,
        bytes32 recipient,
        bytes32 exclusiveRelayer,
        bytes message
    );
}

contract Across {
    using SafeTransferLib for IERC20;

    /// @notice Bridge ERC20 tokens via Across
    /// @param spoke The Across spokePool address
    /// @param depositData Encoded call to `ISpokePool.deposit` without selector
    function bridgeERC20ToAcross(address spoke, bytes memory depositData) internal {
        IERC20 inputToken;
        assembly ("memory-safe") {
            // inputToken is the 3rd parameter in `ISpokePool.deposit` function,
            // then it is at offset 0x40, which at 0x60 in depositData
            inputToken := mload(add(0x60, depositData))
        }
        uint256 amount = inputToken.fastBalanceOf(address(this));
        inputToken.safeApproveIfBelow(spoke, amount);
        _bridgeToAcross(amount, 0 wei, spoke, depositData);
    }

    /// @notice Bridge native tokens via Across
    /// @param spoke The Across spokePool address
    /// @param depositData Encoded call to `ISpokePool.deposit` without selector
    function bridgeNativeToAcross(address spoke, bytes memory depositData) internal {
        uint256 amount = address(this).balance;
        _bridgeToAcross(amount, amount, spoke, depositData);
    }

    function _bridgeToAcross(uint256 updatedInputAmount, uint256 value, address spoke, bytes memory depositData)
        internal
    {
        uint256 inputAmount;
        uint256 outputAmount;
        assembly ("memory-safe") {
            // inputAmount is the 5th parameter in `ISpokePool.deposit` function,
            // then it is at offset 0x80, which at 0xa0 in depositData
            inputAmount := mload(add(0xa0, depositData))
            // outputAmount is the 6th parameter in `ISpokePool.deposit` function,
            // then it is at offset 0xa0, which at 0xc0 in depositData
            outputAmount := mload(add(0xc0, depositData))
        }
        uint256 updatedOutputAmount = tmp().omul(outputAmount, updatedInputAmount).div(inputAmount);

        assembly ("memory-safe") {
            // override inputAmount and outputAmount with updated values
            mstore(add(0xa0, depositData), updatedInputAmount)
            mstore(add(0xc0, depositData), updatedOutputAmount)

            let len := mload(depositData)
            // temporarily clobber `depositData` size memory area
            mstore(depositData, 0xad5425c6) // selector for `ISpokePool.deposit`
            // `spoke` is user-provided but we're calling a specific function `ISpokePool.deposit`
            // which doesn't clash with restricted targets (AllowanceHolder & Permit2)
            if iszero(call(gas(), spoke, value, add(0x1c, depositData), add(0x04, len), 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            // restore clobbered memory
            mstore(depositData, len)
        }
    }
}
