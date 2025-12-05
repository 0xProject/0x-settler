// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {FullMath} from "../vendor/FullMath.sol";

contract Across {
    using SafeTransferLib for IERC20;
    using FullMath for uint256;

    function bridgeERC20ToAcross(address spoke, bytes memory depositData) internal {
        IERC20 inputToken;
        assembly ("memory-safe") {
            inputToken := mload(add(0x60, depositData))
        }
        uint256 amount = inputToken.fastBalanceOf(address(this));
        inputToken.safeApproveIfBelow(spoke, amount);
        _bridgeToAcross(amount, 0 wei, spoke, depositData);
    }

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
            inputAmount := mload(add(0xa0, depositData))
            outputAmount := mload(add(0xc0, depositData))
        }
        uint256 updatedOutputAmount = outputAmount.mulDiv(updatedInputAmount, inputAmount);

        assembly ("memory-safe") {
            mstore(add(0xa0, depositData), updatedInputAmount)
            mstore(add(0xc0, depositData), updatedOutputAmount)

            let len := mload(depositData)
            // temporarily clobber `depositData` size memory area
            mstore(depositData, 0xad5425c6) // selector for `deposit(bytes32,bytes32,bytes32,bytes32,uint256,uint256,uint256,bytes32,uint32,uint32,uint32,bytes)`
            // `deposit` doesn't clash with any relevant function of restricted targets so we can skip checking spoke
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
