// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {FullMath} from "../vendor/FullMath.sol";

contract StargateV2 {
    using SafeTransferLib for IERC20;
    using FullMath for uint256;

    function bridgeERC20ToStargateV2(IERC20 token, address pool, bytes memory sendData) internal {
        uint256 amount = token.fastBalanceOf(address(this));
        token.safeApproveIfBelow(pool, amount);
        _bridgeToStargateV2(amount, address(this).balance, pool, sendData);
    }

    function bridgeNativeToStargateV2(address pool, uint256 destinationGas, bytes memory sendData) internal {
        uint256 amount;
        uint256 value;
        assembly ("memory-safe") {
            value := selfbalance()
            amount := sub(sub(value, destinationGas), mload(add(0x40, sendData)))
        }
        _bridgeToStargateV2(amount, value, pool, sendData);
    }

    function _bridgeToStargateV2(uint256 updatedInputAmount, uint256 value, address pool, bytes memory sendData)
        internal
    {
        assembly ("memory-safe") {
            mstore(add(0xe0, sendData), updatedInputAmount)

            let len := mload(sendData)
            // temporarily clobber `sendData` size memory area
            mstore(sendData, 0xcbef2aa9) // selector for `sendToken((uint32,bytes32,uint256,uint256,bytes,bytes,bytes),(uint256,uint256),address)`
            // `sendToken` doesn't clash with any relevant function of restricted targets so we can skip checking pool
            if iszero(call(gas(), pool, value, add(0x1c, sendData), add(0x04, len), 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            // restore clobbered memory
            mstore(sendData, len)
        }
    }
}
