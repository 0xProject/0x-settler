// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

address constant DLN_SOURCE = 0xeF4fB24aD0916217251F553c0596F8Edc630EB66;

contract DeBridge {
    using SafeTransferLib for IERC20;

    function bridgeToDeBridge(uint256 globalFee, bytes memory createOrderData) internal {
        IERC20 inputToken;
        uint256 value;
        assembly ("memory-safe") {
            // offset to giveTokenAddress
            inputToken := mload(add(0xe0, createOrderData))
            value := selfbalance()
        }
        // Store the constant into source to read it only once
        address source = DLN_SOURCE;
        if(address(inputToken) == address(0)) {
            _bridgeNativeToDeBridge(source, value, value - globalFee, createOrderData);
        }
        else {
            uint256 amount = inputToken.fastBalanceOf(address(this));
            inputToken.safeApproveIfBelow(source, amount);
            
            _bridgeNativeToDeBridge(source, value, value - globalFee, createOrderData);
        }
    }

    function _bridgeNativeToDeBridge(address source, uint256 value, uint256 amount, bytes memory createOrderData)
        internal
    {
        assembly ("memory-safe") {
            // override giveAmount
            mstore(0x100, amount)

            let len := mload(createOrderData)
            // temporarily clobber `createOrderData` size memory area
            mstore(createOrderData, 0xb9303701) // selector for `createSaltedOrder((address,uint256,bytes,uint256,uint256,bytes,address,bytes,bytes,bytes,bytes),uint64,bytes,uint32,bytes,bytes)`
            // `createSaltedOrder` doesn't clash with any relevant function of restricted targets so we can skip checking `source`
            // `source` is also meant to be DLN_SOURCE 
            if iszero(call(gas(), source, value, add(0x1c, createOrderData), add(0x04, len), 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            // restore clobbered memory
            mstore(createOrderData, len)
        }
    }
}
