// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

contract LayerZeroOFT {
    using SafeTransferLib for IERC20;

    function bridgeLayerZeroOFT(IERC20 token, address oft, bytes memory sendData) internal {
        uint256 updatedInputAmount = token.fastBalanceOf(address(this));
        token.safeApproveIfBelow(oft, updatedInputAmount);

         assembly ("memory-safe") {
            mstore(add(0xe0, sendData), updatedInputAmount)

            let len := mload(sendData)
            // temporarily clobber `sendData` size memory area
            mstore(sendData, 0xc7c7f5b3) // selector for `send((uint32,bytes32,uint256,uint256,bytes,bytes,bytes),(uint256,uint256),address)`
            // `send` doesn't clash with any relevant function of restricted targets so we can skip checking oft
            if iszero(call(gas(), oft, selfbalance(), add(0x1c, sendData), add(0x04, len), 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            // restore clobbered memory
            mstore(sendData, len)
        }
    }
}
