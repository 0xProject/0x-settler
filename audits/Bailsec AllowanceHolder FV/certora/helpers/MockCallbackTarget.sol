// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

contract MockCallbackTarget {
    fallback() external payable {
        assembly {
            mstore(0x00, 0x01)
            return(0x00, 0x20)  // EVM RETURN opcode — execution stops here
        }
    }

}