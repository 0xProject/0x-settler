// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {AddressDerivation} from "./AddressDerivation.sol";
import {Panic} from "./Panic.sol";

/*
        // constructor
        | Address | Bytecode | Mnemonic | Argument | Stack | Memory
/-----< | 00 | 6028 | push1 0x28   | [runtimeLen] | {}
|       | 02 | 80   | dup1         | [runtimeLen runtimeLen] | {}
|   /-< | 03 | 6009 | push1 0x09   | [runtimeStart runtimeLen runtimeLen] | {}
|   |   | 05 | 5f   | push0        | [0 runtimeStart runtimeLen runtimeLen] | {}
|   |   | 06 | 39   | codecopy     | [runtimeLen] | {runtime}
|   |   | 07 | 5f   | push0        | [0 runtimeLen] | {runtime}
|   |   | 08 | f3   | return       | X | X
|   \-> | 09 |
|
|       // runtime
|       | Address | Bytecode | Mnemonic | Argument | Stack | Memory
|       | 00 | 36   | calldatasize | [cds] | {}
|   /-< | 01 | 6006 | push1 0x06   | [target cds] | {}
|   |   | 03 | 57   | jumpi        | [] | {}
|   |   | 04 | 32   | origin       | [tx.origin] | {}
|   |   | 05 | ff   | selfdestruct | X | X
|   \-> | 06 | 5b   | jumpdest     | [] | {}
|       | 07 | 5f   | push0        | [0] | {}
|       | 08 | 54   | sload        | [initialized] | {}
| /---< | 09 | 6026 | push1 0x26   | [target initialized] | {}
| |     | 0b | 57   | jumpi        | [] | {}
| |     | 0c | 6001 | push1 0x01   | [1] | {}
| |     | 0e | 5f   | push0        | [0 1] | {}
| |     | 0f | 55   | sstore       | [] | {}
| |     | 10 | 36   | calldatasize | [cds] | {}
| |     | 11 | 5f   | push0        | [0 cds] | {}
| |     | 12 | 5f   | push0        | [0 0 cds] | {}
| |     | 13 | 37   | calldatacopy | [] | {initCode}
| |     | 14 | 36   | calldatasize | [cds] | {initCode}
| |     | 15 | 5f   | push0        | [0 cds] | {initCode}
| |     | 16 | 34   | callvalue    | [msg.value 0 cds] | {initCode}
| |     | 17 | f0   | create       | [deplyed] | {initCode}
| |     | 18 | 80   | dup1         | [deployed deployed] | {initCode}
| | /-< | 19 | 601f | push1 0x1f   | [target deployed deployed] | {initCode}
| | |   | 1b | 57   | jumpi        | [deployed] | {initCode}
| | |   | 1c | 5f   | push0        | [0 deployed] | {initCode}
| | |   | 1d | 5f   | push0        | [0 0 deployed] | {initCode}
| | |   | 1e | fd   | revert       | X | X
| | \-> | 1f | 5b   | jumpdest     | [deployed] | {initCode}
| |     | 20 | 5f   | push0        | [0 deployed] | {initCode}
| |     | 21 | 52   | mstore       | [] | {deployed ...}
| |     | 22 | 6020 | push1 0x20   | [32] | {deployed ...}
| |     | 24 | 5f   | push0        | [0 32] | {deployed ...}
| |     | 25 | f3   | return       | X | X
| \---> | 26 | 5b   | jumpdest     | [] | {}
|       | 27 | fe   | invalid      | X | X
\-----> | 28 |
*/

library Create3 {
    function createFromCalldata(bytes32 salt, bytes calldata initCode, uint256 value)
        internal
        returns (address deployed)
    {
        if (initCode.length == 0) {
            Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
        }
        assembly ("memory-safe") {
            mstore(0x11, 0xf080601f575f5ffd5b5f5260205ff35bfe)
            mstore(0x00, 0x60288060095f395ff33660065732ff5b5f5460265760015f55365f5f37365f34)
            let shim := create2(0x00, 0x00, 0x31, salt)
            if iszero(shim) { revert(0x00, 0x00) }
            let ptr := mload(0x40)
            calldatacopy(ptr, initCode.offset, initCode.length)
            let success := call(gas(), shim, value, ptr, initCode.length, 0x00, 0x20)
            if iszero(success) { revert(0x00, 0x00) }
            deployed := mload(0x00)
            pop(call(gas(), shim, 0x00, 0x00, 0x00, 0x00, 0x00))
        }
    }

    function createFromCalldata(bytes32 salt, bytes calldata initCode) internal returns (address) {
        return createFromCalldata(salt, initCode, 0);
    }

    function createFromMemory(bytes32 salt, bytes memory initCode, uint256 value) internal returns (address deployed) {
        if (initCode.length == 0) {
            Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
        }
        assembly ("memory-safe") {
            mstore(0x11, 0xf080601f575f5ffd5b5f5260205ff35bfe)
            mstore(0x00, 0x60288060095f395ff33660065732ff5b5f5460265760015f55365f5f37365f34)
            let shim := create2(0x00, 0x00, 0x31, salt)
            if iszero(shim) { revert(0x00, 0x00) }
            let success := call(gas(), shim, value, add(0x20, initCode), mload(initCode), 0x00, 0x20)
            if iszero(success) { revert(0x00, 0x00) }
            deployed := mload(0x00)
            pop(call(gas(), shim, 0x00, 0x00, 0x00, 0x00, 0x00))
        }
    }

    function createFromMemory(bytes32 salt, bytes memory initCode) internal returns (address) {
        return createFromMemory(salt, initCode, 0);
    }

    function predict(bytes32 salt, address deployer) internal pure returns (address r) {
        return AddressDerivation.deriveContract(
            AddressDerivation.deriveDeterministicContract(
                deployer, salt, 0xc979a27a67b280ded6080b47b000684d2de0189c7a6a768711e1f69e87da0609
            ),
            1
        );
    }

    function predict(bytes32 salt) internal view returns (address) {
        return predict(salt, address(this));
    }
}
