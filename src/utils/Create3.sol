// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {AddressDerivation} from "./AddressDerivation.sol";
import {Panic} from "./Panic.sol";

/*
        // constructor
        | Address | Bytecode | Mnemonic | Stack                             | Memory
        ----------------------------------------------------------------------------
/-----< | 00 | 6021 | push1 0x22   | [runtimeLen]                           | {}
|       | 02 | 80   | dup1         | [runtimeLen runtimeLen]                | {}
|   /-< | 03 | 6009 | push1 0x09   | [runtimeStart runtimeLen runtimeLen]   | {}
|   |   | 05 | 5f   | push0        | [0 runtimeStart runtimeLen runtimeLen] | {}
|   |   | 06 | 39   | codecopy     | [runtimeLen]                           | {runtime}
|   |   | 07 | 5f   | push0        | [0 runtimeLen]                         | {runtime}
|   |   | 08 | f3   | return       | X                                      | X
|   \-> | 09 |
|
|       // runtime
|       | Address | Bytecode | Mnemonic | Stack                             | Memory
|       ----------------------------------------------------------------------------
|       | 00 | 5f   | push0        | [0]                                    | {}
|       | 01 | 54   | sload        | [initialized]                          | {}
| /---< | 02 | 601e | push1 0x1f   | [target initialized}                   | {}
| |     | 04 | 57   | jumpi        | []                                     | {}
| |     | 05 | 6001 | push1 0x01   | [1]                                    | {}
| |     | 07 | 5f   | push0        | [0 1]                                  | {}
| |     | 08 | 55   | sstore       | []                                     | {}
| |     | 09 | 36   | calldatasize | [cds]                                  | {}
| |     | 0a | 5f   | push0        | [0 cds]                                | {}
| |     | 0b | 5f   | push0        | [0 0 cds]                              | {}
| |     | 0c | 37   | calldatacopy | []                                     | {initCode}
| |     | 0d | 36   | calldatasize | [cds]                                  | {initCode}
| |     | 0e | 5f   | push0        | [0 cds]                                | {initCode}
| |     | 0f | 34   | callvalue    | [msg.value 0 cds]                      | {initCode}
| |     | 10 | f0   | create       | [deployed]                             | {initCode}
| |     | 11   5f   | push0        | [0 deployed]                           | {initCode}
| |     | 12 | 81   | dup2         | [deployed 0 deployed]                  | {initCode}
| | /-< | 13 | 6018 | push1 0x18   | [target deployed 0 deployed]           | {initCode}
| | |   | 15 | 57   | jumpi        | [0 deployed]                           | {initCode}
| | |   | 16 | 5f   | push0        | [0 0 deployed]                         | {initCode}
| | |   | 17 | fd   | revert       | X                                      | X
| | \-> | 18 | 5b   | jumpdest     | [0 deployed]                           | {initCode}
| |     | 19 | 52   | mstore       | []                                     | {deployed ...}
| |     | 1a | 6020 | push1 0x20   | [32]                                   | {deployed ...}
| |     | 1c | 5f   | push0        | [0 32]                                 | {deployed ...}
| |     | 1d | f3   | return       | X                                      | X
| \---> | 1e | 5b   | jumpdest     | []                                     | {}
|       | 1f | 32   | origin       | [tx.origin]                            | {}
|       | 20 | ff   | selfdestruct | X                                      | {}
\-----> | 21 |
*/

library Create3 {
    uint256 private constant _SHIM0 = 0x60218060095f395ff35f54601e5760015f55365f5f37365f34f05f816018575f;
    uint80 private constant _SHIM1 = 0xfd5b5260205ff35b32ff;
    uint8 private constant _SHIM1_LENGTH = 0x0a;
    uint8 private constant _SHIM_LENGTH = 0x2a;
    bytes32 private constant _SHIM_INITHASH = 0x27fc81c6e9350a4023c28ecd8d6d2e02ee484971c16865596228e8241edb4290;

    function createFromCalldata(bytes32 salt, bytes calldata initCode, uint256 value)
        internal
        returns (address deployed)
    {
        if (initCode.length == 0) {
            Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
        }
        assembly ("memory-safe") {
            mstore(_SHIM1_LENGTH, _SHIM1)
            mstore(0x00, _SHIM0)
            let shim := create2(0x00, 0x00, _SHIM_LENGTH, salt)
            if iszero(shim) { revert(0x00, 0x00) }
            let ptr := mload(0x40)
            calldatacopy(ptr, initCode.offset, initCode.length)
            if iszero(call(gas(), shim, value, ptr, initCode.length, 0x00, 0x20)) { revert(0x00, 0x00) }
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
            mstore(_SHIM1_LENGTH, _SHIM1)
            mstore(0x00, _SHIM0)
            let shim := create2(0x00, 0x00, _SHIM_LENGTH, salt)
            if iszero(shim) { revert(0x00, 0x00) }
            if iszero(call(gas(), shim, value, add(0x20, initCode), mload(initCode), 0x00, 0x20)) { revert(0x00, 0x00) }
            deployed := mload(0x00)
            pop(call(gas(), shim, 0x00, 0x00, 0x00, 0x00, 0x00))
        }
    }

    function createFromMemory(bytes32 salt, bytes memory initCode) internal returns (address) {
        return createFromMemory(salt, initCode, 0);
    }

    function predict(bytes32 salt, address deployer) internal pure returns (address) {
        return AddressDerivation.deriveContract(
            AddressDerivation.deriveDeterministicContract(deployer, salt, _SHIM_INITHASH), 1
        );
    }

    function predict(bytes32 salt) internal view returns (address) {
        return predict(salt, address(this));
    }
}
