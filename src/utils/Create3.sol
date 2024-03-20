// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {AddressDerivation} from "./AddressDerivation.sol";

/*
        // constructor
        | Address | Bytecode | Mnemonic | Stack                   | Memory
        ------------------------------------------------------------------
        | 00 | 7f.. | push32       | [runtime]                    | {}
        | 21 | 5f   | push0        | [0 runtime]                  | {}
        | 22 | 52   | mstore       | []                           | {runtime}
/-----< | 23 | 59   | msize        | [32]                         | {runtime}
|       | 24 | 5f   | push0        | [0 32]                       | {runtime}
|       | 25 | f3   | return       | X                            | X
|       | 26 |
|
|       // runtime
|       | Address | Bytecode | Mnemonic | Stack                   | Memory
|       ------------------------------------------------------------------
|       | 00 | 36   | calldatasize | [cds]                        | {}
|       | 01 | 58   | pc           | [1 cds]                      | {}
|       | 02 | 5f   | push0        | [0 1 cds]                    | {}
|       | 03 | 54   | sload        | [initialized 1 cds]          | {}
| /---< | 04 | 601d | push1 0x1d   | [target initialized 1 cds]   | {}
| |     | 06 | 57   | jumpi        | [1 cds]                      | {}
| |     | 07 | 5f   | push0        | [0 1 cds]                    | {}
| |     | 08 | 55   | sstore       [ [cds]                        | {}
| |     | 09 | 5f   | push0        | [0 cds]                      | {}
| |     | 0a | 5f   | push0        | [0 0 cds]                    | {}
| |     | 0b | 37   | calldatacopy | []                           | {initCode}
| |     | 0c | 36   | calldatasize | [cds]                        | {initCode}
| |     | 0d | 5f   | push0        | [0 cds]                      | {initCode}
| |     | 0e | 34   | callvalue    | [msg.value 0 cds]            | {initCode}
| |     | 0f | f0   | create       | [deployed]                   | {initCode}
| |     | 10   5f   | push0        | [0 deployed]                 | {initCode}
| |     | 11 | 81   | dup2         | [deployed 0 deployed]        | {initCode}
| | /-< | 12 | 6017 | push1 0x17   | [target deployed 0 deployed] | {initCode}
| | |   | 14 | 57   | jumpi        | [0 deployed]                 | {initCode}
| | |   | 15 | 5f   | push0        | [0 0 deployed]               | {initCode}
| | |   | 16 | fd   | revert       | X                            | X
| | \-> | 17 | 5b   | jumpdest     | [0 deployed]                 | {initCode}
| |     | 18 | 52   | mstore       | []                           | {deployed ...}
| |     | 19 | 6020 | push1 0x20   | [32]                         | {deployed ...}
| |     | 1b | 5f   | push0        | [0 32]                       | {deployed ...}
| |     | 1c | f3   | return       | X                            | X
| \---> | 1d | 5b   | jumpdest     | [1 cds]                      | {}
|       | 1e | 30   | address      | [this 1 cds]                 | {}
|       | 1f | ff   | selfdestruct | X                            | X
\-----> | 20 |
*/

library Create3 {
    uint256 private constant _SHIM0 = 0x7f36585f54601d575f555f5f37365f34f05f816017575ffd5b5260205ff35b30;
    uint48 private constant _SHIM1 = 0xff5f52595ff3;
    uint8 private constant _SHIM1_LENGTH = 0x06;
    uint8 private constant _SHIM_LENGTH = 0x26;
    bytes32 private constant _SHIM_INITHASH = 0x3bf3f97f0be1e2c00023033eefeb4fc062ac552ff36778b17060d90b6764902f;

    function createFromCalldata(bytes32 salt, bytes calldata initCode, uint256 value)
        internal
        returns (address deployed)
    {
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
