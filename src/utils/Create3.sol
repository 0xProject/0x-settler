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
| |     | 08 | 55   | sstore       | [cds]                        | {}
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





        // constructor
        | Address | Bytecode | Mnemonic | Stack                     | Memory
        ------------------------------------------------------------------
        | 00 | 7f.. | push32         | [runtime]                    | {}
        | 21 | 3d   | returndatasize | [0 runtime]                  | {}
        | 22 | 52   | mstore         | []                           | {runtime}
/-----< | 23 | 59   | msize          | [32]                         | {runtime}
|       | 24 | 3d   | returndatasize | [0 32]                       | {runtime}
|       | 25 | f3   | return         | X                            | X
|       | 26 |
|
|       // runtime
|       | Address | Bytecode | Mnemonic | Stack                     | Memory
|       ------------------------------------------------------------------
|       | 00 | 36   | calldatasize   | [cds]                        | {}
|       | 01 | 58   | pc             | [1 cds]                      | {}
|       | 02 | 3d   | returndatasize | [0 1 cds]                    | {}
|       | 03 | 54   | sload          | [initialized 1 cds]          | {}
| /---< | 04 | 601d | push1 0x1d     | [target initialized 1 cds]   | {}
| |     | 06 | 57   | jumpi          | [1 cds]                      | {}
| |     | 07 | 3d   | returndatasize | [0 1 cds]                    | {}
| |     | 08 | 55   | sstore         | [cds]                        | {}
| |     | 09 | 3d   | returndatasize | [0 cds]                      | {}
| |     | 0a | 3d   | returndatasize | [0 0 cds]                    | {}
| |     | 0b | 37   | calldatacopy   | []                           | {initCode}
| |     | 0c | 36   | calldatasize   | [cds]                        | {initCode}
| |     | 0d | 3d   | returndatasize | [0 cds]                      | {initCode}
| |     | 0e | 34   | callvalue      | [msg.value 0 cds]            | {initCode}
| |     | 0f | f0   | create         | [deployed]                   | {initCode}
| |     | 10   3d   | returndatasize | [0 deployed]                 | {initCode}
| |     | 11 | 81   | dup2           | [deployed 0 deployed]        | {initCode}
| | /-< | 12 | 6017 | push1 0x17     | [target deployed 0 deployed] | {initCode}
| | |   | 14 | 57   | jumpi          | [0 deployed]                 | {initCode}
| | |   | 15 | 3d   | returndatasize | [0 0 deployed]               | {initCode}
| | |   | 16 | fd   | revert         | X                            | X
| | \-> | 17 | 5b   | jumpdest       | [0 deployed]                 | {initCode}
| |     | 18 | 52   | mstore         | []                           | {deployed ...}
| |     | 19 | 6020 | push1 0x20     | [32]                         | {deployed ...}
| |     | 1b | 3d   | returndatasize | [0 32]                       | {deployed ...}
| |     | 1c | f3   | return         | X                            | X
| \---> | 1d | 5b   | jumpdest       | [1 cds]                      | {}
|       | 1e | 30   | address        | [this 1 cds]                 | {}
|       | 1f | ff   | selfdestruct   | X                            | X
\-----> | 20 |


*/

library Create3 {
    uint256 private constant _SHIM0 = 0x7f36585f54601d575f555f5f37365f34f05f816017575ffd5b5260205ff35b30;
    uint48 private constant _SHIM1 = 0xff5f52595ff3;
    uint8 private constant _SHIM1_LENGTH = 0x06;
    uint8 private constant _SHIM_LENGTH = 0x26;
    bytes32 private constant _SHIM_INITHASH = 0x3bf3f97f0be1e2c00023033eefeb4fc062ac552ff36778b17060d90b6764902f;
    bytes32 private constant _SHIM_RUNTIME_HASH = 0xa9549013530fb1542c6fac59b531052d9fd0c0433910571c379618caa172f2cb;

    uint256 private constant _SHIM0_LONDON = 0x7f36583d54601d573d553d3d37363d34f03d816017573dfd5b5260203df35b30;
    uint48 private constant _SHIM1_LONDON = 0xff3d52593df3;
    bytes32 private constant _SHIM_INITHASH_LONDON = 0x1774bbdc4a308eaf5967722c7a4708ea7a3097859cb8768a10611448c29981c3;
    bytes32 private constant _SHIM_RUNTIME_HASH_LONDON =
        0x4181fd95643bb6bf1be20faa449de3be679a53ec38d829a0a789397a5d5d4887;

    function _createFromCalldata(
        bytes32 salt,
        bytes calldata initCode,
        uint256 value,
        uint256 shim0,
        uint48 shim1,
        bytes32 shimRuntimeHash
    ) private returns (address deployed) {
        address shim;
        assembly ("memory-safe") {
            mstore(_SHIM1_LENGTH, shim1)
            mstore(0x00, shim0)
            shim := create2(0x00, 0x00, _SHIM_LENGTH, salt)
            if iszero(shim) { revert(0x00, 0x00) }
            if iszero(eq(extcodehash(shim), shimRuntimeHash)) { revert(0x00, 0x00) }
            let ptr := mload(0x40)
            calldatacopy(ptr, initCode.offset, initCode.length)
            if iszero(call(gas(), shim, value, ptr, initCode.length, 0x00, 0x20)) { revert(0x00, 0x00) }
            deployed := mload(0x00)

            // This causes the shim to selfdestruct. On some chains, `SELFDESTRUCT` reverts,
            // consuming all available gas. We swallow this revert with `pop` and the 51k gas limit
            // gives a 10x multiplier over the expected gas consumption of this call without being
            // *too* wasteful when `SELFDESTRUCT` is unimplemented.
            pop(call(51220, shim, 0x00, 0x00, 0x00, 0x00, 0x00))
        }
    }

    function createFromCalldata(bytes32 salt, bytes calldata initCode, uint256 value) internal returns (address) {
        return _createFromCalldata(salt, initCode, value, _SHIM0, _SHIM1, _SHIM_RUNTIME_HASH);
    }

    function createFromCalldataLondon(bytes32 salt, bytes calldata initCode, uint256 value)
        internal
        returns (address)
    {
        return _createFromCalldata(salt, initCode, value, _SHIM0_LONDON, _SHIM1_LONDON, _SHIM_RUNTIME_HASH_LONDON);
    }

    function createFromCalldata(bytes32 salt, bytes calldata initCode) internal returns (address) {
        return createFromCalldata(salt, initCode, 0);
    }

    function createFromCalldataLondon(bytes32 salt, bytes calldata initCode) internal returns (address) {
        return createFromCalldataLondon(salt, initCode, 0);
    }

    function _createFromMemory(
        bytes32 salt,
        bytes memory initCode,
        uint256 value,
        uint256 shim0,
        uint48 shim1,
        bytes32 shimRuntimeHash
    ) private returns (address deployed) {
        address shim;
        assembly ("memory-safe") {
            mstore(_SHIM1_LENGTH, shim1)
            mstore(0x00, shim0)
            shim := create2(0x00, 0x00, _SHIM_LENGTH, salt)
            if iszero(shim) { revert(0x00, 0x00) }
            if iszero(eq(extcodehash(shim), shimRuntimeHash)) { revert(0x00, 0x00) }
            if iszero(call(gas(), shim, value, add(0x20, initCode), mload(initCode), 0x00, 0x20)) { revert(0x00, 0x00) }
            deployed := mload(0x00)

            // This causes the shim to selfdestruct. On some chains, `SELFDESTRUCT` reverts,
            // consuming all available gas. We swallow this revert with `pop` and the 51k gas limit
            // gives a 10x multiplier over the expected gas consumption of this call without being
            // *too* wasteful when `SELFDESTRUCT` is unimplemented.
            pop(call(51220, shim, 0x00, 0x00, 0x00, 0x00, 0x00))
        }
    }

    function createFromMemory(bytes32 salt, bytes memory initCode, uint256 value) internal returns (address) {
        return _createFromMemory(salt, initCode, value, _SHIM0, _SHIM1, _SHIM_RUNTIME_HASH);
    }

    function createFromMemoryLondon(bytes32 salt, bytes memory initCode, uint256 value) internal returns (address) {
        return _createFromMemory(salt, initCode, value, _SHIM0_LONDON, _SHIM1_LONDON, _SHIM_RUNTIME_HASH_LONDON);
    }

    function createFromMemory(bytes32 salt, bytes memory initCode) internal returns (address) {
        return createFromMemory(salt, initCode, 0);
    }

    function createFromMemoryLondon(bytes32 salt, bytes memory initCode) internal returns (address) {
        return createFromMemoryLondon(salt, initCode, 0);
    }

    function _predict(bytes32 salt, address deployer, bytes32 initHash) private pure returns (address) {
        return
            AddressDerivation.deriveContract(AddressDerivation.deriveDeterministicContract(deployer, salt, initHash), 1);
    }

    function predict(bytes32 salt, address deployer) internal pure returns (address) {
        return _predict(salt, deployer, _SHIM_INITHASH);
    }

    function predictLondon(bytes32 salt, address deployer) internal pure returns (address) {
        return _predict(salt, deployer, _SHIM_INITHASH_LONDON);
    }

    function predict(bytes32 salt) internal view returns (address) {
        return predict(salt, address(this));
    }

    function predictLondon(bytes32 salt) internal view returns (address) {
        return predictLondon(salt, address(this));
    }
}
