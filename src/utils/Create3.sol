// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {AddressDerivation} from "./AddressDerivation.sol";

/*
00 6028 push1 28
02 80 dup1
03 6009 push1 09
05 5f push0
06 39 codecopy
07 5f push0
08 f3 return
09

00 36 calldatasize
01 6006 push1 06
03 57 jumpi
04 32 origin
05 ff selfdestruct
06 5b jumpdest
07 5f push0
08 54 sload
09 6026 push1 26
0b 57 jumpi
0c 6001 push1 01
0e 5f push0
0f 55 sstore
10 36 calldatasize
11 5f push0
12 5f push0
13 37 calldatacopy
14 36 calldatasize
15 5f push0
16 34 callvalue
17 f0 create
18 80 dup1
19 601f push1 1f
1b 57 jumpi
1c 5f push0
1d 5f push0
1e fd revert
1f 5b jumpdest
20 5f push0
21 52 mstore
22 6020 push1 20
24 5f push0
25 f3 return
26 5b jumpdest
27 fe invalid
28
*/

library Create3 {
    function createFromCalldata(bytes32 salt, bytes calldata initCode, uint256 value)
        internal
        returns (address deployed)
    {
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
