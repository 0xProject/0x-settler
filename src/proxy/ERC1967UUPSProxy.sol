// SPDX-License-Identifier: CC0-1.0
pragma solidity ^0.8.21;

/*

        /// from https://eips.ethereum.org/EIPS/eip-1967
        /// bytes32 implSlot = bytes32(uint256(keccak256('eip1967.proxy.implementation')) - 1);
        /// implSlot == 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc;

        /// from runtime code below
        /// bytes9 runtime0 = 0x365f5f375f5f365f7f;
        /// bytes17 runtime1 = 0x545af43d5f5f3e6036573d5ffd5b3d5ff3;

        /// initcode
        PC | OP | Arg | Mnemonic    | [Stack]                                           | {Memory}
        ------------------------------------------------------------------------------------------
        // put ERC1967 slot on the bottom of the stack because it's needed 2 places
        00 | 7f | implSlot | PUSH32 | [implSlot]                                        | {}

        // load the implementation address next because it's needed 3 places
        21 | 60 | 14 | PUSH1        | [14 implSlot]                                     | {}
  /---< 23 | 60 | 70 | PUSH1        | [implPtr 14 implSlot]                             | {}
  |     25 | 60 | 0c | PUSH1        | [0c implPtr 14 implSlot]                          | {}
  |     27 | 39 |    | CODECOPY     | [implSlot]                                        | {impl}
  |     28 | 5f |    | PUSH0        | [0 implSlot]                                      | {impl}
  |     29 | 51 |    | MLOAD        | [impl implSlot]                                   | {impl}
  |
  |     // store impl to the ERC1967 slot
  |     2a | 80 |    | DUP1         | [impl impl implSlot]                              | {impl}
  |     2b | 82 |    | DUP3         | [implSlot impl impl implSlot]                     | {impl}
  |     2c | 55 |    | SSTORE       | [impl implSlot]                                   | {impl}
  |
  |     // prepare empty returndata area for initializer DELEGATECALL
  |     2d | 5f |    | PUSH0        | [0 impl implSlot]                                 | {impl}
  |     2e | 5f |    | PUSH0        | [0 0 impl implSlot]                               | {impl}
  |
  |     // copy initializer into memory; prepare calldata area for DELEGATECALL
/-+---< 2f | 60 | 84 | PUSH1        | [initStart 0 0 impl implSlot]                     | {impl}
| |     31 | 80 |    | DUP1         | [initStart initStart 0 0 impl implSlot]           | {impl}
| |     32 | 38 |    | CODESIZE     | [codeSize initStart initStart 0 0 impl implSlot]  | {impl}
| |     33 | 03 |    | SUB          | [initSize initStart 0 0 impl implSlot]            | {impl}
| |     34 | 80 |    | DUP1         | [initSize initSize initStart 0 0 impl implSlot]   | {impl}
| |     35 | 91 |    | SWAP2        | [initStart initSize initSize 0 0 impl implSlot]   | {impl}
| |     36 | 5f |    | PUSH0        | [0 initStart initSize initSize 0 0 impl implSlot] | {impl}
| |     37 | 39 |    | CODECOPY     | [initSize 0 0 impl implSlot]                      | {init}
| |     38 | 5f |    | PUSH0        | [0 initSize 0 0 impl implSlot]                    | {init}
| |
| |     // do the initializer DELEGATECALL
| |     39 | 84 |    | DUP5         | [impl 0 initSize 0 0 impl implSlot]               | {init}
| |     3a | 5a |    | GAS          | [gas impl 0 initSize 0 0 impl implSlot]           | {init}
| |     3b | f4 |    | DELEGATECALL | [noRevert impl implSlot]                          | {init}
| |
| |     // check for initializer revert and nonexistent implementation
| |     3c | 90 |    | SWAP1        | [impl noRevert implSlot]                          | {init}
| |     3d | 3b |    | EXTCODESIZE  | [implSize noRevert implSlot]                      | {init}
| |     3e | 15 |    | ISZERO       | [emptyImpl noRevert implSlot]                     | {init}
| |     3f | 18 |    | XOR          | [success implSlot]                                | {init}
| | /-< 40 | 60 | 46 | PUSH1        | [target success implSlot]                         | {init}
| | |   42 | 57 |    | JUMPI        | [implSlot]                                        | {init}
| | |
| | |   // initializer reverted or implementation doesn't exist; bubble up revert
| | |   43 | 5f |    | PUSH0        | [0 implSlot]                                      | {init}
| | |   44 | 5f |    | PUSH0        | [0 0 implSlot]                                    | {init}
| | |   45 | fd |    | REVERT       | X                                                 | X
| | |
| | |   // return the runtime
| | \-> 46 | 5b |    | JUMPDEST     | [implSlot]                                        | {init}
| |     47 | 70 | runtime1 | PUSH17 | [runtime1 implSlot]                               | {init}
| |     59 | 60 | 31 | PUSH1        | [31 runtime1 implSlot]                            | {init}
| |     5b | 52 |    | MSTORE       | [implSlot]                                        | {.. runtime1}
| |     5c | 68 | runtime0 | PUSH9  | [runtime0 implSlot]                               | {.. runtime1}
| |     66 | 5f |    | PUSH0        | [0 runtime0 implSlot]                             | {.. runtime1}
| |     67 | 52 |    | MSTORE       | [implSlot]                                        | {.. runtime0 .. runtime1}
| |     68 | 60 | 20 | PUSH1        | [20 implSlot]                                     | {.. runtime0 .. runtime1}
| |     6a | 52 |    | MSTORE       | []                                                | {.. runtime0 implSlot runtime1}
| | /-< 6b | 60 | 3a | PUSH1        | [runtimeSize]                                     | {.. runtime0 implSlot runtime1}
| | |   6d | 60 | 17 | PUSH1        | [17 runtimeSize]                                  | {.. runtime0 implSlot runtime1}
| | |   6f | f3 |    | RETURN       | X                                                 | X
| | |
| | |   // proxy constructor arguments; packed not abiencoded
| \-+-> 70 | <20 bytes of implementation address>
\---+-> 84 | <unlimited bytes of initializer calldata...>
    |
=== | ===
    |
    |   /// runtime code
    |   PC | OP | Arg | Mnemonic      | [Stack]                | {Memory}
    |   -----------------------------------------------------------------
    |   // copy calldata into memory
    |   00 | 36 |    | CALLDATASIZE   | [cds]                  | {}
    |   01 | 5f |    | PUSH0          | [0 cds]                | {}
    |   02 | 5f |    | PUSH0          | [0 0 cds]              | {}
    |   03 | 37 |    | CALLDATACOPY   | []                     | {calldata}
    |
    |   // prepare arguments for DELEGATECALL
    |   04 | 5f |    | PUSH0          | [0]                    | {calldata}
    |   05 | 5f |    | PUSH0          | [0 0]                  | {calldata}
    |   06 | 36 |    | CALLDATASIZE   | [cds 0 0]              | {calldata}
    |   07 | 5f |    | PUSH0          | [0 cds 0 0]            | {calldata}
    |
    |   // load the implementation from the ERC1967 slot
    |   08 | 7f | implSlot | PUSH32   | [implSlot 0 cds 0 0]   | {calldata} // filled in by initcode
    |   29 | 54 |    | SLOAD          | [impl 0 cds 0 0]       | {calldata}
    |
    |   // DELEGATECALL to the implementation
    |   2a | 5a |    | GAS            | [gas impl 0 cds 0 0]   | {calldata}
    |   2b | f4 |    | DELEGATECALL   | [success]              | {calldata}
    |
    |   // copy returndata into memory
    |   2c | 3d |    | RETURNDATASIZE | [rds success]          | {calldata}
    |   2d | 5f |    | PUSH0          | [0 rds success]        | {calldata}
    |   2e | 5f |    | PUSH0          | [0 0 rds success]      | {calldata}
    |   2f | 3e |    | RETURNDATACOPY | [success]              | {returnData}
    |
    |   // check if the call reverted, bubble up
  /-+-< 30 | 60 | 36 | PUSH1          | [returnTarget success] | {returnData}
  | |   32 | 57 |    | JUMPI          | []                     | {returnData}
  | |   33 | 3d |    | RETURNDATASIZE | [rds]                  | {returnData}
  | |   34 | 5f |    | PUSH0          | [0 rds]                | {returnData}
  | |   35 | fd |    | REVERT         | X                      | X
  \-+-> 36 | 5b |    | JUMPDEST       | []                     | {returnData}
    |   37 | 3d |    | RETURNDATASIZE | [rds]                  | {returnData}
    |   38 | 5f |    | PUSH0          | [0 rds]                | {returnData}
    |   39 | f3 |    | RETURN         | X                      | X
    \-> 3a

*/

import {AddressDerivation} from "../utils/AddressDerivation.sol";

library ERC1967UUPSProxy {
    error CreateFailed();
    error Create2Failed();
    error BalanceTooLow(uint256 needed, uint256 possessed);

    bytes private constant _INITCODE =
        hex"7f360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc_6014_6070_600c_39_5f_51_80_82_55_5f_5f_6084_80_38_03_80_91_5f_39_5f_84_5a_f4_90_3b_15_18_6046_57_5f_5f_fd_5b_70545af43d5f5f3e6036573d5ffd5b3d5ff3_6031_52_68365f5f375f5f365f7f_5f_52_6020_52_603a_6017_f3"; // forgefmt: disable-line

    function _packArgs(address payable implementation, bytes memory initializer) private pure returns (bytes memory) {
        return abi.encodePacked(_INITCODE, implementation, initializer);
    }

    function create(address implementation, bytes memory initializer) internal returns (address) {
        return create(payable(implementation), initializer, 0);
    }

    function create(address payable implementation, bytes memory initializer, uint256 value)
        internal
        returns (address result)
    {
        if (address(this).balance < value) {
            revert BalanceTooLow(value, address(this).balance);
        }
        bytes memory initcode = _packArgs(implementation, initializer);
        assembly ("memory-safe") {
            result := create(value, add(0x20, initcode), mload(initcode))
        }
        if (result == address(0)) {
            revert CreateFailed();
        }
    }

    function createDeterministic(address implementation, bytes memory initializer, bytes32 salt)
        internal
        returns (address)
    {
        return createDeterministic(payable(implementation), initializer, salt, 0);
    }

    function createDeterministic(address payable implementation, bytes memory initializer, bytes32 salt, uint256 value)
        internal
        returns (address result)
    {
        if (address(this).balance < value) {
            revert BalanceTooLow(value, address(this).balance);
        }
        bytes memory initcode = _packArgs(implementation, initializer);
        assembly ("memory-safe") {
            result := create2(value, add(0x20, initcode), mload(initcode), salt)
        }
        if (result == address(0)) {
            revert Create2Failed();
        }
    }

    function predict(address implementation, bytes memory initializer, bytes32 salt, address deployer)
        internal
        pure
        returns (address)
    {
        return AddressDerivation.deriveDeterministicContract(
            deployer, salt, keccak256(_packArgs(payable(implementation), initializer))
        );
    }

    function predict(address implementation, bytes memory initializer, bytes32 salt) internal view returns (address) {
        return predict(implementation, initializer, salt, address(this));
    }
}
