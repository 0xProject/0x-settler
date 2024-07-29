// SPDX-License-Identifier: CC0-1.0
pragma solidity ^0.8.25;

/*

        /// from https://eips.ethereum.org/EIPS/eip-1967
        /// bytes32 implSlot = bytes32(uint256(keccak256('eip1967.proxy.implementation')) - 1);
        /// implSlot == 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc;
        /// bytes32 rollSlot = bytes32(uint256(keccak256('eip1967.proxy.rollback')) - 1);
        /// rollSlot == 0x4910fdfa16fed3260ed0e7147f7cc6da11a60208b5b9406d12a635614ffd9143;

        /// from runtime code below
        /// bytes9 runtime0 = 0x365f5f375f5f365f7f;
        /// bytes17 runtime1 = 0x545af43d5f5f3e6036573d5ffd5b3d5ff3;

        /// initcode
        PC | OP | Arg | Mnemonic    | [Stack]                                                | {Memory}
        -----------------------------------------------------------------------------------------------
        // put ERC1967 slot on the bottom of the stack because it's needed 2 places
        00 | 7f | implSlot | PUSH32 | [implSlot]                                             | {}

        // load the implementation address next because it's needed 3 places
        21 | 60 | 14 | PUSH1        | [14 implSlot]                                          | {}
  /---< 23 | 60 | b9 | PUSH1        | [implPtr 14 implSlot]                                  | {}
  |     25 | 60 | 0c | PUSH1        | [0c implPtr 14 implSlot]                               | {}
  |     27 | 39 |    | CODECOPY     | [implSlot]                                             | {impl}
  |     28 | 5f |    | PUSH0        | [0 implSlot]                                           | {impl}
  |     29 | 51 |    | MLOAD        | [impl implSlot]                                        | {impl}
  |
  |     // store impl to the ERC1967 slot
  |     2a | 80 |    | DUP1         | [impl impl implSlot]                                   | {impl}
  |     2b | 82 |    | DUP3         | [implSlot impl impl implSlot]                          | {impl}
  |     2c | 55 |    | SSTORE       | [impl implSlot]                                        | {impl}
  |     2d | 80 |    | DUP1         | [impl impl implSlot]                                   | {impl}
  |
  |     // prepare empty returndata area for initializer DELEGATECALL
  |     2e | 5f |    | PUSH0        | [0 impl impl implSlot]                                 | {impl}
  |     2f | 5f |    | PUSH0        | [0 0 impl impl implSlot]                               | {impl}
  |
  |     // copy initializer into memory; prepare calldata area for DELEGATECALL
/-+---< 30 | 60 | cd | PUSH1        | [initStart 0 0 impl impl implSlot]                     | {impl}
| |     32 | 80 |    | DUP1         | [initStart initStart 0 0 impl impl implSlot]           | {impl}
| |     33 | 38 |    | CODESIZE     | [codeSize initStart initStart 0 0 impl impl implSlot]  | {impl}
| |     34 | 03 |    | SUB          | [initSize initStart 0 0 impl impl implSlot]            | {impl}
| |     35 | 80 |    | DUP1         | [initSize initSize initStart 0 0 impl impl implSlot]   | {impl}
| |     36 | 91 |    | SWAP2        | [initStart initSize initSize 0 0 impl impl implSlot]   | {impl}
| |     37 | 5f |    | PUSH0        | [0 initStart initSize initSize 0 0 impl impl implSlot] | {impl}
| |     38 | 39 |    | CODECOPY     | [initSize 0 0 impl impl implSlot]                      | {init}
| |     39 | 5f |    | PUSH0        | [0 initSize 0 0 impl impl implSlot]                    | {init}
| |
| |     // do the initializer DELEGATECALL
| |     3a | 84 |    | DUP5         | [impl 0 initSize 0 0 impl impl implSlot]               | {init}
| |     3b | 5a |    | GAS          | [gas impl 0 initSize 0 0 impl impl implSlot]           | {init}
| |     3c | f4 |    | DELEGATECALL | [noRevert impl impl implSlot]                          | {init}
| |
| |     // check for initializer revert and nonexistent implementation
| |     3d | 90 |    | SWAP1        | [impl noRevert impl implSlot]                          | {init}
| |     3e | 3b |    | EXTCODESIZE  | [implSize noRevert impl implSlot]                      | {init}
| |     3f | 15 |    | ISZERO       | [emptyImpl noRevert impl implSlot]                     | {init}
| |     40 | 18 |    | XOR          | [success impl implSlot]                                | {init}
| | /-< 41 | 60 | 47 | PUSH1        | [target success impl implSlot]                         | {init}
| | |   43 | 57 |    | JUMPI        | [impl implSlot]                                        | {init}
| | |
| | |   // initializer reverted or implementation doesn't exist; bubble up revert
| | |   44 | 5f |    | PUSH0        | [0 impl implSlot]                                      | {init}
| | |   45 | 5f |    | PUSH0        | [0 0 impl implSlot]                                    | {init}
| | |   46 | fd |    | REVERT       | X                                                      | X
| | |
| | |   // set rollback slot (version) to 1
| | \-> 47 | 5b |    | JUMPDEST     | [implSlot]                                             | {init}
| |     48 | 60 | 01 | PUSH1        | [1 impl impl implSlot]                                 | {impl}
| |     4a | 7f | rollSlot | PUSH32 | [rollSlot 1 impl impl implSlot]                        | {impl}
| |     6b | 55 |    | SSTORE       | [impl impl implSlot]                                   | {impl}
| |
| |     // `emit Upgraded(impl);`
| |     6c | 7f | event | PUSH32    | [upgradeTopic impl implSlot]                           | {init}
| |     8d | 5f |    | PUSH0        | [0 upgradeTopic impl implSlot]                         | {init}
| |     8e | 5f |    | PUSH0        | [0 0 upgradeTopic impl implSlot]                       | {init}
| |     8f | a2 |    | LOG2         | [implSlot]                                             | {init}
| |
| |     // return the runtime
| |     90 | 70 | runtime1 | PUSH17 | [runtime1 implSlot]                                    | {init}
| |     a2 | 60 | 31 | PUSH1        | [31 runtime1 implSlot]                                 | {init}
| |     a4 | 52 |    | MSTORE       | [implSlot]                                             | {.. runtime1}
| |     a5 | 68 | runtime0 | PUSH9  | [runtime0 implSlot]                                    | {.. runtime1}
| |     af | 5f |    | PUSH0        | [0 runtime0 implSlot]                                  | {.. runtime1}
| |     b0 | 52 |    | MSTORE       | [implSlot]                                             | {.. runtime0 .. runtime1}
| |     b1 | 60 | 20 | PUSH1        | [20 implSlot]                                          | {.. runtime0 .. runtime1}
| |     b3 | 52 |    | MSTORE       | []                                                     | {.. runtime0 implSlot runtime1}
| | /-< b4 | 60 | 3a | PUSH1        | [runtimeSize]                                          | {.. runtime0 implSlot runtime1}
| | |   b6 | 60 | 17 | PUSH1        | [17 runtimeSize]                                       | {.. runtime0 implSlot runtime1}
| | |   b8 | f3 |    | RETURN       | X                                                      | X
| | |
| | |   // proxy constructor arguments; packed not abiencoded
| \-+-> b9 | <20 bytes of implementation address>
\---+-> cd | <unlimited bytes of initializer calldata...>
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

========================================================================================================================

        /// London hardfork version (no PUSH0)

        /// from runtime code below
        /// bytes11 runtime0 = 0x363d3d373d3d3d3d363d7f;
        /// bytes14 runtime1 = 0x545af43d3d93803e603757fd5bf3;

        /// initcode
        PC | OP | Arg | Mnemonic    | [Stack]                                                | {Memory}
        -----------------------------------------------------------------------------------------------
        // put ERC1967 slot on the bottom of the stack because it's needed 2 places
        00 | 7f | implSlot | PUSH32 | [implSlot]                                             | {}

        // load the implementation address next because it's needed 3 places
        21 | 60 | 14 | PUSH1        | [14 implSlot]                                          | {}
  /---< 23 | 60 | b8 | PUSH1        | [implPtr 14 implSlot]                                  | {}
  |     25 | 60 | 0c | PUSH1        | [0c implPtr 14 implSlot]                               | {}
  |     27 | 39 |    | CODECOPY     | [implSlot]                                             | {impl}
  |     28 | 36 |    | CALLDATASIZE | [0 implSlot]                                           | {impl}
  |     29 | 51 |    | MLOAD        | [impl implSlot]                                        | {impl}
  |
  |     // store impl to the ERC1967 slot
  |     2a | 80 |    | DUP1         | [impl impl implSlot]                                   | {impl}
  |     2b | 82 |    | DUP3         | [implSlot impl impl implSlot]                          | {impl}
  |     2c | 55 |    | SSTORE       | [impl implSlot]                                        | {impl}
  |     2d | 80 |    | DUP1         | [impl impl implSlot]                                   | {impl}
  |
  |     // prepare empty returndata area for initializer DELEGATECALL
  |     2e | 36 |    | CALLDATASIZE | [0 impl impl implSlot]                                 | {impl}
  |     2f | 36 |    | CALLDATASIZE | [0 0 impl impl implSlot]                               | {impl}
  |
  |     // copy initializer into memory; prepare calldata area for DELEGATECALL
/-+---< 30 | 60 | cc | PUSH1        | [initStart 0 0 impl impl implSlot]                     | {impl}
| |     32 | 80 |    | DUP1         | [initStart initStart 0 0 impl impl implSlot]           | {impl}
| |     33 | 38 |    | CODESIZE     | [codeSize initStart initStart 0 0 impl impl implSlot]  | {impl}
| |     34 | 03 |    | SUB          | [initSize initStart 0 0 impl impl implSlot]            | {impl}
| |     35 | 80 |    | DUP1         | [initSize initSize initStart 0 0 impl impl implSlot]   | {impl}
| |     36 | 91 |    | SWAP2        | [initStart initSize initSize 0 0 impl impl implSlot]   | {impl}
| |     37 | 36 |    | CALLDATASIZE | [0 initStart initSize initSize 0 0 impl impl implSlot] | {impl}
| |     38 | 39 |    | CODECOPY     | [initSize 0 0 impl impl implSlot]                      | {init}
| |     39 | 36 |    | CALLDATASIZE | [0 initSize 0 0 impl impl implSlot]                    | {init}
| |
| |     // do the initializer DELEGATECALL
| |     3a | 84 |    | DUP5         | [impl 0 initSize 0 0 impl impl implSlot]               | {init}
| |     3b | 5a |    | GAS          | [gas impl 0 initSize 0 0 impl impl implSlot]           | {init}
| |     3c | f4 |    | DELEGATECALL | [noRevert impl impl implSlot]                          | {init}
| |
| |     // check for initializer revert and nonexistent implementation
| |     3d | 90 |    | SWAP1        | [impl noRevert impl implSlot]                          | {init}
| |     3e | 3b |    | EXTCODESIZE  | [implSize noRevert impl implSlot]                      | {init}
| |     3f | 15 |    | ISZERO       | [emptyImpl noRevert impl implSlot]                     | {init}
| |     40 | 18 |    | XOR          | [success impl implSlot]                                | {init}
| | /-< 41 | 60 | 47 | PUSH1        | [target success impl implSlot]                         | {init}
| | |   43 | 57 |    | JUMPI        | [impl implSlot]                                        | {init}
| | |
| | |   // initializer reverted or implementation doesn't exist; bubble up revert
| | |   44 | 36 |    | CALLDATASIZE | [0 impl implSlot]                                      | {init}
| | |   45 | 36 |    | CALLDATASIZE | [0 0 impl implSlot]                                    | {init}
| | |   46 | fd |    | REVERT       | X                                                      | X
| | |
| | |   // set rollback slot (version) to 1
| | \-> 47 | 5b |    | JUMPDEST     | [implSlot]                                             | {init}
| |     48 | 60 | 01 | PUSH1        | [1 impl impl implSlot]                                 | {impl}
| |     4a | 7f | rollSlot | PUSH32 | [rollSlot 1 impl impl implSlot]                        | {impl}
| |     6b | 55 |    | SSTORE       | [impl impl implSlot]                                   | {impl}
| |
| |     // `emit Upgraded(impl);`
| |     6c | 7f | event | PUSH32    | [upgradeTopic impl implSlot]                           | {init}
| |     8d | 36 |    | CALLDATASIZE | [0 upgradeTopic impl implSlot]                         | {init}
| |     8e | 36 |    | CALLDATASIZE | [0 0 upgradeTopic impl implSlot]                       | {init}
| |     8f | a2 |    | LOG2         | [implSlot]                                             | {init}
| |
| |     // return the runtime
| |     90 | 6d | runtime1 | PUSH14 | [runtime1 implSlot]                                    | {init}
| |     9f | 60 | 2e | PUSH1        | [2e runtime1 implSlot]                                 | {init}
| |     a0 | 52 |    | MSTORE       | [implSlot]                                             | {.. runtime1}
| |     a1 | 6a | runtime0 | PUSH11 | [runtime0 implSlot]                                    | {.. runtime1}
| |     ad | 36 |    | CALLDATASIZE | [0 runtime0 implSlot]                                  | {.. runtime1}
| |     af | 52 |    | MSTORE       | [implSlot]                                             | {.. runtime0 .. runtime1}
| |     b0 | 60 | 20 | PUSH1        | [20 implSlot]                                          | {.. runtime0 .. runtime1}
| |     b2 | 52 |    | MSTORE       | []                                                     | {.. runtime0 implSlot runtime1}
| | /-< b3 | 60 | 39 | PUSH1        | [runtimeSize]                                          | {.. runtime0 implSlot runtime1}
| | |   b5 | 60 | 15 | PUSH1        | [15 runtimeSize]                                       | {.. runtime0 implSlot runtime1}
| | |   b7 | f3 |    | RETURN       | X                                                      | X
| | |
| | |   // proxy constructor arguments; packed not abiencoded
| \-+-> b8 | <20 bytes of implementation address>
\---+-> cd | <unlimited bytes of initializer calldata...>
    |
=== | ===
    |
    |   /// runtime code
    |   PC | OP | Arg | Mnemonic      | [Stack]                      | {Memory}
    |   -----------------------------------------------------------------------
    |   // copy calldata into memory
    |   00 | 36 |    | CALLDATASIZE   | [cds]                        | {}
    |   01 | 3d |    | RETURNDATASIZE | [0 cds]                      | {}
    |   02 | 3d |    | RETURNDATASIZE | [0 0 cds]                    | {}
    |   03 | 37 |    | CALLDATACOPY   | []                           | {calldata}
    |
    |   // we need these zeroes for later when `RETURNDATASIZE` is no longer zero
    |   04 | 3d |    | RETURNDATASIZE | [0]                          | {calldata}
    |   05 | 3d |    | RETURNDATASIZE | [0 0]                        | {calldata}
    |
    |   // prepare arguments for DELEGATECALL
    |   06 | 3d |    | RETURNDATASIZE | [0 0 0]                      | {calldata}
    |   07 | 3d |    | RETURNDATASIZE | [0 0 0 0]                    | {calldata}
    |   08 | 36 |    | CALLDATASIZE   | [cds 0 0 0 0]                | {calldata}
    |   09 | 3d |    | RETURNDATASIZE | [0 cds 0 0 0 0]              | {calldata}
    |
    |   // load the implementation from the ERC1967 slot
    |   0a | 7f | implSlot | PUSH32   | [implSlot 0 cds 0 0 0 0]     | {calldata} // filled in by initcode
    |   2b | 54 |    | SLOAD          | [impl 0 cds 0 0 0 0]         | {calldata}
    |
    |   // DELEGATECALL to the implementation
    |   2c | 5a |    | GAS            | [gas impl 0 cds 0 0 0 0]     | {calldata}
    |   2d | f4 |    | DELEGATECALL   | [success 0 0]                | {calldata}
    |
    |   // copy returndata into memory
    |   2e | 3d |    | RETURNDATASIZE | [rds success 0 0]            | {calldata}
    |   2f   3d |    | RETURNDATASIZE | [rds rds success 0 0]        | {calldata}
    |   30   93 |    | SWAP4          | [0 rds success 0 rds]        | {calldata}
    |   31   80 |    | DUP1           | [0 0 rds success 0 rds]      | {calldata}
    |   32   3e |    | RETURNDATACOPY | [success 0 rds]              | {returndata}
    |
    |   // check if the call reverted, bubble up
  /-+-< 33 | 60 | 37 | PUSH1          | [returnTarget success 0 rds] | {returnData}
  | |   35 | 57 |    | JUMPI          | [0 rds]                      | {returnData}
  | |   36 | fd |    | REVERT         | X                            | X
  \-+-> 37 | 5b |    | JUMPDEST       | [0 rds]                      | {returnData}
    |   38 | f3 |    | RETURN         | X                            | X
    \-> 39

*/

import {AddressDerivation} from "../utils/AddressDerivation.sol";

library ERC1967UUPSProxy {
    error CreateFailed();
    error Create2Failed();
    error BalanceTooLow(uint256 needed, uint256 possessed);

    bytes private constant _INITCODE =
        hex"7f360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc_6014_60b9_600c_39_5f_51_80_82_55_80_5f_5f_60cd_80_38_03_80_91_5f_39_5f_84_5a_f4_90_3b_15_18_6047_57_5f_5f_fd_5b_6001_7f4910fdfa16fed3260ed0e7147f7cc6da11a60208b5b9406d12a635614ffd9143_55_7fbc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b_5f_5f_a2_70545af43d5f5f3e6036573d5ffd5b3d5ff3_6031_52_68365f5f375f5f365f7f_5f_52_6020_52_603a_6017_f3"; // forgefmt: disable-line
    bytes32 private constant _RUNTIME_HASH = 0x66139d772b392067ed16463c9a9f0c57c9332f9efaa80c6732917a66143942da;
    bytes private constant _INITCODE_LONDON =
        hex"7f360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc_6014_60b8_600c_39_36_51_80_82_55_80_36_36_60cc_80_38_03_80_91_36_39_36_84_5a_f4_90_3b_15_18_6047_57_36_36_fd_5b_6001_7f4910fdfa16fed3260ed0e7147f7cc6da11a60208b5b9406d12a635614ffd9143_55_7fbc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b_36_36_a2_6d545af43d3d93803e603757fd5bf3_602e_52_6a363d3d373d3d3d3d363d7f_36_52_6020_52_6039_6015_f3"; // forgefmt: disable-line
    bytes32 private constant _RUNTIME_HASH_LONDON = 0xb75f746f4a7c8fda9fc450aebc30eeb95644c86bc62f492cd3fb54d83d560805;

    function _packArgs(address payable implementation, bytes memory initializer) private pure returns (bytes memory) {
        return abi.encodePacked(_INITCODE, implementation, initializer);
    }

    function _packArgsLondon(address payable implementation, bytes memory initializer)
        private
        pure
        returns (bytes memory)
    {
        return abi.encodePacked(_INITCODE_LONDON, implementation, initializer);
    }

    function create(address implementation, bytes memory initializer) internal returns (address) {
        return create(payable(implementation), initializer, 0);
    }

    function createLondon(address implementation, bytes memory initializer) internal returns (address) {
        return createLondon(payable(implementation), initializer, 0);
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
        if (result.codehash != _RUNTIME_HASH) {
            revert CreateFailed();
        }
    }

    function createLondon(address payable implementation, bytes memory initializer, uint256 value)
        internal
        returns (address result)
    {
        if (address(this).balance < value) {
            revert BalanceTooLow(value, address(this).balance);
        }
        bytes memory initcode = _packArgsLondon(implementation, initializer);
        assembly ("memory-safe") {
            result := create(value, add(0x20, initcode), mload(initcode))
        }
        if (result == address(0)) {
            revert CreateFailed();
        }
        if (result.codehash != _RUNTIME_HASH_LONDON) {
            revert CreateFailed();
        }
    }

    function createDeterministic(address implementation, bytes memory initializer, bytes32 salt)
        internal
        returns (address)
    {
        return createDeterministic(payable(implementation), initializer, salt, 0);
    }

    function createDeterministicLondon(address implementation, bytes memory initializer, bytes32 salt)
        internal
        returns (address)
    {
        return createDeterministicLondon(payable(implementation), initializer, salt, 0);
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
        if (result.codehash != _RUNTIME_HASH) {
            revert Create2Failed();
        }
    }

    function createDeterministicLondon(
        address payable implementation,
        bytes memory initializer,
        bytes32 salt,
        uint256 value
    ) internal returns (address result) {
        if (address(this).balance < value) {
            revert BalanceTooLow(value, address(this).balance);
        }
        bytes memory initcode = _packArgsLondon(implementation, initializer);
        assembly ("memory-safe") {
            result := create2(value, add(0x20, initcode), mload(initcode), salt)
        }
        if (result == address(0)) {
            revert Create2Failed();
        }
        if (result.codehash != _RUNTIME_HASH_LONDON) {
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

    function predictLondon(address implementation, bytes memory initializer, bytes32 salt, address deployer)
        internal
        pure
        returns (address)
    {
        return AddressDerivation.deriveDeterministicContract(
            deployer, salt, keccak256(_packArgsLondon(payable(implementation), initializer))
        );
    }

    function predict(address implementation, bytes memory initializer, bytes32 salt) internal view returns (address) {
        return predict(implementation, initializer, salt, address(this));
    }

    function predictLondon(address implementation, bytes memory initializer, bytes32 salt)
        internal
        view
        returns (address)
    {
        return predictLondon(implementation, initializer, salt, address(this));
    }
}
