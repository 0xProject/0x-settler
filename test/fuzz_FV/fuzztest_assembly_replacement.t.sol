// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {CheckCall} from "src/utils/CheckCall.sol";

contract AssemblyReplacementHarness {
    /// @notice Function that returns both the assambly and the solidity results of the _msgSender function
    function msgSenderCheck(bytes calldata /*data*/) external pure returns (address senderASM, address senderSOL) {
        //original assembly implementation
        assembly ("memory-safe") {
            senderASM := shr(0x60, calldataload(sub(calldatasize(), 0x14)))
        }
        //solidity replacement
        senderSOL = address(bytes20(msg.data[msg.data.length - 20:]));
    }

    /// @notice Original assembly implementation of CheckCall.checkCall.
    ///         Kept here so we can compare against checkCallSolidity.
    function checkCallAsm(address target, bytes memory data, uint256 minReturnBytes)
        external
        view
        returns (bool success)
    {
        assembly ("memory-safe") {
            let beforeGas
            {
                let offset := add(data, 0x20)
                let length := mload(data)
                beforeGas := gas()
                success := staticcall(gas(), target, offset, length, 0x00, 0x00)
            }
            let afterGas := gas()

            for {} 1 {} {
                if iszero(returndatasize()) {
                    switch success
                    case 0 {
                        let remainingGas := shr(6, beforeGas)
                        remainingGas := add(remainingGas, shr(6, sub(beforeGas, remainingGas)))
                        if iszero(lt(remainingGas, afterGas)) { invalid() }
                    }
                    default {
                        if iszero(extcodesize(target)) { revert(0x00, 0x00) }
                        success := iszero(minReturnBytes)
                    }
                    break
                }
                success := gt(success, lt(returndatasize(), minReturnBytes))
                break
            }
        }
    }

    /// @notice Solidity replacement implementation.
    function checkCallSol(address target, bytes memory data, uint256 minReturnBytes)
        external
        view
        returns (bool)
    {
        return CheckCall.checkCallSolidity(target, data, minReturnBytes);
    }
}

/// @notice Fuzz harness that proves the Solidity replacement of the assembly
///         is observationally equivalent to the original assembly code 
contract MsgSenderReplacementFuzzTest is Test {
    AssemblyReplacementHarness internal harness;


    function setUp() public {
        harness = new AssemblyReplacementHarness();
    }


    function testFuzz_MsgSender_Replacement_Correctness(bytes calldata data) public view {
        (address senderASM, address senderSOL) = harness.msgSenderCheck(data);

        assertEq(senderASM, senderSOL, "asm/sol disagreement on production-shaped calldata");
    }


}

/// @notice Fuzz harness that proves the Solidity replacement of the assembly
///         in CheckCall.checkCall is observationally equivalent to the original
///         assembly across the target-behavior branches the function distinguishes:
///         returns-data / returns-empty / reverts-with-data / reverts-empty / EOA.
///
///         Behavioral note: the original assembly distinguishes a true OOG from a
///         normal revert by consuming all remaining gas via `invalid()`. The
///         Solidity replacement intentionally drops this (gas cannot be modeled by
///         certora). All other branches are required to match, including reverts.
contract CheckCallReplacementFuzzTest is Test {
    AssemblyReplacementHarness internal harness;

    // Etched targets exercising every branch of checkCall.
    // PUSH0 PUSH0 RETURN -> return 0 bytes of data, contract exists.
    address constant T_RETURN_EMPTY = address(uint160(uint256(keccak256("T_RETURN_EMPTY"))));
    // PUSH1 0x20 PUSH1 0x00 MSTORE PUSH1 0x20 PUSH1 0x00 RETURN -> return 32 bytes.
    address constant T_RETURN_32 = address(uint160(uint256(keccak256("T_RETURN_32"))));
    // PUSH0 PUSH0 REVERT -> revert with no data.
    address constant T_REVERT_EMPTY = address(uint160(uint256(keccak256("T_REVERT_EMPTY"))));
    // PUSH1 0xff PUSH1 0x00 MSTORE PUSH1 0x20 PUSH1 0x00 REVERT -> revert with 32 bytes.
    address constant T_REVERT_32 = address(uint160(uint256(keccak256("T_REVERT_32"))));
    // No code etched at this address -- behaves as an EOA.
    address constant T_EOA = address(uint160(uint256(keccak256("T_EOA"))));

    function setUp() public {
        harness = new AssemblyReplacementHarness();
        vm.etch(T_RETURN_EMPTY, hex"5f5ff3");
        vm.etch(T_RETURN_32, hex"602060005260206000f3");
        vm.etch(T_REVERT_EMPTY, hex"5f5ffd");
        vm.etch(T_REVERT_32, hex"60ff60005260206000fd");
    }

    /// @notice Compare ASM and SOL implementations for the same (target, data,
    ///         minReturnBytes), including revert equivalence.
    function _assertEquivalent(address target, bytes memory data, uint256 minReturnBytes) internal view {
        bool asmReverted;
        bool asmResult;
        try harness.checkCallAsm(target, data, minReturnBytes) returns (bool r) {
            asmResult = r;
        } catch {
            asmReverted = true;
        }

        bool solReverted;
        bool solResult;
        try harness.checkCallSol(target, data, minReturnBytes) returns (bool r) {
            solResult = r;
        } catch {
            solReverted = true;
        }

        assertEq(asmReverted, solReverted, "asm/sol disagreement on revert behavior");
        if (!asmReverted) {
            assertEq(asmResult, solResult, "asm/sol disagreement on return value");
        }
    }

    function testFuzz_CheckCall_TargetReturnsEmpty(bytes calldata data, uint256 minReturnBytes) public view {
        _assertEquivalent(T_RETURN_EMPTY, data, minReturnBytes);
    }

    function testFuzz_CheckCall_TargetReturns32(bytes calldata data, uint256 minReturnBytes) public view {
        _assertEquivalent(T_RETURN_32, data, minReturnBytes);
    }

    function testFuzz_CheckCall_TargetRevertsEmpty(bytes calldata data, uint256 minReturnBytes) public view {
        _assertEquivalent(T_REVERT_EMPTY, data, minReturnBytes);
    }

    function testFuzz_CheckCall_TargetRevertsWithData(bytes calldata data, uint256 minReturnBytes) public view {
        _assertEquivalent(T_REVERT_32, data, minReturnBytes);
    }

    function testFuzz_CheckCall_TargetEOA(bytes calldata data, uint256 minReturnBytes) public view {
        _assertEquivalent(T_EOA, data, minReturnBytes);
    }
}
