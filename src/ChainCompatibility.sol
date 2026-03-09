// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

contract ChainCompatibility {
    event GasUsed(uint256 stage, bool success, uint256 gasUsed);

    bytes32 internal constant eventTopic0 = 0x34066e423e4ecea978c55ccba9b1ee65e50ac229845e7a31dec6a737b038dd27;

    constructor() {
        assembly ("memory-safe") {
            let memptr := mload(0x40)
            let zero := calldatasize()
            let testGas := 100000

            function createShim(len, _zero) -> shim {
                shim := create(_zero, sub(0x20, len), len)
                if iszero(shim) {
                    mstore8(_zero, 0xfe)
                    return(_zero, 0x01)
                }
            }

            function runTest(shim, stage, _zero, _testGas) {
                let beforeGas := gas()
                let status := call(_testGas, shim, _zero, _zero, _zero, _zero, _zero)
                let afterGas := gas()
                mstore(_zero, stage)
                mstore(0x20, status)
                mstore(0x40, sub(beforeGas, afterGas))
                log1(_zero, 0x60, eventTopic0)
            }

            // test for SELFDESTRUCT
            // 30 ff => ADDRESS SELFDESTRUCT
            mstore(zero, 0x6130ff36526002601ef3)
            let shim := createShim(0x0a, zero)
            runTest(shim, 0x00, zero, testGas)

            // test for PUSH0
            // 5f 5f f3 => PUSH0 PUSH0 RETURN
            mstore(zero, 0x625f5ff336526003601df3)
            shim := createShim(0x0b, zero)
            runTest(shim, 0x01, zero, testGas)

            // test for TSTORE/TLOAD
            // 6001 80 5f 5d 5f 5c 5f 53 5f f3 => 0x01 DUP1 PUSH0 TSTORE PUSH0 TLOAD PUSH0 MSTORE8 PUSH0 RETURN
            mstore(zero, 0x6a6001805f5d5f5c5f535ff33652600b6015f3)
            shim := createShim(0x13, zero)
            runTest(shim, 0x02, zero, testGas)

            // test for MCOPY
            // 6001 5f 52 6020 80 80 5f 5e 80 f3 => 0x01 PUSH0 MSTORE 0x20 DUP1 DUP1 PUSH0 MCOPY DUP1 RETURN
            mstore(zero, 0x6b60015f52602080805f5e80f33652600c6014f3)
            shim := createShim(0x14, zero)
            runTest(shim, 0x03, zero, testGas)

            // test for CLZ
            // 3d 3d 6001 1e 60ff 14 600c 57 fd 5b f3 => RETURNDATASIZE RETURNDATASIZE 0x01 CLZ 0xff EQ 0x0c JUMPI REVERT JUMPDEST RETURN
            mstore(zero, 0x6d3d3d60011e60ff14600c57fd5bf33652600e6012f3)
            shim := createShim(0x16, zero)
            runTest(shim, 0x04, zero, testGas)

            mstore(0x40, memptr)
            mstore8(zero, zero)
            return(zero, 0x01)
        }
    }
}
