// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {UniswapV4} from "src/core/UniswapV4.sol";
import {POOL_MANAGER, IUnlockCallback} from "src/core/UniswapV4Types.sol";
import {IPoolManager} from "uniswapv4/interfaces/IPoolManager.sol";

import {Test} from "forge-std/Test.sol";

import {console} from "forge-std/console.sol";

contract UniswapV4UnitTest is Test, IUnlockCallback {
    function unlockCallback(bytes calldata) external view override returns (bytes memory) {
        assert(msg.sender == address(POOL_MANAGER));
        return unicode"Hello, World!";
    }

    function _replaceAll(bytes memory haystack, bytes32 needle, bytes32 replace, bytes32 mask) internal view returns (uint256 count) {
        assembly ("memory-safe") {
            let padding
            for {
                let x := and(mask, sub(0x00, mask))
                let i := 0x07
            } gt(i, 0x02) {
                i := sub(i, 0x01)
            } {
                let s := shl(i, 0x01) // [128, 64, 32, 16, 8]
                if shr(s, shr(padding, x)) {
                    padding := add(s, padding)
                }
            }

            padding := add(0x01, shr(0x03, padding))
            needle := and(mask, needle)
            replace := and(mask, replace)

            for {
                let i := add(0x20, haystack)
                let end := add(padding, add(mload(haystack), haystack))
            } lt(i, end) {
                i := add(0x01, i)
            } {
                let word := mload(i)
                if eq(and(mask, word), needle) {
                    mstore(i, or(and(not(mask), word), replace))
                    count := add(0x01, count)
                }
            }
        }
    }

    function _deployPoolManager() internal {
        bytes memory poolManagerCode = vm.getCode("PoolManager.sol:PoolManager");
        address poolManagerSrc;
        assembly ("memory-safe") {
            poolManagerSrc := create(0x00, add(0x20, poolManagerCode), mload(poolManagerCode))
        }
        require(poolManagerSrc != address(0));
        poolManagerCode = poolManagerSrc.code;
        uint256 replaceCount = _replaceAll(poolManagerCode, bytes32(bytes20(uint160(poolManagerSrc))), bytes32(bytes20(uint160(address(POOL_MANAGER)))), bytes32(bytes20(type(uint160).max)));
        console.log("replaced", replaceCount, "occurrences of pool manager immutable address");
        vm.etch(address(POOL_MANAGER), poolManagerCode);

        vm.record();
        (bool success, bytes memory returndata) = address(POOL_MANAGER).staticcall(abi.encodeWithSignature("owner()"));
        assert(abi.decode(returndata, (address)) == address(0));
        (bytes32[] memory readSlots, ) = vm.accesses(address(POOL_MANAGER));
        assert(readSlots.length == 1);
        bytes32 ownerSlot = readSlots[0];
        assert(vm.load(address(POOL_MANAGER), ownerSlot) == bytes32(0));
        vm.store(address(POOL_MANAGER), ownerSlot, bytes32(uint256(uint160(address(this)))));
    }

    function setUp() public {
        _deployPoolManager();
    }

    function testNothing() public {
        assertEq(keccak256(POOL_MANAGER.unlock(new bytes(0))), 0xacaf3289d7b601cbd114fb36c4d29c85bbfd5e133f14cb355c3fd8d99367964f);
    }
}
