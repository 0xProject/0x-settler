// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.8.19;

import {StorageAlias, MemoryAlias} from "../src/Repro.sol";

// No forge-std dependency, so the project compiles with any solc binary under test.
contract ReproTest {
    function test_storage_g_aliasing() external {
        StorageAlias s = new StorageAlias();
        require(s.g(0, 2, 0xaaaa, 0xbbbb) == 0xbbbb, "g(0,2): stale load");
        require(s.g(0, 3, 0xaaaa, 0xbbbb) == 0xaaaa, "g(0,3): wrong value");
    }

    function test_storage_rmw_aliasing() external {
        StorageAlias s = new StorageAlias();
        s.rmw(0, 1);
        require(s.a(1) == 501, "rmw: stale read-modify-write");
    }

    function test_memory_aliasing() external {
        MemoryAlias m = new MemoryAlias();
        require(m.f(0, 0) == 67, "f(0,0): wrong value");
        require(m.f(0, 1) == 7, "f(0,1): stale load");
    }
}
