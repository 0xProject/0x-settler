// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.8.19;

// These contracts are the regression tests that ship with the upstream fix. In an affected compiler
// the optimizer forwards the value stored through the first reference instead of reloading after
// the base variable is reassigned inside a loop or branch.

contract StorageAlias {
    struct S {
        uint256 v;
    }

    S[20] public a;

    // g(0, 2, 0xaaaa, 0xbbbb) must return 0xbbbb (i == k after the second loop)
    function g(uint256 n1, uint256 n2, uint256 v, uint256 w) external returns (uint256) {
        uint256 i;
        for (uint256 j; j < n1; j++) {
            i++;
        }
        uint256 k = i + 2;
        a[k].v = v;
        for (uint256 j; j < n2; j++) {
            i++;
        }
        a[i].v = w;
        return a[k].v;
    }

    // rmw(0, 1) must leave a[1].v == 501 (i == k after the second loop)
    function rmw(uint256 n1, uint256 n2) external {
        uint256 i;
        for (uint256 j; j < n1; j++) {
            i++;
        }
        uint256 k = i + 1;
        a[k].v = 100;
        for (uint256 j; j < n2; j++) {
            i++;
        }
        a[i].v = 500;
        a[k].v += 1;
    }
}

contract MemoryAlias {
    function f(uint256, uint256) public returns (uint256 result) {
        assembly {
            let v := 0x400
            if calldataload(4) { v := 0 }
            let a := add(v, 0x100)
            mstore(a, 67)
            if calldataload(36) { v := 0x300 }
            let b := add(v, 0x200)
            mstore(b, 7)
            result := mload(a)
        }
    }
}
