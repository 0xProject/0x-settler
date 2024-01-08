// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {verifyIPFS} from "src/vendor/verifyIPFS.sol";

import "forge-std/Test.sol";

contract IPFSTest is Test {
    function testF() public {
        bytes32 hash = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
        bytes memory expected = "QmfZy5bvk7a3DQAjCbGNtmrPXWkyVvPrdnZMyBZ5q5ieKG";
        bytes memory actual = verifyIPFS.base58sha256multihash(hash);
        assertEq(keccak256(actual), keccak256(expected));
    }

    function testC() public {
        bytes32 hash = 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc;
        bytes memory expected = "Qmc871JZzbQq4r47Si29Fv1kAcJsmf3ccy4YyiahYXcesD";
        bytes memory actual = verifyIPFS.base58sha256multihash(hash);
        assertEq(keccak256(actual), keccak256(expected));
    }

    function testA() public {
        bytes32 hash = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa;
        bytes memory expected = "QmZprxSLAFJgy9K2wTBzAg7yvg1Ucp9TH64gKQbn2ADKuB";
        bytes memory actual = verifyIPFS.base58sha256multihash(hash);
        assertEq(keccak256(actual), keccak256(expected));
    }

    function test0() public {
        bytes32 hash = 0x00000000000000000000000000000000000000000000000000000000000000000;
        bytes memory expected = "QmNLei78zWmzUdbeRB3CiUfAizWUrbeeZh5K1rhAQKCh51";
        bytes memory actual = verifyIPFS.base58sha256multihash(hash);
        assertEq(keccak256(actual), keccak256(expected));
    }
}
