// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {BridgeFactory} from "src/BridgeFactory.sol";

contract BridgeFactoryTest is Test {
    BridgeFactory factory = BridgeFactory(address(0xf4c70));

    function setUp() public {
        deployCodeTo("BridgeFactory.sol", address(factory));
        vm.label(address(factory), "BridgeFactory");
    }

    function _deployProxy(bytes32 action) internal returns (BridgeFactory proxy) {
        proxy = BridgeFactory(factory.deploy(action));
        vm.label(address(proxy), "Proxy");
    }

    function testSingleAction() public {
        bytes32 action = keccak256(abi.encode("action"));
        BridgeFactory proxy = _deployProxy(action);

        assertEq(proxy.isValidSignature(action, bytes("")), bytes4(0x1626ba7e));
    }

    function testMultipleActions() public {
        bytes32 action1 = keccak256(abi.encode("action1"));
        bytes32 action2 = keccak256(abi.encode("action2"));
        bytes32 root = keccak256(abi.encodePacked(action1, action2));

        bytes32[] memory proof = new bytes32[](1);
        proof[0] = action1;

        BridgeFactory proxy = _deployProxy(root);
        assertEq(proxy.isValidSignature(action2, abi.encode(proof)), bytes4(0x1626ba7e));
        assertEq(proxy.isValidSignature(action1, abi.encode(proof)), bytes4(0x00000000));
        proof[0] = action2;
        assertEq(proxy.isValidSignature(action1, abi.encode(proof)), bytes4(0x1626ba7e));
    }
}
