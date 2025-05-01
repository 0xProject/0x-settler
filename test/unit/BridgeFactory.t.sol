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

    function _deployProxy(bytes32 action, uint256 privateKey) internal returns (BridgeFactory proxy) {
        address owner = vm.addr(privateKey);

        proxy = BridgeFactory(factory.deploy(action, owner, true));
        vm.label(address(proxy), "Proxy");
    }

    function _deployProxy(bytes32 action) internal returns (BridgeFactory proxy) {
        return _deployProxy(action, uint256(keccak256(abi.encode("owner"))));
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

        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        proxy.isValidSignature(action1, abi.encode(proof));

        proof[0] = action2;
        assertEq(proxy.isValidSignature(action1, abi.encode(proof)), bytes4(0x1626ba7e));
    }

    function testPendingOwner() public {
        (address owner, uint256 privateKey) = makeAddrAndKey("owner");
        BridgeFactory proxy = _deployProxy(keccak256(abi.encode("action")), privateKey);

        vm.prank(owner);
        proxy.acceptOwnership();
    }
}
