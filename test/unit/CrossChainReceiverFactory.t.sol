// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {MockERC20} from "@forge-std/mocks/MockERC20.sol";
import {CrossChainReceiverFactory} from "src/CrossChainReceiverFactory.sol";
import {Recover, PackedSignature} from "src/utils/Recover.sol";

contract CrossChainReceiverFactoryTest is Test {
    CrossChainReceiverFactory internal constant factory = CrossChainReceiverFactory(address(0xf4c70));

    function setUp() public {
        deployCodeTo("CrossChainReceiverFactory.sol", address(factory));
        vm.label(address(factory), "CrossChainReceiverFactory");
    }

    function _deployProxyToRoot(bytes32 root, uint256 privateKey)
        internal
        returns (CrossChainReceiverFactory proxy, address owner)
    {
        owner = vm.addr(privateKey);
        proxy = CrossChainReceiverFactory(factory.deploy(root, owner, true));
        vm.label(address(proxy), "Proxy");
    }

    function _deployProxy(bytes32 action, uint256 privateKey) internal returns (CrossChainReceiverFactory, address) {
        bytes32 root = keccak256(abi.encode(action, block.chainid));
        return _deployProxyToRoot(root, privateKey);
    }

    function _deployProxy(bytes32 action) internal returns (CrossChainReceiverFactory, address) {
        return _deployProxy(action, uint256(keccak256(abi.encode("owner"))));
    }

    function testSingleAction() public {
        bytes32 action = keccak256(abi.encode("action"));
        (CrossChainReceiverFactory proxy, address owner) = _deployProxy(action);

        assertEq(proxy.isValidSignature(action, abi.encode(owner, uint256(0x40))), bytes4(0x1626ba7e));
    }

    function testMultipleActions() public {
        bytes32 action1 = keccak256(abi.encode("action1"));
        bytes32 action2 = keccak256(abi.encode("action2"));
        bytes32 leaf1 = keccak256(abi.encode(action1, block.chainid));
        bytes32 leaf2 = keccak256(abi.encode(action2, block.chainid));
        bytes32 root;
        if (leaf2 < leaf1) {
            root = keccak256(abi.encodePacked(leaf2, leaf1));
        } else {
            root = keccak256(abi.encodePacked(leaf1, leaf2));
        }

        bytes32[] memory proof = new bytes32[](1);
        proof[0] = leaf1;

        (CrossChainReceiverFactory proxy, address owner) =
            _deployProxyToRoot(root, uint256(keccak256(abi.encode("owner"))));
        assertEq(proxy.isValidSignature(action2, abi.encode(owner, proof)), bytes4(0x1626ba7e));

        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        proxy.isValidSignature(action1, abi.encode(owner, proof));

        proof[0] = leaf2;
        assertEq(proxy.isValidSignature(action1, abi.encode(owner, proof)), bytes4(0x1626ba7e));
    }

    function testPendingOwner() public {
        (CrossChainReceiverFactory proxy, address owner) = _deployProxy(keccak256(abi.encode("action")));

        vm.prank(owner);
        proxy.acceptOwnership();
    }

    function testExec() public {
        uint256 signerKey = uint256(keccak256(abi.encode("signer")));
        bytes32 leaf = keccak256("leaf");
        (CrossChainReceiverFactory proxy, address signer) = _deployProxy(leaf, signerKey);

        MockERC20 target = deployMockERC20("Test Token", "TT", 18);
        deal(address(target), address(proxy), 1 ether);

        bytes memory data = abi.encodeCall(target.transfer, (address(this), 0.5 ether));
        bytes32 signingHash = keccak256(bytes.concat(
            hex"1901",
            abi.encode(
                keccak256(abi.encode(
                    keccak256("EIP712Domain(string name,uint256 chainId,address verifyingContract)"),
                    keccak256("ZeroExCrossChainReceiver"),
                    block.chainid,
                    address(factory)
                )),
                keccak256(abi.encode(
                    keccak256(
                        "CALL(uint256 nonce,address crossChainReceiver,address target,uint256 value,bytes data)"
                    ),
                    uint256(0),
                    address(proxy),
                    address(target),
                    uint256(0),
                    keccak256(data)
                ))
            )
        ));
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(signerKey, signingHash);
        PackedSignature memory sig = Recover.packSignature(v, r, s);

        bytes32 root = keccak256(abi.encode(leaf, block.chainid));
        vm.prank(signer);
        bytes memory result = proxy.call(root, payable(address(target)), 0, data, sig);

        bool success = abi.decode(result, (bool));
        assertTrue(success, "transfer failed");
        assertEq(target.balanceOf(address(this)), 0.5 ether, "wrong balance after transfer 1");
        assertEq(target.balanceOf(address(proxy)), 0.5 ether, "wrong balance after transfer 2");
    }
}
