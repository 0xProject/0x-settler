// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Deployer, IERC721View, Nonce, zero, Feature, wrap} from "src/deployer/Deployer.sol";
import {ERC1967UUPSProxy} from "src/proxy/ERC1967UUPSProxy.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";
import {Create3} from "src/utils/Create3.sol";
import {IERC1967Proxy} from "src/proxy/ERC1967UUPSUpgradeable.sol";

import "forge-std/Test.sol";

contract Dummy {}

contract DeployerTest is Test {
    Deployer public deployer;
    address public auth = address(0xc0de60d);

    function setUp() public {
        address deployerImpl = address(new Deployer());
        vm.label(deployerImpl, "Deployer (implementation)");
        vm.expectEmit(true, false, false, false, AddressDerivation.deriveContract(address(this), 2));
        emit IERC1967Proxy.Upgraded(deployerImpl);
        deployer = Deployer(ERC1967UUPSProxy.create(deployerImpl, abi.encodeCall(Deployer.initialize, (address(this)))));
        vm.label(address(deployer), "Deployer (proxy)");
        deployer.acceptOwnership();

        vm.expectRevert(abi.encodeWithSignature("VersionMismatch(uint256,uint256)", 1, 1));
        deployer.initialize(address(this));

        vm.expectRevert(abi.encodeWithSignature("OnlyProxy()"));
        Deployer(deployerImpl).owner();

        vm.expectRevert(abi.encodeWithSignature("OnlyProxy()"));
        Deployer(deployerImpl).initialize(address(this));
    }

    bytes32 ipfsHash = 0x6a6743a7e024153ba02b7360e504a0e4600809d79e6eb2da4b6d264f0833b16a;
    bytes32 ipfsUriHash = keccak256("ipfs://QmVW1FdBv7FqKFDgefTmiyX5ueSWoyy2dTBGsEgEVGCAAu");
    bytes32 metadataHash = keccak256("{\"description\": \"nothing to see here\", \"name\": \"0xV5 feature 1\"}\n");

    function testSetDescription() public {
        assertEq(keccak256(bytes(deployer.setDescription(wrap(1), "nothing to see here"))), metadataHash);
        assertEq(deployer.descriptionHash(wrap(1)), ipfsHash);
    }

    function testSetDescriptionNotOwner() public {
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        vm.startPrank(auth);
        deployer.setDescription(wrap(1), "nothing to see here");
    }

    function testAuthorize() public {
        deployer.setDescription(wrap(1), "nothing to see here");
        (address who, uint40 expiry) = deployer.authorized(wrap(1));
        assertEq(who, address(0));
        assertEq(expiry, 0);
        vm.expectEmit(true, true, false, true, address(deployer));
        emit Deployer.Authorized(wrap(1), auth, uint40(block.timestamp + 1 days));
        assertTrue(deployer.authorize(wrap(1), auth, uint40(block.timestamp + 1 days)));
        (who, expiry) = deployer.authorized(wrap(1));
        assertEq(who, auth);
        assertEq(expiry, block.timestamp + 1 days);
    }

    function testAuthorizeZero() public {
        deployer.setDescription(wrap(1), "nothing to see here");
        vm.expectRevert(abi.encodeWithSignature("Panic(uint256)", 0x21));
        deployer.authorize(Feature.wrap(0), auth, uint40(block.timestamp + 1 days));
    }

    function testUnauthorize() public {
        deployer.setDescription(wrap(1), "nothing to see here");
        deployer.authorize(wrap(1), auth, uint40(block.timestamp + 1 days));
        vm.expectEmit(true, true, false, true, address(deployer));
        emit Deployer.Authorized(wrap(1), address(0), 0);
        assertTrue(deployer.authorize(wrap(1), address(0), 0));
        (address who, uint40 expiry) = deployer.authorized(wrap(1));
        assertEq(who, address(0));
        assertEq(expiry, 0);
    }

    function testAuthorizeNotOwner() public {
        deployer.setDescription(wrap(1), "nothing to see here");
        vm.startPrank(auth);
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        deployer.authorize(wrap(1), auth, uint40(block.timestamp + 1 days));
    }

    function _salt(uint128 feature, uint32 nonce) internal view returns (bytes32) {
        return bytes32(uint256(feature) << 128 | uint256(block.chainid) << 64 | uint256(nonce));
    }

    function testDeploy() public {
        deployer.setDescription(wrap(1), "nothing to see here");
        deployer.authorize(wrap(1), address(this), uint40(block.timestamp + 1 days));
        address predicted = Create3.predict(_salt(1, 1), address(deployer));
        vm.expectEmit(true, true, true, false, address(deployer));
        emit IERC721View.Transfer(address(0), predicted, 1);
        vm.expectEmit(true, true, true, false, address(deployer));
        emit Deployer.Deployed(wrap(1), Nonce.wrap(1), predicted);
        (address instance,) = deployer.deploy(wrap(1), type(Dummy).creationCode);
        assertEq(instance, predicted);
        assertEq(deployer.ownerOf(1), predicted);
    }

    function testDeployNotAuthorized() public {
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        deployer.deploy(wrap(1), type(Dummy).creationCode);
    }

    function testDeployRevert() public {
        deployer.setDescription(wrap(1), "nothing to see here");
        deployer.authorize(wrap(1), address(this), uint40(block.timestamp + 1 days));
        vm.expectRevert(new bytes(0));
        deployer.deploy(wrap(1), hex"5f5ffd"); // PUSH0 PUSH0 REVERT; empty revert message
    }

    function testDeployEmpty() public {
        deployer.setDescription(wrap(1), "nothing to see here");
        deployer.authorize(wrap(1), address(this), uint40(block.timestamp + 1 days));
        address predicted = Create3.predict(_salt(1, 1), address(deployer));
        vm.expectRevert(abi.encodeWithSignature("DeployFailed(uint128,uint32,address)", 1, 1, predicted));
        deployer.deploy(wrap(1), hex"00"); // STOP; succeeds with empty returnData
    }

    function testDeployMinimal() public {
        deployer.setDescription(wrap(1), "nothing to see here");
        deployer.authorize(wrap(1), address(this), uint40(block.timestamp + 1 days));
        // PUSH1 1 PUSH0 RETURN; returns hex"00" (STOP; succeeds with empty returnData)
        (address deployed,) = deployer.deploy(wrap(1), hex"60015ff3");
        assertNotEq(deployed, address(0));
        assertNotEq(deployed.code.length, 0);
    }

    function testRemove() public {
        deployer.setDescription(wrap(1), "nothing to see here");
        deployer.authorize(wrap(1), address(this), uint40(block.timestamp + 1 days));

        vm.expectRevert(abi.encodeWithSignature("NoToken(uint256)", 1));
        deployer.ownerOf(1);

        (address instance, Nonce nonce) = deployer.deploy(wrap(1), type(Dummy).creationCode);
        assertEq(deployer.ownerOf(1), instance);

        vm.expectEmit(true, true, true, false, address(deployer));
        emit IERC721View.Transfer(Create3.predict(_salt(1, 1), address(deployer)), address(0), 1);
        vm.expectEmit(true, true, true, false, address(deployer));
        emit Deployer.Removed(wrap(1), Nonce.wrap(1), instance);
        assertTrue(deployer.remove(wrap(1), nonce));
        vm.expectRevert(abi.encodeWithSignature("NoToken(uint256)", 1));
        deployer.ownerOf(1);

        (instance, nonce) = deployer.deploy(wrap(1), type(Dummy).creationCode);
        assertEq(deployer.ownerOf(1), instance, "redeploy after remove");

        address newInstance;
        (newInstance, nonce) = deployer.deploy(wrap(1), type(Dummy).creationCode);
        assertNotEq(newInstance, instance);
        assertEq(deployer.ownerOf(1), newInstance, "2nd redeploy after remove");

        assertTrue(deployer.remove(wrap(1), nonce));
        assertEq(deployer.ownerOf(1), instance, "reverts to previous deployment");
    }

    function testRemoveAll() public {
        deployer.setDescription(wrap(1), "nothing to see here");
        deployer.authorize(wrap(1), address(this), uint40(block.timestamp + 1 days));

        deployer.deploy(wrap(1), type(Dummy).creationCode);
        deployer.deploy(wrap(1), type(Dummy).creationCode);
        deployer.deploy(wrap(1), type(Dummy).creationCode);
        (address instance, Nonce nonce) = deployer.deploy(wrap(1), type(Dummy).creationCode);

        vm.expectEmit(true, true, true, false, address(deployer));
        emit IERC721View.Transfer(instance, address(0), 1);
        vm.expectEmit(true, false, false, false, address(deployer));
        emit Deployer.RemovedAll(wrap(1));
        deployer.removeAll(wrap(1));

        vm.expectEmit(true, true, true, false, address(deployer));
        emit Deployer.Removed(wrap(1), nonce, instance);
        vm.recordLogs();
        deployer.remove(wrap(1), nonce);
        Vm.Log[] memory entries = vm.getRecordedLogs();
        assertEq(entries.length, 1);

        vm.expectRevert(abi.encodeWithSignature("NoToken(uint256)", 1));
        deployer.ownerOf(1);

        for (Nonce i = zero.incr(); nonce > i; i = i.incr()) {
            vm.expectEmit(true, true, true, false, address(deployer));
            emit Deployer.Removed(wrap(1), i, Create3.predict(_salt(1, Nonce.unwrap(i)), address(deployer)));
            vm.recordLogs();
            deployer.remove(wrap(1), i);
            entries = vm.getRecordedLogs();
            assertEq(entries.length, 1);
        }

        deployer.deploy(wrap(1), type(Dummy).creationCode);
        (instance, nonce) = deployer.deploy(wrap(1), type(Dummy).creationCode);

        vm.expectEmit(true, true, true, false, address(deployer));
        emit IERC721View.Transfer(instance, Create3.predict(_salt(1, Nonce.unwrap(nonce) - 1), address(deployer)), 1);
        vm.expectEmit(true, true, true, false, address(deployer));
        emit Deployer.Removed(wrap(1), nonce, instance);
        deployer.remove(wrap(1), nonce);

        instance = Create3.predict(_salt(1, Nonce.unwrap(nonce)), address(deployer));
        vm.expectEmit(true, true, true, false, address(deployer));
        emit IERC721View.Transfer(instance, address(0), 1);
        vm.expectEmit(true, true, true, false, address(deployer));
        emit Deployer.Removed(wrap(1), nonce, instance);
        deployer.remove(wrap(1), nonce);
    }

    function testTokenURI() public {
        deployer.setDescription(wrap(1), "nothing to see here");
        deployer.authorize(wrap(1), address(this), uint40(block.timestamp + 1 days));
        deployer.deploy(wrap(1), type(Dummy).creationCode);
        assertEq(ipfsUriHash, keccak256(bytes(deployer.tokenURI(1))));
    }
}
