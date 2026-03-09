// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Deployer, Nonce, zero, Feature, wrap} from "src/deployer/Deployer.sol";
import {IERC721View, IDeployer} from "src/deployer/IDeployer.sol";
import {ERC1967UUPSProxy} from "src/proxy/ERC1967UUPSProxy.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";
import {Create3} from "src/utils/Create3.sol";
import {IERC1967Proxy} from "src/interfaces/IERC1967Proxy.sol";
import {DEPLOYER} from "src/deployer/DeployerAddress.sol";

import {MainnetDefaultFork} from "../../integration/BaseForkTest.t.sol";

import "@forge-std/Test.sol";

contract Dummy {}

contract DeployerTest is Test, MainnetDefaultFork {
    Deployer public deployer;
    address public auth = address(0xc0de60d);

    function _testBlockNumber() internal pure override returns (uint256) {
        return 19921675;
    }

    function setUp() public {
        vm.createSelectFork(_testChainId(), _testBlockNumber());
        vm.setEvmVersion("osaka");

        deployer = Deployer(DEPLOYER);
        vm.label(address(deployer), "Deployer (proxy)");

        vm.prank(deployer.owner());
        deployer.transferOwnership(address(this));
        deployer.acceptOwnership();

        Deployer newImpl = new Deployer(2);
        vm.label(address(newImpl), "Deployer (implementation)");
        deployer.upgradeAndCall(address(newImpl), abi.encodeCall(newImpl.initialize, (address(0))));

        vm.expectRevert(abi.encodeWithSignature("VersionMismatch(uint256,uint256)", 2, 2));
        deployer.initialize(address(0));

        vm.expectRevert(abi.encodeWithSignature("OnlyProxy()"));
        newImpl.owner();

        vm.chainId(31337);
        vm.expectRevert(abi.encodeWithSignature("Panic(uint256)", 1));
        newImpl.initialize(address(this));
        vm.expectRevert(abi.encodeWithSignature("OnlyProxy()"));
        newImpl.initialize(address(0));
        vm.chainId(1);
        vm.expectRevert(new bytes(0));
        newImpl.initialize(address(0));
    }

    bytes32 internal ipfsHash = 0x364ebf112e53924630d49d5b34708d29b506816610b84844077b2d7f4439ebf1;
    bytes32 internal ipfsUriHash = keccak256("ipfs://QmRzeNMDA42tkFTYPE2eEji12VaU8Eg9YfWrHPAWdzcuLC");
    bytes32 internal metadataHash = keccak256(
        "{\"description\": \"nothing to see here\", \"name\": \"0x Settler feature 340282366920938463463374607431768211455\"}\n"
    );
    Feature internal testFeature = wrap(type(uint128).max);
    uint256 internal testTokenId = Feature.unwrap(testFeature);

    function testSetDescription() public {
        assertEq(keccak256(bytes(deployer.setDescription(testFeature, "nothing to see here"))), metadataHash);
        assertEq(deployer.descriptionHash(testFeature), ipfsHash);
    }

    function testSetDescriptionNotOwner() public {
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        vm.startPrank(auth);
        deployer.setDescription(testFeature, "nothing to see here");
    }

    function testAuthorize() public {
        deployer.setDescription(testFeature, "nothing to see here");
        (address who, uint40 expiry) = deployer.authorized(testFeature);
        assertEq(who, address(0));
        assertEq(expiry, 0);
        vm.expectEmit(true, true, false, true, address(deployer));
        emit IDeployer.Authorized(testFeature, auth, uint40(block.timestamp + 1 days));
        assertTrue(deployer.authorize(testFeature, auth, uint40(block.timestamp + 1 days)));
        (who, expiry) = deployer.authorized(testFeature);
        assertEq(who, auth);
        assertEq(expiry, block.timestamp + 1 days);
    }

    function testAuthorizeZero() public {
        deployer.setDescription(testFeature, "nothing to see here");
        vm.expectRevert(abi.encodeWithSignature("Panic(uint256)", 0x21));
        deployer.authorize(Feature.wrap(0), auth, uint40(block.timestamp + 1 days));
    }

    function testUnauthorize() public {
        deployer.setDescription(testFeature, "nothing to see here");
        deployer.authorize(testFeature, auth, uint40(block.timestamp + 1 days));
        vm.expectEmit(true, true, false, true, address(deployer));
        emit IDeployer.Authorized(testFeature, address(0), 0);
        assertTrue(deployer.authorize(testFeature, address(0), 0));
        (address who, uint40 expiry) = deployer.authorized(testFeature);
        assertEq(who, address(0));
        assertEq(expiry, 0);
    }

    function testAuthorizeNotOwner() public {
        deployer.setDescription(testFeature, "nothing to see here");
        vm.startPrank(auth);
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        deployer.authorize(testFeature, auth, uint40(block.timestamp + 1 days));
    }

    function _salt(uint128 feature, uint32 nonce) internal view returns (bytes32) {
        return bytes32(uint256(feature) << 128 | uint256(block.chainid) << 64 | uint256(nonce));
    }

    function testDeploy() public {
        deployer.setDescription(testFeature, "nothing to see here");
        deployer.authorize(testFeature, address(this), uint40(block.timestamp + 1 days));
        address predicted = Create3.predict(_salt(Feature.unwrap(testFeature), 1), address(deployer));
        vm.expectEmit(true, true, true, false, address(deployer));
        emit IERC721View.Transfer(address(0), predicted, testTokenId);
        vm.expectEmit(true, true, true, false, address(deployer));
        emit IDeployer.Deployed(testFeature, Nonce.wrap(1), predicted);
        (address instance,) = deployer.deploy(testFeature, type(Dummy).creationCode);
        assertEq(instance, predicted);
        assertEq(deployer.ownerOf(testTokenId), predicted);
    }

    function testDeployNotAuthorized() public {
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        deployer.deploy(testFeature, type(Dummy).creationCode);
    }

    function testDeployRevert() public {
        deployer.setDescription(testFeature, "nothing to see here");
        deployer.authorize(testFeature, address(this), uint40(block.timestamp + 1 days));
        vm.expectRevert(new bytes(0));
        deployer.deploy(testFeature, hex"5f5ffd"); // PUSH0 PUSH0 REVERT; empty revert message
    }

    function testDeployEmpty() public {
        deployer.setDescription(testFeature, "nothing to see here");
        deployer.authorize(testFeature, address(this), uint40(block.timestamp + 1 days));
        address predicted = Create3.predict(_salt(Feature.unwrap(testFeature), 1), address(deployer));
        vm.expectRevert(abi.encodeWithSignature("DeployFailed(uint128,uint32,address)", testTokenId, 1, predicted));
        deployer.deploy(testFeature, hex"00"); // STOP; succeeds with empty returnData
    }

    function testDeployMinimal() public {
        deployer.setDescription(testFeature, "nothing to see here");
        deployer.authorize(testFeature, address(this), uint40(block.timestamp + 1 days));
        // PUSH1 1 PUSH0 RETURN; returns hex"00" (STOP; succeeds with empty returnData)
        (address deployed,) = deployer.deploy(testFeature, hex"60015ff3");
        assertNotEq(deployed, address(0));
        assertNotEq(deployed.code.length, 0);
    }

    function testRemove() public {
        deployer.setDescription(testFeature, "nothing to see here");
        deployer.authorize(testFeature, address(this), uint40(block.timestamp + 1 days));

        vm.expectRevert(abi.encodeWithSignature("ERC721NonexistentToken(uint256)", testTokenId));
        deployer.ownerOf(testTokenId);

        (address instance, Nonce nonce) = deployer.deploy(testFeature, type(Dummy).creationCode);
        assertEq(deployer.ownerOf(testTokenId), instance);

        vm.expectEmit(true, true, true, false, address(deployer));
        emit IERC721View.Transfer(
            Create3.predict(_salt(Feature.unwrap(testFeature), 1), address(deployer)), address(0), testTokenId
        );
        vm.expectEmit(true, true, true, false, address(deployer));
        emit IDeployer.Removed(testFeature, Nonce.wrap(1), instance);
        assertTrue(deployer.remove(testFeature, nonce));
        vm.expectRevert(abi.encodeWithSignature("ERC721NonexistentToken(uint256)", testTokenId));
        deployer.ownerOf(testTokenId);

        (instance, nonce) = deployer.deploy(testFeature, type(Dummy).creationCode);
        assertEq(deployer.ownerOf(testTokenId), instance, "redeploy after remove");

        address newInstance;
        (newInstance, nonce) = deployer.deploy(testFeature, type(Dummy).creationCode);
        assertNotEq(newInstance, instance);
        assertEq(deployer.ownerOf(testTokenId), newInstance, "2nd redeploy after remove");

        assertTrue(deployer.remove(testFeature, nonce));
        assertEq(deployer.ownerOf(testTokenId), instance, "reverts to previous deployment");
    }

    function testRemoveAll() public {
        deployer.setDescription(testFeature, "nothing to see here");
        deployer.authorize(testFeature, address(this), uint40(block.timestamp + 1 days));

        deployer.deploy(testFeature, type(Dummy).creationCode);
        deployer.deploy(testFeature, type(Dummy).creationCode);
        deployer.deploy(testFeature, type(Dummy).creationCode);
        (address instance, Nonce nonce) = deployer.deploy(testFeature, type(Dummy).creationCode);

        vm.expectEmit(true, true, true, false, address(deployer));
        emit IERC721View.Transfer(instance, address(0), testTokenId);
        vm.expectEmit(true, false, false, false, address(deployer));
        emit IDeployer.RemovedAll(testFeature);
        deployer.removeAll(testFeature);

        vm.expectEmit(true, true, true, false, address(deployer));
        emit IDeployer.Removed(testFeature, nonce, instance);
        vm.recordLogs();
        deployer.remove(testFeature, nonce);
        Vm.Log[] memory entries = vm.getRecordedLogs();
        assertEq(entries.length, 1);

        vm.expectRevert(abi.encodeWithSignature("ERC721NonexistentToken(uint256)", testTokenId));
        deployer.ownerOf(testTokenId);

        for (Nonce i = zero.incr(); nonce > i; i = i.incr()) {
            vm.expectEmit(true, true, true, false, address(deployer));
            emit IDeployer.Removed(
                testFeature, i, Create3.predict(_salt(Feature.unwrap(testFeature), Nonce.unwrap(i)), address(deployer))
            );
            vm.recordLogs();
            deployer.remove(testFeature, i);
            entries = vm.getRecordedLogs();
            assertEq(entries.length, 1);
        }

        deployer.deploy(testFeature, type(Dummy).creationCode);
        (instance, nonce) = deployer.deploy(testFeature, type(Dummy).creationCode);

        vm.expectEmit(true, true, true, false, address(deployer));
        emit IERC721View.Transfer(
            instance,
            Create3.predict(_salt(Feature.unwrap(testFeature), Nonce.unwrap(nonce) - 1), address(deployer)),
            testTokenId
        );
        vm.expectEmit(true, true, true, false, address(deployer));
        emit IDeployer.Removed(testFeature, nonce, instance);
        deployer.remove(testFeature, nonce);

        nonce = Nonce.wrap(Nonce.unwrap(nonce) - 1);
        instance = Create3.predict(_salt(Feature.unwrap(testFeature), Nonce.unwrap(nonce)), address(deployer));
        vm.expectEmit(true, true, true, false, address(deployer));
        emit IERC721View.Transfer(instance, address(0), testTokenId);
        vm.expectEmit(true, true, true, false, address(deployer));
        emit IDeployer.Removed(testFeature, nonce, instance);
        deployer.remove(testFeature, nonce);
    }

    function testNext() public {
        deployer.setDescription(testFeature, "nothing to see here");
        deployer.authorize(testFeature, address(this), uint40(block.timestamp + 1 days));

        address next = Create3.predict(_salt(Feature.unwrap(testFeature), 1), address(deployer));
        assertEq(deployer.next(testFeature), next);

        (address instance,) = deployer.deploy(testFeature, type(Dummy).creationCode);
        assertEq(instance, next);

        assertEq(deployer.ownerOf(Feature.unwrap(testFeature)), next);
    }

    function testPrev() public {
        deployer.setDescription(testFeature, "nothing to see here");
        deployer.authorize(testFeature, address(this), uint40(block.timestamp + 1 days));

        (address firstInstance, Nonce firstNonce) = deployer.deploy(testFeature, type(Dummy).creationCode);
        (address secondInstance, Nonce secondNonce) = deployer.deploy(testFeature, type(Dummy).creationCode);
        (address thirdInstance, Nonce thirdNonce) = deployer.deploy(testFeature, type(Dummy).creationCode);
        (, Nonce fourthNonce) = deployer.deploy(testFeature, type(Dummy).creationCode);

        address prev = Create3.predict(_salt(Feature.unwrap(testFeature), Nonce.unwrap(thirdNonce)), address(deployer));

        assertEq(prev, thirdInstance);
        assertEq(deployer.prev(testFeature), prev);

        deployer.remove(testFeature, fourthNonce);

        assertEq(deployer.ownerOf(Feature.unwrap(testFeature)), prev);
        assertEq(deployer.prev(testFeature), secondInstance);

        deployer.remove(testFeature, secondNonce);

        assertEq(deployer.ownerOf(Feature.unwrap(testFeature)), prev);
        assertEq(deployer.prev(testFeature), firstInstance);

        deployer.remove(testFeature, firstNonce);

        assertEq(deployer.ownerOf(Feature.unwrap(testFeature)), prev);
        vm.expectRevert(abi.encodeWithSignature("NoInstance()"));
        deployer.prev(testFeature);
    }

    function testTokenURI() public {
        deployer.setDescription(testFeature, "nothing to see here");
        deployer.authorize(testFeature, address(this), uint40(block.timestamp + 1 days));
        deployer.deploy(testFeature, type(Dummy).creationCode);
        assertEq(ipfsUriHash, keccak256(bytes(deployer.tokenURI(testTokenId))));
    }

    function testDoubleRemove() public {
        deployer.setDescription(testFeature, "nothing to see here");
        deployer.authorize(testFeature, address(this), uint40(block.timestamp + 1 days));
        deployer.deploy(testFeature, type(Dummy).creationCode);
        address instance1 = deployer.ownerOf(testTokenId);
        deployer.deploy(testFeature, type(Dummy).creationCode);
        address instance2 = deployer.ownerOf(testTokenId);

        vm.expectEmit(true, true, true, false, address(deployer));
        emit IERC721View.Transfer(instance2, instance1, testTokenId);
        vm.expectEmit(true, true, true, false, address(deployer));
        emit IDeployer.Removed(testFeature, Nonce.wrap(2), instance2);
        deployer.remove(testFeature, Nonce.wrap(2));

        address instance3 = Create3.predict(_salt(Feature.unwrap(testFeature), 3), address(deployer));
        vm.expectEmit(true, true, true, false, address(deployer));
        emit IERC721View.Transfer(instance1, instance3, testTokenId);
        deployer.deploy(testFeature, type(Dummy).creationCode);
        assertEq(deployer.ownerOf(testTokenId), instance3);

        vm.expectEmit(true, true, true, false, address(deployer));
        emit IERC721View.Transfer(instance3, instance1, testTokenId);
        vm.expectEmit(true, true, true, false, address(deployer));
        emit IDeployer.Removed(testFeature, Nonce.wrap(3), instance3);
        deployer.remove(testFeature, Nonce.wrap(3));
        assertEq(deployer.ownerOf(testTokenId), instance1);

        // `remove` is idempotent
        vm.expectEmit(true, true, true, false, address(deployer));
        emit IDeployer.Removed(testFeature, Nonce.wrap(2), instance2);
        deployer.remove(testFeature, Nonce.wrap(2));
        assertEq(deployer.ownerOf(testTokenId), instance1);

        vm.expectEmit(true, true, true, false, address(deployer));
        emit IERC721View.Transfer(instance1, address(0), testTokenId);
        vm.expectEmit(true, true, true, false, address(deployer));
        emit IDeployer.Removed(testFeature, Nonce.wrap(1), instance1);
        deployer.remove(testFeature, Nonce.wrap(1));

        vm.expectRevert(abi.encodeWithSignature("ERC721NonexistentToken(uint256)", testTokenId));
        deployer.ownerOf(testTokenId);
    }
}
