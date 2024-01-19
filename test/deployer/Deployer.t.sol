// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {Deployer} from "src/deployer/Deployer.sol";
import {ERC1967UUPSProxy} from "src/proxy/ERC1967UUPSProxy.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";
import {IFeeCollector} from "src/core/IFeeCollector.sol";

import "forge-std/Test.sol";

contract Dummy is IFeeCollector {
    address public immutable override feeCollector;

    constructor(address _feeCollector) {
        feeCollector = _feeCollector;
    }
}

contract DeployerTest is Test {
    Deployer public deployer;
    address public auth = address(0xc0de60d);

    event Upgraded(address indexed);

    function setUp() public {
        address deployerImpl = address(new Deployer());
        vm.label(deployerImpl, "Deployer (implementation)");
        vm.expectEmit(true, false, false, false, AddressDerivation.deriveContract(address(this), 2));
        emit Upgraded(deployerImpl);
        deployer = Deployer(ERC1967UUPSProxy.create(deployerImpl, abi.encodeCall(Deployer.initialize, (address(this)))));
        vm.label(address(deployer), "Deployer (proxy)");
        deployer.acceptOwnership();

        vm.expectRevert(abi.encodeWithSignature("AlreadyInitialized()"));
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
        assertEq(keccak256(bytes(deployer.setDescription(1, "nothing to see here"))), metadataHash);
        assertEq(deployer.descriptionHash(1), ipfsHash);
    }

    function testSetDescriptionNotOwner() public {
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        vm.startPrank(auth);
        deployer.setDescription(1, "nothing to see here");
    }

    event Authorized(uint128 indexed, address indexed, uint256);

    function testAuthorize() public {
        deployer.setDescription(1, "nothing to see here");
        (address who, uint96 expiry) = deployer.authorized(1);
        assertEq(who, address(0));
        assertEq(expiry, 0);
        vm.expectEmit(true, true, false, true, address(deployer));
        emit Authorized(1, auth, uint96(block.timestamp + 1 days));
        assertTrue(deployer.authorize(1, auth, uint96(block.timestamp + 1 days)));
        (who, expiry) = deployer.authorized(1);
        assertEq(who, auth);
        assertEq(expiry, block.timestamp + 1 days);
    }

    function testAuthorizeZero() public {
        deployer.setDescription(1, "nothing to see here");
        vm.expectRevert(abi.encodeWithSignature("Panic(uint256)", 0x11));
        deployer.authorize(0, auth, uint96(block.timestamp + 1 days));
    }

    function testUnauthorize() public {
        deployer.setDescription(1, "nothing to see here");
        deployer.authorize(1, auth, uint96(block.timestamp + 1 days));
        vm.expectEmit(true, true, false, true, address(deployer));
        emit Authorized(1, address(0), 0);
        assertTrue(deployer.authorize(1, address(0), 0));
        (address who, uint96 expiry) = deployer.authorized(1);
        assertEq(who, address(0));
        assertEq(expiry, 0);
    }

    function testAuthorizeNotOwner() public {
        deployer.setDescription(1, "nothing to see here");
        vm.startPrank(auth);
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        deployer.authorize(1, auth, uint96(block.timestamp + 1 days));
    }

    event FeeCollectorChanged(uint128 indexed, address indexed);

    function testFeeCollector() public {
        assertEq(deployer.feeCollector(1), address(0));
        vm.expectEmit(true, true, false, false, address(deployer));
        emit FeeCollectorChanged(1, address(this));
        assertTrue(deployer.setFeeCollector(1, address(this)));
        assertEq(deployer.feeCollector(1), address(this));
    }

    function testFeeCollectorNotOwner() public {
        vm.startPrank(auth);
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        deployer.setFeeCollector(1, auth);
    }

    event Deployed(uint128 indexed, uint64 indexed, address indexed);
    event Transfer(address indexed, address indexed, uint256 indexed);

    function testDeploy() public {
        deployer.setDescription(1, "nothing to see here");
        deployer.authorize(1, address(this), uint96(block.timestamp + 1 days));
        deployer.setFeeCollector(1, auth);
        address predicted = AddressDerivation.deriveContract(address(deployer), 1);
        vm.expectEmit(true, true, true, false, address(deployer));
        emit Deployed(1, 1, predicted);
        vm.expectEmit(true, true, true, false, address(deployer));
        emit Transfer(address(0), predicted, 1);
        address instance = deployer.deploy(1, type(Dummy).creationCode);
        assertEq(instance, predicted);
        assertEq(deployer.ownerOf(1), predicted);
        assertEq(Dummy(instance).feeCollector(), auth);
    }

    function testDeployNotAuthorized() public {
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        deployer.deploy(1, type(Dummy).creationCode);
    }

    function testDeployRevert() public {
        deployer.setDescription(1, "nothing to see here");
        deployer.authorize(1, address(this), uint96(block.timestamp + 1 days));
        vm.expectRevert(abi.encodeWithSignature("DeployFailed(uint64)", 1));
        deployer.deploy(1, hex"5f5ffd"); // PUSH0 PUSH0 REVERT; empty revert message
    }

    function testDeployEmpty() public {
        deployer.setDescription(1, "nothing to see here");
        deployer.authorize(1, address(this), uint96(block.timestamp + 1 days));
        vm.expectRevert(abi.encodeWithSignature("DeployFailed(uint64)", 1));
        deployer.deploy(1, hex"00"); // STOP; succeeds with empty returnData
    }

    function testDeployNoFee() public {
        deployer.setDescription(1, "nothing to see here");
        deployer.authorize(1, address(this), uint96(block.timestamp + 1 days));
        vm.expectRevert(abi.encodeWithSignature("DeployFailed(uint64)", 1));
        deployer.deploy(1, hex"60015ff3"); // PUSH1 1 PUSH0 RETURN; returns hex"00" (STOP; succeeds with empty returnData)
    }

    function testDeployThenEmpty() public {
        deployer.setDescription(1, "nothing to see here");
        deployer.authorize(1, address(this), uint96(block.timestamp + 1 days));
        assertEq(deployer.feeCollector(1), address(0));
        // PUSH4 60205ff3 PUSH0 MSTORE PUSH1 4 PUSH1 1c RETURN; returns hex"60205ff3"
        // PUSH1 20 PUSH0 RETURN; returns zero address (technically the whole word is zero)
        address deployed = deployer.deploy(1, hex"6360205ff35f526004601cf3");
        assertNotEq(deployed, address(0));
        assertEq(IFeeCollector(deployed).feeCollector(), address(0)); // technically all selectors return zero
    }

    function testDeployThenRevert() public {
        deployer.setDescription(1, "nothing to see here");
        deployer.authorize(1, address(this), uint96(block.timestamp + 1 days));
        assertEq(deployer.feeCollector(1), address(0));
        vm.expectRevert(abi.encodeWithSignature("DeployFailed(uint64)", 1));
        // PUSH4 60205ffd PUSH0 MSTORE PUSH1 4 PUSH1 1c RETURN; returns hex"60205ffd"
        // PUSH1 20 PUSH0 REVERT; reverts with zero word
        deployer.deploy(1, hex"6360205ffd5f526004601cf3");
    }

    event Unsafe(uint128 indexed, uint64 indexed, address indexed);

    function testSafeDeployment() public {
        deployer.setDescription(1, "nothing to see here");
        deployer.authorize(1, address(this), uint96(block.timestamp + 1 days));

        vm.expectRevert(abi.encodeWithSignature("NoToken(uint256)", 1));
        deployer.ownerOf(1);

        uint64 nonce = deployer.nextNonce();
        address instance = deployer.deploy(1, type(Dummy).creationCode);
        assertEq(deployer.ownerOf(1), instance);

        vm.expectEmit(true, true, true, false, address(deployer));
        emit Transfer(AddressDerivation.deriveContract(address(deployer), 1), address(0), 1);
        vm.expectEmit(true, true, true, false, address(deployer));
        emit Unsafe(1, 1, instance);
        assertTrue(deployer.setUnsafe(1, nonce));
        vm.expectRevert(abi.encodeWithSignature("NoToken(uint256)", 1));
        deployer.ownerOf(1);

        nonce = deployer.nextNonce();
        instance = deployer.deploy(1, type(Dummy).creationCode);
        assertEq(deployer.ownerOf(1), instance, "redeploy after unsafe");

        nonce = deployer.nextNonce();
        address newInstance = deployer.deploy(1, type(Dummy).creationCode);
        assertNotEq(newInstance, instance);
        assertEq(deployer.ownerOf(1), newInstance, "2nd redeploy after unsafe");

        assertTrue(deployer.setUnsafe(1, nonce));
        assertEq(deployer.ownerOf(1), instance, "reverts to previous deployment");
    }

    event AllUnsafe(uint256 indexed);

    function testAllUnsafe() public {
        deployer.setDescription(1, "nothing to see here");
        deployer.authorize(1, address(this), uint96(block.timestamp + 1 days));

        deployer.deploy(1, type(Dummy).creationCode);
        deployer.deploy(1, type(Dummy).creationCode);
        deployer.deploy(1, type(Dummy).creationCode);
        address instance = deployer.deploy(1, type(Dummy).creationCode);
        uint64 nonce = deployer.nextNonce() - 1;

        vm.expectEmit(true, true, true, false, address(deployer));
        emit Transfer(instance, address(0), 1);
        vm.expectEmit(true, false, false, false, address(deployer));
        emit AllUnsafe(1);
        deployer.setAllUnsafe(1);

        vm.expectEmit(true, true, true, false, address(deployer));
        emit Unsafe(1, nonce, instance);
        vm.recordLogs();
        deployer.setUnsafe(1, nonce);
        Vm.Log[] memory entries = vm.getRecordedLogs();
        assertEq(entries.length, 1);

        vm.expectRevert(abi.encodeWithSignature("NoToken(uint256)", 1));
        deployer.ownerOf(1);

        for (uint64 i = 1; i < nonce; i++) {
            vm.expectEmit(true, true, true, false, address(deployer));
            emit Unsafe(1, i, AddressDerivation.deriveContract(address(deployer), i));
            vm.recordLogs();
            deployer.setUnsafe(1, i);
            entries = vm.getRecordedLogs();
            assertEq(entries.length, 1);
        }

        deployer.deploy(1, type(Dummy).creationCode);
        instance = deployer.deploy(1, type(Dummy).creationCode);
        nonce = deployer.nextNonce() - 1;

        vm.expectEmit(true, true, true, false, address(deployer));
        emit Transfer(instance, AddressDerivation.deriveContract(address(deployer), nonce - 1), 1);
        vm.expectEmit(true, true, true, false, address(deployer));
        emit Unsafe(1, nonce, instance);
        deployer.setUnsafe(1, nonce);

        nonce--;
        instance = AddressDerivation.deriveContract(address(deployer), nonce);
        vm.expectEmit(true, true, true, false, address(deployer));
        emit Transfer(instance, address(0), 1);
        vm.expectEmit(true, true, true, false, address(deployer));
        emit Unsafe(1, nonce, instance);
        deployer.setUnsafe(1, nonce);
    }

    function testTokenURI() public {
        deployer.setDescription(1, "nothing to see here");
        deployer.authorize(1, address(this), uint96(block.timestamp + 1 days));
        deployer.deploy(1, type(Dummy).creationCode);
        assertEq(ipfsUriHash, keccak256(bytes(deployer.tokenURI(1))));
    }
}
