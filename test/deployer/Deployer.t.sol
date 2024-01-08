// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {Deployer} from "src/deployer/Deployer.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";

import "forge-std/Test.sol";

contract Dummy {
    address public feeCollector;

    constructor(address _feeCollector) {
        feeCollector = _feeCollector;
    }
}

contract DeployerTest is Test {
    Deployer public deployer;
    address public auth = address(0xc0de60d);

    function setUp() public {
        deployer = new Deployer(address(this));
        deployer.acceptOwnership();
    }

    bytes32 ipfsHash = 0x55fa85b555094012e583d2ddcb777745ff7f343991c11aa6e75dccca1bb456ed;
    bytes32 ipfsUriHash = keccak256("ipfs://QmU8GviotZ9EvE2zHd8DwM8RqNnJfinax8s8mgTg8k4Tm6");

    function testSetDescription() public {
        assertEq(keccak256(bytes(deployer.setDescription(1, "nothing to see here"))), ipfsUriHash);
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
        assertEq(deployer.authorizedUntil(1, auth), 0);
        vm.expectEmit(true, true, false, true, address(deployer));
        emit Authorized(1, auth, block.timestamp + 1 days);
        assertTrue(deployer.authorize(1, auth, block.timestamp + 1 days));
        assertEq(deployer.authorizedUntil(1, auth), block.timestamp + 1 days);
    }

    function testAuthorizeZero() public {
        deployer.setDescription(1, "nothing to see here");
        vm.expectRevert(abi.encodeWithSignature("Panic(uint256)", 0x11));
        deployer.authorize(0, auth, block.timestamp + 1 days);
    }

    function testUnauthorize() public {
        deployer.setDescription(1, "nothing to see here");
        deployer.authorize(1, auth, block.timestamp + 1 days);
        vm.expectEmit(true, true, false, true, address(deployer));
        emit Authorized(1, auth, 0);
        assertTrue(deployer.authorize(1, auth, 0));
        assertEq(deployer.authorizedUntil(1, auth), 0);
    }

    function testAuthorizeNotOwner() public {
        deployer.setDescription(1, "nothing to see here");
        vm.startPrank(auth);
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        deployer.authorize(1, auth, block.timestamp + 1 days);
    }

    event FeeCollectorChanged(uint128 indexed, address indexed);

    function testFeeCollector() public {
        assertEq(deployer.feeCollector(1), address(0));
        vm.expectEmit(true, false, false, false, address(deployer));
        emit FeeCollectorChanged(1, address(this));
        assertTrue(deployer.setFeeCollector(1, address(this)));
        assertEq(deployer.feeCollector(1), address(this));
    }

    function testFeeCollectorNotOwner() public {
        vm.startPrank(auth);
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        deployer.setFeeCollector(1, auth);
    }

    event Deployed(uint128 indexed, address indexed);
    event Transfer(address indexed, address indexed, uint256 indexed);

    function testDeploy() public {
        deployer.setDescription(1, "nothing to see here");
        deployer.authorize(1, address(this), block.timestamp + 1 days);
        deployer.setFeeCollector(1, auth);
        address predicted = AddressDerivation.deriveContract(address(deployer), 1);
        vm.expectEmit(true, true, false, false, address(deployer));
        emit Deployed(1, predicted);
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
        deployer.authorize(1, address(this), block.timestamp + 1 days);
        vm.expectRevert(abi.encodeWithSignature("DeployFailed()"));
        deployer.deploy(1, hex"5f5ffd"); // PUSH0 PUSH0 REVERT; empty revert message
    }

    function testDeployEmpty() public {
        deployer.setDescription(1, "nothing to see here");
        deployer.authorize(1, address(this), block.timestamp + 1 days);
        vm.expectRevert(abi.encodeWithSignature("DeployFailed()"));
        deployer.deploy(1, hex"00"); // STOP; succeeds with empty returnData
    }

    event Unsafe(uint128 indexed, uint64 indexed);

    function testSafeDeployment() public {
        deployer.setDescription(1, "nothing to see here");
        deployer.authorize(1, address(this), block.timestamp + 1 days);

        assertEq(deployer.ownerOf(1), address(0));

        uint64 nonce = deployer.nextNonce();
        address instance = deployer.deploy(1, type(Dummy).creationCode);
        assertEq(deployer.ownerOf(1), instance);

        vm.expectEmit(true, true, true, false, address(deployer));
        emit Transfer(AddressDerivation.deriveContract(address(deployer), 1), address(0), 1);
        vm.expectEmit(true, true, false, false, address(deployer));
        emit Unsafe(1, 1);
        assertTrue(deployer.setUnsafe(1, nonce));
        assertEq(deployer.ownerOf(1), address(0), "goes to zero");

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

    function testTokenURI() public {
        deployer.setDescription(1, "nothing to see here");
        deployer.authorize(1, address(this), block.timestamp + 1 days);
        deployer.deploy(1, type(Dummy).creationCode);
        assertEq(ipfsUriHash, keccak256(bytes(deployer.tokenURI(1))));
    }
}
