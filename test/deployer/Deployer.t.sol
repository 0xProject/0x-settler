// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {Deployer} from "src/deployer/Deployer.sol";

import "forge-std/Test.sol";

contract Dummy {
    address public feeCollector;

    constructor(address _feeCollector) {
        feeCollector = _feeCollector;
    }
}

contract DeployFail {
    constructor() {
        revert();
    }
}

contract DeployerTest is Test {
    Deployer public deployer;
    address public auth = address(0xc0de60d);

    function setUp() public {
        deployer = new Deployer(address(this));
        deployer.acceptOwnership();
    }

    event Authorized(address indexed, bool);

    function testAuthorize() public {
        assertFalse(deployer.isAuthorized(auth));
        vm.expectEmit(true, false, false, true);
        emit Authorized(auth, true);
        assertTrue(deployer.authorize(auth, true));
        assertTrue(deployer.isAuthorized(auth));
    }

    function testUnauthorize() public {
        deployer.authorize(auth, true);
        vm.expectEmit(true, false, false, true);
        emit Authorized(auth, false);
        assertTrue(deployer.authorize(auth, false));
        assertFalse(deployer.isAuthorized(auth));
    }

    function testAuthorizeNotOwner() public {
        vm.startPrank(auth);
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        deployer.authorize(auth, true);
    }

    event FeeCollectorChanged(address indexed);

    function testFeeCollector() public {
        assertEq(deployer.feeCollector(), address(0));
        vm.expectEmit(true, false, false, false);
        emit FeeCollectorChanged(address(this));
        assertTrue(deployer.setFeeCollector(address(this)));
        assertEq(deployer.feeCollector(), address(this));
    }

    function testFeeCollectorNotOwner() public {
        vm.startPrank(auth);
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        deployer.setFeeCollector(auth);
    }

    event Deployed(uint64 indexed, address indexed);

    function testDeploy() public {
        deployer.authorize(address(this), true);
        deployer.setFeeCollector(auth);
        assertEq(deployer.nonce(), 0);
        address predicted = deployer.deployment(1);
        vm.expectEmit(true, true, false, false);
        emit Deployed(1, predicted);
        (uint64 nonce, address instance) = deployer.deploy(type(Dummy).creationCode);
        assertEq(nonce, 1);
        assertEq(instance, predicted);
        assertEq(deployer.nonce(), 1);
        assertEq(deployer.deployment(), predicted);
        assertEq(Dummy(instance).feeCollector(), auth);
    }

    function testDeployNotAuthorized() public {
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        deployer.deploy(type(Dummy).creationCode);
    }

    function testDeployRevert() public {
        deployer.authorize(address(this), true);
        vm.expectRevert(abi.encodeWithSignature("DeployFailed()"));
        deployer.deploy(type(DeployFail).creationCode);
    }

    function testDeployEmpty() public {
        deployer.authorize(address(this), true);
        vm.expectRevert(abi.encodeWithSignature("DeployFailed()"));
        deployer.deploy(hex"00"); // STOP opcode; succeeds with empty returnData
    }

    function testSafeDeployment() public {
        deployer.authorize(address(this), true);

        vm.expectRevert(new bytes(0));
        deployer.safeDeployment();

        (, address instance) = deployer.deploy(type(Dummy).creationCode);
        assertEq(deployer.safeDeployment(), instance);

        assertTrue(deployer.setUnsafe(1));
        vm.expectRevert(new bytes(0));
        deployer.safeDeployment();

        (, instance) = deployer.deploy(type(Dummy).creationCode);
        assertEq(deployer.safeDeployment(), instance);

        deployer.deploy(type(Dummy).creationCode);
        assertNotEq(deployer.safeDeployment(), instance);

        assertTrue(deployer.setUnsafe(3));
        assertEq(deployer.safeDeployment(), instance);
    }
}
