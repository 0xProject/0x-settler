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

    event Authorized(uint256 indexed, address indexed, uint256);

    function testAuthorize() public {
        assertEq(deployer.authorizedUntil(1, auth), 0);
        vm.expectEmit(true, true, false, true);
        emit Authorized(1, auth, block.timestamp + 1 days);
        assertTrue(deployer.authorize(1, auth, block.timestamp + 1 days));
        assertEq(deployer.authorizedUntil(1, auth), block.timestamp + 1 days);
    }

    function testAuthorizeZero() public {
        vm.expectRevert(abi.encodeWithSignature("Panic(uint256)", 0x11));
        deployer.authorize(0, auth, block.timestamp + 1 days);
    }

    function testUnauthorize() public {
        deployer.authorize(1, auth, block.timestamp + 1 days);
        vm.expectEmit(true, true, false, true);
        emit Authorized(1, auth, 0);
        assertTrue(deployer.authorize(1, auth, 0));
        assertEq(deployer.authorizedUntil(1, auth), 0);
    }

    function testAuthorizeNotOwner() public {
        vm.startPrank(auth);
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        deployer.authorize(1, auth, block.timestamp + 1 days);
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

    event Deployed(uint256 indexed, address indexed);

    function testDeploy() public {
        deployer.authorize(1, address(this), block.timestamp + 1 days);
        deployer.setFeeCollector(auth);
        address predicted = AddressDerivation.deriveDeterministicContract(
            address(deployer),
            bytes32(0),
            keccak256(bytes.concat(type(Dummy).creationCode, bytes32(uint256(uint160(deployer.feeCollector())))))
        );
        vm.expectEmit(true, true, false, false);
        emit Deployed(1, predicted);
        address instance = deployer.deploy(1, type(Dummy).creationCode, bytes32(0));
        assertEq(instance, predicted);
        assertEq(deployer.deployments(1), predicted);
        assertEq(Dummy(instance).feeCollector(), auth);
    }

    function testDeployNotAuthorized() public {
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        deployer.deploy(1, type(Dummy).creationCode, bytes32(0));
    }

    function testDeployRevert() public {
        deployer.authorize(1, address(this), block.timestamp + 1 days);
        vm.expectRevert(abi.encodeWithSignature("DeployFailed()"));
        deployer.deploy(1, hex"5f5ffd", bytes32(0)); // PUSH0 PUSH0 REVERT; empty revert message
    }

    function testDeployEmpty() public {
        deployer.authorize(1, address(this), block.timestamp + 1 days);
        vm.expectRevert(abi.encodeWithSignature("DeployFailed()"));
        deployer.deploy(1, hex"00", bytes32(0)); // STOP; succeeds with empty returnData
    }

    function testSafeDeployment() public {
        deployer.authorize(1, address(this), block.timestamp + 1 days);

        assertEq(deployer.deployments(1), address(0));

        address instance = deployer.deploy(1, type(Dummy).creationCode, bytes32(0));
        assertEq(deployer.deployments(1), instance);

        assertTrue(deployer.setUnsafe(1, instance));
        assertEq(deployer.deployments(1), address(0));

        instance = deployer.deploy(1, type(Dummy).creationCode, bytes32(uint256(1)));
        assertEq(deployer.deployments(1), instance);

        address newInstance = deployer.deploy(1, type(Dummy).creationCode, bytes32(uint256(2)));
        assertNotEq(newInstance, instance);
        assertEq(deployer.deployments(1), newInstance);

        assertTrue(deployer.setUnsafe(1, newInstance));
        assertEq(deployer.deployments(1), instance);
    }
}
