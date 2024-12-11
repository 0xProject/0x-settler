// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {AllowanceHolder} from "src/allowanceholder/AllowanceHolderOld.sol";
import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {Utils} from "./Utils.sol";

import {Test} from "@forge-std/Test.sol";

contract AllowanceHolderDummy is AllowanceHolder {
    function getAllowed(address operator, address owner, address token) external view returns (uint256 r) {
        TSlot allowance = _ephemeralAllowance(operator, owner, token);
        return _get(allowance);
    }

    function setAllowed(address operator, address owner, address token, uint256 allowed) external {
        TSlot allowance = _ephemeralAllowance(operator, owner, token);
        _set(allowance, allowed);
    }
}

interface IAllowanceHolderDummy is IAllowanceHolder {
    function getAllowed(address operator, address owner, address token) external view returns (uint256 r);

    function setAllowed(address operator, address owner, address token, uint256 allowed) external;
}

contract AllowanceHolderUnitTest is Utils, Test {
    IAllowanceHolderDummy ah;
    address OPERATOR = _createNamedRejectionDummy("OPERATOR");
    address TOKEN = _createNamedRejectionDummy("TOKEN");
    address OWNER = address(this);
    address RECIPIENT = _createNamedRejectionDummy("RECIPIENT");
    uint256 AMOUNT = 123456;

    function setUp() public {
        ah = IAllowanceHolderDummy(address(new AllowanceHolderDummy()));
    }

    function testPermitSetGet() public {
        ah.setAllowed(OPERATOR, OWNER, TOKEN, 123456);
        assertEq(ah.getAllowed(OPERATOR, OWNER, TOKEN), 123456);
    }

    function testPermitAuthorised() public {
        ah.setAllowed(OPERATOR, OWNER, TOKEN, AMOUNT);

        assertEq(ah.getAllowed(OPERATOR, OWNER, TOKEN), AMOUNT);
        _mockExpectCall(
            TOKEN, abi.encodeWithSelector(IERC20.transferFrom.selector, OWNER, RECIPIENT, AMOUNT), new bytes(0)
        );
        vm.prank(OPERATOR, address(this));
        assertTrue(ah.transferFrom(TOKEN, OWNER, RECIPIENT, AMOUNT));
        assertEq(ah.getAllowed(OPERATOR, OWNER, TOKEN), 0);
    }

    function testPermitAuthorisedMultipleConsumption() public {
        ah.setAllowed(OPERATOR, OWNER, TOKEN, AMOUNT);

        assertEq(ah.getAllowed(OPERATOR, OWNER, TOKEN), AMOUNT);
        _mockExpectCall(
            TOKEN, abi.encodeWithSelector(IERC20.transferFrom.selector, OWNER, RECIPIENT, AMOUNT / 2 + 1), new bytes(0)
        );
        vm.prank(OPERATOR, address(this));
        assertTrue(ah.transferFrom(TOKEN, OWNER, RECIPIENT, AMOUNT / 2 + 1));
        assertEq(ah.getAllowed(OPERATOR, OWNER, TOKEN), AMOUNT / 2 - 1);
        _mockExpectCall(
            TOKEN, abi.encodeWithSelector(IERC20.transferFrom.selector, OWNER, RECIPIENT, AMOUNT / 2 - 1), new bytes(0)
        );
        vm.prank(OPERATOR, address(this));
        assertTrue(ah.transferFrom(TOKEN, OWNER, RECIPIENT, AMOUNT / 2 - 1));
        assertEq(ah.getAllowed(OPERATOR, OWNER, TOKEN), 0);
    }

    function testPermitUnauthorisedOperator() public {
        ah.setAllowed(OPERATOR, OWNER, TOKEN, AMOUNT);
        vm.expectRevert(abi.encodeWithSignature("Panic(uint256)", 0x11));
        ah.transferFrom(TOKEN, OWNER, RECIPIENT, AMOUNT);
    }

    function testPermitUnauthorisedAmount() public {
        ah.setAllowed(OPERATOR, OWNER, TOKEN, AMOUNT);
        vm.expectRevert(abi.encodeWithSignature("Panic(uint256)", 0x11));
        vm.prank(OPERATOR, address(this));
        ah.transferFrom(TOKEN, OWNER, RECIPIENT, AMOUNT + 1);
    }

    function testPermitUnauthorisedToken() public {
        ah.setAllowed(OPERATOR, OWNER, address(0xdead), AMOUNT);
        vm.expectRevert(abi.encodeWithSignature("Panic(uint256)", 0x11));
        vm.prank(OPERATOR, address(this));
        ah.transferFrom(TOKEN, OWNER, RECIPIENT, AMOUNT);
    }

    function testPermitAuthorisedStorageKey() public {
        vm.record();
        ah.setAllowed(OPERATOR, OWNER, TOKEN, AMOUNT);
        (bytes32[] memory reads, bytes32[] memory writes) = vm.accesses(address(ah));

        // Authorisation key is calculated as packed encoded keccak(operator, owner, token)
        bytes32 key = keccak256(abi.encodePacked(OPERATOR, OWNER, TOKEN));
        assertEq(reads.length, 1);
        assertEq(writes.length, 1);
        assertEq(reads[0], key);
        assertEq(writes[0], key);

        ah.getAllowed(OPERATOR, OWNER, TOKEN);
        (reads, writes) = vm.accesses(address(ah));
        assertEq(reads.length, 2);
        assertEq(writes.length, 1);
        assertEq(reads[1], key);
    }

    function testPermitExecute() public {
        address target = _createNamedRejectionDummy("TARGET");
        address operator = target;
        uint256 value = 999;

        bytes memory data = hex"deadbeef";

        _mockExpectCall(address(target), abi.encodePacked(data, address(this)), abi.encode(true));
        ah.exec{value: value}(operator, TOKEN, AMOUNT, payable(target), data);
    }
}
