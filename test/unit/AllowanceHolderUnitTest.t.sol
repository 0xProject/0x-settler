// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {AllowanceHolder} from "../../src/AllowanceHolder.sol";
import {IAllowanceHolder} from "../../src/IAllowanceHolder.sol";

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {Test} from "forge-std/Test.sol";
import {VmSafe} from "forge-std/Vm.sol";

contract AllowanceHolderDummy is AllowanceHolder {
    function getAllowed(address operator, address owner, address token) external view returns (uint256 r) {
        return _getAllowed(operator, owner, token);
    }

    function setAllowed(address operator, address owner, address token, uint256 allowed) external {
        return _setAllowed(operator, owner, token, allowed);
    }
}

contract FallbackDummy {
    fallback() external payable {}
}

contract AllowanceHolderUnitTest is Test {
    AllowanceHolderDummy ah;
    address OPERATOR = address(0x01);
    address TOKEN = address(0x02);
    address OWNER = address(this);
    address RECIPIENT = address(0);
    uint256 AMOUNT = 123456;

    function setUp() public {
        ah = new AllowanceHolderDummy();
    }

    function testPermitSetGet() public {
        ah.setAllowed(OPERATOR, OWNER, TOKEN, 123456);
        assertEq(ah.getAllowed(OPERATOR, OWNER, TOKEN), 123456);
    }

    function testPermitAuthorised() public {
        address token = address(new FallbackDummy());
        address operator = address(this);

        ah.setAllowed(operator, OWNER, token, AMOUNT);

        assertEq(ah.getAllowed(operator, OWNER, token), AMOUNT);
        assertTrue(ah.transferFrom(token, OWNER, RECIPIENT, AMOUNT));
        assertEq(ah.getAllowed(operator, OWNER, token), 0);
    }

    function testPermitAuthorisedMultipleConsumption() public {
        address token = address(new FallbackDummy());
        address operator = address(this);

        ah.setAllowed(operator, OWNER, token, AMOUNT);

        assertEq(ah.getAllowed(operator, OWNER, token), AMOUNT);
        assertTrue(ah.transferFrom(token, OWNER, RECIPIENT, AMOUNT / 2));
        assertEq(ah.getAllowed(operator, OWNER, token), AMOUNT / 2);
        assertTrue(ah.transferFrom(token, OWNER, RECIPIENT, AMOUNT / 2));
        assertEq(ah.getAllowed(operator, OWNER, token), 0);
    }

    function testPermitUnauthorisedOperator() public {
        ah.setAllowed(OPERATOR, OWNER, TOKEN, AMOUNT);

        vm.expectRevert();
        ah.transferFrom(TOKEN, OWNER, RECIPIENT, AMOUNT);
    }

    function testPermitUnauthorisedAmount() public {
        address token = address(new FallbackDummy());
        address operator = address(this);

        ah.setAllowed(operator, OWNER, token, AMOUNT);

        vm.expectRevert();
        ah.transferFrom(token, OWNER, RECIPIENT, AMOUNT + 1);
    }

    function testPermitUnauthorisedToken() public {
        address token = address(new FallbackDummy());
        address operator = address(this);

        ah.setAllowed(operator, OWNER, token, AMOUNT);

        vm.expectRevert();
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
        address token = address(new FallbackDummy());
        address target = address(new FallbackDummy());
        address operator = target;
        uint256 value = 999;

        bytes memory data = hex"deadbeef";

        vm.startStateDiffRecording();
        ah.exec{value: value}(operator, token, AMOUNT, payable(target), data);
        VmSafe.AccountAccess[] memory calls =
            _foundry_filterAccessKind(vm.stopAndReturnStateDiff(), VmSafe.AccountAccessKind.Call);

        // First Call is to AllowanceHolder with the `execute` calldata
        // Second Call is to the Target with the `data`
        // We test that the msg.sender is passed along appended to `data`
        assertEq(calls[1].account, target);
        assertEq(calls[1].data, abi.encodePacked(data, address(this)));
        assertEq(calls[1].value, value);
    }

    /// @dev Utility to filter the AccountAccess[] to just the particular kind we want
    function _foundry_filterAccessKind(VmSafe.AccountAccess[] memory accesses, VmSafe.AccountAccessKind kind)
        public
        pure
        returns (VmSafe.AccountAccess[] memory filtered)
    {
        filtered = new VmSafe.AccountAccess[](accesses.length);
        uint256 count = 0;

        for (uint256 i = 0; i < accesses.length; i++) {
            if (accesses[i].kind == kind) {
                filtered[count] = accesses[i];
                count++;
            }
        }

        assembly {
            // Resize the array
            mstore(filtered, count)
        }
    }
}
