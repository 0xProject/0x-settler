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
        IAllowanceHolder.TransferDetails[] memory transferDetails = new IAllowanceHolder.TransferDetails[](1);
        transferDetails[0] = IAllowanceHolder.TransferDetails(token, RECIPIENT, AMOUNT);

        assertEq(ah.getAllowed(operator, OWNER, token), AMOUNT);
        assertTrue(ah.holderTransferFrom(OWNER, transferDetails));
        assertEq(ah.getAllowed(operator, OWNER, token), 0);
    }

    function testPermitAuthorisedMultipleConsumption() public {
        address token = address(new FallbackDummy());
        address operator = address(this);

        ah.setAllowed(operator, OWNER, token, AMOUNT);
        IAllowanceHolder.TransferDetails[] memory transferDetails = new IAllowanceHolder.TransferDetails[](1);
        transferDetails[0] = IAllowanceHolder.TransferDetails(token, RECIPIENT, AMOUNT / 2);

        assertEq(ah.getAllowed(operator, OWNER, token), AMOUNT);
        assertTrue(ah.holderTransferFrom(OWNER, transferDetails));
        assertEq(ah.getAllowed(operator, OWNER, token), AMOUNT / 2);
        assertTrue(ah.holderTransferFrom(OWNER, transferDetails));
        assertEq(ah.getAllowed(operator, OWNER, token), 0);
    }

    function testPermitUnauthorisedOperator() public {
        ah.setAllowed(OPERATOR, OWNER, TOKEN, AMOUNT);
        IAllowanceHolder.TransferDetails[] memory transferDetails = new IAllowanceHolder.TransferDetails[](1);
        transferDetails[0] = IAllowanceHolder.TransferDetails({token: TOKEN, recipient: RECIPIENT, amount: AMOUNT});

        vm.expectRevert();
        ah.holderTransferFrom(OWNER, transferDetails);
    }

    function testPermitUnauthorisedAmount() public {
        address token = address(new FallbackDummy());
        address operator = address(this);

        ah.setAllowed(operator, OWNER, token, AMOUNT);
        IAllowanceHolder.TransferDetails[] memory transferDetails = new IAllowanceHolder.TransferDetails[](1);
        transferDetails[0] = IAllowanceHolder.TransferDetails({token: token, recipient: RECIPIENT, amount: AMOUNT + 1});

        vm.expectRevert();
        ah.holderTransferFrom(OWNER, transferDetails);
    }

    function testPermitUnauthorisedToken() public {
        address token = address(new FallbackDummy());
        address operator = address(this);

        ah.setAllowed(operator, OWNER, token, AMOUNT);
        IAllowanceHolder.TransferDetails[] memory transferDetails = new IAllowanceHolder.TransferDetails[](1);
        transferDetails[0] = IAllowanceHolder.TransferDetails({token: TOKEN, recipient: RECIPIENT, amount: AMOUNT});

        vm.expectRevert();
        ah.holderTransferFrom(OWNER, transferDetails);
    }

    function testPermitAuthorisedStorageKey() public {
        vm.record();
        ah.setAllowed(OPERATOR, OWNER, TOKEN, AMOUNT);
        (bytes32[] memory reads, bytes32[] memory writes) = vm.accesses(address(ah));

        // Authorisation key is calculated as keccak(oeprator, owner, token)
        bytes32 key = keccak256(abi.encode(OPERATOR, OWNER, TOKEN));
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

        ISignatureTransfer.TokenPermissions[] memory permits = new ISignatureTransfer.TokenPermissions[](1);
        permits[0] = ISignatureTransfer.TokenPermissions({token: token, amount: AMOUNT});
        bytes memory data = hex"deadbeef";

        vm.startStateDiffRecording();
        ah.execute{value: value}(operator, permits, payable(target), data);
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
