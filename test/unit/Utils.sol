// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {Vm} from "@forge-std/Vm.sol";

contract RejectionFallbackDummy {
    fallback() external payable {
        revert("Rejected");
    }
}

contract Utils {
    Vm internal constant _vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function _deterministicAddress(string memory name) internal returns (address a) {
        a = address(bytes20(keccak256(abi.encodePacked(name))));
        _vm.label(a, name);
    }

    function _createNamedRejectionDummy(string memory name) internal returns (address a) {
        a = address(new RejectionFallbackDummy());
        _vm.label(a, name);
    }

    function _etchNamedRejectionDummy(string memory name, address a) internal returns (address) {
        _vm.etch(a, type(RejectionFallbackDummy).runtimeCode);
        _vm.label(a, name);
        return a;
    }

    function _mockExpectCall(address callee, bytes memory data, bytes memory returnData) internal {
        _vm.mockCall(callee, data, returnData);
        _vm.expectCall(callee, data);
    }

    function _mockExpectCall(address callee, uint256 value, bytes memory data, bytes memory returnData) internal {
        _vm.mockCall(callee, value, data, returnData);
        _vm.expectCall(callee, value, data);
    }
}
