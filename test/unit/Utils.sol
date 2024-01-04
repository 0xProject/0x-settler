// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {Test} from "forge-std/Test.sol";
import {Vm, VmSafe} from "forge-std/Vm.sol";

contract FallbackDummy {
    fallback() external payable {}
}

contract RejectionFallbackDummy {
    fallback() external payable {
        require(false, "Rejected");
    }
}

contract Utils {
    Vm internal constant _vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function _deterministicAddress(string memory name) internal returns (address a) {
        a = address(bytes20(keccak256(abi.encodePacked(name))));
        _vm.label(a, name);
    }

    function _createNamedDummy(string memory name) internal returns (address a) {
        a = address(new FallbackDummy());
        _vm.label(a, name);
    }

    function _createNamedRejectionDummy(string memory name) internal returns (address a) {
        a = address(new RejectionFallbackDummy());
        _vm.label(a, name);
    }

    function _mockExpectCall(address callee, bytes memory data, bytes memory returnData) internal {
        _vm.mockCall(callee, data, returnData);
        _vm.expectCall(callee, data);
    }
}
