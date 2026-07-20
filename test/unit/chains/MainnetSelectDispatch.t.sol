// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {Test} from "@forge-std/Test.sol";

import {ISettlerActions} from "src/ISettlerActions.sol";

contract MainnetSelectDispatchTest is Test {
    function test_productionRuntime_excludesExperimentalSelectDispatch() public {
        bytes memory runtime = vm.getDeployedCode("TakerSubmitted.sol:MainnetSettler");

        assertFalse(_contains(runtime, ISettlerActions.SELECT.selector), "SELECT included");
        assertFalse(_contains(runtime, ISettlerActions.SELECT_VIP_CANDIDATES.selector), "SELECT_VIP_CANDIDATES included");
    }

    function _contains(bytes memory haystack, bytes4 needle) private pure returns (bool) {
        if (haystack.length < 4) return false;
        for (uint256 i; i <= haystack.length - 4; ++i) {
            bytes4 candidate;
            assembly ("memory-safe") {
                candidate := mload(add(add(haystack, 0x20), i))
            }
            if (candidate == needle) return true;
        }
        return false;
    }
}
