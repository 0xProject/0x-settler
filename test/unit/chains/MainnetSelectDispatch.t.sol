// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {Test} from "@forge-std/Test.sol";

import {ISettlerActions} from "src/ISettlerActions.sol";

contract MainnetSelectDispatchTest is Test {
    function test_productionRuntime_includesSelectDispatch() public {
        bytes memory runtime = vm.getDeployedCode("TakerSubmitted.sol:MainnetSettler");

        assertTrue(_contains(runtime, ISettlerActions.SELECT.selector), "SELECT excluded");
    }

    function test_optimismRuntime_includesSelectViaSettlerBase() public {
        bytes memory runtime = vm.getDeployedCode("TakerSubmitted.sol:OptimismSettler");

        assertTrue(_contains(runtime, ISettlerActions.SELECT.selector), "SELECT excluded on Optimism");
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
