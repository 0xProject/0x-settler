// SPDX-License-Identifier: MIT
pragma solidity 0.8.17;

import {Permit2} from "@permit2/Permit2.sol";

// Forces Permit2 artifact compilation for tests that deploy it by contract name.
contract SelectPermit2ArtifactBuildShim {
    function test_selectPermit2ArtifactBuildShim() external pure {
        assert(type(Permit2).creationCode.length != 0);
    }
}
