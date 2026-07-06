// SPDX-License-Identifier: MIT
pragma solidity 0.8.17;

import {Permit2Artifact} from "./Permit2Artifact.sol";

// Forces Permit2 artifact compilation for tests that deploy it by contract name.
contract SelectPermit2ArtifactBuildShim is Permit2Artifact {
    function test_selectPermit2ArtifactBuildShim() external pure {}
}
