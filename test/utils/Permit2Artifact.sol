// SPDX-License-Identifier: MIT
pragma solidity 0.8.17;

import {Permit2} from "@permit2/Permit2.sol";

contract Permit2Artifact {
    function permit2CreationCodeHash() external pure returns (bytes32) {
        return keccak256(type(Permit2).creationCode);
    }
}
