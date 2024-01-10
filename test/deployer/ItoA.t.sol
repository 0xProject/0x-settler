// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {AltItoA} from "./AltItoA.sol";
import {ItoA} from "src/deployer/ItoA.sol";

import "forge-std/Test.sol";

contract ItoATest is Test {
    function testItoAFuzz(uint256 x) public {
        string memory expected = AltItoA.altItoa(x);
        string memory actual = ItoA.itoa(x);
        assertEq(keccak256(bytes(actual)), keccak256(bytes(expected)), string.concat(actual, "\n", expected));
    }
}
