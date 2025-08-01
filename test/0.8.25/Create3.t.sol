// SPDX-License-Identifier: MIT
pragma solidity 0.8.25;

import "@forge-std/Test.sol";

import {Create3} from "src/utils/Create3.sol";

contract Dummy {}

contract Create3Test is Test {
    function testCreate3() public {
        bytes32 salt = bytes32(uint256(1));
        address predicted = Create3.predict(salt);
        assertEq(Create3.createFromMemory(salt, type(Dummy).creationCode), predicted);
        assertNotEq(predicted.code.length, 0);
    }
}
