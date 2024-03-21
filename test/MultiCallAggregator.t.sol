// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";

import {
    MultiCallAggregator,
    IMultiCallAggregator,
    RevertDisposition,
    Call,
    Result
} from "src/utils/MultiCallAggregator.sol";
import {ItoA} from "src/utils/ItoA.sol";

contract Echo {
    fallback(bytes calldata data) external returns (bytes memory) {
        return data;
    }
}

contract Reject {
    fallback() external {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            calldatacopy(ptr, 0x00, calldatasize())
            revert(ptr, calldatasize())
        }
    }
}

contract OOG {
    fallback() external {
        assembly ("memory-safe") {
            invalid()
        }
    }
}

contract MultiCallAggregatorTest is Test {
    IMultiCallAggregator multicall;
    Echo echo;
    Reject reject;
    OOG oog;

    uint256 internal constant contextdepth = 4;

    function setUp() external {
        multicall = IMultiCallAggregator(address(new MultiCallAggregator()));
        echo = new Echo();
        reject = new Reject();
        oog = new OOG();
    }

    function testSimple() external {
        Call[] memory calls = new Call[](2);
        Call memory call_ = calls[0];
        call_.target = address(echo);
        call_.revertDisposition = RevertDisposition.REVERT;
        call_.data = "Hello, World!";
        call_ = calls[1];
        call_.target = address(reject);
        call_.revertDisposition = RevertDisposition.CONTINUE;
        call_.data = "Go away!";

        Result[] memory result = multicall.multicall(calls, contextdepth);
        assertEq(result.length, calls.length);
        assertTrue(result[0].success);
        assertEq(result[0].data, "Hello, World!");
        assertFalse(result[1].success);
        assertEq(result[1].data, "Go away!");
    }

    function testFailAbiEncoding() external {
        Call[] memory calls = new Call[](2);
        Call memory call_ = calls[0];
        call_.target = address(echo);
        call_.revertDisposition = RevertDisposition.REVERT;
        call_.data = "Hello, World!";
        call_ = calls[1];
        call_.target = address(reject);
        call_.revertDisposition = RevertDisposition.CONTINUE;
        call_.data = "Go away!";

        bytes memory data = abi.encodeCall(multicall.multicall, (calls, contextdepth));
        bool success;
        (success, data) = address(multicall).call(data);
        assertTrue(success);
        assertEq(abi.encode(abi.decode(data, (Result[]))), data);
    }

    function testContinue() external {
        Call[] memory calls = new Call[](3);
        Call memory call_ = calls[0];
        call_.target = address(echo);
        call_.data = "Hello, World!";
        call_.revertDisposition = RevertDisposition.REVERT;
        call_ = calls[1];
        call_.target = address(reject);
        call_.revertDisposition = RevertDisposition.CONTINUE;
        call_.data = "Go away!";
        call_ = calls[2];
        call_.target = address(echo);
        call_.revertDisposition = RevertDisposition.REVERT;
        call_.data = "Hello, Again!";

        Result[] memory result = multicall.multicall(calls, contextdepth);
        assertEq(result.length, calls.length);
        assertTrue(result[0].success);
        assertEq(result[0].data, "Hello, World!");
        assertFalse(result[1].success);
        assertEq(result[1].data, "Go away!");
        assertTrue(result[2].success);
        assertEq(result[2].data, "Hello, Again!");
    }

    function testStop() external {
        Call[] memory calls = new Call[](3);
        Call memory call_ = calls[0];
        call_.target = address(echo);
        call_.data = "Hello, World!";
        call_.revertDisposition = RevertDisposition.REVERT;
        call_ = calls[1];
        call_.target = address(reject);
        call_.revertDisposition = RevertDisposition.STOP;
        call_.data = "Go away!";
        call_ = calls[2];
        call_.target = address(echo);
        call_.revertDisposition = RevertDisposition.REVERT;
        call_.data = "Hello, Again!";

        Result[] memory result = multicall.multicall(calls, contextdepth);
        assertEq(result.length, calls.length - 1);
        assertTrue(result[0].success);
        assertEq(result[0].data, "Hello, World!");
        assertFalse(result[1].success);
        assertEq(result[1].data, "Go away!");
    }

    function testRevert() external {
        Call[] memory calls = new Call[](3);
        Call memory call_ = calls[0];
        call_.target = address(echo);
        call_.data = "Hello, World!";
        call_.revertDisposition = RevertDisposition.REVERT;
        call_ = calls[1];
        call_.target = address(reject);
        call_.revertDisposition = RevertDisposition.REVERT;
        call_.data = "Go away!";
        call_ = calls[2];
        call_.target = address(echo);
        call_.revertDisposition = RevertDisposition.REVERT;
        call_.data = "Hello, Again!";

        bytes memory data = abi.encodeCall(multicall.multicall, (calls, contextdepth));
        (bool success, bytes memory returndata) = address(multicall).call(data);
        assertFalse(success);
        assertEq(returndata, "Go away!");
    }

    function testOOGSimple() external {
        Call[] memory calls = new Call[](2);
        Call memory call_ = calls[0];
        call_.target = address(echo);
        call_.revertDisposition = RevertDisposition.REVERT;
        call_.data = "Hello, World!";
        call_ = calls[1];
        call_.target = address(oog);
        call_.revertDisposition = RevertDisposition.CONTINUE;
        call_.data = "";

        vm.expectRevert(new bytes(0));
        multicall.multicall(calls, contextdepth);
    }

    function testOOGReverse() external {
        Call[] memory calls = new Call[](2);
        Call memory call_ = calls[0];
        call_.target = address(oog);
        call_.revertDisposition = RevertDisposition.CONTINUE;
        call_.data = "";
        call_ = calls[1];
        call_.target = address(echo);
        call_.revertDisposition = RevertDisposition.REVERT;
        call_.data = "Hello, World!";

        vm.expectRevert(new bytes(0));
        multicall.multicall(calls, contextdepth);
    }

    function testMany() external {
        Call[] memory calls = new Call[](256);
        for (uint256 i; i < 256; i++) {
            Call memory call_ = calls[i];
            call_.target = address(echo);
            call_.revertDisposition = RevertDisposition.REVERT;
            call_.data = bytes(ItoA.itoa(i));
        }
        Result[] memory result = multicall.multicall(calls, contextdepth);
        assertEq(result.length, calls.length);
        for (uint256 i; i < 256; i++) {
            Result memory r = result[i];
            assertTrue(r.success);
            assertEq(r.data, bytes(ItoA.itoa(i)));
        }
    }
}
