// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {Test} from "@forge-std/Test.sol";

import {IMultiCall, MultiCallContext} from "src/multicall/MultiCallContext.sol";
import {ItoA} from "src/utils/ItoA.sol";

contract Echo {
    fallback(bytes calldata data) external returns (bytes memory) {
        return data;
    }
}

contract Payable {
    event Paid(uint256 value);

    fallback(bytes calldata data) external payable returns (bytes memory) {
        emit Paid(msg.value);
        return data;
    }
}

contract Reject {
    fallback() external payable {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            calldatacopy(ptr, 0x00, calldatasize())
            revert(ptr, calldatasize())
        }
    }
}

contract OOG {
    fallback() external payable {
        assembly ("memory-safe") {
            invalid()
        }
    }
}

contract Empty {
    fallback() external payable {
        assembly ("memory-safe") {
            stop()
        }
    }
}

contract MsgSenderEcho is MultiCallContext {
    fallback() external payable {
        address msgSender = _msgSender();
        assembly ("memory-safe") {
            mstore(0x00, msgSender)
            return(0x0c, 0x14)
        }
    }
}

contract MultiCallTest is Test {
    IMultiCall multicall;
    Echo echo;
    Payable payable_;
    Reject reject;
    OOG oog;
    Empty empty;
    MsgSenderEcho senderEcho;

    uint256 internal constant contextdepth = 4;

    function setUp() external {
        bytes32 salt = 0x0000000000000000000000000000000000000031a5e6991d522b26211cf840ce;
        bytes memory initcode = vm.getCode("MultiCall.sol:MultiCall");
        assertEq(keccak256(initcode), 0x92cb7a4e0928b80f225369f560682dde07adc172db616138e522eaf7278c109a);
        vm.chainId(1);
        (bool success, bytes memory returndata) =
            0x4e59b44847b379578588920cA78FbF26c0B4956C.call(bytes.concat(salt, initcode));
        require(success);
        multicall = IMultiCall(payable(address(uint160(bytes20(returndata)))));
        vm.chainId(31337);
        assert(address(multicall).code.length > 0);
        assert(address(multicall) == 0x00000000000000CF9E3c5A26621af382fA17f24f);

        echo = new Echo();
        payable_ = new Payable();
        reject = new Reject();
        oog = new OOG();
        senderEcho = new MsgSenderEcho();

        assembly ("memory-safe") {
            mstore(0x00, 0x60016000f3)
            sstore(empty.slot, create(0x00, 0x1b, 0x05))
        }
        assertEq(address(empty).code, hex"00");
    }

    function testSimple() external {
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](2);
        IMultiCall.Call memory call_ = calls[0];
        call_.target = payable(address(echo));
        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;
        call_.data = "Hello, World!";
        call_ = calls[1];
        call_.target = payable(address(reject));
        call_.revertPolicy = IMultiCall.RevertPolicy.CONTINUE;
        call_.data = "Go away!";

        IMultiCall.Result[] memory result = multicall.multicall(calls, contextdepth);
        assertEq(result.length, calls.length);
        assertTrue(result[0].success);
        assertEq(result[0].data, bytes.concat("Hello, World!", bytes20(uint160(address(this)))));
        assertFalse(result[1].success);
        assertEq(result[1].data, bytes.concat("Go away!", bytes20(uint160(address(this)))));
    }

    function testAbiEncoding() external {
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](2);
        IMultiCall.Call memory call_ = calls[0];
        call_.target = payable(address(echo));
        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;
        call_.data = "Hello, World!";
        call_ = calls[1];
        call_.target = payable(address(reject));
        call_.revertPolicy = IMultiCall.RevertPolicy.CONTINUE;
        call_.data = "Go away!";

        bytes memory data = abi.encodeCall(multicall.multicall, (calls, contextdepth));
        bool success;
        (success, data) = address(multicall).call(data);
        assertTrue(success);
        assertNotEq(abi.encode(abi.decode(data, (IMultiCall.Result[]))), data);
    }

    function testContinue() external {
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](3);
        IMultiCall.Call memory call_ = calls[0];
        call_.target = payable(address(echo));
        call_.data = "Hello, World!";
        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;
        call_ = calls[1];
        call_.target = payable(address(reject));
        call_.revertPolicy = IMultiCall.RevertPolicy.CONTINUE;
        call_.data = "Go away!";
        call_ = calls[2];
        call_.target = payable(address(echo));
        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;
        call_.data = "Hello, Again!";

        IMultiCall.Result[] memory result = multicall.multicall(calls, contextdepth);
        assertEq(result.length, calls.length);
        assertTrue(result[0].success);
        assertEq(result[0].data, bytes.concat("Hello, World!", bytes20(uint160(address(this)))));
        assertFalse(result[1].success);
        assertEq(result[1].data, bytes.concat("Go away!", bytes20(uint160(address(this)))));
        assertTrue(result[2].success);
        assertEq(result[2].data, bytes.concat("Hello, Again!", bytes20(uint160(address(this)))));
    }

    function testStop() external {
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](3);
        IMultiCall.Call memory call_ = calls[0];
        call_.target = payable(address(echo));
        call_.data = "Hello, World!";
        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;
        call_ = calls[1];
        call_.target = payable(address(reject));
        call_.revertPolicy = IMultiCall.RevertPolicy.HALT;
        call_.data = "Go away!";
        call_ = calls[2];
        call_.target = payable(address(echo));
        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;
        call_.data = "Hello, Again!";

        IMultiCall.Result[] memory result = multicall.multicall(calls, contextdepth);
        assertEq(result.length, calls.length - 1);
        assertTrue(result[0].success);
        assertEq(result[0].data, bytes.concat("Hello, World!", bytes20(uint160(address(this)))));
        assertFalse(result[1].success);
        assertEq(result[1].data, bytes.concat("Go away!", bytes20(uint160(address(this)))));
    }

    function testRevert() external {
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](3);
        IMultiCall.Call memory call_ = calls[0];
        call_.target = payable(address(echo));
        call_.data = "Hello, World!";
        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;
        call_ = calls[1];
        call_.target = payable(address(reject));
        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;
        call_.data = "Go away!";
        call_ = calls[2];
        call_.target = payable(address(echo));
        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;
        call_.data = "Hello, Again!";

        bytes memory data = abi.encodeCall(multicall.multicall, (calls, contextdepth));
        (bool success, bytes memory returndata) = address(multicall).call(data);
        assertFalse(success);
        assertEq(returndata, bytes.concat("Go away!", bytes20(uint160(address(this)))));
    }

    function testOOGSimple() external {
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](2);
        IMultiCall.Call memory call_ = calls[0];
        call_.target = payable(address(echo));
        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;
        call_.data = "Hello, World!";
        call_ = calls[1];
        call_.target = payable(oog);
        call_.revertPolicy = IMultiCall.RevertPolicy.CONTINUE;
        call_.data = "";

        // Can't use `vm.expectRevert` here. It does weird things with gas.
        bytes memory data = abi.encodeCall(multicall.multicall, (calls, contextdepth));
        uint256 gasBefore = gasleft();
        (bool success, bytes memory returndata) = address(multicall).call(data);
        uint256 gasAfter = gasleft();
        assertFalse(success);
        assertEq(returndata.length, 0);
        assertLe(gasAfter, gasBefore >> 6);
    }

    function testOOGReverse() external {
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](2);
        IMultiCall.Call memory call_ = calls[0];
        call_.target = payable(oog);
        call_.revertPolicy = IMultiCall.RevertPolicy.CONTINUE;
        call_.data = "";
        call_ = calls[1];
        call_.target = payable(address(echo));
        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;
        call_.data = "Hello, World!";

        // Can't use `vm.expectRevert` here. It does weird things with gas.
        bytes memory data = abi.encodeCall(multicall.multicall, (calls, contextdepth));
        uint256 gasBefore = gasleft();
        (bool success, bytes memory returndata) = address(multicall).call(data);
        uint256 gasAfter = gasleft();
        assertFalse(success);
        assertEq(returndata.length, 0);
        assertLe(gasAfter, gasBefore >> 6);
    }

    function testMany() external {
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](1024);
        for (uint256 i; i < 1024; i++) {
            IMultiCall.Call memory call_ = calls[i];
            call_.target = payable(address(echo));
            call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;
            call_.data = bytes(ItoA.itoa(i));
        }
        IMultiCall.Result[] memory result = multicall.multicall(calls, contextdepth);
        assertEq(result.length, calls.length);
        for (uint256 i; i < 1024; i++) {
            IMultiCall.Result memory r = result[i];
            assertTrue(r.success);
            bytes memory expected = bytes(ItoA.itoa(i));
            if (expected.length >= 4) {
                expected = bytes.concat(expected, bytes20(uint160(address(this))));
            }
            assertEq(r.data, expected);
        }
    }

    function testPayable() external {
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](1);
        IMultiCall.Call memory call_ = calls[0];
        call_.target = payable(payable_);
        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;
        call_.value = 1 ether;
        call_.data = "Hello, World!";

        vm.expectEmit(true, false, false, true, address(payable_));
        emit Payable.Paid(1 ether);

        IMultiCall.Result[] memory result = multicall.multicall{value: 1 ether}(calls, contextdepth);
        assertEq(result.length, 1);
        assertTrue(result[0].success);
        assertEq(result[0].data, bytes.concat("Hello, World!", bytes20(uint160(address(this)))));
    }

    function testPayableMulti() external {
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](2);
        IMultiCall.Call memory call_ = calls[0];
        call_.target = payable(payable_);
        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;
        call_.value = 1 ether;
        call_.data = "Hello, World!";
        call_ = calls[1];
        call_.target = payable(address(echo));
        call_.revertPolicy = IMultiCall.RevertPolicy.CONTINUE;
        call_.value = 1 ether;
        call_.data = "Hello, Again!";

        vm.expectEmit(true, false, false, true, address(payable_));
        emit Payable.Paid(1 ether);

        IMultiCall.Result[] memory result = multicall.multicall{value: 2 ether}(calls, contextdepth);
        assertEq(result.length, 2);
        assertTrue(result[0].success);
        assertEq(result[0].data, bytes.concat("Hello, World!", bytes20(uint160(address(this)))));
        assertFalse(result[1].success);
        assertEq(result[1].data, "");

        assertEq(address(multicall).balance, 1 ether);
    }

    function testPayableNotEnoughValue() external {
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](2);
        IMultiCall.Call memory call_ = calls[0];
        call_.target = payable(payable_);
        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;
        call_.value = 1 ether;
        call_.data = "Hello, World!";
        call_ = calls[1];
        call_.target = payable(payable_);
        call_.revertPolicy = IMultiCall.RevertPolicy.CONTINUE;
        call_.value = 1 ether;
        call_.data = "Hello, Again!";

        vm.expectEmit(true, false, false, true, address(payable_));
        emit Payable.Paid(1 ether);

        IMultiCall.Result[] memory result = multicall.multicall{value: 1 ether}(calls, contextdepth);
        assertEq(result.length, 2);
        assertTrue(result[0].success);
        assertEq(result[0].data, bytes.concat("Hello, World!", bytes20(uint160(address(this)))));
        assertFalse(result[1].success);
        assertEq(result[1].data, "");

        assertEq(address(multicall).balance, 0 ether);
    }

    function testReceieveEth() external {
        (bool success, bytes memory returndata) = address(multicall).call{value: 1 ether}("");
        assertTrue(success);
        assertEq(returndata, "");
    }

    function testReceiveEthGas() external {
        payable(multicall).transfer(1 ether);
    }

    function testRecursion() external {
        IMultiCall.Call[] memory callsInner = new IMultiCall.Call[](1);
        IMultiCall.Call memory call_ = callsInner[0];
        call_.target = payable(address(reject));
        call_.revertPolicy = IMultiCall.RevertPolicy.CONTINUE;
        call_.data = "Go away!";
        IMultiCall.Call[] memory callsOuter = new IMultiCall.Call[](1);
        call_ = callsOuter[0];
        call_.target = payable(multicall);
        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;
        call_.data = abi.encodeCall(IMultiCall.multicall, (callsInner, contextdepth));

        IMultiCall.Result[] memory resultOuter = multicall.multicall(callsOuter, contextdepth);

        assertEq(resultOuter.length, 1);
        assertTrue(resultOuter[0].success);

        IMultiCall.Result[] memory resultInner = abi.decode(resultOuter[0].data, (IMultiCall.Result[]));
        assertEq(resultInner.length, 1);
        assertFalse(resultInner[0].success);
        assertEq(resultInner[0].data, bytes.concat("Go away!", bytes20(uint160(address(this)))));
    }

    function testSendEthAndNoDataToEoa() external {
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](1);
        IMultiCall.Call memory call_ = calls[0];
        call_.target = payable(address(0xdead));
        call_.revertPolicy = IMultiCall.RevertPolicy.HALT;
        call_.value = 1 ether;
        call_.data = "";

        IMultiCall.Result[] memory result = multicall.multicall{value: 1 ether}(calls, contextdepth);

        assertEq(result.length, 1);
        assertTrue(result[0].success);
        assertEq(result[0].data, "");

        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;

        result = multicall.multicall{value: 1 ether}(calls, contextdepth);

        assertEq(result.length, 1);
        assertTrue(result[0].success);
        assertEq(result[0].data, "");
    }

    function testSendEthAndDataToEoa() external {
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](1);
        IMultiCall.Call memory call_ = calls[0];
        call_.target = payable(address(0xdead));
        call_.revertPolicy = IMultiCall.RevertPolicy.HALT;
        call_.value = 1 ether;
        call_.data = "Hello, World!";

        vm.expectRevert(bytes(""));
        multicall.multicall{value: 1 ether}(calls, contextdepth);

        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;

        vm.expectRevert(bytes(""));
        multicall.multicall{value: 1 ether}(calls, contextdepth);
    }

    function testSendDataAndNoEthToEoa() external {
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](1);
        IMultiCall.Call memory call_ = calls[0];
        call_.target = payable(address(0xdead));
        call_.revertPolicy = IMultiCall.RevertPolicy.HALT;
        call_.value = 0 ether;
        call_.data = "Hello, World!";

        vm.expectRevert(bytes(""));
        multicall.multicall{value: 1 ether}(calls, contextdepth);

        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;

        vm.expectRevert(bytes(""));
        multicall.multicall{value: 1 ether}(calls, contextdepth);
    }

    function testSendNoEthAndNoDataToEoa() external {
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](1);
        IMultiCall.Call memory call_ = calls[0];
        call_.target = payable(address(0xdead));
        call_.revertPolicy = IMultiCall.RevertPolicy.HALT;
        call_.value = 0 ether;
        call_.data = "";

        vm.expectRevert(bytes(""));
        multicall.multicall{value: 1 ether}(calls, contextdepth);

        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;

        vm.expectRevert(bytes(""));
        multicall.multicall{value: 1 ether}(calls, contextdepth);
    }

    function testSendEthAndNoDataToEmpty() external {
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](1);
        IMultiCall.Call memory call_ = calls[0];
        call_.target = payable(empty);
        call_.revertPolicy = IMultiCall.RevertPolicy.HALT;
        call_.value = 1 ether;
        call_.data = "";

        IMultiCall.Result[] memory result = multicall.multicall{value: 1 ether}(calls, contextdepth);

        assertEq(result.length, 1);
        assertTrue(result[0].success);
        assertEq(result[0].data, "");

        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;

        result = multicall.multicall{value: 1 ether}(calls, contextdepth);

        assertEq(result.length, 1);
        assertTrue(result[0].success);
        assertEq(result[0].data, "");
    }

    function testSendEthAndDataToEmpty() external {
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](1);
        IMultiCall.Call memory call_ = calls[0];
        call_.target = payable(empty);
        call_.revertPolicy = IMultiCall.RevertPolicy.HALT;
        call_.value = 1 ether;
        call_.data = "Hello, World!";

        IMultiCall.Result[] memory result = multicall.multicall{value: 1 ether}(calls, contextdepth);

        assertEq(result.length, 1);
        assertTrue(result[0].success);
        assertEq(result[0].data, "");

        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;

        result = multicall.multicall{value: 1 ether}(calls, contextdepth);

        assertEq(result.length, 1);
        assertTrue(result[0].success);
        assertEq(result[0].data, "");
    }

    function testSendDataAndNoEthToEmpty() external {
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](1);
        IMultiCall.Call memory call_ = calls[0];
        call_.target = payable(empty);
        call_.revertPolicy = IMultiCall.RevertPolicy.HALT;
        call_.value = 0 ether;
        call_.data = "Hello, World!";

        IMultiCall.Result[] memory result = multicall.multicall{value: 1 ether}(calls, contextdepth);

        assertEq(result.length, 1);
        assertTrue(result[0].success);
        assertEq(result[0].data, "");

        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;

        result = multicall.multicall{value: 1 ether}(calls, contextdepth);

        assertEq(result.length, 1);
        assertTrue(result[0].success);
        assertEq(result[0].data, "");
    }

    function testSendNoEthAndNoDataToEmpty() external {
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](1);
        IMultiCall.Call memory call_ = calls[0];
        call_.target = payable(empty);
        call_.revertPolicy = IMultiCall.RevertPolicy.HALT;
        call_.value = 0 ether;
        call_.data = "";

        IMultiCall.Result[] memory result = multicall.multicall{value: 1 ether}(calls, contextdepth);

        assertEq(result.length, 1);
        assertTrue(result[0].success);
        assertEq(result[0].data, "");

        call_.revertPolicy = IMultiCall.RevertPolicy.REVERT;

        result = multicall.multicall{value: 1 ether}(calls, contextdepth);

        assertEq(result.length, 1);
        assertTrue(result[0].success);
        assertEq(result[0].data, "");
    }

    function testMultiCallContext() external {
        (bool success, bytes memory returndata) = address(senderEcho).call("");
        assertTrue(success);
        assertEq(returndata, bytes.concat(bytes20(uint160(address(this)))));

        IMultiCall.Call[] memory calls = new IMultiCall.Call[](1);
        IMultiCall.Call memory call_ = calls[0];
        call_.target = payable(senderEcho);
        call_.revertPolicy = IMultiCall.RevertPolicy.HALT;
        call_.value = 0 ether;
        call_.data = hex"00000000";

        IMultiCall.Result[] memory result = multicall.multicall(calls, contextdepth);

        assertEq(result.length, 1);
        assertTrue(result[0].success);
        assertEq(result[0].data, bytes.concat(bytes20(uint160(address(this)))));

        call_.data = hex"000000";

        result = multicall.multicall(calls, contextdepth);

        assertEq(result.length, 1);
        assertTrue(result[0].success);
        assertEq(result[0].data, bytes.concat(bytes20(uint160(address(multicall)))));
    }
}
