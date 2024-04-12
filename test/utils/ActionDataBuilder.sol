// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {LibBytes} from "./LibBytes.sol";

// Sorry you had to see this

library ActionDataBuilder {
    using LibBytes for bytes;

    function build(bytes memory a) internal pure returns (bytes[] memory) {
        bytes[] memory datas = new bytes[](1);
        datas[0] = a;
        return datas;
    }

    function build(bytes memory a, bytes memory b) internal pure returns (bytes[] memory) {
        bytes[] memory datas = new bytes[](2);
        datas[0] = a;
        datas[1] = b;
        return datas;
    }

    function build(bytes memory a, bytes memory b, bytes memory c) internal pure returns (bytes[] memory) {
        bytes[] memory datas = new bytes[](3);
        datas[0] = a;
        datas[1] = b;
        datas[2] = c;
        return datas;
    }

    function build(bytes memory a, bytes memory b, bytes memory c, bytes memory d)
        internal
        pure
        returns (bytes[] memory)
    {
        bytes[] memory datas = new bytes[](4);
        datas[0] = a;
        datas[1] = b;
        datas[2] = c;
        datas[3] = d;
        return datas;
    }

    function build(bytes memory a, bytes memory b, bytes memory c, bytes memory d, bytes memory e)
        internal
        pure
        returns (bytes[] memory)
    {
        bytes[] memory datas = new bytes[](5);
        datas[0] = a;
        datas[1] = b;
        datas[2] = c;
        datas[3] = d;
        datas[4] = e;
        return datas;
    }

    function build(bytes memory a, bytes memory b, bytes memory c, bytes memory d, bytes memory e, bytes memory f)
        internal
        pure
        returns (bytes[] memory)
    {
        bytes[] memory datas = new bytes[](6);
        datas[0] = a;
        datas[1] = b;
        datas[2] = c;
        datas[3] = d;
        datas[4] = e;
        datas[5] = f;
        return datas;
    }

    function build(
        bytes memory a,
        bytes memory b,
        bytes memory c,
        bytes memory d,
        bytes memory e,
        bytes memory f,
        bytes memory g
    ) internal pure returns (bytes[] memory) {
        bytes[] memory datas = new bytes[](7);
        datas[0] = a;
        datas[1] = b;
        datas[2] = c;
        datas[3] = d;
        datas[4] = e;
        datas[5] = f;
        datas[6] = g;
        return datas;
    }
}
