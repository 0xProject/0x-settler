// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {LibBytes} from "./LibBytes.sol";

// Sorry you had to see this

library ActionDataBuilder {
    using LibBytes for bytes;

    function build(bytes memory a) internal pure returns (bytes[] memory) {
        bytes[] memory datas = new bytes[](1);
        datas[0] = a.popSelector();
        return datas;
    }

    function build(bytes memory a, bytes memory b) internal pure returns (bytes[] memory) {
        bytes[] memory datas = new bytes[](2);
        datas[0] = a.popSelector();
        datas[1] = b.popSelector();
        return datas;
    }

    function build(bytes memory a, bytes memory b, bytes memory c) internal pure returns (bytes[] memory) {
        bytes[] memory datas = new bytes[](3);
        datas[0] = a.popSelector();
        datas[1] = b.popSelector();
        datas[2] = c.popSelector();
        return datas;
    }

    function build(bytes memory a, bytes memory b, bytes memory c, bytes memory d)
        internal
        pure
        returns (bytes[] memory)
    {
        bytes[] memory datas = new bytes[](4);
        datas[0] = a.popSelector();
        datas[1] = b.popSelector();
        datas[2] = c.popSelector();
        datas[3] = d.popSelector();
        return datas;
    }

    function build(bytes memory a, bytes memory b, bytes memory c, bytes memory d, bytes memory e)
        internal
        pure
        returns (bytes[] memory)
    {
        bytes[] memory datas = new bytes[](5);
        datas[0] = a.popSelector();
        datas[1] = b.popSelector();
        datas[2] = c.popSelector();
        datas[3] = d.popSelector();
        datas[4] = e.popSelector();
        return datas;
    }

    function build(bytes memory a, bytes memory b, bytes memory c, bytes memory d, bytes memory e, bytes memory f)
        internal
        pure
        returns (bytes[] memory)
    {
        bytes[] memory datas = new bytes[](6);
        datas[0] = a.popSelector();
        datas[1] = b.popSelector();
        datas[2] = c.popSelector();
        datas[3] = d.popSelector();
        datas[4] = e.popSelector();
        datas[5] = f.popSelector();
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
        datas[0] = a.popSelector();
        datas[1] = b.popSelector();
        datas[2] = c.popSelector();
        datas[3] = d.popSelector();
        datas[4] = e.popSelector();
        datas[5] = f.popSelector();
        datas[6] = g.popSelector();
        return datas;
    }
}
