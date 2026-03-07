// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Vm} from "@forge-std/Vm.sol";

abstract contract FormalModelFFI {
    Vm internal constant _vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function _ffiScalar(string memory bin, string memory fn, uint256 x) internal returns (uint256) {
        string[] memory args = new string[](3);
        args[0] = bin;
        args[1] = fn;
        args[2] = _vm.toString(bytes32(x));
        bytes memory result = _vm.ffi(args);
        return abi.decode(result, (uint256));
    }

    function _ffiWord512(string memory bin, string memory fn, uint256 x_hi, uint256 x_lo)
        internal
        returns (uint256)
    {
        string[] memory args = new string[](4);
        args[0] = bin;
        args[1] = fn;
        args[2] = _vm.toString(bytes32(x_hi));
        args[3] = _vm.toString(bytes32(x_lo));
        bytes memory result = _vm.ffi(args);
        return abi.decode(result, (uint256));
    }

    function _ffiPair512(string memory bin, string memory fn, uint256 x_hi, uint256 x_lo)
        internal
        returns (uint256, uint256)
    {
        string[] memory args = new string[](4);
        args[0] = bin;
        args[1] = fn;
        args[2] = _vm.toString(bytes32(x_hi));
        args[3] = _vm.toString(bytes32(x_lo));
        bytes memory result = _vm.ffi(args);
        return abi.decode(result, (uint256, uint256));
    }
}
