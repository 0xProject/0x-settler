// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SqrtTest} from "../Sqrt.t.sol";

/// @dev Runs the SqrtTest fuzz suite against the generated Lean model
/// via `vm.ffi`. Requires the `sqrt-model` binary to be pre-built:
///   cd formal/sqrt/SqrtProof && lake build sqrt-model
contract SqrtModelTest is SqrtTest {
    string private constant _BIN = "formal/sqrt/SqrtProof/.lake/build/bin/sqrt-model";

    function _ffi(string memory fn, uint256 x) private returns (uint256) {
        string[] memory args = new string[](3);
        args[0] = _BIN;
        args[1] = fn;
        args[2] = vm.toString(bytes32(x));
        bytes memory result = vm.ffi(args);
        return abi.decode(result, (uint256));
    }

    function _sqrtFloor(uint256 x) internal override returns (uint256) {
        return _ffi("sqrt_floor", x);
    }

    function _sqrtUp(uint256 x) internal override returns (uint256) {
        return _ffi("sqrt_up", x);
    }
}
