// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {CbrtTest} from "../Cbrt.t.sol";

/// @dev Runs the CbrtTest fuzz suite against the generated Lean model
/// via `vm.ffi`. Requires the `cbrt-model` binary to be pre-built:
///   cd formal/cbrt/CbrtProof && lake build cbrt-model
contract CbrtModelTest is CbrtTest {
    string private constant _BIN = "formal/cbrt/CbrtProof/.lake/build/bin/cbrt-model";

    function _ffi(string memory fn, uint256 x) private returns (uint256) {
        string[] memory args = new string[](3);
        args[0] = _BIN;
        args[1] = fn;
        args[2] = vm.toString(bytes32(x));
        bytes memory result = vm.ffi(args);
        return abi.decode(result, (uint256));
    }

    function _cbrtFloor(uint256 x) internal override returns (uint256) {
        return _ffi("cbrt_floor", x);
    }

    function _cbrtUp(uint256 x) internal override returns (uint256) {
        return _ffi("cbrt_up", x);
    }
}
