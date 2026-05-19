// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {CbrtTest} from "../Cbrt.t.sol";
import {FormalModelFFI} from "./FormalModelFFI.t.sol";
import {CbrtWrapper} from "src/wrappers/CbrtWrapper.sol";

/// @dev Runs the CbrtTest fuzz suite against the generated Lean model
/// via `vm.ffi`. Requires the `cbrt-model` binary to be pre-built:
///   cd formal/cbrt/CbrtProof && lake build cbrt-model
contract CbrtModelTest is CbrtTest, FormalModelFFI {
    string private constant _BIN = "formal/cbrt/CbrtProof/.lake/build/bin/cbrt-model";
    CbrtWrapper private _wrapper;

    function setUp() external {
        _wrapper = new CbrtWrapper();
    }

    function _cbrtFloor(uint256 x) internal override returns (uint256) {
        return _ffiScalar(_BIN, "cbrt_floor", x);
    }

    function _cbrtUp(uint256 x) internal override returns (uint256) {
        return _ffiScalar(_BIN, "cbrt_up", x);
    }

    function testDiffCbrtFloor(uint256 x) external {
        assertEq(_wrapper.wrap_cbrt(x), _ffiScalar(_BIN, "cbrt_floor", x));
    }

    function testDiffCbrtUp(uint256 x) external {
        assertEq(_wrapper.wrap_cbrtUp(x), _ffiScalar(_BIN, "cbrt_up", x));
    }
}
