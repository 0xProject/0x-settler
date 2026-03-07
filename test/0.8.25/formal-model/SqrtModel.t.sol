// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SqrtTest} from "../Sqrt.t.sol";
import {FormalModelFFI} from "./FormalModelFFI.t.sol";
import {SqrtWrapper} from "src/wrappers/SqrtWrapper.sol";

/// @dev Runs the SqrtTest fuzz suite against the generated Lean model
/// via `vm.ffi`. Requires the `sqrt-model` binary to be pre-built:
///   cd formal/sqrt/SqrtProof && lake build sqrt-model
contract SqrtModelTest is SqrtTest, FormalModelFFI {
    string private constant _BIN = "formal/sqrt/SqrtProof/.lake/build/bin/sqrt-model";
    SqrtWrapper private _wrapper;

    function setUp() external {
        _wrapper = new SqrtWrapper();
    }

    function _sqrtFloor(uint256 x) internal override returns (uint256) {
        return _ffiScalar(_BIN, "sqrt_floor", x);
    }

    function _sqrtUp(uint256 x) internal override returns (uint256) {
        return _ffiScalar(_BIN, "sqrt_up", x);
    }

    function testDiffSqrtFloor(uint256 x) external {
        assertEq(_wrapper.wrap_sqrt(x), _ffiScalar(_BIN, "sqrt_floor", x));
    }

    function testDiffSqrtUp(uint256 x) external {
        assertEq(_wrapper.wrap_sqrtUp(x), _ffiScalar(_BIN, "sqrt_up", x));
    }
}
