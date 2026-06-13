// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

import {LnTest} from "../../0.8.34/Ln.t.sol";
import {FormalModelFFI} from "./FormalModelFFI.t.sol";
import {LnWrapper} from "src/wrappers/LnWrapper.sol";

/// @dev Runs the LnTest suite against the generated Lean model via `vm.ffi`,
/// and differentially fuzzes the model against the real contract. Requires
/// the `ln-model` binary to be pre-built:
///   cd formal/ln/LnProof && lake build ln-model
contract LnModelTest is LnTest, FormalModelFFI {
    string private constant _BIN = "formal/ln/LnProof/.lake/build/bin/ln-model";
    LnWrapper private _wrapper;

    function setUp() external {
        _wrapper = new LnWrapper();
    }

    function _lnWadToRay(int256 x) internal override returns (int256) {
        return int256(_ffiScalar(_BIN, "ln_wad", uint256(x)));
    }

    /// The generated model strips the revert guard (it models the non-reverting
    /// domain), so the revert behavior is exercised against the real contract.
    function testLnWadUndefined() external override {
        vm.expectRevert(LnWadUndefined.selector);
        _wrapper.wrap_lnWadToRay(0);
        vm.expectRevert(LnWadUndefined.selector);
        _wrapper.wrap_lnWadToRay(-1);
        vm.expectRevert(LnWadUndefined.selector);
        _wrapper.wrap_lnWad(type(int256).min);
    }

    function testDiffLnWad(int256 x) external {
        x = bound(x, 1, type(int256).max);
        assertEq(_wrapper.wrap_lnWadToRay(x), int256(_ffiScalar(_BIN, "ln_wad", uint256(x))));
    }

    function testDiffLnWadToWad(int256 x) external {
        x = bound(x, 1, type(int256).max);
        assertEq(_wrapper.wrap_lnWad(x), int256(_ffiScalar(_BIN, "ln_wad_to_wad", uint256(x))));
    }
}
