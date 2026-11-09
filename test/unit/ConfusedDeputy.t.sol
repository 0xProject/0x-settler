// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {Test} from "@forge-std/Test.sol";

import {BaseSettler} from "src/chains/Base/TakerSubmitted.sol";
import {PERMIT2} from "src/core/Permit2Payment.sol";
import {ConfusedDeputy} from "src/core/SettlerErrors.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

contract ConfusedDeputyTest is Test {
    BaseSettler internal settler;

    function setUp() public {
        settler = BaseSettler(payable(deployCode("TakerSubmitted.sol:BaseSettler", abi.encode(bytes20(0)))));
    }

    /// @dev The pool is rejected before tokens move, so the call can be empty.
    function test_Basic_RestrictedPermit2_Reverts() public {
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.BASIC, (address(0), 0, address(PERMIT2), 0, bytes("")));

        vm.expectRevert(ConfusedDeputy.selector);
        settler.execute(ISettlerBase.AllowedSlippage(payable(address(0)), IERC20(address(0)), 0), actions, bytes32(0));
    }
}
