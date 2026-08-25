// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {MainnetSettler} from "src/chains/Mainnet/TakerSubmitted.sol";
import {Shortfall} from "src/core/SettlerErrors.sol";

contract MainnetSelectDispatchTest is Test {
    MainnetSettler private settler;

    function setUp() public {
        vm.mockCall(
            0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48, abi.encodeCall(IERC20.decimals, ()), abi.encode(uint8(6))
        );
        vm.mockCall(
            0xdAC17F958D2ee523a2206206994597C13D831ec7, abi.encodeCall(IERC20.decimals, ()), abi.encode(uint8(6))
        );
        settler = new MainnetSettler(bytes20(0));
    }

    function _select(uint256 target) private pure returns (bytes[] memory actions) {
        bytes[] memory candidate = new bytes[](0);
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = candidate;
        uint256[] memory targets = new uint256[](1);
        targets[0] = target;

        actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.SELECT, (0, address(0), targets, candidates));
    }

    function _execute(bytes[] memory actions) private {
        ISettlerBase.AllowedSlippage memory slippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(this)), buyToken: IERC20(address(0)), minAmountOut: 0
        });
        settler.execute(slippage, actions, bytes32(0));
    }

    function test_mainnetSelect_emptyCandidate_commits() public {
        bytes[] memory actions = _select(0);

        vm.recordLogs();
        _execute(actions);

        // Success plus silence: an unwired SELECT reverts ActionInvalid, and a commit logs nothing.
        assertEq(vm.getRecordedLogs().length, 0, "no logs");
    }

    function test_mainnetSelect_unmetTarget_revertsShortfall() public {
        bytes[] memory actions = _select(1);

        vm.expectRevert(abi.encodeWithSelector(Shortfall.selector, 0));
        _execute(actions);
    }
}
