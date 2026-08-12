// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {MainnetSettler} from "src/chains/Mainnet/TakerSubmitted.sol";

contract MainnetSelectDispatchTest is Test {
    function test_mainnetSelect_executesEmptyCandidate() public {
        vm.mockCall(
            0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48, abi.encodeCall(IERC20.decimals, ()), abi.encode(uint8(6))
        );
        vm.mockCall(
            0xdAC17F958D2ee523a2206206994597C13D831ec7, abi.encodeCall(IERC20.decimals, ()), abi.encode(uint8(6))
        );
        MainnetSettler settler = new MainnetSettler(bytes20(0));
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = new bytes[](0);

        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.SELECT, (0, address(0), new uint256[](1), candidates));
        ISettlerBase.AllowedSlippage memory slippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(this)), buyToken: IERC20(address(0)), minAmountOut: 0
        });

        assertTrue(settler.execute(slippage, actions, bytes32(0)));
    }
}
