// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "src/IERC20.sol";

import {Test} from "forge-std/Test.sol";
import {WETH} from "solmate/src/tokens/WETH.sol";
import {AllowanceHolder} from "src/allowanceholder/AllowanceHolder.sol";
import {MainnetSettler as Settler} from "src/chains/Mainnet.sol";
import {SettlerBase} from "src/SettlerBase.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {GasSnapshot} from "forge-gas-snapshot/GasSnapshot.sol";

contract WethWrapTest is Test, GasSnapshot {
    WETH private constant _weth = WETH(payable(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2));
    address private constant _eth = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;
    Settler private _settler;

    function setUp() public {
        vm.createSelectFork(vm.envString("MAINNET_RPC_URL"), 18685612);
        vm.label(address(this), "FoundryTest");
        vm.label(address(_weth), "WETH");

        assertEq(block.chainid, 1);
        vm.chainId(31337);
        _settler = new Settler(bytes20(0));
        vm.chainId(1);
        vm.label(address(_settler), "Settler");
    }

    function testWethDeposit() public {
        vm.deal(address(_settler), 1e18);
        bytes[] memory actions =
            ActionDataBuilder.build(abi.encodeCall(ISettlerActions.BASIC, (_eth, 10_000, address(_weth), 0, "")));

        uint256 balanceBefore = _weth.balanceOf(address(this));
        Settler settler = _settler;
        vm.startPrank(address(this));
        snapStart("wethDeposit");
        settler.execute(
            SettlerBase.AllowedSlippage({recipient: address(this), buyToken: IERC20(address(_weth)), minAmountOut: 1e18}),
            actions
        );
        snapEnd();
        assertEq(_weth.balanceOf(address(this)) - balanceBefore, 1e18);
    }

    function testWethWithdraw() public {
        deal(address(_weth), address(_settler), 1e18);
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.BASIC, (address(_weth), 10_000, address(_weth), 4, abi.encodeCall(_weth.withdraw, (0)))
            )
        );

        uint256 balanceBefore = address(this).balance;
        Settler settler = _settler;
        vm.startPrank(address(this));
        snapStart("wethWithdraw");
        settler.execute(
            SettlerBase.AllowedSlippage({
                recipient: address(this),
                buyToken: IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE),
                minAmountOut: 1e18
            }),
            actions
        );
        snapEnd();
        assertEq(address(this).balance - balanceBefore, 1e18);
    }

    receive() external payable {}
}
