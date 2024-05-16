// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

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

        _settler = new Settler();
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
            actions,
            SettlerBase.AllowedSlippage({
                buyToken: address(_weth),
                recipient: address(this),
                minAmountOut: 1 ether - 1 wei
            })
        );
        snapEnd();
        assertEq(_weth.balanceOf(address(this)) - balanceBefore, 1 ether - 1 wei);
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
            actions,
            SettlerBase.AllowedSlippage({
                buyToken: 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE,
                recipient: address(this),
                minAmountOut: 1 ether - 1 wei
            })
        );
        snapEnd();
        assertEq(address(this).balance - balanceBefore, 1 ether - 1 wei);
    }

    receive() external payable {}
}
