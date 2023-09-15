// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {Test} from "forge-std/Test.sol";
import {WETH} from "solmate/src/tokens/WETH.sol";
import {Settler} from "../../src/Settler.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {ISettlerActions} from "../../src/ISettlerActions.sol";

contract WethWrapTest is Test {
    WETH private constant _weth = WETH(payable(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2));
    Settler private _settler;

    function setUp() public {
        vm.createSelectFork(vm.envString("MAINNET_RPC_URL"));
        vm.label(address(this), "FoundryTest");

        _settler = new Settler(
            0x000000000022D473030F116dDEE9F6B43aC78BA3, // Permit2
            0xDef1C0ded9bec7F1a1670819833240f027b25EfF, // ZeroEx
            0x1F98431c8aD98523631AE4a59f267346ea31F984, // UniV3 Factory
            payable(_weth), // WETH
            0xe34f199b19b2b4f47f68442619d555527d244f78a3297ea89325f843f87b8b54, // UniV3 pool init code hash
            0x2222222222222222222222222222222222222222
        );
    }

    function testWethDeposit() public {
        vm.deal(address(_settler), 1e18);
        bytes[] memory actions = ActionDataBuilder.build(abi.encodeCall(ISettlerActions.WETH_DEPOSIT, (10_000)));

        uint256 balanceBefore = _weth.balanceOf(address(this));
        _settler.execute(actions, address(_weth), address(this), 1e18);
        assert(_weth.balanceOf(address(this)) - balanceBefore == 1e18);
    }

    function testWethWithdraw() public {
        deal(address(_weth), address(_settler), 1e18);
        bytes[] memory actions = ActionDataBuilder.build(abi.encodeCall(ISettlerActions.WETH_WITHDRAW, (10_000)));

        uint256 balanceBefore = address(this).balance;
        _settler.execute(actions, 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE, address(this), 1e18);
        assert(address(this).balance - balanceBefore == 1e18);
    }

    receive() external payable {}
}
