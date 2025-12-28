// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

import {Test} from "@forge-std/Test.sol";
import {WETH as WETHERC20} from "@solmate/tokens/WETH.sol";
import {MainnetSettler as Settler} from "src/chains/Mainnet/TakerSubmitted.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {GasSnapshot} from "@forge-gas-snapshot/GasSnapshot.sol";
import {BasePairTest} from "./BasePairTest.t.sol";

contract WethWrapTest is BasePairTest {
    WETHERC20 private constant _weth = WETHERC20(payable(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2));
    address private constant _eth = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;
    Settler private _settler;

    function amount() internal pure override returns (uint256) {
        return 1 ether;
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(_eth);
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(address(_weth));
    }

    function _testName() internal pure override returns (string memory) {
        return "WETHwrap";
    }

    function setUp() public override {
        super.setUp();

        assertEq(block.chainid, 1);
        vm.chainId(31337);
        _settler = new Settler(bytes20(0));
        vm.chainId(1);

        vm.label(address(_settler), "Settler");
    }

    function testWethDeposit() public {
        vm.deal(address(_settler), amount());
        bytes[] memory actions =
            ActionDataBuilder.build(abi.encodeCall(ISettlerActions.BASIC, (_eth, 10_000, address(_weth), 0, "")));

        uint256 balanceBefore = balanceOf(toToken(), address(this));
        Settler settler = _settler;
        vm.startPrank(address(this));
        snapStart("wethDeposit");
        settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(address(this)),
                buyToken: IERC20(address(_weth)),
                minAmountOut: amount()
            }),
            actions,
            bytes32(0)
        );
        snapEnd();
        assertEq(_weth.balanceOf(address(this)) - balanceBefore, amount());
    }

    function testWethWithdraw() public {
        deal(address(_weth), address(_settler), amount());
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
            ISettlerBase.AllowedSlippage({
                recipient: payable(address(this)),
                buyToken: IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE),
                minAmountOut: amount()
            }),
            actions,
            bytes32(0)
        );
        snapEnd();
        assertEq(address(this).balance - balanceBefore, amount());
    }

    receive() external payable {}
}
