// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {Settler} from "src/Settler.sol";
import {rubiconCLMMForkId} from "src/core/univ3forks/RubiconCLMM.sol";
import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";

import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";

interface IRubiconCLMMPool {
    function mint(address recipient, int24 tickLower, int24 tickUpper, uint128 liquidity, bytes calldata data)
        external
        returns (uint256 amount0, uint256 amount1);
}

contract RubiconCLMMTest is SettlerBasePairTest {
    using SafeTransferLib for IERC20;

    IERC20 private constant USDC = IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
    IRubiconCLMMPool private constant POOL = IRubiconCLMMPool(0xe7c40CFaaB7EA4084a34a89387265Db9D5611A89);

    function _testName() internal pure override returns (string memory) {
        return "USDC-WETH";
    }

    function _testBlockNumber() internal pure override returns (uint256) {
        return 26033334;
    }

    function fromToken() internal pure override returns (IERC20) {
        return USDC;
    }

    function toToken() internal pure override returns (IERC20) {
        return WETH;
    }

    function amount() internal pure override returns (uint256) {
        return 1000e6;
    }

    function setUp() public override {
        super.setUp();

        vm.etch(FROM, "");
        vm.makePersistent(FROM);
        deal(address(USDC), address(this), type(uint128).max);
        deal(address(WETH), address(this), type(uint128).max);
        POOL.mint(address(this), 198600, 198660, 1e18, "");

        safeApproveIfBelow(USDC, FROM, address(PERMIT2), amount());
        warmPermit2Nonce(FROM);
    }

    function testRubiconCLMMVIP() public {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.UNISWAPV3_VIP,
                (FROM, permit, abi.encodePacked(rubiconCLMMForkId, uint24(3000), uint160(4295128740), WETH), sig, 0)
            )
        );

        uint256 balanceBefore = WETH.balanceOf(FROM);
        vm.startPrank(FROM);
        Settler.AllowedSlippage memory slippage;
        Settler(settler).execute(slippage, actions, bytes32(0));
        vm.stopPrank();

        assertEq(USDC.balanceOf(FROM), 0);
        assertGt(WETH.balanceOf(FROM), balanceBefore);
    }

    function uniswapV3MintCallback(uint256 amount0Owed, uint256 amount1Owed, bytes calldata) external {
        require(msg.sender == address(POOL));
        USDC.safeTransfer(msg.sender, amount0Owed);
        WETH.safeTransfer(msg.sender, amount1Owed);
    }
}
