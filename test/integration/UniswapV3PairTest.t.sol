// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {SafeTransferLib} from "../../src/utils/SafeTransferLib.sol";

import {BasePairTest} from "./BasePairTest.t.sol";
import {IUniswapV3Router} from "./vendor/IUniswapV3Router.sol";

abstract contract UniswapV3PairTest is BasePairTest {
    using SafeTransferLib for ERC20;
    IUniswapV3Router UNISWAP_ROUTER = IUniswapV3Router(0xE592427A0AEce92De3Edee1F18E0157C05861564);

    function setUp() public virtual override {
        super.setUp();
        safeApproveIfBelow(fromToken(), FROM, address(UNISWAP_ROUTER), amount());
    }

    function uniswapV3Path() internal virtual returns (bytes memory);

    function testUniswapRouter() public {
        snapStartName("uniswapRouter_uniswapV3");
        vm.startPrank(FROM);
        UNISWAP_ROUTER.exactInput(
            IUniswapV3Router.ExactInputParams({
                path: uniswapV3Path(),
                recipient: FROM,
                deadline: block.timestamp + 1,
                amountIn: amount(),
                amountOutMinimum: 1
            })
        );
        snapEnd();
    }
}
