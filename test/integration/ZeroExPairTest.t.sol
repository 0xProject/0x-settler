// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {BasePairTest} from "./BasePairTest.t.sol";
import {IZeroEx} from "./vendor/IZeroEx.sol";

abstract contract ZeroExPairTest is BasePairTest {
    IZeroEx ZERO_EX = IZeroEx(0xDef1C0ded9bec7F1a1670819833240f027b25EfF);

    function uniswapV3Path() internal virtual returns (bytes memory);

    function testZeroEx_uniswapV3VIP() public {
        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().approve(address(ZERO_EX), type(uint256).max);
        snapStartName("zeroEx_uniswapV3VIP");
        ZERO_EX.sellTokenForTokenToUniswapV3(uniswapV3Path(), amount(), 1, FROM);
        snapEnd();
    }

    function testZeroEx_uniswapV3VIP_multiplex1() public {
        IZeroEx.BatchSellSubcall[] memory calls = new IZeroEx.BatchSellSubcall[](1);
        calls[0] = IZeroEx.BatchSellSubcall({
            id: IZeroEx.MultiplexSubcall.UniswapV3,
            sellAmount: amount(),
            data: uniswapV3Path()
        });

        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().approve(address(ZERO_EX), type(uint256).max);

        snapStartName("zeroEx_uniswapV3VIP_multiplex1");
        ZERO_EX.multiplexBatchSellTokenForToken(fromToken(), toToken(), calls, amount(), 1);
        snapEnd();
    }

    function testZeroEx_uniswapV3VIP_multiplex2() public {
        IZeroEx.BatchSellSubcall[] memory calls = new IZeroEx.BatchSellSubcall[](2);
        calls[0] = IZeroEx.BatchSellSubcall({
            id: IZeroEx.MultiplexSubcall.UniswapV3,
            sellAmount: amount() / 2,
            data: uniswapV3Path()
        });
        calls[1] = IZeroEx.BatchSellSubcall({
            id: IZeroEx.MultiplexSubcall.UniswapV3,
            sellAmount: amount() / 2,
            data: uniswapV3Path()
        });

        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().approve(address(ZERO_EX), type(uint256).max);

        snapStartName("zeroEx_uniswapV3VIP_multiplex2");
        ZERO_EX.multiplexBatchSellTokenForToken(fromToken(), toToken(), calls, amount(), 1);
        snapEnd();
    }
}
