// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {SafeTransferLib} from "solmate/src/utils/SafeTransferLib.sol";
import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {BasePairTest} from "./BasePairTest.t.sol";
import {IZeroEx} from "./vendor/IZeroEx.sol";

import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";

abstract contract ZeroExPairTest is BasePairTest {
    using SafeTransferLib for ERC20;

    IZeroEx ZERO_EX = IZeroEx(0xDef1C0ded9bec7F1a1670819833240f027b25EfF);
    address ZERO_EX_CURVE_LIQUIDITY_PROVIDER = 0x561B94454b65614aE3db0897B74303f4aCf7cc75;

    function uniswapV3Path() internal virtual returns (bytes memory);
    function getCurveV2PoolData() internal pure virtual returns (ICurveV2Pool.CurveV2PoolData memory);

    function testZeroEx_uniswapV3VIP() public {
        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().safeApprove(address(ZERO_EX), type(uint256).max);
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
        fromToken().safeApprove(address(ZERO_EX), type(uint256).max);

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
        fromToken().safeApprove(address(ZERO_EX), type(uint256).max);

        snapStartName("zeroEx_uniswapV3VIP_multiplex2");
        ZERO_EX.multiplexBatchSellTokenForToken(fromToken(), toToken(), calls, amount(), 1);
        snapEnd();
    }

    function testZeroEx_curveV2VIP() skipIf(getCurveV2PoolData().pool == address(0)) public {
        ICurveV2Pool.CurveV2PoolData memory poolData = getCurveV2PoolData();

        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().safeApprove(address(ZERO_EX), type(uint256).max);

        // ZeroEx can access Curve via CurveLiquidityProvider sandbox
        // Note: this bytes4 selector is exchange(uint256,uint256,uint256,uint256)
        // which mostly found on CurveV2 (not older Curve V1) pools
        bytes memory data = abi.encode(address(poolData.pool), bytes4(0x5b41b908), int128(int256(poolData.fromTokenIndex)), int128(int256(poolData.toTokenIndex)));
        snapStartName("zeroEx_curveV2VIP");
        ZERO_EX.sellToLiquidityProvider(fromToken(), toToken(), ZERO_EX_CURVE_LIQUIDITY_PROVIDER, FROM, amount(), 1, data);
        snapEnd();
    }
}
