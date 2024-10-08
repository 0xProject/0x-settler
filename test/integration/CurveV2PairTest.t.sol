// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";

import {BasePairTest} from "./BasePairTest.t.sol";
import {ICurveV2Pool, ICurveV2SwapRouter} from "./vendor/ICurveV2Pool.sol";

abstract contract CurveV2PairTest is BasePairTest {
    using SafeTransferLib for IERC20;

    ICurveV2SwapRouter private constant CURVEV2_SWAP_ROUTER =
        ICurveV2SwapRouter(0x99a58482BD75cbab83b27EC03CA68fF489b5788f);

    function setUp() public virtual override {
        super.setUp();
        ICurveV2Pool.CurveV2PoolData memory poolData = getCurveV2PoolData();
        safeApproveIfBelow(fromToken(), FROM, address(poolData.pool), amount());
        safeApproveIfBelow(fromToken(), FROM, address(CURVEV2_SWAP_ROUTER), amount());
    }

    function getCurveV2PoolData() internal pure virtual returns (ICurveV2Pool.CurveV2PoolData memory);

    function testCurveV2() public skipIf(getCurveV2PoolData().pool == address(0)) {
        ICurveV2Pool.CurveV2PoolData memory poolData = getCurveV2PoolData();

        snapStartName("curveV2Pool");
        vm.startPrank(FROM);
        ICurveV2Pool(poolData.pool).exchange(poolData.fromTokenIndex, poolData.toTokenIndex, amount(), 1);
        snapEnd();
    }

    function testCurveV2_swapRouter() public skipIf(getCurveV2PoolData().pool == address(0)) {
        // https://github.com/curvefi/curve-pool-registry/blob/master/contracts/Swaps.vy#L506
        ICurveV2Pool.CurveV2PoolData memory poolData = getCurveV2PoolData();

        address[9] memory route;
        route[0] = address(fromToken());
        route[1] = address(poolData.pool);
        route[2] = address(toToken());
        uint256[3][4] memory swapParams;
        /**
         * 1 for a stableswap `exchange`,
         *         2 for stableswap `exchange_underlying`,
         *         3 for a cryptoswap `exchange`,
         *         4 for a cryptoswap `exchange_underlying`,
         */
        swapParams[0] = [poolData.fromTokenIndex, poolData.toTokenIndex, 3];

        vm.startPrank(FROM);
        snapStartName("curveV2Pool_swapRouter");
        CURVEV2_SWAP_ROUTER.exchange_multiple(route, swapParams, amount(), 1);
        snapEnd();
    }
}
