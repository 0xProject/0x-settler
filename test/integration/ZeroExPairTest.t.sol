// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {SafeTransferLib} from "../../src/utils/SafeTransferLib.sol";

import {BasePairTest} from "./BasePairTest.t.sol";
import {
    IZeroEx,
    ITransformERC20Feature,
    IFillQuoteTransformer,
    IBridgeAdapter,
    BridgeProtocols
} from "./vendor/IZeroEx.sol";

import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";

abstract contract ZeroExPairTest is BasePairTest {
    using SafeTransferLib for ERC20;

    IZeroEx private ZERO_EX = IZeroEx(0xDef1C0ded9bec7F1a1670819833240f027b25EfF);
    // Note: Eventually this will be outdated
    uint32 FQT_DEPLOYMENT_NONCE = 31;
    address ZERO_EX_CURVE_LIQUIDITY_PROVIDER = 0x561B94454b65614aE3db0897B74303f4aCf7cc75;
    address UNISWAP_V3_ROUTER = 0xE592427A0AEce92De3Edee1F18E0157C05861564;

    function uniswapV3Path() internal virtual returns (bytes memory);
    function getCurveV2PoolData() internal pure virtual returns (ICurveV2Pool.CurveV2PoolData memory);

    function testZeroEx_otcOrder() public {
        dealAndApprove(fromToken(), amount(), address(ZERO_EX));
        dealAndApprove(MAKER, toToken(), amount(), address(ZERO_EX));

        IZeroEx.OtcOrder memory order;
        order.makerToken = toToken();
        order.takerToken = fromToken();
        order.makerAmount = uint128(amount());
        order.takerAmount = uint128(amount());
        order.taker = address(0);
        order.txOrigin = FROM;
        order.expiryAndNonce = type(uint256).max;
        order.maker = MAKER;
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(MAKER_PRIVATE_KEY, ZERO_EX.getOtcOrderHash(order));

        snapStartName("zeroEx_otcOrder");
        vm.startPrank(FROM, FROM);
        ZERO_EX.fillOtcOrder(order, IZeroEx.Signature(IZeroEx.SignatureType.EIP712, v, r, s), uint128(amount()));
        snapEnd();
    }

    function testZeroEx_uniswapV3VIP() public {
        dealAndApprove(fromToken(), amount(), address(ZERO_EX));

        snapStartName("zeroEx_uniswapV3VIP");
        vm.startPrank(FROM);
        ZERO_EX.sellTokenForTokenToUniswapV3(uniswapV3Path(), amount(), 1, FROM);
        snapEnd();
    }

    function testZeroEx_uniswapV3VIP_multiplex1() public {
        dealAndApprove(fromToken(), amount(), address(ZERO_EX));

        IZeroEx.BatchSellSubcall[] memory calls = new IZeroEx.BatchSellSubcall[](1);
        calls[0] = IZeroEx.BatchSellSubcall({
            id: IZeroEx.MultiplexSubcall.UniswapV3,
            sellAmount: amount(),
            data: uniswapV3Path()
        });

        snapStartName("zeroEx_uniswapV3VIP_multiplex1");
        vm.startPrank(FROM);
        ZERO_EX.multiplexBatchSellTokenForToken(fromToken(), toToken(), calls, amount(), 1);
        snapEnd();
    }

    function testZeroEx_uniswapV3VIP_multiplex2() public {
        dealAndApprove(fromToken(), amount(), address(ZERO_EX));

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

        snapStartName("zeroEx_uniswapV3VIP_multiplex2");
        vm.startPrank(FROM);
        ZERO_EX.multiplexBatchSellTokenForToken(fromToken(), toToken(), calls, amount(), 1);
        snapEnd();
    }

    function testZeroEx_curveV2VIP() public skipIf(getCurveV2PoolData().pool == address(0)) {
        dealAndApprove(fromToken(), amount(), address(ZERO_EX));

        ICurveV2Pool.CurveV2PoolData memory poolData = getCurveV2PoolData();
        // ZeroEx can access Curve via CurveLiquidityProvider sandbox
        // Note: this bytes4 selector is exchange(uint256,uint256,uint256,uint256)
        // which mostly found on CurveV2 (not older Curve V1) pools
        bytes memory data = abi.encode(
            address(poolData.pool),
            bytes4(0x5b41b908),
            int128(int256(poolData.fromTokenIndex)),
            int128(int256(poolData.toTokenIndex))
        );

        snapStartName("zeroEx_curveV2VIP");
        vm.startPrank(FROM);
        ZERO_EX.sellToLiquidityProvider(
            fromToken(), toToken(), ZERO_EX_CURVE_LIQUIDITY_PROVIDER, FROM, amount(), 1, data
        );
        snapEnd();
    }

    function testZeroEx_uniswapV3_transformERC20() public {
        dealAndApprove(fromToken(), amount(), address(ZERO_EX));

        ITransformERC20Feature.Transformation[] memory transformations =
            createSimpleFQTTransformation(BridgeProtocols.UNISWAPV3, abi.encode(UNISWAP_V3_ROUTER, uniswapV3Path()));

        snapStartName("zeroEx_uniswapV3_transformERC20");
        vm.startPrank(FROM);
        ZERO_EX.transformERC20(fromToken(), toToken(), amount(), 1, transformations);
        snapEnd();
    }

    function testZeroEx_curveV2_transformERC20() public skipIf(getCurveV2PoolData().pool == address(0)) {
        dealAndApprove(fromToken(), amount(), address(ZERO_EX));

        ICurveV2Pool.CurveV2PoolData memory poolData = getCurveV2PoolData();
        // Note: this bytes4 selector is exchange(uint256,uint256,uint256,uint256)
        // which mostly found on CurveV2 (not older Curve V1) pools
        bytes memory data = abi.encode(
            address(poolData.pool),
            bytes4(0x5b41b908),
            int128(int256(poolData.fromTokenIndex)),
            int128(int256(poolData.toTokenIndex))
        );
        ITransformERC20Feature.Transformation[] memory transformations =
            createSimpleFQTTransformation(BridgeProtocols.CURVEV2, data);

        snapStartName("zeroEx_curveV2_transformERC20");
        vm.startPrank(FROM);
        ZERO_EX.transformERC20(fromToken(), toToken(), amount(), 1, transformations);
        snapEnd();
    }

    function createSimpleFQTTransformation(uint128 protocol, bytes memory bridgeData)
        internal
        returns (ITransformERC20Feature.Transformation[] memory transformations)
    {
        transformations = new ITransformERC20Feature.Transformation[](1);

        IFillQuoteTransformer.TransformData memory fqtData;
        fqtData.side = IFillQuoteTransformer.Side.Sell;
        fqtData.bridgeOrders = new IBridgeAdapter.BridgeOrder[](1);
        fqtData.sellToken = fromToken();
        fqtData.buyToken = toToken();
        fqtData.fillSequence = new IFillQuoteTransformer.OrderType[](1);
        fqtData.fillSequence[0] = IFillQuoteTransformer.OrderType.Bridge;
        fqtData.fillAmount = amount();

        IBridgeAdapter.BridgeOrder memory order;
        order.source = bytes32(uint256(protocol) << 128);
        order.takerTokenAmount = amount();
        order.makerTokenAmount = 1;
        order.bridgeData = bridgeData;

        fqtData.bridgeOrders[0] = order;
        transformations[0].deploymentNonce = FQT_DEPLOYMENT_NONCE;
        transformations[0].data = abi.encode(fqtData);
    }
}
