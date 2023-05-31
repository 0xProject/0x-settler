// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {SafeTransferLib} from "../../src/utils/SafeTransferLib.sol";

import {BasePairTest} from "./BasePairTest.t.sol";
import {
    IZeroEx,
    IBridgeAdapter,
    BridgeProtocols,
    IFillQuoteTransformer,
    IMetaTransactionsFeatureV2,
    ITransformERC20Feature
} from "./vendor/IZeroEx.sol";

import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";

abstract contract ZeroExPairTest is BasePairTest {
    using SafeTransferLib for ERC20;

    IZeroEx private ZERO_EX = IZeroEx(ZERO_EX_ADDRESS);
    // Note: Eventually this will be outdated
    uint32 private FQT_DEPLOYMENT_NONCE = 31;
    address private ZERO_EX_CURVE_LIQUIDITY_PROVIDER = 0x561B94454b65614aE3db0897B74303f4aCf7cc75;
    address private UNISWAP_V3_ROUTER = 0xE592427A0AEce92De3Edee1F18E0157C05861564;
    address private ZERO_EX_TRANSFORMER_DEPLOYER = 0x39dce47a67ad34344eab877eae3ef1fa2a1d50bb;

    function uniswapV3Path() internal virtual returns (bytes memory);
    function getCurveV2PoolData() internal pure virtual returns (ICurveV2Pool.CurveV2PoolData memory);

    // OTCOrder
    IZeroEx.OtcOrder private otcOrder;
    bytes32 private otcOrderHash;

    // MetaTransactionV2
    IMetaTransactionsFeatureV2.MetaTransactionDataV2 private mtx;
    bytes32 private mtxHash;

    function setUp() public virtual override {
        super.setUp();
        safeApproveIfBelow(fromToken(), FROM, address(ZERO_EX), amount());
        safeApproveIfBelow(toToken(), MAKER, address(ZERO_EX), amount());

        // OTC Order
        otcOrder.makerToken = toToken();
        otcOrder.takerToken = fromToken();
        otcOrder.makerAmount = uint128(amount());
        otcOrder.takerAmount = uint128(amount());
        otcOrder.taker = address(0);
        otcOrder.txOrigin = FROM;
        otcOrder.expiryAndNonce = ((block.timestamp + 60) << 192) | 2;
        otcOrder.maker = MAKER;
        otcOrderHash = ZERO_EX.getOtcOrderHash(otcOrder);

        // MetaTransactionV2
        IZeroEx.BatchSellSubcall[] memory calls = new IZeroEx.BatchSellSubcall[](1);
        calls[0] = IZeroEx.BatchSellSubcall({
            id: IZeroEx.MultiplexSubcall.UniswapV3,
            sellAmount: amount(),
            data: uniswapV3Path()
        });

        bytes memory mtxCallData = abi.encodeWithSelector(
            ZERO_EX.multiplexBatchSellTokenForToken.selector, fromToken(), toToken(), calls, amount(), 1
        );
        IMetaTransactionsFeatureV2.MetaTransactionFeeData[] memory fees =
            new IMetaTransactionsFeatureV2.MetaTransactionFeeData[](0);
        mtx = IMetaTransactionsFeatureV2.MetaTransactionDataV2({
            signer: payable(FROM),
            sender: address(0),
            expirationTimeSeconds: block.timestamp + 60,
            salt: 123,
            callData: mtxCallData,
            feeToken: ERC20(address(0)),
            fees: fees
        });
        mtxHash = ZERO_EX.getMetaTransactionV2Hash(mtx);

        warmZeroExOtcNonce(FROM);
    }

    function testZeroEx_otcOrder() public {
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(MAKER_PRIVATE_KEY, otcOrderHash);
        vm.startPrank(FROM, FROM);
        snapStartName("zeroEx_otcOrder");
        ZERO_EX.fillOtcOrder(otcOrder, IZeroEx.Signature(IZeroEx.SignatureType.EIP712, v, r, s), uint128(amount()));
        snapEnd();
    }

    function testZeroEx_uniswapV3VIP() public {
        snapStartName("zeroEx_uniswapV3VIP");
        vm.startPrank(FROM);
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

        snapStartName("zeroEx_uniswapV3VIP_multiplex1");
        vm.startPrank(FROM);
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

        snapStartName("zeroEx_uniswapV3VIP_multiplex2");
        vm.startPrank(FROM);
        ZERO_EX.multiplexBatchSellTokenForToken(fromToken(), toToken(), calls, amount(), 1);
        snapEnd();
    }

    function testZeroEx_curveV2VIP() public skipIf(getCurveV2PoolData().pool == address(0)) {
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
        ITransformERC20Feature.Transformation[] memory transformations =
            createSimpleFQTTransformation(BridgeProtocols.UNISWAPV3, abi.encode(UNISWAP_V3_ROUTER, uniswapV3Path()), 1);

        snapStartName("zeroEx_uniswapV3_transformERC20");
        vm.startPrank(FROM);
        ZERO_EX.transformERC20(fromToken(), toToken(), amount(), 1, transformations);
        snapEnd();
    }

    function testZeroEx_uniswapV3_transformERC20() public {
        ITransformERC20Feature.Transformation[] memory transformations =
            createSimpleFQTTransformation(BridgeProtocols.UNISWAPV3, abi.encode(UNISWAP_V3_ROUTER, uniswapV3Path()), 1);

        snapStartName("zeroEx_uniswapV3_transformERC20_fee");
        vm.startPrank(FROM);
        ZERO_EX.transformERC20(fromToken(), toToken(), amount(), 1, transformations);
        snapEnd();
    }

    function testZeroEx_curveV2_transformERC20() public skipIf(getCurveV2PoolData().pool == address(0)) {
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
            createSimpleFQTTransformation(BridgeProtocols.CURVEV2, data, 1);

        snapStartName("zeroEx_curveV2_transformERC20");
        vm.startPrank(FROM);
        ZERO_EX.transformERC20(fromToken(), toToken(), amount(), 1, transformations);
        snapEnd();
    }

    function testZeroEx_metaTxn_uniswapV3() public {
        IZeroEx.BatchSellSubcall[] memory calls = new IZeroEx.BatchSellSubcall[](1);
        calls[0] = IZeroEx.BatchSellSubcall({
            id: IZeroEx.MultiplexSubcall.UniswapV3,
            sellAmount: amount(),
            data: uniswapV3Path()
        });

        (uint8 v, bytes32 r, bytes32 s) = vm.sign(FROM_PRIVATE_KEY, mtxHash);
        snapStartName("zeroEx_metaTxn_uniswapV3");
        ZERO_EX.executeMetaTransactionV2(mtx, IZeroEx.Signature(IZeroEx.SignatureType.EIP712, v, r, s));
        snapEnd();
    }

    function createSimpleFQTTransformation(uint128 protocol, bytes memory bridgeData, uint256 numTransformations)
        internal
        returns (ITransformERC20Feature.Transformation[] memory transformations)
    {
        transformations = new ITransformERC20Feature.Transformation[](numTransformations);

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


    /// @dev RLP-encode a 32-bit or less account nonce.
    /// @param nonce A positive integer in the range 0 <= nonce < 2^32.
    /// @return rlpNonce The RLP encoding.
    function rlpEncodeNonce(uint32 nonce) internal pure returns (bytes memory rlpNonce) {
        // See https://github.com/ethereum/wiki/wiki/RLP for RLP encoding rules.
        if (nonce == 0) {
            rlpNonce = new bytes(1);
            rlpNonce[0] = 0x80;
        } else if (nonce < 0x80) {
            rlpNonce = new bytes(1);
            rlpNonce[0] = bytes1(uint8(nonce));
        } else if (nonce <= 0xFF) {
            rlpNonce = new bytes(2);
            rlpNonce[0] = 0x81;
            rlpNonce[1] = bytes1(uint8(nonce));
        } else if (nonce <= 0xFFFF) {
            rlpNonce = new bytes(3);
            rlpNonce[0] = 0x82;
            rlpNonce[1] = bytes1(uint8((nonce & 0xFF00) >> 8));
            rlpNonce[2] = bytes1(uint8(nonce));
        } else if (nonce <= 0xFFFFFF) {
            rlpNonce = new bytes(4);
            rlpNonce[0] = 0x83;
            rlpNonce[1] = bytes1(uint8((nonce & 0xFF0000) >> 16));
            rlpNonce[2] = bytes1(uint8((nonce & 0xFF00) >> 8));
            rlpNonce[3] = bytes1(uint8(nonce));
        } else {
            rlpNonce = new bytes(5);
            rlpNonce[0] = 0x84;
            rlpNonce[1] = bytes1(uint8((nonce & 0xFF000000) >> 24));
            rlpNonce[2] = bytes1(uint8((nonce & 0xFF0000) >> 16));
            rlpNonce[3] = bytes1(uint8((nonce & 0xFF00) >> 8));
            rlpNonce[4] = bytes1(uint8(nonce));
        }
    }

    /// @dev Compute the expected deployment address by `deployer` at
    ///      the nonce given by `deploymentNonce`.
    /// @param deployer The address of the deployer.
    /// @param deploymentNonce The nonce that the deployer had when deploying
    ///        a contract.
    /// @return deploymentAddress The deployment address.
    function getDeployedAddress(
        address deployer,
        uint32 deploymentNonce
    ) internal pure returns (address payable deploymentAddress) {
        // The address of if a deployed contract is the lower 20 bytes of the
        // hash of the RLP-encoded deployer's account address + account nonce.
        // See: https://ethereum.stackexchange.com/questions/760/how-is-the-address-of-an-ethereum-contract-computed
        bytes memory rlpNonce = rlpEncodeNonce(deploymentNonce);
        return
            address(
                uint160(
                    uint256(
                        keccak256(
                            abi.encodePacked(
                                bytes1(uint8(0xC0 + 21 + rlpNonce.length)),
                                bytes1(uint8(0x80 + 20)),
                                deployer,
                                rlpNonce
                            )
                        )
                    )
                )
            );
    }
}
