// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";
import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";
import {IZeroEx} from "./vendor/IZeroEx.sol";

import {LibBytes} from "../utils/LibBytes.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";

import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";

import {Settler} from "src/Settler.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {RfqOrderSettlement} from "src/core/RfqOrderSettlement.sol";

abstract contract SettlerPairTest is SettlerBasePairTest {
    using SafeTransferLib for IERC20;
    using LibBytes for bytes;

    IZeroEx.OtcOrder private otcOrder;
    bytes32 private otcOrderHash;

    function setUp() public virtual override {
        super.setUp();

        // ### Taker ###
        safeApproveIfBelow(fromToken(), FROM, address(PERMIT2), amount());

        // ### Maker / Seller ###
        // Otc via ZeroEx
        safeApproveIfBelow(toToken(), MAKER, address(ZERO_EX), amount());
        // Rfq inside of Settler
        safeApproveIfBelow(toToken(), MAKER, address(PERMIT2), amount());

        // First time inits for Settler
        // We set up allowances to contracts which are inited on the first trade for a fair comparison
        // e.g to a Curve Pool
        ICurveV2Pool.CurveV2PoolData memory poolData = getCurveV2PoolData();
        safeApproveIfBelow(fromToken(), address(settler), address(poolData.pool), amount());
        // ZeroEx for Settler using ZeroEx OTC
        safeApproveIfBelow(fromToken(), address(settler), address(ZERO_EX), amount());

        // Otc 0x v4 order
        otcOrder.makerToken = toToken();
        otcOrder.takerToken = fromToken();
        otcOrder.makerAmount = uint128(amount());
        otcOrder.takerAmount = uint128(amount());
        otcOrder.taker = address(0);
        otcOrder.txOrigin = FROM;
        otcOrder.expiryAndNonce = type(uint256).max;
        otcOrder.maker = MAKER;
        otcOrderHash = ZERO_EX.getOtcOrderHash(otcOrder);

        warmPermit2Nonce(FROM);
        warmPermit2Nonce(MAKER);
    }

    function uniswapV3Path() internal virtual returns (bytes memory);
    function uniswapV2Pool() internal virtual returns (address);
    function getCurveV2PoolData() internal pure virtual returns (ICurveV2Pool.CurveV2PoolData memory);

    function testSettler_zeroExOtcOrder() public {
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(MAKER_PRIVATE_KEY, otcOrderHash);

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(
                ISettlerActions.BASIC,
                (
                    address(fromToken()),
                    10_000,
                    address(ZERO_EX),
                    0x184,
                    abi.encodeCall(
                        ZERO_EX.fillOtcOrder, (otcOrder, IZeroEx.Signature(IZeroEx.SignatureType.EIP712, v, r, s), 0)
                    )
                )
            )
        );

        Settler _settler = settler;
        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: FROM,
            buyToken: otcOrder.makerToken,
            minAmountOut: otcOrder.makerAmount
        });
        vm.startPrank(FROM, FROM);
        snapStartName("settler_zeroExOtc");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
    }

    function testSettler_zeroExOtcOrder_partialFill() public {
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(MAKER_PRIVATE_KEY, otcOrderHash);

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(
                ISettlerActions.BASIC,
                (
                    address(fromToken()),
                    5_000,
                    address(ZERO_EX),
                    0x184,
                    abi.encodeCall(
                        ZERO_EX.fillOtcOrder, (otcOrder, IZeroEx.Signature(IZeroEx.SignatureType.EIP712, v, r, s), 0)
                    )
                )
            ),
            abi.encodeCall(
                ISettlerActions.BASIC,
                (
                    address(fromToken()),
                    10_000,
                    address(fromToken()),
                    0x24,
                    abi.encodeCall(fromToken().transfer, (FROM, 0))
                )
            )
        );

        Settler _settler = settler;
        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: FROM,
            buyToken: otcOrder.makerToken,
            minAmountOut: otcOrder.makerAmount / 2
        });
        vm.startPrank(FROM, FROM);
        snapStartName("settler_zeroExOtc_partialFill");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
    }

    function testSettler_uniswapV3VIP() public skipIf(uniswapV3Path().length == 0) {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.UNISWAPV3_VIP, (FROM, permit, uniswapV3Path(), sig, 0))
        );
        ISettlerBase.AllowedSlippage memory slippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)),
            buyToken: IERC20(address(0)),
            minAmountOut: 0 ether
        });

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV3VIP");
        _settler.execute(slippage, actions, bytes32(0));
        snapEnd();
    }

    function testSettler_uniswapV3_multiplex2() public skipIf(uniswapV3Path().length == 0) {
        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(ISettlerActions.UNISWAPV3, (FROM, 5_000, uniswapV3Path(), 0)),
            abi.encodeCall(ISettlerActions.UNISWAPV3, (FROM, 10_000, uniswapV3Path(), 0))
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV3_multiplex2");
        _settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(address(0)),
                buyToken: IERC20(address(0)),
                minAmountOut: 0 ether
            }),
            actions,
            bytes32(0)
        );
        snapEnd();
    }

    function testSettler_uniswapV3() public skipIf(uniswapV3Path().length == 0) {
        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(ISettlerActions.UNISWAPV3, (FROM, 10_000, uniswapV3Path(), 0))
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV3");
        _settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(address(0)),
                buyToken: IERC20(address(0)),
                minAmountOut: 0 ether
            }),
            actions,
            bytes32(0)
        );
        snapEnd();
    }

    function testSettler_uniswapV3_buyToken_fee_full_custody() public skipIf(uniswapV3Path().length == 0) {
        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(ISettlerActions.UNISWAPV3, (address(settler), 10_000, uniswapV3Path(), 0)),
            abi.encodeCall(
                ISettlerActions.BASIC,
                (
                    address(toToken()),
                    1_000,
                    address(toToken()),
                    0x24,
                    abi.encodeCall(toToken().transfer, (BURN_ADDRESS, 0))
                )
            )
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV3_buyToken_fee_full_custody");
        _settler.execute(
            ISettlerBase.AllowedSlippage({recipient: FROM, buyToken: toToken(), minAmountOut: 0 ether}),
            actions,
            bytes32(0)
        );
        snapEnd();
    }

    function testSettler_uniswapV3_buyToken_fee_single_custody() public skipIf(uniswapV3Path().length == 0) {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.UNISWAPV3_VIP, (address(settler), permit, uniswapV3Path(), sig, 0)),
            abi.encodeCall(
                ISettlerActions.BASIC,
                (
                    address(toToken()),
                    1_000,
                    address(toToken()),
                    0x24,
                    abi.encodeCall(toToken().transfer, (BURN_ADDRESS, 0))
                )
            )
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV3_buyToken_fee_single_custody");
        _settler.execute(
            ISettlerBase.AllowedSlippage({recipient: FROM, buyToken: toToken(), minAmountOut: 0 ether}),
            actions,
            bytes32(0)
        );
        snapEnd();
    }

    function testSettler_uniswapV3_sellToken_fee_full_custody() public skipIf(uniswapV3Path().length == 0) {
        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(
                ISettlerActions.BASIC,
                (
                    address(fromToken()),
                    1_000,
                    address(fromToken()),
                    0x24,
                    abi.encodeCall(fromToken().transfer, (BURN_ADDRESS, 0))
                )
            ),
            abi.encodeCall(ISettlerActions.UNISWAPV3, (FROM, 10_000, uniswapV3Path(), 0))
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV3_sellToken_fee_full_custody");
        _settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(address(0)),
                buyToken: IERC20(address(0)),
                minAmountOut: 0 ether
            }),
            actions,
            bytes32(0)
        );
        snapEnd();
    }

    function testSettler_uniswapV2() public skipIf(uniswapV2Pool() == address(0)) {
        // |7|6|5|4|3|2|1|0| - bit positions in swapInfo (uint8)
        // |0|0|0|0|0|0|F|Z| - Z: zeroForOne flag, F: sellTokenHasFee flag
        bool sellTokenHasFee = false;
        uint24 swapInfo = (address(fromToken()) < address(toToken()) ? 1 : 0) | (sellTokenHasFee ? 2 : 0) | (30 << 8);

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(
                ISettlerActions.UNISWAPV2, (FROM, address(fromToken()), 10_000, uniswapV2Pool(), swapInfo, 0)
            )
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV2");
        _settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(address(0)),
                buyToken: IERC20(address(0)),
                minAmountOut: 0 ether
            }),
            actions,
            bytes32(0)
        );
        snapEnd();
    }

    function testSettler_uniswapV2_multihop_single_chain()
        public
        skipIf(uniswapV2Pool() == address(0))
        skipIf(toToken() != WETH)
    {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);
        bytes memory sig = getPermitTransferSignature(permit, address(settler), FROM_PRIVATE_KEY, permit2Domain);
        bytes memory permit2Action = abi.encodeCall(ISettlerActions.TRANSFER_FROM, (uniswapV2Pool(), permit, sig));
        IERC20 wBTC = IERC20(0x2260FAC5E5542a773Aa44fBCfeDf7C193bc2C599);

        // |7|6|5|4|3|2|1|0| - bit positions in swapInfo (uint8)
        // |0|0|0|0|0|0|F|Z| - Z: zeroForOne flag, F: sellTokenHasFee flag
        bool sellTokenHasFee = false;
        uint24 swapInfo = (address(fromToken()) < address(toToken()) ? 1 : 0) | (sellTokenHasFee ? 2 : 0) | (30 << 8);
        uint24 swapInfo2 = (address(toToken()) < address(wBTC) ? 1 : 0) | (sellTokenHasFee ? 2 : 0) | (30 << 8);

        address nextPool = 0xBb2b8038a1640196FbE3e38816F3e67Cba72D940; // UniswapV2 WETH/WBTC
        bytes[] memory actions = ActionDataBuilder.build(
            permit2Action,
            abi.encodeCall(ISettlerActions.UNISWAPV2, (nextPool, address(fromToken()), 0, uniswapV2Pool(), swapInfo, 0)),
            abi.encodeCall(ISettlerActions.UNISWAPV2, (FROM, address(toToken()), 0, nextPool, swapInfo2, 0))
        );

        uint256 balanceBefore = balanceOf(wBTC, FROM);

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV2_multihop_single_chain");
        _settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(address(0)),
                buyToken: IERC20(address(0)),
                minAmountOut: 0 ether
            }),
            actions,
            bytes32(0)
        );
        snapEnd();

        assertGt(wBTC.balanceOf(FROM), balanceBefore);
    }

    function testSettler_uniswapV2_single_chain() public skipIf(uniswapV2Pool() == address(0)) {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);
        bytes memory sig = getPermitTransferSignature(permit, address(settler), FROM_PRIVATE_KEY, permit2Domain);
        bytes memory permit2Action = abi.encodeCall(ISettlerActions.TRANSFER_FROM, (uniswapV2Pool(), permit, sig));

        // |7|6|5|4|3|2|1|0| - bit positions in swapInfo (uint8)
        // |0|0|0|0|0|0|F|Z| - Z: zeroForOne flag, F: sellTokenHasFee flag
        bool sellTokenHasFee = false;
        uint24 swapInfo = (address(fromToken()) < address(toToken()) ? 1 : 0) | (sellTokenHasFee ? 2 : 0) | (30 << 8);

        bytes[] memory actions = ActionDataBuilder.build(
            permit2Action,
            abi.encodeCall(ISettlerActions.UNISWAPV2, (FROM, address(fromToken()), 0, uniswapV2Pool(), swapInfo, 0))
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV2_single_chain");
        _settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(address(0)),
                buyToken: IERC20(address(0)),
                minAmountOut: 0 ether
            }),
            actions,
            bytes32(0)
        );
        snapEnd();
    }

    function testSettler_uniswapV2_multihop() public skipIf(uniswapV2Pool() == address(0)) skipIf(toToken() != WETH) {
        IERC20 wBTC = IERC20(0x2260FAC5E5542a773Aa44fBCfeDf7C193bc2C599);
        address nextPool = 0xBb2b8038a1640196FbE3e38816F3e67Cba72D940; // UniswapV2 WETH/WBTC

        // |7|6|5|4|3|2|1|0| - bit positions in swapInfo (uint8)
        // |0|0|0|0|0|0|F|Z| - Z: zeroForOne flag, F: sellTokenHasFee flag
        bool sellTokenHasFee = false;
        uint24 swapInfo = (address(fromToken()) < address(toToken()) ? 1 : 0) | (sellTokenHasFee ? 2 : 0) | (30 << 8);
        uint24 swapInfo2 = (address(toToken()) < address(wBTC) ? 1 : 0) | (sellTokenHasFee ? 2 : 0) | (30 << 8);

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(
                ISettlerActions.UNISWAPV2, (nextPool, address(fromToken()), 10_000, uniswapV2Pool(), swapInfo, 0)
            ),
            abi.encodeCall(ISettlerActions.UNISWAPV2, (FROM, address(toToken()), 0, nextPool, swapInfo2, 0))
        );

        uint256 balanceBefore = balanceOf(wBTC, FROM);

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV2_multihop");
        _settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(address(0)),
                buyToken: IERC20(address(0)),
                minAmountOut: 0 ether
            }),
            actions,
            bytes32(0)
        );
        snapEnd();

        assertGt(wBTC.balanceOf(FROM), balanceBefore);
    }

    function testSettler_curveV2_fee() public skipIf(getCurveV2PoolData().pool == address(0)) {
        ICurveV2Pool.CurveV2PoolData memory poolData = getCurveV2PoolData();

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(
                ISettlerActions.BASIC,
                (
                    address(fromToken()),
                    10_000,
                    poolData.pool,
                    0x44,
                    abi.encodeCall(ICurveV2Pool.exchange, (poolData.fromTokenIndex, poolData.toTokenIndex, 0, 0))
                )
            ),
            abi.encodeCall(
                ISettlerActions.BASIC,
                (
                    address(toToken()),
                    1_000,
                    address(toToken()),
                    0x24,
                    abi.encodeCall(toToken().transfer, (BURN_ADDRESS, 0))
                )
            )
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_curveV2_fee");
        _settler.execute(
            ISettlerBase.AllowedSlippage({recipient: FROM, buyToken: toToken(), minAmountOut: 0 ether}),
            actions,
            bytes32(0)
        );
        snapEnd();
    }

    function testSettler_basic_curve() public skipIf(getCurveV2PoolData().pool == address(0)) {
        ICurveV2Pool.CurveV2PoolData memory poolData = getCurveV2PoolData();

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(
                ISettlerActions.BASIC,
                (
                    address(fromToken()),
                    10_000, // bps
                    poolData.pool,
                    0x44, // offset
                    abi.encodeCall(ICurveV2Pool.exchange, (poolData.fromTokenIndex, poolData.toTokenIndex, 0, 0))
                )
            )
        );

        uint256 beforeBalance = balanceOf(toToken(), FROM);
        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_basic_curve");
        _settler.execute(
            ISettlerBase.AllowedSlippage({buyToken: toToken(), recipient: FROM, minAmountOut: 0 ether}),
            actions,
            bytes32(0)
        );
        snapEnd();
        assertGt(toToken().balanceOf(FROM), beforeBalance);
    }

    function testSettler_externalMoveExecute_uniswapV3() public skipIf(uniswapV3Path().length == 0) {
        bytes[] memory actions =
            ActionDataBuilder.build(abi.encodeCall(ISettlerActions.UNISWAPV3, (FROM, 10_000, uniswapV3Path(), 0)));

        Settler _settler = settler;

        vm.startPrank(FROM, FROM); // prank both msg.sender and tx.origin
        snapStartName("settler_externalMoveExecute_uniswapV3");
        // Transfer the tokens INTO Settler then execute against its own balance
        fromToken().safeTransfer(address(_settler), amount());

        _settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(address(0)),
                buyToken: IERC20(address(0)),
                minAmountOut: 0 ether
            }),
            actions,
            bytes32(0)
        );
        snapEnd();
    }
}
