// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IERC20} from "../../src/IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";
import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";
import {IZeroEx} from "./vendor/IZeroEx.sol";

import {LibBytes} from "../utils/LibBytes.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";

import {SafeTransferLib} from "../../src/vendor/SafeTransferLib.sol";

import {Settler} from "../../src/Settler.sol";
import {ISettlerActions} from "../../src/ISettlerActions.sol";
import {OtcOrderSettlement} from "../../src/core/OtcOrderSettlement.sol";

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
        // Otc inside of Settler
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
                ISettlerActions.BASIC_SELL,
                (
                    address(ZERO_EX),
                    address(fromToken()),
                    10_000,
                    0x184,
                    abi.encodeCall(
                        ZERO_EX.fillOtcOrder, (otcOrder, IZeroEx.Signature(IZeroEx.SignatureType.EIP712, v, r, s), 0)
                        )
                )
            )
        );

        Settler _settler = settler;
        Settler.AllowedSlippage memory allowedSlippage = Settler.AllowedSlippage({
            buyToken: address(otcOrder.makerToken),
            recipient: FROM,
            minAmountOut: otcOrder.makerAmount
        });
        vm.startPrank(FROM, FROM);
        snapStartName("settler_zeroExOtc");
        _settler.execute(actions, allowedSlippage);
        snapEnd();
    }

    function testSettler_zeroExOtcOrder_partialFill() public {
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(MAKER_PRIVATE_KEY, otcOrderHash);

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(
                ISettlerActions.BASIC_SELL,
                (
                    address(ZERO_EX),
                    address(fromToken()),
                    5_000,
                    0x184,
                    abi.encodeCall(
                        ZERO_EX.fillOtcOrder, (otcOrder, IZeroEx.Signature(IZeroEx.SignatureType.EIP712, v, r, s), 0)
                        )
                )
            ),
            abi.encodeCall(
                ISettlerActions.BASIC_SELL,
                (
                    address(fromToken()),
                    address(fromToken()),
                    10_000,
                    0x24,
                    abi.encodeCall(fromToken().transfer, (FROM, 0))
                )
            )
        );

        Settler _settler = settler;
        Settler.AllowedSlippage memory allowedSlippage = Settler.AllowedSlippage({
            buyToken: address(otcOrder.makerToken),
            recipient: FROM,
            minAmountOut: otcOrder.makerAmount / 2
        });
        vm.startPrank(FROM, FROM);
        snapStartName("settler_zeroExOtc_partialFill");
        _settler.execute(actions, allowedSlippage);
        snapEnd();
    }

    function testSettler_uniswapV3VIP() public {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.UNISWAPV3_PERMIT2_SWAP_EXACT_IN, (FROM, amount(), 0, uniswapV3Path(), permit, sig)
            )
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV3VIP");
        _settler.execute(
            actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether})
        );
        snapEnd();
    }

    function testSettler_uniswapV3_multiplex2() public {
        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(ISettlerActions.UNISWAPV3_SWAP_EXACT_IN, (FROM, 5_000, 0, uniswapV3Path())),
            abi.encodeCall(ISettlerActions.UNISWAPV3_SWAP_EXACT_IN, (FROM, 10_000, 0, uniswapV3Path()))
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV3_multiplex2");
        _settler.execute(
            actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether})
        );
        snapEnd();
    }

    function testSettler_uniswapV3() public {
        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(ISettlerActions.UNISWAPV3_SWAP_EXACT_IN, (FROM, 10_000, 0, uniswapV3Path()))
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV3");
        _settler.execute(
            actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether})
        );
        snapEnd();
    }

    function testSettler_uniswapV3_buyToken_fee_full_custody() public {
        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(ISettlerActions.UNISWAPV3_SWAP_EXACT_IN, (address(settler), 10_000, 0, uniswapV3Path())),
            abi.encodeCall(
                ISettlerActions.BASIC_SELL,
                (
                    address(toToken()),
                    address(toToken()),
                    1_000,
                    0x24,
                    abi.encodeCall(toToken().transfer, (BURN_ADDRESS, 0))
                )
            )
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV3_buyToken_fee_full_custody");
        _settler.execute(
            actions, Settler.AllowedSlippage({buyToken: address(toToken()), recipient: FROM, minAmountOut: 0 ether})
        );
        snapEnd();
    }

    function testSettler_uniswapV3_buyToken_fee_single_custody() public {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.UNISWAPV3_PERMIT2_SWAP_EXACT_IN,
                (address(settler), amount(), 0, uniswapV3Path(), permit, sig)
            ),
            abi.encodeCall(
                ISettlerActions.BASIC_SELL,
                (
                    address(toToken()),
                    address(toToken()),
                    1_000,
                    0x24,
                    abi.encodeCall(toToken().transfer, (BURN_ADDRESS, 0))
                )
            )
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV3_buyToken_fee_single_custody");
        _settler.execute(
            actions, Settler.AllowedSlippage({buyToken: address(toToken()), recipient: FROM, minAmountOut: 0 ether})
        );
        snapEnd();
    }

    function testSettler_uniswapV3_sellToken_fee_full_custody() public {
        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(
                ISettlerActions.BASIC_SELL,
                (
                    address(fromToken()),
                    address(fromToken()),
                    1_000,
                    0x24,
                    abi.encodeCall(fromToken().transfer, (BURN_ADDRESS, 0))
                )
            ),
            abi.encodeCall(ISettlerActions.UNISWAPV3_SWAP_EXACT_IN, (FROM, 10_000, 0, uniswapV3Path()))
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV3_sellToken_fee_full_custody");
        _settler.execute(
            actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether})
        );
        snapEnd();
    }

    function testSettler_uniswapV2() public {
        // |7|6|5|4|3|2|1|0| - bit positions in swapInfo (uint8)
        // |0|0|0|0|0|0|F|Z| - Z: zeroForOne flag, F: sellTokenHasFee flag
        bool sellTokenHasFee = false;
        uint8 swapInfo = (address(fromToken()) < address(toToken()) ? 1 : 0) | (sellTokenHasFee ? 1 : 0) << 1;

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(
                ISettlerActions.UNISWAPV2_SWAP, (FROM, address(fromToken()), uniswapV2Pool(), swapInfo, 10_000, 0)
            )
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV2");
        _settler.execute(
            actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether})
        );
        snapEnd();
    }

    function testSettler_uniswapV2_multihop_single_chain() public {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);
        bytes memory sig = getPermitTransferSignature(permit, address(settler), FROM_PRIVATE_KEY, permit2Domain);
        bytes memory permit2Action =
            abi.encodeCall(ISettlerActions.PERMIT2_TRANSFER_FROM, (uniswapV2Pool(), permit, sig));
        IERC20 wBTC = IERC20(0x2260FAC5E5542a773Aa44fBCfeDf7C193bc2C599);

        // |7|6|5|4|3|2|1|0| - bit positions in swapInfo (uint8)
        // |0|0|0|0|0|0|F|Z| - Z: zeroForOne flag, F: sellTokenHasFee flag
        bool sellTokenHasFee = false;
        uint8 swapInfo = (address(fromToken()) < address(toToken()) ? 1 : 0) | (sellTokenHasFee ? 1 : 0) << 1;
        uint8 swapInfo2 = (address(toToken()) < address(wBTC) ? 1 : 0) | (sellTokenHasFee ? 1 : 0) << 1;

        address nextPool = 0xBb2b8038a1640196FbE3e38816F3e67Cba72D940; // UniswapV2 WETH/WBTC
        bytes[] memory actions = ActionDataBuilder.build(
            permit2Action,
            abi.encodeCall(
                ISettlerActions.UNISWAPV2_SWAP, (nextPool, address(fromToken()), uniswapV2Pool(), swapInfo, 0, 0)
            ),
            abi.encodeCall(ISettlerActions.UNISWAPV2_SWAP, (FROM, address(toToken()), nextPool, swapInfo2, 0, 0))
        );

        uint256 balanceBefore = wBTC.balanceOf(FROM);

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV2_multihop_single_chain");
        _settler.execute(
            actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether})
        );
        snapEnd();

        assertGt(wBTC.balanceOf(FROM), balanceBefore);
    }

    function testSettler_uniswapV2_single_chain() public {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);
        bytes memory sig = getPermitTransferSignature(permit, address(settler), FROM_PRIVATE_KEY, permit2Domain);
        bytes memory permit2Action =
            abi.encodeCall(ISettlerActions.PERMIT2_TRANSFER_FROM, (uniswapV2Pool(), permit, sig));

        // |7|6|5|4|3|2|1|0| - bit positions in swapInfo (uint8)
        // |0|0|0|0|0|0|F|Z| - Z: zeroForOne flag, F: sellTokenHasFee flag
        bool sellTokenHasFee = false;
        uint8 swapInfo = (address(fromToken()) < address(toToken()) ? 1 : 0) | (sellTokenHasFee ? 1 : 0) << 1;

        bytes[] memory actions = ActionDataBuilder.build(
            permit2Action,
            abi.encodeCall(
                ISettlerActions.UNISWAPV2_SWAP, (FROM, address(fromToken()), uniswapV2Pool(), swapInfo, 0, 0)
            )
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV2_single_chain");
        _settler.execute(
            actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether})
        );
        snapEnd();
    }

    function testSettler_uniswapV2_multihop() public {
        IERC20 wBTC = IERC20(0x2260FAC5E5542a773Aa44fBCfeDf7C193bc2C599);
        address nextPool = 0xBb2b8038a1640196FbE3e38816F3e67Cba72D940; // UniswapV2 WETH/WBTC

        // |7|6|5|4|3|2|1|0| - bit positions in swapInfo (uint8)
        // |0|0|0|0|0|0|F|Z| - Z: zeroForOne flag, F: sellTokenHasFee flag
        bool sellTokenHasFee = false;
        uint8 swapInfo = (address(fromToken()) < address(toToken()) ? 1 : 0) | (sellTokenHasFee ? 1 : 0) << 1;
        uint8 swapInfo2 = (address(toToken()) < address(wBTC) ? 1 : 0) | (sellTokenHasFee ? 1 : 0) << 1;

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(
                ISettlerActions.UNISWAPV2_SWAP, (nextPool, address(fromToken()), uniswapV2Pool(), swapInfo, 10_000, 0)
            ),
            abi.encodeCall(ISettlerActions.UNISWAPV2_SWAP, (FROM, address(toToken()), nextPool, swapInfo2, 0, 0))
        );

        uint256 balanceBefore = wBTC.balanceOf(FROM);

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV2_multihop");
        _settler.execute(
            actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether})
        );
        snapEnd();

        assertGt(wBTC.balanceOf(FROM), balanceBefore);
    }

    function testSettler_curveV2_fee() public skipIf(getCurveV2PoolData().pool == address(0)) {
        ICurveV2Pool.CurveV2PoolData memory poolData = getCurveV2PoolData();

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(
                ISettlerActions.BASIC_SELL,
                (
                    poolData.pool,
                    address(fromToken()),
                    10_000,
                    0x44,
                    abi.encodeCall(ICurveV2Pool.exchange, (poolData.fromTokenIndex, poolData.toTokenIndex, 0, 0))
                )
            ),
            abi.encodeCall(
                ISettlerActions.BASIC_SELL,
                (
                    address(toToken()),
                    address(toToken()),
                    1_000,
                    0x24,
                    abi.encodeCall(toToken().transfer, (BURN_ADDRESS, 0))
                )
            )
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_curveV2_fee");
        _settler.execute(
            actions, Settler.AllowedSlippage({buyToken: address(toToken()), recipient: FROM, minAmountOut: 0 ether})
        );
        snapEnd();
    }

    function testSettler_basic_curve() public skipIf(getCurveV2PoolData().pool == address(0)) {
        ICurveV2Pool.CurveV2PoolData memory poolData = getCurveV2PoolData();

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(
                ISettlerActions.BASIC_SELL,
                (
                    poolData.pool,
                    address(fromToken()),
                    10_000, // bips
                    0x44, // offset
                    abi.encodeCall(ICurveV2Pool.exchange, (poolData.fromTokenIndex, poolData.toTokenIndex, 0, 0))
                )
            )
        );

        uint256 beforeBalance = toToken().balanceOf(FROM);
        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_basic_curve");
        _settler.execute(
            actions, Settler.AllowedSlippage({buyToken: address(toToken()), recipient: FROM, minAmountOut: 0 ether})
        );
        snapEnd();
        assertGt(toToken().balanceOf(FROM), beforeBalance);
    }

    function testSettler_externalMoveExecute_uniswapV3() public {
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.UNISWAPV3_SWAP_EXACT_IN, (FROM, 10_000, 0, uniswapV3Path()))
        );

        Settler _settler = settler;

        vm.startPrank(FROM, FROM); // prank both msg.sender and tx.origin
        snapStartName("settler_externalMoveExecute_uniswapV3");
        // Transfer the tokens INTO Settler then execute against its own balance
        fromToken().safeTransfer(address(_settler), amount());

        _settler.execute(
            actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether})
        );
        snapEnd();
    }
}
