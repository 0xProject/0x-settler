// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {IAllowanceTransfer} from "@permit2/interfaces/IAllowanceTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

import {
    UNIVERSAL_ROUTER,
    CONTRACT_BALANCE,
    RECIPIENT_ROUTER,
    RECIPIENT_TAKER,
    encodePermit2Permit,
    encodeV3Swap,
    encodeWrapEth,
    encodeUnwrapWeth
} from "src/vendor/IUniswapUniversalRouter.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {Settler} from "src/Settler.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";

import {SettlerPairTest} from "./SettlerPairTest.t.sol";
import {IUniswapV3Router} from "./vendor/IUniswapV3Router.sol";

import {SettlerMetaTxnPairTest} from "./SettlerMetaTxnPairTest.t.sol";
import {BaseSettlerMetaTxn} from "src/chains/Base/MetaTxn.sol";
import {RobinHoodSettlerMetaTxn} from "src/chains/RobinHood/MetaTxn.sol";
import {TooMuchSlippage} from "src/core/SettlerErrors.sol";
import {BaseSettler} from "src/chains/Base/TakerSubmitted.sol";
import {RobinHoodSettler} from "src/chains/RobinHood/TakerSubmitted.sol";
import {IUniswapV3Pool} from "src/core/UniswapV3Fork.sol";
import {IAlgebraCallback} from "src/core/univ3forks/Algebra.sol";
import {
    namiMainnetFactory,
    namiBaseFactory,
    namiRobinhoodFactory,
    namiInitHash,
    namiForkId
} from "src/core/univ3forks/Nami.sol";

abstract contract UniswapV3PairTest is SettlerPairTest {
    IUniswapV3Router private constant UNISWAP_ROUTER = IUniswapV3Router(0xE592427A0AEce92De3Edee1F18E0157C05861564);

    function setUp() public virtual override {
        super.setUp();
        safeApproveIfBelow(fromToken(), FROM, address(UNISWAP_ROUTER), amount());
    }

    function _testBlockNumber() internal pure virtual override returns (uint256) {
        return 22333955;
    }

    function uniswapV3PathCompat() internal view virtual returns (bytes memory);

    function testUniswapRouter() public {
        vm.startPrank(FROM);
        snapStartName("uniswapRouter_uniswapV3");
        UNISWAP_ROUTER.exactInput(
            IUniswapV3Router.ExactInputParams({
                path: uniswapV3PathCompat(),
                recipient: FROM,
                deadline: block.timestamp + 1,
                amountIn: amount(),
                amountOutMinimum: 1
            })
        );
        snapEnd();
    }

    function testUniswapV3UniversalRouterToNative()
        public
        skipIf(uniswapV3PathCompat().length == 0)
        skipIf(toToken() != WETH)
    {
        bytes memory commands = new bytes(3);
        bytes[] memory inputs = new bytes[](3);

        IAllowanceTransfer.PermitSingle memory permit =
            defaultERC20PermitSingle(address(fromToken()), PERMIT2_FROM_NONCE);
        bytes memory signature =
            getPermitSingleSignature(permit, address(UNIVERSAL_ROUTER), FROM_PRIVATE_KEY, permit2Domain);
        bytes memory path = uniswapV3PathCompat();

        (commands[0], inputs[0]) = encodePermit2Permit(fromToken(), PERMIT2_FROM_NONCE, signature);
        (commands[1], inputs[1]) = encodeV3Swap(RECIPIENT_ROUTER, amount(), 0 wei, path, true);
        (commands[2], inputs[2]) = encodeUnwrapWeth(RECIPIENT_TAKER, slippageLimit());

        (bool success,) = FROM.call(""); // touch FROM to warm it; in normal operation this would already be warmed
        require(success);

        vm.startPrank(FROM, FROM);
        snapStartName("universalRouter_uniswapV3");
        UNIVERSAL_ROUTER.execute(commands, inputs, block.timestamp);
        snapEnd();
        vm.stopPrank();
    }

    function testUniswapV3UniversalRouterFromNative()
        public
        skipIf(uniswapV3PathCompat().length == 0)
        skipIf(fromToken() != WETH)
    {
        bytes memory commands = new bytes(2);
        bytes[] memory inputs = new bytes[](2);

        bytes memory path = uniswapV3PathCompat();

        (commands[0], inputs[0]) = encodeWrapEth(RECIPIENT_ROUTER, CONTRACT_BALANCE);
        (commands[1], inputs[1]) = encodeV3Swap(RECIPIENT_TAKER, CONTRACT_BALANCE, slippageLimit(), path, false);

        vm.deal(FROM, amount());

        vm.startPrank(FROM, FROM);
        snapStartName("universalRouter_uniswapV3");
        UNIVERSAL_ROUTER.execute{value: amount()}(commands, inputs, block.timestamp);
        snapEnd();
        vm.stopPrank();
    }

    function testSettler_uniswapV3VIP_toNative()
        public
        skipIf(uniswapV3PathVIP().length == 0)
        skipIf(toToken() != WETH)
    {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        Settler _settler = settler;

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.UNISWAPV3_VIP, (address(_settler), permit, uniswapV3PathVIP(), sig, 0 wei)),
            abi.encodeCall(
                ISettlerActions.BASIC,
                (address(WETH), 1_000_000, address(WETH), 4, abi.encodeWithSignature("withdraw(uint256)", 0 wei))
            )
        );
        ISettlerBase.AllowedSlippage memory slippage =
            ISettlerBase.AllowedSlippage({recipient: FROM, buyToken: ETH, minAmountOut: slippageLimit()});

        (bool success,) = FROM.call(""); // touch FROM to warm it; in normal operation this would already be warmed
        require(success);

        vm.startPrank(FROM, FROM);
        snapStartName("settler_uniswapV3VIP_toNative");
        _settler.execute(slippage, actions, bytes32(0));
        snapEnd();
    }

    function testSettler_uniswapV3_fromNative() public skipIf(uniswapV3Path().length == 0) skipIf(fromToken() != WETH) {
        Settler _settler = settler;

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.BASIC,
                (address(ETH), 1_000_000, address(WETH), 4, abi.encodeWithSignature("deposit()", 0 wei))
            ),
            abi.encodeCall(ISettlerActions.UNISWAPV3, (FROM, 1_000_000, uniswapV3Path(), slippageLimit()))
        );
        ISettlerBase.AllowedSlippage memory slippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0 ether
        });

        vm.deal(FROM, amount());
        vm.startPrank(FROM, FROM);
        snapStartName("settler_uniswapV3_fromNative");
        _settler.execute{value: amount()}(slippage, actions, bytes32(0));
        snapEnd();
    }
}

interface INamiPool is IUniswapV3Pool {
    function token0() external view returns (IERC20);
    function token1() external view returns (IERC20);
    function factory() external view returns (address);
}

interface INamiFactory {
    function poolDeployer() external view returns (address);
    function poolByPair(address, address) external view returns (address);
}

abstract contract NamiPairTest is SettlerMetaTxnPairTest {
    bytes private callbackData;
    bool private underpay;
    bool private callbackReceived;
    int256 private callbackAmount0;
    int256 private callbackAmount1;

    function setUp() public override {
        super.setUp();
        // Permit2 signatures require the test payer to behave as an EOA.
        vm.etch(FROM, bytes(""));
    }

    function namiFactory() internal pure virtual returns (address);
    function namiPoolDeployer() internal pure virtual returns (address);
    function namiPool() internal pure virtual returns (INamiPool);

    function _testName() internal pure override returns (string memory) {
        return string.concat("NAMI-", _testChainId());
    }

    function amount() internal pure override returns (uint256) {
        return 0.0001 ether;
    }

    function uniswapV3Path() internal view override returns (bytes memory) {
        return abi.encodePacked(fromToken(), namiForkId, uint24(0), sqrtPriceLimitX96FromTo(), toToken());
    }

    function testNami_poolDerivation() public view {
        IERC20 token0 = namiPool().token0();
        IERC20 token1 = namiPool().token1();
        address derived = address(
            uint160(
                uint256(
                    keccak256(
                        abi.encodePacked(
                            hex"ff", namiPoolDeployer(), keccak256(abi.encode(token0, token1)), namiInitHash
                        )
                    )
                )
            )
        );
        assertEq(derived, address(namiPool()));
        assertEq(namiPool().factory(), namiFactory());
        assertEq(INamiFactory(namiFactory()).poolDeployer(), namiPoolDeployer());
        assertEq(INamiFactory(namiFactory()).poolByPair(address(token0), address(token1)), derived);
    }

    function testNami_settler() public {
        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(ISettlerActions.UNISWAPV3, (address(settler), 1_000_000, uniswapV3Path(), 1))
        );
        _executeNami(actions, "settler_nami");
    }

    function testNami_settlerVIP() public {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.UNISWAPV3_VIP, (address(settler), permit, uniswapV3PathVIP(), sig, 1))
        );
        _executeNami(actions, "settler_namiVIP");
    }

    function testNami_slippageReverts() public {
        safeApproveIfBelow(fromToken(), FROM, address(PERMIT2), amount());
        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(ISettlerActions.UNISWAPV3, (address(settler), 1_000_000, uniswapV3Path(), type(uint256).max))
        );
        vm.expectPartialRevert(TooMuchSlippage.selector);
        vm.prank(FROM);
        settler.execute(
            ISettlerBase.AllowedSlippage({recipient: FROM, buyToken: toToken(), minAmountOut: 1}), actions, bytes32(0)
        );
    }

    function _executeNami(bytes[] memory actions, string memory name) private {
        safeApproveIfBelow(fromToken(), FROM, address(PERMIT2), amount());
        uint256 beforeIn = fromToken().balanceOf(FROM);
        uint256 beforeOut = toToken().balanceOf(FROM);
        vm.prank(FROM);
        snapStartName(name);
        settler.execute(
            ISettlerBase.AllowedSlippage({recipient: FROM, buyToken: toToken(), minAmountOut: 1}), actions, bytes32(0)
        );
        snapEnd();
        assertEq(beforeIn - fromToken().balanceOf(FROM), amount());
        assertGt(toToken().balanceOf(FROM), beforeOut);
        assertEq(fromToken().balanceOf(address(settler)), 0);
        assertEq(toToken().balanceOf(address(settler)), 0);
    }

    function testNami_callbackAndDeltas_zeroForOne() public {
        _checkSwap(true);
    }

    function testNami_callbackAndDeltas_oneForZero() public {
        _checkSwap(false);
    }

    function _checkSwap(bool zeroForOne) private {
        IERC20 input = zeroForOne ? namiPool().token0() : namiPool().token1();
        IERC20 output = zeroForOne ? namiPool().token1() : namiPool().token0();
        uint256 sellAmount = input.decimals() > 12 ? 0.0001 ether : 10_000;
        deal(address(input), address(this), sellAmount);
        uint256 beforeOut = output.balanceOf(address(this));
        callbackData = abi.encodePacked(bytes32(type(uint256).max), address(this), hex"00010200ff", bytes32(uint256(7)));
        (int256 amount0, int256 amount1) = namiPool()
            .swap(
                address(this),
                zeroForOne,
                int256(sellAmount),
                zeroForOne ? uint160(4295128740) : uint160(1461446703485210103287273052203988822378723970341),
                callbackData
            );
        assertTrue(callbackReceived);
        assertEq(amount0, callbackAmount0);
        assertEq(amount1, callbackAmount1);
        int256 paid = zeroForOne ? amount0 : amount1;
        int256 received = -(zeroForOne ? amount1 : amount0);
        assertGt(paid, 0);
        assertGt(received, 0);
        assertEq(sellAmount - input.balanceOf(address(this)), uint256(paid));
        assertEq(output.balanceOf(address(this)) - beforeOut, uint256(received));
    }

    function testNami_underpaymentReverts() public {
        underpay = true;
        callbackData = hex"00ff0001";
        deal(address(fromToken()), address(this), amount());
        vm.expectRevert(bytes4(keccak256("insufficientInputAmount()")));
        namiPool()
            .swap(
                address(this),
                address(fromToken()) < address(toToken()),
                int256(amount()),
                sqrtPriceLimitX96FromTo(),
                callbackData
            );
    }

    function testNami_unsolicitedCallbackReverts() public {
        vm.expectRevert();
        IAlgebraCallback(address(settler)).algebraSwapCallback(1, -1, abi.encodePacked(FROM, fromToken()));
    }

    function algebraSwapCallback(int256 amount0, int256 amount1, bytes calldata data) external {
        assertEq(msg.sender, address(namiPool()));
        assertEq(data, callbackData);
        assertFalse(callbackReceived);
        callbackReceived = true;
        callbackAmount0 = amount0;
        callbackAmount1 = amount1;
        if (amount0 > 0) assertTrue(namiPool().token0().transfer(msg.sender, uint256(amount0) - (underpay ? 1 : 0)));
        if (amount1 > 0) assertTrue(namiPool().token1().transfer(msg.sender, uint256(amount1) - (underpay ? 1 : 0)));
    }
}

contract NamiMainnetTest is NamiPairTest {
    function _testBlockNumber() internal pure override returns (uint256) {
        return 26193140;
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
    }

    function namiFactory() internal pure override returns (address) {
        return 0xD1Bf4A24DC17Da21410a7b047471E191eA538d43;
    }

    function namiPoolDeployer() internal pure override returns (address) {
        return namiMainnetFactory;
    }

    function namiPool() internal pure override returns (INamiPool) {
        return INamiPool(0x152cFC187A0C0695eb946c3a2f0a8C6604f0026d);
    }
}

contract NamiBaseTest is NamiPairTest {
    function _testChainId() internal pure override returns (string memory) {
        return "base";
    }

    function _testBlockNumber() internal pure override returns (uint256) {
        return 52610225;
    }

    function settlerInitCode() internal pure override returns (bytes memory) {
        return bytes.concat(type(BaseSettler).creationCode, abi.encode(bytes20(0)));
    }

    function settlerMetaTxnInitCode() internal pure override returns (bytes memory) {
        return bytes.concat(type(BaseSettlerMetaTxn).creationCode, abi.encode(bytes20(0)));
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(0x4200000000000000000000000000000000000006);
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913);
    }

    function namiFactory() internal pure override returns (address) {
        return 0xf4502A98A15e82D66d28D2381E2F3A407ea45b83;
    }

    function namiPoolDeployer() internal pure override returns (address) {
        return namiBaseFactory;
    }

    function namiPool() internal pure override returns (INamiPool) {
        return INamiPool(0x0E8AF367DbA0c9CB4674D38539eF3465A25a7237);
    }
}

contract NamiRobinhoodTest is NamiPairTest {
    function _testChainId() internal pure override returns (string memory) {
        return "robinhood";
    }

    function _testBlockNumber() internal pure override returns (uint256) {
        return 88654012;
    }

    function settlerInitCode() internal pure override returns (bytes memory) {
        return bytes.concat(type(RobinHoodSettler).creationCode, abi.encode(bytes20(0)));
    }

    function settlerMetaTxnInitCode() internal pure override returns (bytes memory) {
        return bytes.concat(type(RobinHoodSettlerMetaTxn).creationCode, abi.encode(bytes20(0)));
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(0x0Bd7D308f8E1639FAb988df18A8011f41EAcAD73);
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(0x5fc5360D0400a0Fd4f2af552ADD042D716F1d168);
    }

    function namiFactory() internal pure override returns (address) {
        return 0xDeDB80903df19f9dB9b393eb66E07511CB9ABdA2;
    }

    function namiPoolDeployer() internal pure override returns (address) {
        return namiRobinhoodFactory;
    }

    function namiPool() internal pure override returns (INamiPool) {
        return INamiPool(0xA730C5d09DD9926F798530D52e572D7594b952F3);
    }
}
