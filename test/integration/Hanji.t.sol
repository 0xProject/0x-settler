// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {IHanjiPool} from "src/core/Hanji.sol";

import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {Settler} from "src/Settler.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";
import {MonadSettler} from "src/chains/Monad/TakerSubmitted.sol";

import {AllowanceHolderPairTest} from "./AllowanceHolderPairTest.t.sol";

/// @title Hanji Integration Tests
/// @notice Tests all boolean flag combinations for the Hanji DEX integration on Monad
/// @dev Pool: 0xe27d2334ab6402956c2e6e517d16fa206b3053ae (WMON/USDC)
///      - tokenX (WMON): 0x3bd359C1119dA7Da1D913D1C4D2B7c461115433A (18 decimals)
///      - tokenY (USDC): 0x754704Bc059F8C67012fEd69BC8A327a5aafb603 (6 decimals)
///      - supports_native_eth: true
///      - is_token_x_weth: true
abstract contract HanjiTest is AllowanceHolderPairTest {
    // Pool configuration from getConfig()
    // scaling_factor_token_x = 1e18, scaling_factor_token_y = 1
    uint256 internal constant WMON_SCALING_FACTOR = 1e18;
    uint256 internal constant USDC_SCALING_FACTOR = 1;

    // Price limit for trades - use extreme values to execute as market orders
    // Price is encoded as uint72 with constraint: 0 < price <= 999999000000000000000
    // For isAsk=true (sell tokenX for tokenY): use 1 (minimum price, executes at best bid)
    // For isAsk=false (buy tokenX with tokenY): use max valid price (executes at best ask)
    uint256 internal constant PRICE_LIMIT_ASK = 1;
    uint256 internal constant PRICE_LIMIT_BID = 999999000000000000000;

    function _testBlockNumber() internal pure virtual override returns (uint256) {
        return 48413547;
    }

    function _testChainId() internal pure virtual override returns (string memory) {
        return "monad";
    }

    function settlerInitCode() internal virtual override returns (bytes memory) {
        return bytes.concat(type(MonadSettler).creationCode, abi.encode(bytes20(0)));
    }

    function setUp() public virtual override {
        super.setUp();
        vm.makePersistent(address(allowanceHolder));
        vm.makePersistent(address(settler));
        vm.makePersistent(address(fromToken()));
        vm.makePersistent(address(toToken()));
        if (address(toToken()).code.length != 0) {
            deal(address(toToken()), FROM, amount());
        }
        _setHanjiLabels();
    }

    function _setHanjiLabels() private {
        vm.label(address(hanjiPool()), "HanjiPool_WMON_USDC");
        vm.label(wmon(), "WMON");
        vm.label(usdc(), "USDC");
    }

    // Test must implement receive() to accept native ETH
    receive() external payable {}

    function hanjiPool() internal pure virtual returns (IHanjiPool) {
        return IHanjiPool(0xE27d2334Ab6402956c2E6E517d16fa206B3053ae);
    }

    function wmon() internal pure returns (address) {
        return 0x3bd359C1119dA7Da1D913D1C4D2B7c461115433A;
    }

    function usdc() internal pure returns (address) {
        return 0x754704Bc059F8C67012fEd69BC8A327a5aafb603;
    }

    // ========== BASIC ERC20 SWAP TESTS ==========

    /// @notice Test where Settler is the order_owner (no proxy check needed)
    function testHanji_settlerAsOrderOwner() public skipIf(address(hanjiPool()) == address(0)) {
        uint256 sellAmount = 1 ether;
        IERC20 sellToken = IERC20(wmon());
        IERC20 buyToken = IERC20(usdc());

        deal(address(sellToken), FROM, sellAmount);

        uint256 beforeBalanceTo = buyToken.balanceOf(address(settler));

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(sellToken), sellAmount, 0);
        bytes memory sig = new bytes(0);

        // Use address(settler) as recipient so Settler is the order_owner
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.HANJI,
                (
                    address(settler), // recipient = order_owner = Settler itself
                    address(sellToken),
                    10_000,
                    address(hanjiPool()),
                    WMON_SCALING_FACTOR,
                    USDC_SCALING_FACTOR,
                    true, // isAsk
                    false, // useNative
                    PRICE_LIMIT_ASK,
                    0
                )
            )
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0});

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        vm.startPrank(FROM, FROM);
        snapStartName("hanji_settlerAsOrderOwner");
        _allowanceHolder.exec(address(_settler), address(sellToken), sellAmount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = buyToken.balanceOf(address(settler));
        assertGt(afterBalanceTo, beforeBalanceTo, "Settler should have received USDC");
    }

    /// @notice Test selling WMON for USDC (isAsk=true, useNative=false)
    function testHanji_sellWmonForUsdc() public skipIf(address(hanjiPool()) == address(0)) {
        _testHanjiSwap({
            sellToken: IERC20(wmon()),
            buyToken: IERC20(usdc()),
            sellAmount: 1 ether,
            isAsk: true,
            useNative: false,
            sellScalingFactor: WMON_SCALING_FACTOR,
            buyScalingFactor: USDC_SCALING_FACTOR,
            priceLimit: PRICE_LIMIT_ASK,
            testName: "hanji_sellWmonForUsdc"
        });
    }

    /// @notice Test selling USDC for WMON (isAsk=false, useNative=false)
    function testHanji_sellUsdcForWmon() public skipIf(address(hanjiPool()) == address(0)) {
        _testHanjiSwap({
            sellToken: IERC20(usdc()),
            buyToken: IERC20(wmon()),
            sellAmount: 10e6, // 10 USDC
            isAsk: false,
            useNative: false,
            sellScalingFactor: USDC_SCALING_FACTOR,
            buyScalingFactor: WMON_SCALING_FACTOR,
            priceLimit: PRICE_LIMIT_BID,
            testName: "hanji_sellUsdcForWmon"
        });
    }

    // ========== NATIVE ETH SWAP TESTS ==========

    /// @notice Test selling native ETH for USDC (sendNative=true, isAsk=true)
    /// @dev When sellToken is ETH_ADDRESS, sendNative becomes true
    function testHanji_sellNativeForUsdc() public skipIf(address(hanjiPool()) == address(0)) {
        uint256 sellAmount = 1 ether;
        IERC20 buyToken = IERC20(usdc());

        // Fund the settler with native ETH
        vm.deal(address(settler), sellAmount);

        uint256 beforeBalanceTo = buyToken.balanceOf(FROM);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.HANJI,
                (
                    FROM,
                    0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE, // ETH_ADDRESS
                    10_000, // 100% of balance
                    address(hanjiPool()),
                    WMON_SCALING_FACTOR,
                    USDC_SCALING_FACTOR,
                    true, // isAsk (selling tokenX/WMON for tokenY/USDC)
                    false, // useNative (not receiving native)
                    PRICE_LIMIT_ASK,
                    0 // minBuyAmount
                )
            )
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0});

        vm.startPrank(FROM, FROM);
        snapStartName("hanji_sellNativeForUsdc");
        settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = buyToken.balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo, "Should have received USDC");
        assertEq(address(settler).balance, 0, "Settler should have no ETH left");
    }

    /// @notice Test selling USDC for native ETH (receiveNative=true, isAsk=false, useNative=true)
    /// @dev When useNative=true and not sending native, receiveNative becomes true
    function testHanji_sellUsdcForNative() public skipIf(address(hanjiPool()) == address(0)) {
        uint256 sellAmount = 10e6; // 10 USDC
        IERC20 sellToken = IERC20(usdc());

        // Fund FROM with USDC
        deal(address(sellToken), FROM, sellAmount);

        uint256 beforeBalanceEth = FROM.balance;
        uint256 beforeBalanceUsdc = sellToken.balanceOf(FROM);

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(sellToken), sellAmount, 0);
        bytes memory sig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.HANJI,
                (
                    FROM,
                    address(sellToken),
                    10_000, // 100% of balance
                    address(hanjiPool()),
                    USDC_SCALING_FACTOR,
                    WMON_SCALING_FACTOR,
                    false, // isAsk (selling tokenY/USDC for tokenX/WMON)
                    true, // useNative (receiving native ETH)
                    PRICE_LIMIT_BID,
                    0 // minBuyAmount
                )
            )
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0});

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;

        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        vm.startPrank(FROM, FROM);
        snapStartName("hanji_sellUsdcForNative");
        _allowanceHolder.exec(address(_settler), address(sellToken), sellAmount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceEth = FROM.balance;
        uint256 afterBalanceUsdc = sellToken.balanceOf(FROM);
        assertGt(afterBalanceEth, beforeBalanceEth, "Should have received native ETH");
        assertEq(afterBalanceUsdc, beforeBalanceUsdc - sellAmount, "Should have spent USDC");
    }

    // ========== USE_NATIVE FLAG INTERACTION TESTS ==========

    /// @notice Test that useNative=true has no effect when selling native (sendNative already true)
    /// @dev receiveNative = useNative.andNot(sendNative), so when sendNative=true, receiveNative=false
    function testHanji_sellNative_useNativeFlag() public skipIf(address(hanjiPool()) == address(0)) {
        uint256 sellAmount = 1 ether;
        IERC20 buyToken = IERC20(usdc());

        // Fund the settler with native ETH
        vm.deal(address(settler), sellAmount);

        uint256 beforeBalanceTo = buyToken.balanceOf(FROM);

        // useNative=true but since we're sending native, receiveNative will be false
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.HANJI,
                (
                    FROM,
                    0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE, // ETH_ADDRESS
                    10_000,
                    address(hanjiPool()),
                    WMON_SCALING_FACTOR,
                    USDC_SCALING_FACTOR,
                    true, // isAsk
                    true, // useNative (has no effect when sendNative=true)
                    PRICE_LIMIT_ASK,
                    0
                )
            )
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0});

        vm.startPrank(FROM, FROM);
        snapStartName("hanji_sellNative_useNativeFlag");
        settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = buyToken.balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo, "Should have received USDC");
    }

    /// @notice Test useNative=true when buying WMON (tokenX) - should receive native
    function testHanji_buyWmon_receiveNative() public skipIf(address(hanjiPool()) == address(0)) {
        uint256 sellAmount = 10e6; // 10 USDC
        IERC20 sellToken = IERC20(usdc());

        deal(address(sellToken), FROM, sellAmount);

        uint256 beforeBalanceEth = FROM.balance;

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(sellToken), sellAmount, 0);
        bytes memory sig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.HANJI,
                (
                    FROM,
                    address(sellToken),
                    10_000,
                    address(hanjiPool()),
                    USDC_SCALING_FACTOR,
                    WMON_SCALING_FACTOR,
                    false, // isAsk=false (buying tokenX/WMON)
                    true, // useNative=true (receive native ETH)
                    PRICE_LIMIT_BID,
                    0
                )
            )
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0});

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        vm.startPrank(FROM, FROM);
        snapStartName("hanji_buyWmon_receiveNative");
        _allowanceHolder.exec(address(_settler), address(sellToken), sellAmount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceEth = FROM.balance;
        assertGt(afterBalanceEth, beforeBalanceEth, "Should have received native ETH");
    }

    /// @notice Test useNative=false when buying WMON - should receive WMON token
    function testHanji_buyWmon_receiveWrapped() public skipIf(address(hanjiPool()) == address(0)) {
        uint256 sellAmount = 10e6; // 10 USDC
        IERC20 sellToken = IERC20(usdc());
        IERC20 buyToken = IERC20(wmon());

        deal(address(sellToken), FROM, sellAmount);

        uint256 beforeBalanceWmon = buyToken.balanceOf(FROM);
        uint256 beforeBalanceEth = FROM.balance;

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(sellToken), sellAmount, 0);
        bytes memory sig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.HANJI,
                (
                    FROM,
                    address(sellToken),
                    10_000,
                    address(hanjiPool()),
                    USDC_SCALING_FACTOR,
                    WMON_SCALING_FACTOR,
                    false, // isAsk=false (buying tokenX/WMON)
                    false, // useNative=false (receive wrapped WMON)
                    PRICE_LIMIT_BID,
                    0
                )
            )
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0});

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        vm.startPrank(FROM, FROM);
        snapStartName("hanji_buyWmon_receiveWrapped");
        _allowanceHolder.exec(address(_settler), address(sellToken), sellAmount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceWmon = buyToken.balanceOf(FROM);
        uint256 afterBalanceEth = FROM.balance;
        assertGt(afterBalanceWmon, beforeBalanceWmon, "Should have received WMON token");
        assertEq(afterBalanceEth, beforeBalanceEth, "Should not have received native ETH");
    }

    // ========== CUSTODY TRANSFER TESTS ==========

    /// @notice Test custody transfer: tokens sent directly to pool (bps=0)
    function testHanji_custody_sellWmonForUsdc() public skipIf(address(hanjiPool()) == address(0)) {
        uint256 sellAmount = 1 ether;
        IERC20 sellToken = IERC20(wmon());
        IERC20 buyToken = IERC20(usdc());

        deal(address(sellToken), FROM, sellAmount);

        uint256 beforeBalanceFrom = sellToken.balanceOf(FROM);
        uint256 beforeBalanceTo = buyToken.balanceOf(FROM);

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(sellToken), sellAmount, 0);
        bytes memory sig = new bytes(0);

        // Transfer directly to pool, then use bps=0
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(hanjiPool()), permit, sig)),
            abi.encodeCall(
                ISettlerActions.HANJI,
                (
                    FROM,
                    address(sellToken),
                    0, // bps=0 means use pool's custody balance
                    address(hanjiPool()),
                    WMON_SCALING_FACTOR,
                    USDC_SCALING_FACTOR,
                    true, // isAsk
                    false, // useNative
                    PRICE_LIMIT_ASK,
                    0
                )
            )
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0});

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        vm.startPrank(FROM, FROM);
        snapStartName("hanji_custody_sellWmonForUsdc");
        _allowanceHolder.exec(address(_settler), address(sellToken), sellAmount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceFrom = sellToken.balanceOf(FROM);
        uint256 afterBalanceTo = buyToken.balanceOf(FROM);
        assertEq(afterBalanceFrom, beforeBalanceFrom - sellAmount, "Should have spent WMON");
        assertGt(afterBalanceTo, beforeBalanceTo, "Should have received USDC");
    }

    /// @notice Test custody transfer for reverse direction (USDC -> WMON)
    function testHanji_custody_sellUsdcForWmon() public skipIf(address(hanjiPool()) == address(0)) {
        uint256 sellAmount = 10e6; // 10 USDC
        IERC20 sellToken = IERC20(usdc());
        IERC20 buyToken = IERC20(wmon());

        deal(address(sellToken), FROM, sellAmount);

        uint256 beforeBalanceFrom = sellToken.balanceOf(FROM);
        uint256 beforeBalanceTo = buyToken.balanceOf(FROM);

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(sellToken), sellAmount, 0);
        bytes memory sig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(hanjiPool()), permit, sig)),
            abi.encodeCall(
                ISettlerActions.HANJI,
                (
                    FROM,
                    address(sellToken),
                    0, // bps=0 for custody
                    address(hanjiPool()),
                    USDC_SCALING_FACTOR,
                    WMON_SCALING_FACTOR,
                    false, // isAsk
                    false, // useNative
                    PRICE_LIMIT_BID,
                    0
                )
            )
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0});

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        vm.startPrank(FROM, FROM);
        snapStartName("hanji_custody_sellUsdcForWmon");
        _allowanceHolder.exec(address(_settler), address(sellToken), sellAmount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceFrom = sellToken.balanceOf(FROM);
        uint256 afterBalanceTo = buyToken.balanceOf(FROM);
        assertEq(afterBalanceFrom, beforeBalanceFrom - sellAmount, "Should have spent USDC");
        assertGt(afterBalanceTo, beforeBalanceTo, "Should have received WMON");
    }

    // ========== SLIPPAGE TESTS ==========

    /// @notice Test that minBuyAmount causes revert when not met
    function testHanji_revert_tooMuchSlippage() public skipIf(address(hanjiPool()) == address(0)) {
        uint256 sellAmount = 1 ether;
        IERC20 sellToken = IERC20(wmon());

        deal(address(sellToken), FROM, sellAmount);

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(sellToken), sellAmount, 0);
        bytes memory sig = new bytes(0);

        // Set an impossibly high minBuyAmount
        uint256 impossibleMinBuyAmount = type(uint128).max;

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.HANJI,
                (
                    FROM,
                    address(sellToken),
                    10_000,
                    address(hanjiPool()),
                    WMON_SCALING_FACTOR,
                    USDC_SCALING_FACTOR,
                    true, // isAsk
                    false, // useNative
                    PRICE_LIMIT_ASK,
                    impossibleMinBuyAmount // This should cause a revert
                )
            )
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0});

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        vm.startPrank(FROM, FROM);
        vm.expectRevert(); // Should revert due to slippage check
        _allowanceHolder.exec(address(_settler), address(sellToken), sellAmount, payable(address(_settler)), ahData);
        vm.stopPrank();
    }

    // ========== HELPER FUNCTIONS ==========

    function _testHanjiSwap(
        IERC20 sellToken,
        IERC20 buyToken,
        uint256 sellAmount,
        bool isAsk,
        bool useNative,
        uint256 sellScalingFactor,
        uint256 buyScalingFactor,
        uint256 priceLimit,
        string memory testName
    ) internal {
        deal(address(sellToken), FROM, sellAmount);

        uint256 beforeBalanceFrom = sellToken.balanceOf(FROM);
        uint256 beforeBalanceTo = buyToken.balanceOf(FROM);

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(sellToken), sellAmount, 0);
        bytes memory sig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.HANJI,
                (
                    FROM,
                    address(sellToken),
                    10_000, // 100% of balance
                    address(hanjiPool()),
                    sellScalingFactor,
                    buyScalingFactor,
                    isAsk,
                    useNative,
                    priceLimit,
                    0 // minBuyAmount
                )
            )
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0});

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        vm.startPrank(FROM, FROM);
        snapStartName(testName);
        _allowanceHolder.exec(address(_settler), address(sellToken), sellAmount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceFrom = sellToken.balanceOf(FROM);
        uint256 afterBalanceTo = buyToken.balanceOf(FROM);
        assertEq(afterBalanceFrom, beforeBalanceFrom - sellAmount, "Should have spent sell token");
        assertGt(afterBalanceTo, beforeBalanceTo, "Should have received buy token");
    }

    // Required overrides - these are set per-test but we provide defaults
    function fromToken() internal view virtual override returns (IERC20) {
        return IERC20(wmon());
    }

    function toToken() internal view virtual override returns (IERC20) {
        return IERC20(usdc());
    }

    function amount() internal view virtual override returns (uint256) {
        return 1 ether;
    }

    function uniswapV3Path() internal virtual override returns (bytes memory) {
        return new bytes(0); // Not used for Hanji tests
    }

    function uniswapV2Pool() internal virtual override returns (address) {
        return address(0); // Not used for Hanji tests
    }
}

/// @title Hanji WMON/USDC Test
/// @notice Concrete implementation for testing WMON/USDC pair
contract HanjiWmonUsdcTest is HanjiTest {
    function _testName() internal pure override returns (string memory) {
        return "hanji_wmon_usdc";
    }
}
