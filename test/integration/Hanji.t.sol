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

interface IWMON {
    function withdraw(uint256 amount) external;
}

/// @title Hanji Integration Tests - Base
/// @notice Base contract for Hanji DEX integration tests on Monad
/// @dev Pool: 0xE27d2334Ab6402956c2E6E517d16fa206B3053ae (WMON/USDC)
///      - tokenX (WMON): 0x3bd359C1119dA7Da1D913D1C4D2B7c461115433A (18 decimals)
///      - tokenY (USDC): 0x754704Bc059F8C67012fEd69BC8A327a5aafb603 (6 decimals)
///      - supports_native_eth: true
///      - is_token_x_weth: true
abstract contract HanjiTestBase is AllowanceHolderPairTest {
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

    address internal constant WMON = 0x3bd359C1119dA7Da1D913D1C4D2B7c461115433A;
    address internal constant USDC = 0x754704Bc059F8C67012fEd69BC8A327a5aafb603;
    address internal constant ETH_ADDRESS = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;

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
        _setHanjiLabels();
    }

    function _setHanjiLabels() private {
        vm.label(address(hanjiPool()), "HanjiPool_WMON_USDC");
        vm.label(WMON, "WMON");
        vm.label(USDC, "USDC");
    }

    // Required for receiving native ETH
    receive() external payable {}

    function hanjiPool() internal pure virtual returns (IHanjiPool) {
        return IHanjiPool(0xE27d2334Ab6402956c2E6E517d16fa206B3053ae);
    }

    function uniswapV3Path() internal virtual override returns (bytes memory) {
        return new bytes(0); // Not used for Hanji tests
    }

    function uniswapV2Pool() internal virtual override returns (address) {
        return address(0); // Not used for Hanji tests
    }

    /// @dev Returns scaling factor for sell token based on trade direction
    function sellScalingFactor() internal view virtual returns (uint256);

    /// @dev Returns scaling factor for buy token based on trade direction
    function buyScalingFactor() internal view virtual returns (uint256);

    /// @dev Returns whether this is an ask order (selling tokenX/WMON)
    function isAsk() internal pure virtual returns (bool);

    /// @dev Returns the appropriate price limit for the trade direction
    function priceLimit() internal pure virtual returns (uint256) {
        return isAsk() ? PRICE_LIMIT_ASK : PRICE_LIMIT_BID;
    }
}

// ============================================================================
// WMON -> USDC Tests (isAsk = true)
// ============================================================================

/// @title Hanji WMON to USDC Tests
/// @notice Tests selling WMON for USDC (isAsk=true)
contract HanjiWmonToUsdcTest is HanjiTestBase {
    function _testName() internal pure override returns (string memory) {
        return "hanji_wmon_to_usdc";
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(WMON);
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(USDC);
    }

    function amount() internal pure override returns (uint256) {
        return 1 ether;
    }

    function sellScalingFactor() internal pure override returns (uint256) {
        return WMON_SCALING_FACTOR;
    }

    function buyScalingFactor() internal pure override returns (uint256) {
        return USDC_SCALING_FACTOR;
    }

    function isAsk() internal pure override returns (bool) {
        return true;
    }

    // ========== BASIC SWAP TEST ==========

    /// @notice Test selling WMON for USDC (isAsk=true, useNative=false)
    function testHanji_sellWmonForUsdc() public skipIf(address(hanjiPool()) == address(0)) {
        uint256 _amount = amount();
        IERC20 _fromToken = fromToken();
        IERC20 _toToken = toToken();

        uint256 beforeBalanceFrom = _fromToken.balanceOf(FROM);
        uint256 beforeBalanceTo = _toToken.balanceOf(FROM);

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(_fromToken), _amount, 0);
        bytes memory sig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.HANJI,
                (
                    FROM,
                    address(_fromToken),
                    10_000, // 100% of balance
                    address(hanjiPool()),
                    sellScalingFactor(),
                    buyScalingFactor(),
                    isAsk(),
                    false, // useNative
                    priceLimit(),
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
        snapStartName("hanji_sellWmonForUsdc");
        _allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceFrom = _fromToken.balanceOf(FROM);
        uint256 afterBalanceTo = _toToken.balanceOf(FROM);
        assertEq(afterBalanceFrom, beforeBalanceFrom - _amount, "Should have spent WMON");
        assertGt(afterBalanceTo, beforeBalanceTo, "Should have received USDC");
    }

    // ========== NATIVE ETH SWAP TEST ==========

    /// @notice Test selling native MON for USDC (sendNative=true, isAsk=true)
    /// @dev Unwraps WMON to native using BASIC, then sells via HANJI
    function testHanji_sellNativeForUsdc() public skipIf(address(hanjiPool()) == address(0)) {
        uint256 _amount = amount();
        IERC20 _fromToken = fromToken(); // WMON
        IERC20 _toToken = toToken(); // USDC

        uint256 beforeBalanceFrom = _fromToken.balanceOf(FROM);
        uint256 beforeBalanceTo = _toToken.balanceOf(FROM);

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(_fromToken), _amount, 0);
        bytes memory sig = new bytes(0);

        // Transfer WMON to Settler, unwrap to native, then sell native for USDC
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            // Unwrap WMON to native ETH using BASIC
            abi.encodeCall(
                ISettlerActions.BASIC,
                (address(_fromToken), 10_000, address(_fromToken), 4, abi.encodeCall(IWMON.withdraw, (0)))
            ),
            // Sell native ETH for USDC
            abi.encodeCall(
                ISettlerActions.HANJI,
                (
                    FROM,
                    ETH_ADDRESS, // Selling native ETH
                    10_000,
                    address(hanjiPool()),
                    sellScalingFactor(),
                    buyScalingFactor(),
                    isAsk(),
                    false, // useNative (not receiving native)
                    priceLimit(),
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
        snapStartName("hanji_sellNativeForUsdc");
        _allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceFrom = _fromToken.balanceOf(FROM);
        uint256 afterBalanceTo = _toToken.balanceOf(FROM);
        assertEq(afterBalanceFrom, beforeBalanceFrom - _amount, "Should have spent WMON");
        assertGt(afterBalanceTo, beforeBalanceTo, "Should have received USDC");
        assertEq(address(settler).balance, 0, "Settler should have no ETH left");
    }

    // ========== CUSTODY TRANSFER TEST ==========

    /// @notice Test custody transfer: tokens sent directly to pool (bps=0)
    function testHanji_custody_sellWmonForUsdc() public skipIf(address(hanjiPool()) == address(0)) {
        uint256 _amount = amount();
        IERC20 _fromToken = fromToken();
        IERC20 _toToken = toToken();

        uint256 beforeBalanceFrom = _fromToken.balanceOf(FROM);
        uint256 beforeBalanceTo = _toToken.balanceOf(FROM);

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(_fromToken), _amount, 0);
        bytes memory sig = new bytes(0);

        // Transfer directly to pool, then use bps=0
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(hanjiPool()), permit, sig)),
            abi.encodeCall(
                ISettlerActions.HANJI,
                (
                    FROM,
                    address(_fromToken),
                    0, // bps=0 means use pool's custody balance
                    address(hanjiPool()),
                    sellScalingFactor(),
                    buyScalingFactor(),
                    isAsk(),
                    false, // useNative
                    priceLimit(),
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
        _allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceFrom = _fromToken.balanceOf(FROM);
        uint256 afterBalanceTo = _toToken.balanceOf(FROM);
        assertEq(afterBalanceFrom, beforeBalanceFrom - _amount, "Should have spent WMON");
        assertGt(afterBalanceTo, beforeBalanceTo, "Should have received USDC");
    }

    // ========== SLIPPAGE TEST ==========

    /// @notice Test that minBuyAmount causes revert when not met
    function testHanji_revert_tooMuchSlippage() public skipIf(address(hanjiPool()) == address(0)) {
        uint256 _amount = amount();
        IERC20 _fromToken = fromToken();

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(_fromToken), _amount, 0);
        bytes memory sig = new bytes(0);

        // Set an impossibly high minBuyAmount
        uint256 impossibleMinBuyAmount = type(uint128).max;

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.HANJI,
                (
                    FROM,
                    address(_fromToken),
                    10_000,
                    address(hanjiPool()),
                    sellScalingFactor(),
                    buyScalingFactor(),
                    isAsk(),
                    false,
                    priceLimit(),
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
        _allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        vm.stopPrank();
    }

    // ========== SETTLER AS ORDER OWNER TEST ==========

    /// @notice Test where Settler is the order_owner (to check if proxy auth is needed even for self)
    function testHanji_settlerAsOrderOwner() public skipIf(address(hanjiPool()) == address(0)) {
        uint256 _amount = amount();
        IERC20 _fromToken = fromToken();
        IERC20 _toToken = toToken();

        uint256 beforeBalanceTo = _toToken.balanceOf(address(settler));

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(_fromToken), _amount, 0);
        bytes memory sig = new bytes(0);

        // Use address(settler) as recipient so Settler is the order_owner
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.HANJI,
                (
                    address(settler), // recipient = order_owner = Settler itself
                    address(_fromToken),
                    10_000,
                    address(hanjiPool()),
                    sellScalingFactor(),
                    buyScalingFactor(),
                    isAsk(),
                    false, // useNative
                    priceLimit(),
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
        _allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = _toToken.balanceOf(address(settler));
        assertGt(afterBalanceTo, beforeBalanceTo, "Settler should have received USDC");
    }
}

// ============================================================================
// USDC -> WMON Tests (isAsk = false)
// ============================================================================

/// @title Hanji USDC to WMON Tests
/// @notice Tests selling USDC for WMON (isAsk=false)
contract HanjiUsdcToWmonTest is HanjiTestBase {
    function _testName() internal pure override returns (string memory) {
        return "hanji_usdc_to_wmon";
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(USDC);
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(WMON);
    }

    function amount() internal pure override returns (uint256) {
        return 10e6; // 10 USDC
    }

    function sellScalingFactor() internal pure override returns (uint256) {
        return USDC_SCALING_FACTOR;
    }

    function buyScalingFactor() internal pure override returns (uint256) {
        return WMON_SCALING_FACTOR;
    }

    function isAsk() internal pure override returns (bool) {
        return false;
    }

    // ========== BASIC SWAP TEST ==========

    /// @notice Test selling USDC for WMON (isAsk=false, useNative=false)
    function testHanji_sellUsdcForWmon() public skipIf(address(hanjiPool()) == address(0)) {
        uint256 _amount = amount();
        IERC20 _fromToken = fromToken();
        IERC20 _toToken = toToken();

        uint256 beforeBalanceFrom = _fromToken.balanceOf(FROM);
        uint256 beforeBalanceTo = _toToken.balanceOf(FROM);

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(_fromToken), _amount, 0);
        bytes memory sig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.HANJI,
                (
                    FROM,
                    address(_fromToken),
                    10_000,
                    address(hanjiPool()),
                    sellScalingFactor(),
                    buyScalingFactor(),
                    isAsk(),
                    false, // useNative
                    priceLimit(),
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
        snapStartName("hanji_sellUsdcForWmon");
        _allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceFrom = _fromToken.balanceOf(FROM);
        uint256 afterBalanceTo = _toToken.balanceOf(FROM);
        assertEq(afterBalanceFrom, beforeBalanceFrom - _amount, "Should have spent USDC");
        assertGt(afterBalanceTo, beforeBalanceTo, "Should have received WMON");
    }

    // ========== RECEIVE NATIVE TEST ==========

    /// @notice Test selling USDC and receiving native MON (useNative=true)
    function testHanji_sellUsdcForNative() public skipIf(address(hanjiPool()) == address(0)) {
        uint256 _amount = amount();
        IERC20 _fromToken = fromToken();

        uint256 beforeBalanceFrom = _fromToken.balanceOf(FROM);
        uint256 beforeBalanceEth = FROM.balance;

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(_fromToken), _amount, 0);
        bytes memory sig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.HANJI,
                (
                    FROM,
                    address(_fromToken),
                    10_000,
                    address(hanjiPool()),
                    sellScalingFactor(),
                    buyScalingFactor(),
                    isAsk(),
                    true, // useNative - receive native MON instead of WMON
                    priceLimit(),
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
        snapStartName("hanji_sellUsdcForNative");
        _allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceFrom = _fromToken.balanceOf(FROM);
        uint256 afterBalanceEth = FROM.balance;
        assertEq(afterBalanceFrom, beforeBalanceFrom - _amount, "Should have spent USDC");
        assertGt(afterBalanceEth, beforeBalanceEth, "Should have received native MON");
    }

    // ========== RECEIVE WRAPPED VS NATIVE COMPARISON ==========

    /// @notice Test useNative=false when buying WMON - should receive WMON token
    function testHanji_buyWmon_receiveWrapped() public skipIf(address(hanjiPool()) == address(0)) {
        uint256 _amount = amount();
        IERC20 _fromToken = fromToken();
        IERC20 _toToken = toToken();

        uint256 beforeBalanceWmon = _toToken.balanceOf(FROM);
        uint256 beforeBalanceEth = FROM.balance;

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(_fromToken), _amount, 0);
        bytes memory sig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.HANJI,
                (
                    FROM,
                    address(_fromToken),
                    10_000,
                    address(hanjiPool()),
                    sellScalingFactor(),
                    buyScalingFactor(),
                    isAsk(),
                    false, // useNative=false - receive wrapped WMON
                    priceLimit(),
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
        _allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceWmon = _toToken.balanceOf(FROM);
        uint256 afterBalanceEth = FROM.balance;
        assertGt(afterBalanceWmon, beforeBalanceWmon, "Should have received WMON token");
        assertEq(afterBalanceEth, beforeBalanceEth, "Should not have received native MON");
    }

    // ========== CUSTODY TRANSFER TEST ==========

    /// @notice Test custody transfer for USDC -> WMON
    function testHanji_custody_sellUsdcForWmon() public skipIf(address(hanjiPool()) == address(0)) {
        uint256 _amount = amount();
        IERC20 _fromToken = fromToken();
        IERC20 _toToken = toToken();

        uint256 beforeBalanceFrom = _fromToken.balanceOf(FROM);
        uint256 beforeBalanceTo = _toToken.balanceOf(FROM);

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(_fromToken), _amount, 0);
        bytes memory sig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(hanjiPool()), permit, sig)),
            abi.encodeCall(
                ISettlerActions.HANJI,
                (
                    FROM,
                    address(_fromToken),
                    0, // bps=0 for custody
                    address(hanjiPool()),
                    sellScalingFactor(),
                    buyScalingFactor(),
                    isAsk(),
                    false, // useNative
                    priceLimit(),
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
        _allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceFrom = _fromToken.balanceOf(FROM);
        uint256 afterBalanceTo = _toToken.balanceOf(FROM);
        assertEq(afterBalanceFrom, beforeBalanceFrom - _amount, "Should have spent USDC");
        assertGt(afterBalanceTo, beforeBalanceTo, "Should have received WMON");
    }
}
