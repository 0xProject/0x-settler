// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {Settler} from "src/Settler.sol";

import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";

import {IEulerSwap} from "src/core/EulerSwap.sol";

import {AllowanceHolderPairTest} from "./AllowanceHolderPairTest.t.sol";

interface IEVC {
    function setAccountOperator(address account, address operator, bool authorized) external;
    function isAccountOperatorAuthorized(address account, address operator) external view returns (bool);
}

abstract contract EulerSwapTest is AllowanceHolderPairTest {
    using SafeTransferLib for IERC20;

    function eulerSwapPool() internal view virtual returns (address) {
        return address(0);
    }

    function eulerSwapBlock() internal view virtual returns (uint256) {
        return 0;
    }

    function eulerSwapAmount() internal view virtual returns (uint256) {
        return amount();
    }

    /// @dev Override to enable the operator-disabled regression tests. Returning the zero address
    /// skips them. The owner is the EVC owner of the pool's eulerAccount (sub-accounts cannot
    /// manage their own operators in the EVC).
    function eulerSwapEvc() internal view virtual returns (IEVC) {
        return IEVC(address(0));
    }

    function eulerSwapAccount() internal view virtual returns (address) {
        return address(0);
    }

    function eulerSwapAccountOwner() internal view virtual returns (address) {
        return address(0);
    }

    function reverseTestName() internal view virtual returns (string memory);

    modifier setEulerSwapBlock() {
        uint256 blockNumber = vm.getBlockNumber();
        vm.rollFork(eulerSwapBlock());
        vm.setEvmVersion("osaka");
        _;
        vm.rollFork(blockNumber);
        vm.setEvmVersion("osaka");
    }

    function setUp() public virtual override {
        super.setUp();
        if (eulerSwapPool() != address(0)) {
            vm.label(eulerSwapPool(), string.concat("EulerSwap ", _testName(), " pool"));
            vm.makePersistent(address(PERMIT2));
            vm.makePersistent(address(allowanceHolder));
            vm.makePersistent(address(settler));
            vm.makePersistent(address(fromToken()));
            vm.makePersistent(address(toToken()));
            deal(address(toToken()), FROM, eulerSwapAmount());
            vm.prank(FROM, FROM);
            toToken().safeApprove(address(PERMIT2), type(uint256).max);
        }
    }

    function testEulerSwap() public skipIf(eulerSwapPool() == address(0)) setEulerSwapBlock {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) =
            _getDefaultFromPermit2(eulerSwapAmount());

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(ISettlerActions.EULERSWAP, (FROM, address(fromToken()), 10_000, eulerSwapPool(), true, 0))
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
        });
        Settler _settler = settler;
        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);
        uint256 expectedBuyAmount =
            IEulerSwap(eulerSwapPool()).computeQuote(fromToken(), toToken(), eulerSwapAmount(), true);

        vm.startPrank(FROM, FROM);
        snapStartName("settler_eulerSwap");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGe(afterBalanceTo - beforeBalanceTo, expectedBuyAmount);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + eulerSwapAmount(), beforeBalanceFrom);
    }

    function testEulerSwapReverse() public skipIf(eulerSwapPool() == address(0)) setEulerSwapBlock {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) =
            _getDefaultFromPermit2(toToken(), eulerSwapAmount());

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(ISettlerActions.EULERSWAP, (FROM, address(toToken()), 10_000, eulerSwapPool(), false, 0))
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
        });
        Settler _settler = settler;
        uint256 beforeBalanceFrom = balanceOf(toToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(fromToken(), FROM);
        uint256 expectedBuyAmount =
            IEulerSwap(eulerSwapPool()).computeQuote(toToken(), fromToken(), eulerSwapAmount(), true);

        vm.startPrank(FROM, FROM);
        snapStart(string.concat("settler_eulerSwap_", reverseTestName()));
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = fromToken().balanceOf(FROM);
        assertGe(afterBalanceTo - beforeBalanceTo, expectedBuyAmount);
        uint256 afterBalanceFrom = toToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + eulerSwapAmount(), beforeBalanceFrom);
    }

    function testEulerSwapCustody() public skipIf(eulerSwapPool() == address(0)) setEulerSwapBlock {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) =
            _getDefaultFromPermit2(eulerSwapAmount());

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (eulerSwapPool(), permit, sig)),
            abi.encodeCall(ISettlerActions.EULERSWAP, (FROM, address(fromToken()), 0, eulerSwapPool(), true, 0))
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
        });
        Settler _settler = settler;
        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);
        uint256 expectedBuyAmount =
            IEulerSwap(eulerSwapPool()).computeQuote(fromToken(), toToken(), eulerSwapAmount(), true);

        vm.startPrank(FROM, FROM);
        snapStartName("settler_eulerSwapCustody");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGe(afterBalanceTo - beforeBalanceTo, expectedBuyAmount);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + eulerSwapAmount(), beforeBalanceFrom);
    }

    function testEulerSwapV2QuoteAndLimits() public skipIf(eulerSwapPool() == address(0)) setEulerSwapBlock {
        IEulerSwap pool = IEulerSwap(eulerSwapPool());

        (IERC20 asset0, IERC20 asset1) = pool.getAssets();
        assertEq(address(asset0), address(fromToken()));
        assertEq(address(asset1), address(toToken()));

        (uint256 limitIn, uint256 limitOut) = pool.getLimits(fromToken(), toToken());
        assertGe(limitIn, eulerSwapAmount());
        assertGt(limitOut, 0);
        assertGt(pool.computeQuote(fromToken(), toToken(), eulerSwapAmount(), true), 0);

        (limitIn, limitOut) = pool.getLimits(toToken(), fromToken());
        assertGe(limitIn, eulerSwapAmount());
        assertGt(limitOut, 0);
        assertGt(pool.computeQuote(toToken(), fromToken(), eulerSwapAmount(), true), 0);
    }

    // The settler integration relies on two v2 properties when the pool's operator authorization
    // is revoked: `getLimits` returns (0, 0), and `computeQuote(0)` returns 0 cleanly. Together
    // these let `sellToEulerSwap` no-op without reverting when a pool has been abandoned. These
    // tests pin those properties.

    modifier skipIfNoOperatorContext() {
        if (
            address(eulerSwapEvc()) == address(0) || eulerSwapAccount() == address(0)
                || eulerSwapAccountOwner() == address(0)
        ) return;
        _;
    }

    function testEulerSwapLimitsZeroWhenOperatorDisabled()
        public
        skipIf(eulerSwapPool() == address(0))
        skipIfNoOperatorContext
        setEulerSwapBlock
    {
        IEulerSwap pool = IEulerSwap(eulerSwapPool());

        (uint256 inLimit, uint256 outLimit) = pool.getLimits(fromToken(), toToken());
        assertGt(inLimit, 0);
        assertGt(outLimit, 0);

        vm.prank(eulerSwapAccountOwner());
        eulerSwapEvc().setAccountOperator(eulerSwapAccount(), address(pool), false);
        assertFalse(eulerSwapEvc().isAccountOperatorAuthorized(eulerSwapAccount(), address(pool)));

        (inLimit, outLimit) = pool.getLimits(fromToken(), toToken());
        assertEq(inLimit, 0);
        assertEq(outLimit, 0);
    }

    function testEulerSwapComputeQuoteRevertsWhenOperatorDisabled()
        public
        skipIf(eulerSwapPool() == address(0))
        skipIfNoOperatorContext
        setEulerSwapBlock
    {
        IEulerSwap pool = IEulerSwap(eulerSwapPool());

        vm.prank(eulerSwapAccountOwner());
        eulerSwapEvc().setAccountOperator(eulerSwapAccount(), address(pool), false);

        // computeQuote(0) returns 0 even when disabled, which the settler relies on for clean
        // no-op behavior when sellAmount is clamped to zero by getLimits.
        assertEq(pool.computeQuote(fromToken(), toToken(), 0, true), 0);

        // Non-zero amounts revert with OperatorNotInstalled. The settler avoids this path because
        // getLimits has already returned 0, clamping sellAmount to zero.
        vm.expectRevert();
        pool.computeQuote(fromToken(), toToken(), eulerSwapAmount(), true);
    }
}
