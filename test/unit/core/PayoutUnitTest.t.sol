// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {MockERC20} from "@solmate/test/utils/mocks/MockERC20.sol";

import {MainnetSettler} from "src/chains/Mainnet/TakerSubmitted.sol";
import {USDC, USDT} from "src/core/MakerPSM.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {TooMuchSlippage} from "src/core/SettlerErrors.sol";

contract PayoutUnitTest is Test {
    IERC20 private constant ETH = IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);

    MainnetSettler private settler;
    MockERC20 private token;
    address payable private taker;

    function setUp() public {
        vm.mockCall(address(USDC), abi.encodeCall(IERC20.decimals, ()), abi.encode(uint8(6)));
        vm.mockCall(address(USDT), abi.encodeCall(IERC20.decimals, ()), abi.encode(uint8(6)));
        settler = new MainnetSettler(bytes20(0));
        token = new MockERC20("Test Token", "TT", 18);
        taker = payable(makeAddr("taker"));
    }

    function test_Payout_KeepsOneWei() public {
        token.mint(address(settler), 1_000);
        _payout(999);
        assertEq(token.balanceOf(taker), 999);
        assertEq(token.balanceOf(address(settler)), 1);
    }

    function test_Payout_PaysAllWhenBalanceEqualsMinimum() public {
        token.mint(address(settler), 1_000);
        _payout(1_000);
        assertEq(token.balanceOf(taker), 1_000);
        assertEq(token.balanceOf(address(settler)), 0);
    }

    function test_Payout_RevertsBelowMinimum() public {
        token.mint(address(settler), 999);
        vm.expectRevert(abi.encodeWithSelector(TooMuchSlippage.selector, token, 1_000, 999));
        _payout(1_000);
    }

    function test_Payout_SteadyStatePaysFullOutput() public {
        token.mint(address(settler), 1);
        token.mint(address(settler), 1_000);
        _payout(1_000);
        assertEq(token.balanceOf(taker), 1_000);
        assertEq(token.balanceOf(address(settler)), 1);
    }

    function test_Payout_NativePaysAll() public {
        vm.deal(address(settler), 1_000);
        _payout(ETH, 1_000);
        assertEq(taker.balance, 1_000);
        assertEq(address(settler).balance, 0);
    }

    function test_Payout_ExactLimitPaysExactlyTheMinimum() public {
        token.mint(address(settler), 1_002);
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.CHECK_SLIPPAGE, (true));
        settler.execute(
            ISettlerBase.AllowedSlippage({recipient: taker, buyToken: IERC20(address(token)), minAmountOut: 1_000}),
            actions,
            bytes32(0)
        );
        assertEq(token.balanceOf(taker), 1_000);
        assertEq(token.balanceOf(address(settler)), 2);
    }

    function test_Payout_ZeroBalanceZeroMinimum() public {
        _payout(0);
        assertEq(token.balanceOf(taker), 0);
        assertEq(token.balanceOf(address(settler)), 0);
    }

    function testFuzz_Payout_KeepsOneWei(uint256 balance, uint256 minAmountOut) public {
        minAmountOut = bound(minAmountOut, 1, type(uint128).max);
        balance = bound(balance, 0, type(uint128).max);
        token.mint(address(settler), balance);
        if (balance < minAmountOut) {
            vm.expectRevert(abi.encodeWithSelector(TooMuchSlippage.selector, token, minAmountOut, balance));
            _payout(minAmountOut);
            return;
        }
        _payout(minAmountOut);
        uint256 kept = balance == minAmountOut ? 0 : 1;
        assertEq(token.balanceOf(taker), balance - kept);
        assertEq(token.balanceOf(address(settler)), kept);
    }

    function test_SellAll_KeepsOneWeiAcrossTrades() public {
        address recipient = makeAddr("recipient");
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(
            ISettlerActions.BASIC,
            (address(token), 1_000_000, address(token), 0x24, abi.encodeCall(IERC20.transfer, (recipient, 0)))
        );
        ISettlerBase.AllowedSlippage memory noSlippage;

        token.mint(address(settler), 1);
        settler.execute(noSlippage, actions, bytes32(0));
        assertEq(token.balanceOf(recipient), 0);
        assertEq(token.balanceOf(address(settler)), 1);

        token.mint(address(settler), 999);
        settler.execute(noSlippage, actions, bytes32(0));
        assertEq(token.balanceOf(recipient), 999);
        assertEq(token.balanceOf(address(settler)), 1);

        token.mint(address(settler), 500);
        settler.execute(noSlippage, actions, bytes32(0));
        assertEq(token.balanceOf(recipient), 1_499);
        assertEq(token.balanceOf(address(settler)), 1);
    }

    function test_PositiveSlippage_SteadyStateZeroSlippagePaysMinimum() public {
        address feeRecipient = makeAddr("feeRecipient");
        token.mint(address(settler), 1);
        token.mint(address(settler), 1_000);
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(
            ISettlerActions.POSITIVE_SLIPPAGE, (payable(feeRecipient), address(token), 1_000, 1_000_000, 1_000_000)
        );
        settler.execute(
            ISettlerBase.AllowedSlippage({recipient: taker, buyToken: IERC20(address(token)), minAmountOut: 1_000}),
            actions,
            bytes32(0)
        );
        assertEq(token.balanceOf(taker), 1_000);
        assertEq(token.balanceOf(feeRecipient), 0);
    }

    function _payout(uint256 minAmountOut) private {
        _payout(IERC20(address(token)), minAmountOut);
    }

    function _payout(IERC20 buyToken, uint256 minAmountOut) private {
        settler.execute(
            ISettlerBase.AllowedSlippage({recipient: taker, buyToken: buyToken, minAmountOut: minAmountOut}),
            new bytes[](0),
            bytes32(0)
        );
    }
}
