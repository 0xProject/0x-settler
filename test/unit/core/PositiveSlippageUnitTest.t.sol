// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {MockERC20} from "@solmate/test/utils/mocks/MockERC20.sol";

import {MainnetSettler} from "src/chains/Mainnet/TakerSubmitted.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

IERC20 constant USDC = IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
IERC20 constant USDT = IERC20(0xdAC17F958D2ee523a2206206994597C13D831ec7);

contract PositiveSlippageUnitTest is Test {
    uint256 private constant BASIS = 1_000_000;
    IERC20 private constant ETH_ADDRESS = IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);

    MainnetSettler private settler;
    MockERC20 private token;
    address payable private recipient;

    function setUp() public {
        // Both stablecoins must report six decimals for Mainnet deployment.
        vm.mockCall(address(USDC), abi.encodeCall(IERC20.decimals, ()), abi.encode(uint8(6)));
        vm.mockCall(address(USDT), abi.encodeCall(IERC20.decimals, ()), abi.encode(uint8(6)));
        settler = new MainnetSettler(bytes20(0));
        token = new MockERC20("Test Token", "TT", 18);
        recipient = payable(makeAddr("recipient"));
    }

    function test_PositiveSlippage_TransfersProportionOfTokenSurplus() public {
        _executeToken(2_000_000, 1_000_000, 250_000, BASIS);

        assertEq(token.balanceOf(recipient), 250_000);
        assertEq(token.balanceOf(address(settler)), 1_750_000);
    }

    function test_PositiveSlippage_CapsTokenTransfer() public {
        _executeToken(2_000_000, 1_000_000, 750_000, 100_000);

        assertEq(token.balanceOf(recipient), 200_000);
        assertEq(token.balanceOf(address(settler)), 1_800_000);
    }

    function test_PositiveSlippage_DoesNotTransferWithoutSurplus() public {
        _executeToken(1_000_000, 1_500_000, BASIS, BASIS);

        assertEq(token.balanceOf(recipient), 0);
        assertEq(token.balanceOf(address(settler)), 1_000_000);
    }

    function test_PositiveSlippage_TransfersProportionOfEthSurplus() public {
        vm.deal(address(settler), 2_000_000);
        _execute(ETH_ADDRESS, 1_000_000, 250_000, BASIS);

        assertEq(recipient.balance, 250_000);
        assertEq(address(settler).balance, 1_750_000);
    }

    function testFuzz_PositiveSlippage_TransfersExpectedTokenAmount(
        uint128 balance,
        uint128 expectedAmount,
        uint24 surplusPpm,
        uint24 maxPpm
    ) public {
        expectedAmount = uint128(bound(expectedAmount, 0, balance));
        surplusPpm = uint24(bound(surplusPpm, 0, BASIS));
        maxPpm = uint24(bound(maxPpm, 0, BASIS));

        _executeToken(balance, expectedAmount, surplusPpm, maxPpm);

        uint256 proportionalAmount = (uint256(balance) - expectedAmount) * surplusPpm / BASIS;
        uint256 cappedAmount = uint256(balance) * maxPpm / BASIS;
        uint256 transferredAmount = proportionalAmount < cappedAmount ? proportionalAmount : cappedAmount;
        assertEq(token.balanceOf(recipient), transferredAmount);
        assertEq(token.balanceOf(address(settler)), uint256(balance) - transferredAmount);
    }

    function _executeToken(uint256 balance, uint256 expectedAmount, uint256 surplusPpm, uint256 maxPpm) private {
        token.mint(address(settler), balance);
        _execute(IERC20(address(token)), expectedAmount, surplusPpm, maxPpm);
    }

    function _execute(IERC20 asset, uint256 expectedAmount, uint256 surplusPpm, uint256 maxPpm) private {
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(
            ISettlerActions.POSITIVE_SLIPPAGE, (recipient, address(asset), expectedAmount, surplusPpm, maxPpm)
        );
        settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
            }),
            actions,
            bytes32(0)
        );
    }
}
