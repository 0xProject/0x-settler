// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Basic} from "src/core/Basic.sol";
import {Permit2PaymentTakerSubmitted} from "src/core/Permit2Payment.sol";
import {Permit2PaymentAbstract} from "src/core/Permit2PaymentAbstract.sol";
import {AllowanceHolderContext} from "src/allowanceholder/AllowanceHolderContext.sol";
import {BaseSettler} from "src/chains/Base/TakerSubmitted.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

import {uint512} from "src/utils/512Math.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {Utils} from "../Utils.sol";

import {Test} from "@forge-std/Test.sol";
import {MockERC20} from "@solmate/test/utils/mocks/MockERC20.sol";

contract BasicDummy is Permit2PaymentTakerSubmitted, Basic {
    function sellToPool(IERC20 sellToken, uint256 ppm, address pool, uint256 offset, bytes memory data) public {
        super.basicSellToPool(sellToken, ppm, pool, offset, data);
    }

    function _tokenId() internal pure override returns (uint256) {
        revert("unimplemented");
    }

    function _hasMetaTxn() internal pure override returns (bool) {
        return false;
    }

    function _div512to256(uint512, uint512) internal view override returns (uint256) {
        revert("unimplemented");
    }

    function _isRestrictedTarget(address target)
        internal
        view
        override(Permit2PaymentTakerSubmitted, Permit2PaymentAbstract)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }
}

contract BasicUnitTest is Utils, Test {
    BasicDummy basic;
    address PERMIT2 = _etchNamedRejectionDummy("PERMIT2", 0x000000000022D473030F116dDEE9F6B43aC78BA3);
    address ALLOWANCE_HOLDER = _etchNamedRejectionDummy("ALLOWANCE_HOLDER", 0x0000000000001fF3684f28c67538d4D072C22734);
    address POOL = _createNamedRejectionDummy("POOL");
    IERC20 TOKEN = IERC20(_createNamedRejectionDummy("TOKEN"));

    function setUp() public {
        basic = new BasicDummy();
    }

    function testBasicSell() public {
        uint256 ppm = 1_000_000;
        uint256 offset = 4;
        uint256 amount = 99999;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        _mockExpectCall(
            address(TOKEN), abi.encodeWithSelector(IERC20.balanceOf.selector, address(basic)), abi.encode(amount)
        );
        _mockExpectCall(
            address(TOKEN),
            abi.encodeWithSelector(IERC20.allowance.selector, address(basic), address(POOL)),
            abi.encode(amount)
        );

        _mockExpectCall(address(POOL), data, abi.encode(true));

        basic.sellToPool(TOKEN, ppm, POOL, offset, data);
    }

    /// @dev adjust the balange of the contract to be less than expected
    function testBasicSellLowerBalanceAmount() public {
        uint256 ppm = 1_000_000;
        uint256 offset = 4;
        uint256 amount = 99999;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        _mockExpectCall(
            address(TOKEN), abi.encodeWithSelector(IERC20.balanceOf.selector, address(basic)), abi.encode(amount / 2)
        );
        _mockExpectCall(
            address(TOKEN),
            abi.encodeWithSelector(IERC20.allowance.selector, address(basic), address(POOL)),
            abi.encode(amount)
        );

        _mockExpectCall(address(POOL), abi.encodePacked(selector, amount / 2), abi.encode(true));
        basic.sellToPool(TOKEN, ppm, POOL, offset, data);
    }

    /// @dev adjust the balange of the contract to be greater than expected
    function testBasicSellGreaterBalanceAmount() public {
        uint256 ppm = 1_000_000;
        uint256 offset = 4;
        uint256 amount = 99999;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        _mockExpectCall(
            address(TOKEN), abi.encodeWithSelector(IERC20.balanceOf.selector, address(basic)), abi.encode(amount * 2)
        );
        _mockExpectCall(
            address(TOKEN),
            abi.encodeWithSelector(IERC20.allowance.selector, address(basic), address(POOL)),
            abi.encode(amount * 2)
        );

        _mockExpectCall(address(POOL), abi.encodePacked(selector, amount * 2), abi.encode(true));
        basic.sellToPool(TOKEN, ppm, POOL, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to transfer as value
    function testBasicSellEthValue() public {
        uint256 ppm = 1_000_000;
        uint256 offset = 4;
        uint256 amount = 99999;
        uint256 value = amount;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        _mockExpectCall(address(POOL), value, abi.encodePacked(selector, amount), abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), ppm, POOL, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to transfer as value and adjust for the current balance if lower
    function testBasicSellLowerEthValue() public {
        uint256 ppm = 1_000_000;
        uint256 offset = 4;
        uint256 amount = 99999;
        uint256 value = amount / 2;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        _mockExpectCall(address(POOL), value, abi.encodePacked(selector, value), abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), ppm, POOL, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to transfer as value and adjust for the current balance if greater
    function testBasicSellGreaterEthValue() public {
        uint256 ppm = 1_000_000;
        uint256 offset = 4;
        uint256 amount = 99999;
        uint256 value = amount * 2;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        _mockExpectCall(address(POOL), value, abi.encodePacked(selector, value), abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), ppm, POOL, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to transfer as value and adjust for the current balance
    function testBasicSellAdjustedEthValue() public {
        uint256 ppm = 500_000; // sell half
        uint256 offset = 4;
        uint256 amount = 99999;
        uint256 value = amount * 2;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        // 500_000 / 1_000_000 * value == amount
        _mockExpectCall(address(POOL), amount, abi.encodePacked(selector, amount), abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), ppm, POOL, offset, data);
    }

    /// @dev A proportion below one basis point (here 30 ppm) sells a nonzero amount
    function testBasicSellSubBasisPointProportion() public {
        uint256 ppm = 30;
        uint256 offset = 4;
        uint256 value = 1_000_000;
        uint256 amount = 30;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        // 30 / 1_000_000 * value == amount
        _mockExpectCall(address(POOL), amount, abi.encodePacked(selector, amount), abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), ppm, POOL, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to support a transfer with no data
    function testBasicSellTransferValue() public {
        uint256 ppm = 1_000_000;
        uint256 offset = 0;
        uint256 amount = 99999;
        uint256 value = amount;
        bytes memory data;

        _mockExpectCall(address(POOL), value, data, abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), ppm, POOL, offset, data);
    }

    function testBasicRestrictedTarget() public {
        uint256 ppm = 1_000_000;
        uint256 offset = 0;
        bytes memory data;

        vm.expectRevert();
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), ppm, PERMIT2, offset, data);

        vm.expectRevert();
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), ppm, ALLOWANCE_HOLDER, offset, data);
    }

    function testBasicBubblesUpRevert() public {
        uint256 ppm = 1_000_000;
        uint256 offset = 0;
        bytes memory data;

        vm.expectRevert();
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), ppm, POOL, offset, data);
    }
}

contract PositiveSlippageUnitTest is Test {
    uint256 private constant BASIS = 1_000_000;
    IERC20 private constant ETH_ADDRESS = IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);

    BaseSettler private settler;
    MockERC20 private token;
    address payable private recipient;

    function setUp() public {
        settler = new BaseSettler(bytes20(0));
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
