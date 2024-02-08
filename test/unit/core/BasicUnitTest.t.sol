// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {Basic} from "../../../src/core/Basic.sol";
import {Permit2Payment} from "../../../src/core/Permit2Payment.sol";

import {IERC20} from "../../../src/IERC20.sol";
import {Utils} from "../Utils.sol";

import {Test} from "forge-std/Test.sol";

contract BasicDummy is Basic, Permit2Payment {
    constructor(address permit2, address feeRecipient, address allowanceHolder)
        Permit2Payment(permit2, feeRecipient, allowanceHolder)
    {}

    function sellToPool(address pool, IERC20 sellToken, uint256 bips, uint256 offset, bytes memory data) public {
        super.basicSellToPool(pool, sellToken, bips, offset, data);
    }
}

contract BasicUnitTest is Utils, Test {
    BasicDummy basic;
    address PERMIT2 = _deterministicAddress("PERMIT2");
    address FEE_RECIPIENT = _deterministicAddress("FEE_RECIPIENT");
    address ALLOWANCE_HOLDER = _deterministicAddress("ALLOWANCE_HOLDER");
    address POOL = _createNamedRejectionDummy("POOL");
    IERC20 TOKEN = IERC20(_createNamedRejectionDummy("TOKEN"));

    function setUp() public {
        basic = new BasicDummy(PERMIT2, FEE_RECIPIENT, ALLOWANCE_HOLDER);
    }

    function testBasicSell() public {
        uint256 bips = 10_000;
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

        basic.sellToPool(POOL, TOKEN, bips, offset, data);
    }

    /// @dev adjust the balange of the contract to be less than expected
    function testBasicSellLowerBalanceAmount() public {
        uint256 bips = 10_000;
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
        basic.sellToPool(POOL, TOKEN, bips, offset, data);
    }

    /// @dev adjust the balange of the contract to be greater than expected
    function testBasicSellGreaterBalanceAmount() public {
        uint256 bips = 10_000;
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
        basic.sellToPool(POOL, TOKEN, bips, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to transfer as value
    function testBasicSellEthValue() public {
        uint256 bips = 10_000;
        uint256 offset = 4;
        uint256 amount = 99999;
        uint256 value = amount;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        _mockExpectCall(address(POOL), value, abi.encodePacked(selector, amount), abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(POOL, IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), bips, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to transfer as value and adjust for the current balance if lower
    function testBasicSellLowerEthValue() public {
        uint256 bips = 10_000;
        uint256 offset = 4;
        uint256 amount = 99999;
        uint256 value = amount / 2;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        _mockExpectCall(address(POOL), value, abi.encodePacked(selector, value), abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(POOL, IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), bips, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to transfer as value and adjust for the current balance if greater
    function testBasicSellGreaterEthValue() public {
        uint256 bips = 10_000;
        uint256 offset = 4;
        uint256 amount = 99999;
        uint256 value = amount * 2;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        _mockExpectCall(address(POOL), value, abi.encodePacked(selector, value), abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(POOL, IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), bips, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to transfer as value and adjust for the current balance
    function testBasicSellAdjustedEthValue() public {
        uint256 bips = 5_000; // sell half
        uint256 offset = 4;
        uint256 amount = 99999;
        uint256 value = amount * 2;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        // 5_000 / 10_000 * value == amount
        _mockExpectCall(address(POOL), amount, abi.encodePacked(selector, amount), abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(POOL, IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), bips, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to support a transfer with no data
    function testBasicSellTransferValue() public {
        uint256 bips = 10_000;
        uint256 offset = 0;
        uint256 amount = 99999;
        uint256 value = amount;
        bytes memory data;

        _mockExpectCall(address(POOL), value, data, abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(POOL, IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), bips, offset, data);
    }

    function testBasicRestrictedTarget() public {
        uint256 bips = 10_000;
        uint256 offset = 0;
        bytes memory data;

        vm.expectRevert();
        basic.sellToPool(PERMIT2, IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), bips, offset, data);

        vm.expectRevert();
        basic.sellToPool(ALLOWANCE_HOLDER, IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), bips, offset, data);
    }

    function testBasicBubblesUpRevert() public {
        uint256 bips = 10_000;
        uint256 offset = 0;
        bytes memory data;

        vm.expectRevert();
        basic.sellToPool(POOL, IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), bips, offset, data);
    }
}
