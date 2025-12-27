// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Basic} from "src/core/Basic.sol";
import {Permit2PaymentTakerSubmitted} from "src/core/Permit2Payment.sol";
import {Permit2PaymentAbstract} from "src/core/Permit2PaymentAbstract.sol";
import {AllowanceHolderContext} from "src/allowanceholder/AllowanceHolderContext.sol";

import {uint512} from "src/utils/512Math.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {Utils} from "../Utils.sol";

import {Test} from "@forge-std/Test.sol";

contract BasicDummy is Permit2PaymentTakerSubmitted, Basic {
    function sellToPool(IERC20 sellToken, uint256 bps, address pool, uint256 offset, bytes memory data) public {
        super.basicSellToPool(sellToken, bps, pool, offset, data);
    }

    function _tokenId() internal pure override returns (uint256) {
        revert("unimplemented");
    }

    function _hasMetaTxn() internal pure override returns (bool) {
        return false;
    }

    function _dispatch(uint256, uint256, bytes calldata) internal pure override returns (bool) {
        revert("unimplemented");
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
        uint256 bps = 10_000;
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

        basic.sellToPool(TOKEN, bps, POOL, offset, data);
    }

    /// @dev adjust the balange of the contract to be less than expected
    function testBasicSellLowerBalanceAmount() public {
        uint256 bps = 10_000;
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
        basic.sellToPool(TOKEN, bps, POOL, offset, data);
    }

    /// @dev adjust the balange of the contract to be greater than expected
    function testBasicSellGreaterBalanceAmount() public {
        uint256 bps = 10_000;
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
        basic.sellToPool(TOKEN, bps, POOL, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to transfer as value
    function testBasicSellEthValue() public {
        uint256 bps = 10_000;
        uint256 offset = 4;
        uint256 amount = 99999;
        uint256 value = amount;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        _mockExpectCall(address(POOL), value, abi.encodePacked(selector, amount), abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), bps, POOL, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to transfer as value and adjust for the current balance if lower
    function testBasicSellLowerEthValue() public {
        uint256 bps = 10_000;
        uint256 offset = 4;
        uint256 amount = 99999;
        uint256 value = amount / 2;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        _mockExpectCall(address(POOL), value, abi.encodePacked(selector, value), abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), bps, POOL, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to transfer as value and adjust for the current balance if greater
    function testBasicSellGreaterEthValue() public {
        uint256 bps = 10_000;
        uint256 offset = 4;
        uint256 amount = 99999;
        uint256 value = amount * 2;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        _mockExpectCall(address(POOL), value, abi.encodePacked(selector, value), abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), bps, POOL, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to transfer as value and adjust for the current balance
    function testBasicSellAdjustedEthValue() public {
        uint256 bps = 5_000; // sell half
        uint256 offset = 4;
        uint256 amount = 99999;
        uint256 value = amount * 2;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        // 5_000 / 10_000 * value == amount
        _mockExpectCall(address(POOL), amount, abi.encodePacked(selector, amount), abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), bps, POOL, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to support a transfer with no data
    function testBasicSellTransferValue() public {
        uint256 bps = 10_000;
        uint256 offset = 0;
        uint256 amount = 99999;
        uint256 value = amount;
        bytes memory data;

        _mockExpectCall(address(POOL), value, data, abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), bps, POOL, offset, data);
    }

    function testBasicRestrictedTarget() public {
        uint256 bps = 10_000;
        uint256 offset = 0;
        bytes memory data;

        vm.expectRevert();
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), bps, PERMIT2, offset, data);

        vm.expectRevert();
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), bps, ALLOWANCE_HOLDER, offset, data);
    }

    function testBasicBubblesUpRevert() public {
        uint256 bps = 10_000;
        uint256 offset = 0;
        bytes memory data;

        vm.expectRevert();
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), bps, POOL, offset, data);
    }
}
