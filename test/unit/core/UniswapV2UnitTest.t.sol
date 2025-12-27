// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {UniswapV2, IUniV2Pair} from "src/core/UniswapV2.sol";
import {Permit2PaymentTakerSubmitted} from "src/core/Permit2Payment.sol";
import {Permit2PaymentAbstract} from "src/core/Permit2PaymentAbstract.sol";
import {Context} from "src/Context.sol";

import {uint512} from "src/utils/512Math.sol";

import {Utils} from "../Utils.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {Test} from "@forge-std/Test.sol";

contract UniswapV2Dummy is Permit2PaymentTakerSubmitted, UniswapV2 {
    function sell(
        address recipient,
        address sellToken,
        uint256 bps,
        address pool,
        uint24 swapInfo,
        uint256 minBuyAmount
    ) public {
        super.sellToUniswapV2(recipient, sellToken, bps, pool, swapInfo, minBuyAmount);
    }

    function _hasMetaTxn() internal pure override returns (bool) {
        return false;
    }

    function _tokenId() internal pure override returns (uint256) {
        revert("unimplemented");
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

contract UniswapV2UnitTest is Utils, Test {
    UniswapV2Dummy uni;
    address TOKEN0 = _createNamedRejectionDummy("TOKEN0");
    address TOKEN1 = _createNamedRejectionDummy("TOKEN1");
    address TOKEN2 = _createNamedRejectionDummy("TOKEN2");
    address POOL = _etchNamedRejectionDummy("POOL", 0xabedA74b789DBa7D817889Eb0266E1F58219f13f); // created from TOKEN0/TOKEN1 combo
    address POOL2 = _etchNamedRejectionDummy("POOL2", 0x62D5437A22Ab167ABbe5e2FADe8C49bE7276ab2F); // created from TOKEN1/TOKEN2 combo
    address RECIPIENT = _createNamedRejectionDummy("RECIPIENT");

    function setUp() public {
        uni = new UniswapV2Dummy();
    }

    function testUniswapV2Sell() public {
        uint256 bps = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = 9087;
        uint24 swapInfo = (TOKEN0 < TOKEN1 ? 1 : 0) | (30 << 8);

        _mockExpectCall(TOKEN0, abi.encodeCall(IERC20.balanceOf, (address(uni))), abi.encode(amount));
        _mockExpectCall(TOKEN0, abi.encodeCall(IERC20.transfer, (POOL, amount)), new bytes(0));

        // UniswapV2Pool.getReserves
        _mockExpectCall(POOL, abi.encodeCall(IUniV2Pair.getReserves, ()), abi.encode(uint256(9999), uint256(9999)));
        // UniswapV2Pool.swap
        _mockExpectCall(
            POOL, abi.encodeCall(IUniV2Pair.swap, (uint256(9087), 0, RECIPIENT, new bytes(0))), new bytes(0)
        );

        uni.sell(RECIPIENT, TOKEN0, bps, POOL, swapInfo, minBuyAmount);
    }

    function testUniswapV2SellSlippageCheck() public {
        uint256 bps = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = 1e18;
        uint24 swapInfo = (TOKEN0 < TOKEN1 ? 1 : 0) | (30 << 8);

        _mockExpectCall(TOKEN0, abi.encodeCall(IERC20.balanceOf, (address(uni))), abi.encode(amount));
        _mockExpectCall(TOKEN0, abi.encodeCall(IERC20.transfer, (POOL, amount)), new bytes(0));

        // UniswapV2Pool.getReserves
        _mockExpectCall(POOL, abi.encodeCall(IUniV2Pair.getReserves, ()), abi.encode(uint256(9999), uint256(9999)));
        // UniswapV2Pool.swap

        // slippage is now checked before the swap call
        // _mockExpectCall(
        //     POOL, abi.encodeCall(IUniV2Pair.swap, (uint256(9087), 0, RECIPIENT, new bytes(0))), new bytes(0)
        // );

        vm.expectRevert();
        uni.sell(RECIPIENT, TOKEN0, bps, POOL, swapInfo, minBuyAmount);
    }

    function testUniswapV2LowerAmount() public {
        uint256 bps = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = 1;
        uint24 swapInfo = (TOKEN0 < TOKEN1 ? 1 : 0) | (30 << 8);

        _mockExpectCall(TOKEN0, abi.encodeCall(IERC20.balanceOf, (address(uni))), abi.encode(amount / 2));
        _mockExpectCall(TOKEN0, abi.encodeCall(IERC20.transfer, (POOL, amount / 2)), new bytes(0));

        // UniswapV2Pool.getReserves
        _mockExpectCall(POOL, abi.encodeCall(IUniV2Pair.getReserves, ()), abi.encode(uint256(9999), uint256(9999)));
        // UniswapV2Pool.swap
        _mockExpectCall(
            POOL, abi.encodeCall(IUniV2Pair.swap, (uint256(8328), 0, RECIPIENT, new bytes(0))), new bytes(0)
        );

        uni.sell(RECIPIENT, TOKEN0, bps, POOL, swapInfo, minBuyAmount);
    }

    function testUniswapV2GreaterAmount() public {
        uint256 bps = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = 9521;
        uint24 swapInfo = (TOKEN0 < TOKEN1 ? 1 : 0) | (30 << 8);

        _mockExpectCall(TOKEN0, abi.encodeCall(IERC20.balanceOf, (address(uni))), abi.encode(amount * 2));
        _mockExpectCall(TOKEN0, abi.encodeCall(IERC20.transfer, (POOL, amount * 2)), new bytes(0));

        // UniswapV2Pool.getReserves
        _mockExpectCall(POOL, abi.encodeCall(IUniV2Pair.getReserves, ()), abi.encode(uint256(9999), uint256(9999)));
        // UniswapV2Pool.swap
        _mockExpectCall(
            POOL, abi.encodeCall(IUniV2Pair.swap, (uint256(9521), 0, RECIPIENT, new bytes(0))), new bytes(0)
        );

        uni.sell(RECIPIENT, TOKEN0, bps, POOL, swapInfo, minBuyAmount);
    }

    function testUniswapV2SellTokenFee() public {
        uint256 bps = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = 1;
        uint24 swapInfo = (TOKEN0 < TOKEN1 ? 3 : 2) | (30 << 8);

        // We emulate a token which has a 50% fee when transferring to the Uniswap pool
        _mockExpectCall(TOKEN0, abi.encodeCall(IERC20.balanceOf, (POOL)), abi.encode(amount / 2));

        _mockExpectCall(TOKEN0, abi.encodeCall(IERC20.balanceOf, (address(uni))), abi.encode(amount));
        _mockExpectCall(TOKEN0, abi.encodeCall(IERC20.transfer, (POOL, amount)), new bytes(0));

        // UniswapV2Pool.getReserves
        _mockExpectCall(POOL, abi.encodeCall(IUniV2Pair.getReserves, ()), abi.encode(uint256(9999), uint256(9999)));
        // UniswapV2Pool.swap
        _mockExpectCall(
            POOL, abi.encodeCall(IUniV2Pair.swap, (uint256(7994), 0, RECIPIENT, new bytes(0))), new bytes(0)
        );
        // the pool is responsible for transferring to receipient, since the pool is a dummy, this transfer is not mocked

        uni.sell(RECIPIENT, TOKEN0, bps, POOL, swapInfo, minBuyAmount);
    }

    function testUniswapV2Multihop() public {
        uint256 bps = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = 9521;
        uint24 swapInfo0 = (TOKEN0 < TOKEN1 ? 1 : 0) | (30 << 8);
        uint24 swapInfo1 = (TOKEN1 < TOKEN2 ? 1 : 0) | (30 << 8);

        _mockExpectCall(TOKEN0, abi.encodeCall(IERC20.balanceOf, (address(uni))), abi.encode(amount * 2));
        _mockExpectCall(TOKEN0, abi.encodeCall(IERC20.transfer, (POOL, amount * 2)), new bytes(0));

        // UniswapV2Pool.getReserves
        _mockExpectCall(POOL, abi.encodeCall(IUniV2Pair.getReserves, ()), abi.encode(uint256(9999), uint256(9999)));
        // UniswapV2Pool.swap
        //   POOL specifies POOL2 as recipient
        _mockExpectCall(POOL, abi.encodeCall(IUniV2Pair.swap, (uint256(9521), 0, POOL2, new bytes(0))), new bytes(0));
        _mockExpectCall(POOL2, abi.encodeCall(IUniV2Pair.getReserves, ()), abi.encode(uint256(9999), uint256(9999)));
        _mockExpectCall(TOKEN1, abi.encodeCall(IERC20.balanceOf, (POOL2)), abi.encode(amount * 2 + 9999));
        // UniswapV2Pool.swap
        //   POOL2 specifies RECIPIENT as recipient
        _mockExpectCall(
            POOL2, abi.encodeCall(IUniV2Pair.swap, (uint256(0), uint256(9521), RECIPIENT, new bytes(0))), new bytes(0)
        );

        uni.sell(POOL2, TOKEN0, bps, POOL, swapInfo0, 0);
        uni.sell(RECIPIENT, TOKEN1, 0, POOL2, swapInfo1, minBuyAmount);
    }
}
