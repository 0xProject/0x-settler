// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {UniswapV2} from "src/core/UniswapV2.sol";
import {Permit2Payment} from "src/core/Permit2Payment.sol";

import {Utils} from "../Utils.sol";
import {IERC20} from "src/IERC20.sol";

import {Test} from "forge-std/Test.sol";

contract UniswapV2Dummy is Permit2Payment, UniswapV2 {
    constructor() Permit2Payment(address(0xdead), address(0xdead), address(0xdead)) {}

    function sell(
        address recipient,
        address sellToken,
        address pool,
        uint8 swapInfo,
        uint256 bips,
        uint256 minBuyAmount
    ) public {
        super.sellToUniswapV2(recipient, sellToken, pool, swapInfo, bips, minBuyAmount);
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
        uint256 bips = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = 9087;

        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.balanceOf.selector, address(uni)), abi.encode(amount));
        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.transfer.selector, POOL, amount), new bytes(0));

        // UniswapV2Pool.getReserves
        _mockExpectCall(POOL, abi.encodePacked(bytes4(0x0902f1ac)), abi.encode(uint256(9999), uint256(9999)));
        // UniswapV2Pool.swap
        _mockExpectCall(
            POOL,
            abi.encodePacked(bytes4(0x022c0d9f), abi.encode(uint256(9087), 0, RECIPIENT, new bytes(0))),
            new bytes(0)
        );

        uni.sell(RECIPIENT, TOKEN0, POOL, TOKEN0 < TOKEN1 ? 1 : 0, bips, minBuyAmount);
    }

    function testUniswapV2SellSlippageCheck() public {
        uint256 bips = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = 1e18;

        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.balanceOf.selector, address(uni)), abi.encode(amount));
        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.transfer.selector, POOL, amount), new bytes(0));

        // UniswapV2Pool.getReserves
        _mockExpectCall(POOL, abi.encodePacked(bytes4(0x0902f1ac)), abi.encode(uint256(9999), uint256(9999)));
        // UniswapV2Pool.swap
        _mockExpectCall(
            POOL,
            abi.encodePacked(bytes4(0x022c0d9f), abi.encode(uint256(9087), 0, RECIPIENT, new bytes(0))),
            new bytes(0)
        );

        vm.expectRevert();
        uni.sell(RECIPIENT, TOKEN0, POOL, TOKEN0 < TOKEN1 ? 1 : 0, bips, minBuyAmount);
    }

    function testUniswapV2LowerAmount() public {
        uint256 bips = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = 1;

        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.balanceOf.selector, address(uni)), abi.encode(amount / 2));
        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.transfer.selector, POOL, amount / 2), new bytes(0));

        // UniswapV2Pool.getReserves
        _mockExpectCall(POOL, abi.encodePacked(bytes4(0x0902f1ac)), abi.encode(uint256(9999), uint256(9999)));
        // UniswapV2Pool.swap
        _mockExpectCall(
            POOL,
            abi.encodePacked(bytes4(0x022c0d9f), abi.encode(uint256(8328), 0, RECIPIENT, new bytes(0))),
            new bytes(0)
        );

        uni.sell(RECIPIENT, TOKEN0, POOL, TOKEN0 < TOKEN1 ? 1 : 0, bips, minBuyAmount);
    }

    function testUniswapV2GreaterAmount() public {
        uint256 bips = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = 9521;

        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.balanceOf.selector, address(uni)), abi.encode(amount * 2));
        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.transfer.selector, POOL, amount * 2), new bytes(0));

        // UniswapV2Pool.getReserves
        _mockExpectCall(POOL, abi.encodePacked(bytes4(0x0902f1ac)), abi.encode(uint256(9999), uint256(9999)));
        // UniswapV2Pool.swap
        _mockExpectCall(
            POOL,
            abi.encodePacked(bytes4(0x022c0d9f), abi.encode(uint256(9521), 0, RECIPIENT, new bytes(0))),
            new bytes(0)
        );

        uni.sell(RECIPIENT, TOKEN0, POOL, TOKEN0 < TOKEN1 ? 1 : 0, bips, minBuyAmount);
    }

    function testUniswapV2SellTokenFee() public {
        uint256 bips = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = 1;

        // We emulate a token which has a 50% fee when transferring to the Uniswap pool
        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.balanceOf.selector, POOL), abi.encode(amount / 2));

        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.balanceOf.selector, address(uni)), abi.encode(amount));
        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.transfer.selector, POOL, amount), new bytes(0));

        // UniswapV2Pool.getReserves
        _mockExpectCall(POOL, abi.encodePacked(bytes4(0x0902f1ac)), abi.encode(uint256(9999), uint256(9999)));
        // UniswapV2Pool.swap
        _mockExpectCall(
            POOL,
            abi.encodePacked(bytes4(0x022c0d9f), abi.encode(uint256(7994), 0, RECIPIENT, new bytes(0))),
            new bytes(0)
        );
        // the pool is responsible for transferring to receipient, since the pool is a dummy, this transfer is not mocked

        uni.sell(RECIPIENT, TOKEN0, POOL, TOKEN0 < TOKEN1 ? 3 : 2, bips, minBuyAmount);
    }

    function testUniswapV2Multihop() public {
        uint256 bips = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = 9521;

        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.balanceOf.selector, address(uni)), abi.encode(amount * 2));
        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.transfer.selector, POOL, amount * 2), new bytes(0));

        // UniswapV2Pool.getReserves
        _mockExpectCall(POOL, abi.encodePacked(bytes4(0x0902f1ac)), abi.encode(uint256(9999), uint256(9999)));
        // UniswapV2Pool.swap
        //   POOL specifies POOL2 as recipient
        _mockExpectCall(
            POOL, abi.encodePacked(bytes4(0x022c0d9f), abi.encode(uint256(9521), 0, POOL2, new bytes(0))), new bytes(0)
        );
        _mockExpectCall(POOL2, abi.encodePacked(bytes4(0x0902f1ac)), abi.encode(uint256(9999), uint256(9999)));
        _mockExpectCall(TOKEN1, abi.encodeCall(IERC20.balanceOf, (POOL2)), abi.encode(amount * 2 + 9999));
        // UniswapV2Pool.swap
        //   POOL2 specifies RECIPIENT as recipient
        _mockExpectCall(
            POOL2,
            abi.encodePacked(bytes4(0x022c0d9f), abi.encode(uint256(0), uint256(9521), RECIPIENT, new bytes(0))),
            new bytes(0)
        );

        uni.sell(POOL2, TOKEN0, POOL, TOKEN0 < TOKEN1 ? 1 : 0, bips, 0);
        uni.sell(RECIPIENT, TOKEN1, POOL2, TOKEN1 < TOKEN2 ? 1 : 0, 0, minBuyAmount);
    }
}
