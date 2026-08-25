// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {MockERC20} from "@solmate/test/utils/mocks/MockERC20.sol";

import {BnbSettler} from "src/chains/Bnb/TakerSubmitted.sol";
import {FLUX_SWAP, FLUX_VAULT, IFluxSwap, IFluxSwapCallback} from "src/core/FluxPool.sol";
import {ConfusedDeputy, TooMuchSlippage} from "src/core/SettlerErrors.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {ActionDataBuilder} from "test/utils/ActionDataBuilder.sol";

contract FluxSwapMock {
    enum CallbackMode {
        Normal,
        WrongToken,
        WrongAmount,
        WrongLength
    }

    CallbackMode internal callbackMode;
    IERC20 internal buyToken;
    uint256 internal buyAmount;

    function configure(CallbackMode callbackMode_, IERC20 buyToken_, uint256 buyAmount_) external {
        callbackMode = callbackMode_;
        buyToken = buyToken_;
        buyAmount = buyAmount_;
    }

    function swapWithCallback(bytes32, bool, uint256, uint256, address swapReceiver, bytes calldata callbackData)
        external
        returns (uint256 amountOut)
    {
        if (buyAmount != 0) buyToken.transfer(swapReceiver, buyAmount);

        IERC20 sellToken = IERC20(address(bytes20(callbackData[:20])));
        uint256 sellAmount = uint256(bytes32(callbackData[20:]));
        IERC20 callbackToken = callbackMode == CallbackMode.WrongToken ? IERC20(address(0xdead)) : sellToken;
        uint256 callbackAmount = callbackMode == CallbackMode.WrongAmount ? sellAmount + 1 : sellAmount;
        bytes calldata callbackData_ = callbackMode == CallbackMode.WrongLength ? callbackData[:0] : callbackData;
        IFluxSwapCallback(msg.sender).fluxSwapCallback(callbackToken, callbackAmount, callbackData_);
        return buyAmount;
    }
}

contract FluxPoolUnitTest is Test {
    uint256 private constant SELL_BALANCE = 100 ether;
    uint256 private constant BUY_AMOUNT = 30 ether;
    uint256 private constant MIN_BUY_AMOUNT = 29 ether;
    bytes32 private constant POOL_ID = keccak256("pool");

    BnbSettler private settler;
    FluxSwapMock private fluxSwap;
    IERC20 private sellToken;
    IERC20 private buyToken;

    function setUp() public {
        settler = new BnbSettler(bytes20(0));
        FluxSwapMock implementation = new FluxSwapMock();
        vm.etch(FLUX_SWAP, address(implementation).code);
        fluxSwap = FluxSwapMock(FLUX_SWAP);

        MockERC20 sellToken_ = new MockERC20("Sell", "SELL", 18);
        MockERC20 buyToken_ = new MockERC20("Buy", "BUY", 18);
        sellToken_.mint(address(settler), SELL_BALANCE);
        buyToken_.mint(FLUX_SWAP, BUY_AMOUNT);
        sellToken = IERC20(address(sellToken_));
        buyToken = IERC20(address(buyToken_));
        fluxSwap.configure(FluxSwapMock.CallbackMode.Normal, buyToken, BUY_AMOUNT);
    }

    function testFuzzFluxPoolPaysBoundAmountAndMeasuresOutput(uint96 sellBalance, uint24 ppm_) public {
        sellBalance = uint96(bound(sellBalance, 1_000_000, type(uint96).max));
        uint256 ppm = bound(ppm_, 1, 1_000_000);
        deal(address(sellToken), address(settler), sellBalance);

        uint256 sellAmount = uint256(sellBalance) * ppm / 1_000_000;
        vm.expectCall(
            FLUX_SWAP,
            abi.encodeCall(
                IFluxSwap.swapWithCallback,
                (POOL_ID, true, sellAmount, 0, address(settler), abi.encodePacked(sellToken, sellAmount))
            )
        );
        _execute(ppm, buyToken, 0);

        assertEq(sellToken.balanceOf(FLUX_VAULT), sellAmount);
        assertEq(sellToken.balanceOf(address(settler)), sellBalance - sellAmount);
        assertEq(buyToken.balanceOf(address(settler)), BUY_AMOUNT);
    }

    function testFluxPoolRejectsWrongCallbackToken() public {
        fluxSwap.configure(FluxSwapMock.CallbackMode.WrongToken, buyToken, BUY_AMOUNT);
        vm.expectRevert(ConfusedDeputy.selector);
        _execute(1_000_000, buyToken, MIN_BUY_AMOUNT);
    }

    function testFluxPoolRejectsWrongCallbackAmount() public {
        fluxSwap.configure(FluxSwapMock.CallbackMode.WrongAmount, buyToken, BUY_AMOUNT);
        vm.expectRevert(ConfusedDeputy.selector);
        _execute(1_000_000, buyToken, MIN_BUY_AMOUNT);
    }

    function testFluxPoolRejectsWrongCallbackLength() public {
        fluxSwap.configure(FluxSwapMock.CallbackMode.WrongLength, buyToken, BUY_AMOUNT);
        vm.expectRevert(ConfusedDeputy.selector);
        _execute(1_000_000, buyToken, MIN_BUY_AMOUNT);
    }

    function testFluxPoolRejectsUnexpectedBuyToken() public {
        IERC20 unexpectedBuyToken = IERC20(address(new MockERC20("Unexpected", "UNEXPECTED", 18)));
        vm.expectRevert(abi.encodeWithSelector(TooMuchSlippage.selector, unexpectedBuyToken, MIN_BUY_AMOUNT, 0));
        _execute(1_000_000, unexpectedBuyToken, MIN_BUY_AMOUNT);
    }

    function testFluxPoolExcludesExistingBuyBalance() public {
        deal(address(buyToken), address(settler), BUY_AMOUNT);
        vm.expectRevert(abi.encodeWithSelector(TooMuchSlippage.selector, buyToken, BUY_AMOUNT + 1, BUY_AMOUNT));
        _execute(1_000_000, buyToken, BUY_AMOUNT + 1);
    }

    function _execute(uint256 ppm, IERC20 expectedBuyToken, uint256 minBuyAmount) private {
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.FLUXPOOL,
                (address(sellToken), ppm, POOL_ID, true, address(expectedBuyToken), minBuyAmount)
            )
        );
        ISettlerBase.AllowedSlippage memory slippage;
        settler.execute(slippage, actions, bytes32(0));
    }
}
