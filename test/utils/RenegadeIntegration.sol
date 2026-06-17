// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ActionDataBuilder} from "./ActionDataBuilder.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {SettlerBasePairTest} from "../integration/SettlerBasePairTest.t.sol";
import {InvalidRenegadeData, TooMuchSlippage} from "src/core/SettlerErrors.sol";

abstract contract RenegadeIntegrationTest is SettlerBasePairTest {
    uint256 private constant RECIPIENT_ARG = 1;
    uint256 private constant OUTPUT_TOKEN_ARG = 3;
    uint256 private constant PRICE_ARG = 4;
    uint256 private constant MIN_BUY_AMOUNT_ARG = 5;
    uint256 private constant MAX_BUY_AMOUNT_ARG = 6;

    function setUp() public virtual override {
        super.setUp();
        vm.label(_gasSponsor(), "GasSponsor");
    }

    function _gasSponsor() internal pure virtual returns (address);
    function _txnCalldata() internal pure virtual returns (bytes memory);

    function _buildExecData(bytes memory txnCalldata, uint256 minBuyAmount) internal view returns (bytes memory) {
        return _buildExecData(txnCalldata, minBuyAmount, 0);
    }

    function _buildExecData(bytes memory txnCalldata, uint256 minBuyAmount, uint256 outerMinAmountOut)
        internal
        view
        returns (bytes memory)
    {
        bytes memory data = txnCalldata;
        assembly ("memory-safe") {
            let len := mload(data)
            data := add(0x04, data)
            mstore(data, sub(len, 4))
        }

        return abi.encodeCall(
            settler.execute,
            (
                ISettlerBase.AllowedSlippage({
                    recipient: payable(address(this)), buyToken: toToken(), minAmountOut: outerMinAmountOut
                }),
                ActionDataBuilder.build(
                    abi.encodeCall(
                        ISettlerActions.TRANSFER_FROM,
                        (address(settler), defaultERC20PermitTransfer(address(fromToken()), amount(), 0), new bytes(0))
                    ),
                    abi.encodeCall(ISettlerActions.RENEGADE, (address(fromToken()), data, minBuyAmount))
                ),
                bytes32(0)
            )
        );
    }

    // Overwrites ABI arg word `argIndex` in a copy of `cd` (4-byte selector at byte 0).
    // args: 1=recipient, 4=price, 5=min, 6=max.
    function _mutate(bytes memory cd, uint256 argIndex, uint256 value) internal pure returns (bytes memory out) {
        out = bytes.concat(cd);
        uint256 off = 0x24 + (argIndex * 0x20);
        assembly ("memory-safe") {
            mstore(add(off, out), value)
        }
    }

    function _readWord(bytes memory cd, uint256 argIndex) internal pure returns (uint256 v) {
        uint256 off = 0x24 + (argIndex * 0x20);
        assembly ("memory-safe") {
            v := mload(add(off, cd))
        }
    }

    function _price(bytes memory cd) internal pure returns (uint256) {
        return _readWord(cd, PRICE_ARG);
    }

    function _withRecipient(bytes memory cd, address recipient) internal pure returns (bytes memory) {
        return _mutate(cd, RECIPIENT_ARG, uint256(uint160(recipient)));
    }

    function _withOutputToken(bytes memory cd, IERC20 token) internal pure returns (bytes memory) {
        return _mutate(cd, OUTPUT_TOKEN_ARG, uint256(uint160(address(token))));
    }

    function _withPrice(bytes memory cd, uint256 price) internal pure returns (bytes memory) {
        return _mutate(cd, PRICE_ARG, price);
    }

    function _withMinBuyAmount(bytes memory cd, uint256 minBuyAmount) internal pure returns (bytes memory) {
        return _mutate(cd, MIN_BUY_AMOUNT_ARG, minBuyAmount);
    }

    function _withMaxBuyAmount(bytes memory cd, uint256 maxBuyAmount) internal pure returns (bytes memory) {
        return _mutate(cd, MAX_BUY_AMOUNT_ARG, maxBuyAmount);
    }

    function _expectRevert(bytes memory ahData, bytes4 selector) internal {
        deal(address(fromToken()), address(this), amount());
        fromToken().approve(address(allowanceHolder), amount());
        vm.expectRevert(selector);
        allowanceHolder.exec(address(settler), address(fromToken()), amount(), payable(address(settler)), ahData);
    }

    function _expectSlippageRevert(bytes memory ahData) internal {
        deal(address(fromToken()), address(this), amount());
        fromToken().approve(address(allowanceHolder), amount());

        try allowanceHolder.exec(address(settler), address(fromToken()), amount(), payable(address(settler)), ahData) {
            revert("expected TooMuchSlippage revert");
        } catch (bytes memory reason) {
            assertEq(bytes4(reason), TooMuchSlippage.selector);
            IERC20 revertedToken;
            assembly ("memory-safe") {
                revertedToken := mload(add(reason, 0x24))
            }
            assertEq(address(revertedToken), address(toToken()), "revert should report buyToken, not sellToken");
        }
    }

    function testSellToRenegade() public {
        uint256 balanceBefore = balanceOf(toToken(), address(this));
        bytes memory ahData = _buildExecData(_txnCalldata(), 0);
        deal(address(fromToken()), address(this), amount());
        fromToken().approve(address(allowanceHolder), amount());
        allowanceHolder.exec(address(settler), address(fromToken()), amount(), payable(address(settler)), ahData);
        assertGt(balanceOf(toToken(), address(this)), balanceBefore);
    }

    function testSlippageRevertReportsBuyToken() public {
        _expectSlippageRevert(_buildExecData(_txnCalldata(), type(uint256).max));
    }

    function testSellTokenMustMatchRenegadeOutputToken() public {
        bytes memory cd = _withOutputToken(_txnCalldata(), toToken());
        _expectRevert(_buildExecData(cd, 0), InvalidRenegadeData.selector);
    }

    function testRecipientMustBeSettlerOrZero() public {
        bytes memory cd = _withRecipient(_txnCalldata(), address(0xBEEF));
        _expectRevert(_buildExecData(cd, 0), InvalidRenegadeData.selector);
    }

    function testZeroPriceReverts() public {
        // Zero price and min bound so the price guard reverts, not the bounds check.
        bytes memory cd = _withMinBuyAmount(_withPrice(_txnCalldata(), 0), 0);
        _expectRevert(_buildExecData(cd, 0), InvalidRenegadeData.selector);
    }

    function testBuyAmountBelowMinBoundReverts() public {
        _expectRevert(
            _buildExecData(_withMinBuyAmount(_txnCalldata(), type(uint256).max), 0), InvalidRenegadeData.selector
        );
    }

    function testBuyAmountAboveMaxBoundReverts() public {
        _expectRevert(_buildExecData(_withMaxBuyAmount(_txnCalldata(), 1), 0), InvalidRenegadeData.selector);
    }
}
