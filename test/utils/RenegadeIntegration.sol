// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ActionDataBuilder} from "./ActionDataBuilder.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {SettlerBasePairTest} from "../integration/SettlerBasePairTest.t.sol";
import {InvalidRenegadeData, TooMuchSlippage} from "src/core/SettlerErrors.sol";

abstract contract RenegadeIntegrationTest is SettlerBasePairTest {
    uint256 private constant INPUT_TOKEN_ARG = 2;
    uint256 private constant OUTPUT_TOKEN_ARG = 3;
    uint256 private constant OPTIONS_OFFSET_ARG = 9;

    function setUp() public virtual override {
        super.setUp();
        vm.label(_gasSponsor(), "GasSponsor");
    }

    function _gasSponsor() internal pure virtual returns (address);
    function _txnCalldata() internal pure virtual returns (bytes memory);

    function _buildExecData(bytes memory txnCalldata) internal view returns (bytes memory) {
        return _buildExecData(txnCalldata, address(settler), type(uint256).max, 0, toToken(), 0);
    }

    function _buildExecData(
        bytes memory txnCalldata,
        address recipient,
        uint256 maxSellAmount,
        uint256 minBuyAmount,
        IERC20 outerBuyToken,
        uint256 outerMinAmountOut
    ) internal view returns (bytes memory) {
        (bool refundNativeEth, uint256 maxRefundAmount) = _refund(txnCalldata);
        return _buildExecDataFromPayload(
            _withoutSelector(txnCalldata),
            recipient,
            maxSellAmount,
            refundNativeEth,
            maxRefundAmount,
            minBuyAmount,
            outerBuyToken,
            outerMinAmountOut
        );
    }

    function _buildExecDataFromPayload(
        bytes memory renegadeData,
        address recipient,
        uint256 maxSellAmount,
        bool refundNativeEth,
        uint256 maxRefundAmount,
        uint256 minBuyAmount,
        IERC20 outerBuyToken,
        uint256 outerMinAmountOut
    ) internal view returns (bytes memory) {
        return abi.encodeCall(
            settler.execute,
            (
                ISettlerBase.AllowedSlippage({
                    recipient: payable(address(this)), buyToken: outerBuyToken, minAmountOut: outerMinAmountOut
                }),
                ActionDataBuilder.build(
                    abi.encodeCall(
                        ISettlerActions.TRANSFER_FROM,
                        (address(settler), defaultERC20PermitTransfer(address(fromToken()), amount(), 0), new bytes(0))
                    ),
                    abi.encodeCall(
                        ISettlerActions.RENEGADE,
                        (
                            recipient,
                            address(fromToken()),
                            address(toToken()),
                            maxSellAmount,
                            refundNativeEth,
                            maxRefundAmount,
                            renegadeData,
                            minBuyAmount
                        )
                    )
                ),
                bytes32(0)
            )
        );
    }

    function _refund(bytes memory txnCalldata) internal pure returns (bool refundNativeEth, uint256 maxRefundAmount) {
        // Equivalent Solidity: decode the refund fields from the captured sponsor calldata fixture.
        assembly ("memory-safe") {
            let optionsOffset := mload(add(0x144, txnCalldata))
            refundNativeEth := mload(add(0x44, add(txnCalldata, optionsOffset)))
            maxRefundAmount := mload(add(0x64, add(txnCalldata, optionsOffset)))
        }
    }

    function _withoutSelector(bytes memory txnCalldata) internal pure returns (bytes memory data) {
        data = txnCalldata;
        assembly ("memory-safe") {
            let len := mload(data)
            data := add(0x04, data)
            mstore(data, sub(len, 4))
        }
    }

    // Overwrites ABI arg word `argIndex` in a copy of `cd` (4-byte selector at byte 0).
    // args: 2=internalPartyInputToken, 3=internalPartyOutputToken, 9=gasSponsorOptions offset.
    function _mutate(bytes memory cd, uint256 argIndex, uint256 value) internal pure returns (bytes memory out) {
        out = bytes.concat(cd);
        uint256 off = 0x24 + (argIndex * 0x20);
        assembly ("memory-safe") {
            mstore(add(off, out), value)
        }
    }

    function _withOutputToken(bytes memory cd, IERC20 token) internal pure returns (bytes memory) {
        return _mutate(cd, OUTPUT_TOKEN_ARG, uint256(uint160(address(token))));
    }

    function _withInputToken(bytes memory cd, IERC20 token) internal pure returns (bytes memory) {
        return _mutate(cd, INPUT_TOKEN_ARG, uint256(uint160(address(token))));
    }

    // Halfway between the quote's min bound and the captured trade's implied fill.
    function _partialMaxSell(bytes memory cd) internal view returns (uint256) {
        uint256 price;
        uint256 minBaseAmount;
        assembly ("memory-safe") {
            price := mload(add(0xa4, cd))
            minBaseAmount := mload(add(0xc4, cd))
        }
        uint256 mid = (minBaseAmount + (amount() << 63) / price) / 2;
        return (mid * price) >> 63;
    }

    function _exec(bytes memory ahData) internal {
        deal(address(fromToken()), address(this), amount());
        fromToken().approve(address(allowanceHolder), amount());
        allowanceHolder.exec(address(settler), address(fromToken()), amount(), payable(address(settler)), ahData);
    }

    function _expectTooMuchSlippage(bytes memory ahData, IERC20 expectedToken) internal {
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
            assertEq(address(revertedToken), address(expectedToken), "revert should report buyToken");
        }
    }

    function testSellToRenegade() public {
        uint256 balanceBefore = balanceOf(toToken(), address(this));
        _exec(_buildExecData(_txnCalldata()));
        assertGt(balanceOf(toToken(), address(this)), balanceBefore);
    }

    // Outer slippage is enforced by the central _checkSlippageAndTransfer against signed minAmountOut.
    function testOuterSlippageBinds() public {
        bytes memory ahData =
            _buildExecData(_txnCalldata(), address(settler), type(uint256).max, 0, toToken(), type(uint256).max);
        _expectTooMuchSlippage(ahData, toToken());
    }

    function testPerLegSlippageBinds() public {
        bytes memory ahData =
            _buildExecData(_txnCalldata(), address(settler), type(uint256).max, type(uint256).max, toToken(), 0);
        _expectTooMuchSlippage(ahData, toToken());
    }

    function testCustodyOptimization() public {
        uint256 balanceBefore = balanceOf(toToken(), address(this));
        _exec(_buildExecData(_txnCalldata(), address(this), type(uint256).max, 1, IERC20(address(0)), 0));
        assertGt(balanceOf(toToken(), address(this)), balanceBefore);
    }

    function testClampPartialFill() public {
        uint256 maxSellAmount = _partialMaxSell(_txnCalldata());
        assertLt(maxSellAmount, amount());

        uint256 balanceBefore = balanceOf(toToken(), address(this));
        _exec(_buildExecData(_txnCalldata(), address(settler), maxSellAmount, 0, toToken(), 0));
        assertGt(balanceOf(toToken(), address(this)), balanceBefore);
        // The solver models Renegade as quote-capped so a following action consumes this remainder.
        assertEq(balanceOf(fromToken(), address(settler)), amount() - maxSellAmount);
    }

    function testInputTokenForcedToBuyToken() public {
        uint256 balanceBefore = balanceOf(toToken(), address(this));
        _exec(_buildExecData(_withInputToken(_txnCalldata(), fromToken())));
        assertGt(balanceOf(toToken(), address(this)), balanceBefore);
    }

    function testOutputTokenForcedToSellToken() public {
        uint256 balanceBefore = balanceOf(toToken(), address(this));
        _exec(_buildExecData(_withOutputToken(_txnCalldata(), toToken())));
        assertGt(balanceOf(toToken(), address(this)), balanceBefore);
    }

    function testShortDataReverts() public {
        bytes memory ahData =
            _buildExecDataFromPayload(new bytes(0x80), address(settler), type(uint256).max, false, 0, 0, toToken(), 0);
        deal(address(fromToken()), address(this), amount());
        fromToken().approve(address(allowanceHolder), amount());
        vm.expectRevert(InvalidRenegadeData.selector);
        allowanceHolder.exec(address(settler), address(fromToken()), amount(), payable(address(settler)), ahData);
    }

    function testUnalignedOptionsOffsetReverts() public {
        bytes memory renegadeData = _withoutSelector(_mutate(_txnCalldata(), OPTIONS_OFFSET_ARG, 0x141));
        bytes memory ahData =
            _buildExecDataFromPayload(renegadeData, address(settler), type(uint256).max, false, 0, 0, toToken(), 0);
        deal(address(fromToken()), address(this), amount());
        fromToken().approve(address(allowanceHolder), amount());
        vm.expectRevert(InvalidRenegadeData.selector);
        allowanceHolder.exec(address(settler), address(fromToken()), amount(), payable(address(settler)), ahData);
    }
}
