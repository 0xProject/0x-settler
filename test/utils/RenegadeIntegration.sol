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

    function setUp() public virtual override {
        super.setUp();
        vm.label(_gasSponsor(), "GasSponsor");
    }

    function _gasSponsor() internal pure virtual returns (address);
    function _txnCalldata() internal pure virtual returns (bytes memory);

    function _buildExecData(bytes memory txnCalldata) internal view returns (bytes memory) {
        return _buildExecData(txnCalldata, 0);
    }

    function _buildExecData(bytes memory txnCalldata, uint256 outerMinAmountOut) internal view returns (bytes memory) {
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
                    abi.encodeCall(ISettlerActions.RENEGADE, (address(fromToken()), data))
                ),
                bytes32(0)
            )
        );
    }

    // Overwrites ABI arg word `argIndex` in a copy of `cd` (4-byte selector at byte 0).
    // args: 1=recipient, 3=internalPartyOutputToken.
    function _mutate(bytes memory cd, uint256 argIndex, uint256 value) internal pure returns (bytes memory out) {
        out = bytes.concat(cd);
        uint256 off = 0x24 + (argIndex * 0x20);
        assembly ("memory-safe") {
            mstore(add(off, out), value)
        }
    }

    function _withRecipient(bytes memory cd, address recipient) internal pure returns (bytes memory) {
        return _mutate(cd, RECIPIENT_ARG, uint256(uint160(recipient)));
    }

    function _withOutputToken(bytes memory cd, IERC20 token) internal pure returns (bytes memory) {
        return _mutate(cd, OUTPUT_TOKEN_ARG, uint256(uint160(address(token))));
    }

    function _exec(bytes memory ahData) internal {
        deal(address(fromToken()), address(this), amount());
        fromToken().approve(address(allowanceHolder), amount());
        allowanceHolder.exec(address(settler), address(fromToken()), amount(), payable(address(settler)), ahData);
    }

    function _expectRevert(bytes memory ahData, bytes4 selector) internal {
        deal(address(fromToken()), address(this), amount());
        fromToken().approve(address(allowanceHolder), amount());
        vm.expectRevert(selector);
        allowanceHolder.exec(address(settler), address(fromToken()), amount(), payable(address(settler)), ahData);
    }

    function testSellToRenegade() public {
        uint256 balanceBefore = balanceOf(toToken(), address(this));
        _exec(_buildExecData(_txnCalldata()));
        assertGt(balanceOf(toToken(), address(this)), balanceBefore);
    }

    // Slippage is enforced only by the central _checkSlippageAndTransfer against the signed minAmountOut.
    function testOuterSlippageBinds() public {
        bytes memory ahData = _buildExecData(_txnCalldata(), type(uint256).max);
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
            assertEq(address(revertedToken), address(toToken()), "revert should report buyToken");
        }
    }

    function testSellTokenMustMatchRenegadeOutputToken() public {
        bytes memory cd = _withOutputToken(_txnCalldata(), toToken());
        _expectRevert(_buildExecData(cd), InvalidRenegadeData.selector);
    }

    // The settler overrides recipient to itself, so a solver-named recipient is ignored and the
    // output still reaches the taker via the central transfer.
    function testRecipientForcedToSettler() public {
        uint256 balanceBefore = balanceOf(toToken(), address(this));
        _exec(_buildExecData(_withRecipient(_txnCalldata(), address(0xBEEF))));
        assertGt(balanceOf(toToken(), address(this)), balanceBefore);
    }

    function testShortDataReverts() public {
        _expectRevert(_buildExecData(new bytes(0x80)), InvalidRenegadeData.selector);
    }
}
