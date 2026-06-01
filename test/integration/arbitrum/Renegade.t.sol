// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ArbitrumSettler} from "src/chains/Arbitrum/TakerSubmitted.sol";
import {ActionDataBuilder} from "../../utils/ActionDataBuilder.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {SettlerBasePairTest} from "../SettlerBasePairTest.t.sol";
import {InvalidRenegadeData, TooMuchSlippage} from "src/core/SettlerErrors.sol";
import {
    ARBITRUM_AMOUNT,
    ARBITRUM_GMX,
    ARBITRUM_GAS_SPONSOR,
    ARBITRUM_TXN_BLOCK,
    ARBITRUM_TXN_CALLDATA,
    ARBITRUM_USDC
} from "../RenegadeTxn.t.sol";

contract RenegadeArbitrumIntegrationTest is SettlerBasePairTest {
    function setUp() public virtual override {
        super.setUp();
        vm.label(ARBITRUM_GAS_SPONSOR, "GasSponsor");
    }

    function settlerInitCode() internal virtual override returns (bytes memory) {
        return bytes.concat(type(ArbitrumSettler).creationCode, abi.encode(bytes20(0)));
    }

    function _testChainId() internal pure virtual override returns (string memory) {
        return "arbitrum";
    }

    function _testBlockNumber() internal pure virtual override returns (uint256) {
        return ARBITRUM_TXN_BLOCK - 1;
    }

    function fromToken() internal pure virtual override returns (IERC20) {
        return ARBITRUM_GMX;
    }

    function toToken() internal pure virtual override returns (IERC20) {
        return ARBITRUM_USDC;
    }

    function _testName() internal pure virtual override returns (string memory) {
        return "ARBITRUM-RENEGADE";
    }

    function amount() internal pure virtual override returns (uint256) {
        return ARBITRUM_AMOUNT;
    }

    function _buildExecData(
        bytes memory txnCalldata,
        IERC20 sellToken,
        IERC20 buyToken,
        uint256 sellAmount,
        uint256 minBuyAmount
    ) internal view returns (bytes memory) {
        bytes memory _calldata = txnCalldata;
        assembly ("memory-safe") {
            let len := mload(_calldata)
            _calldata := add(0x04, _calldata)
            mstore(_calldata, sub(len, 4))
        }

        return abi.encodeCall(
            settler.execute,
            (
                ISettlerBase.AllowedSlippage({recipient: payable(address(this)), buyToken: buyToken, minAmountOut: 0}),
                ActionDataBuilder.build(
                    abi.encodeCall(
                        ISettlerActions.TRANSFER_FROM,
                        (address(settler), defaultERC20PermitTransfer(address(sellToken), sellAmount, 0), new bytes(0))
                    ),
                    abi.encodeCall(
                        ISettlerActions.RENEGADE, (ARBITRUM_GAS_SPONSOR, address(sellToken), _calldata, minBuyAmount)
                    )
                ),
                bytes32(0)
            )
        );
    }

    function _rerunTxn(bytes memory txnCalldata, IERC20 sellToken, IERC20 buyToken, uint256 sellAmount) internal {
        bytes memory ahData = _buildExecData(txnCalldata, sellToken, buyToken, sellAmount, 0);

        uint256 balanceBefore = balanceOf(buyToken, address(this));
        deal(address(sellToken), address(this), sellAmount);
        sellToken.approve(address(allowanceHolder), sellAmount);
        allowanceHolder.exec(address(settler), address(sellToken), sellAmount, payable(address(settler)), ahData);
        assertGt(balanceOf(buyToken, address(this)), balanceBefore);
    }

    function _expectSlippageRevert(bytes memory ahData, IERC20 sellToken, IERC20 expectedBuyToken, uint256 sellAmount)
        internal
    {
        deal(address(sellToken), address(this), sellAmount);
        sellToken.approve(address(allowanceHolder), sellAmount);

        try allowanceHolder.exec(address(settler), address(sellToken), sellAmount, payable(address(settler)), ahData) {
            revert("expected TooMuchSlippage revert");
        } catch (bytes memory reason) {
            assertEq(bytes4(reason), TooMuchSlippage.selector);
            IERC20 revertedToken;
            assembly ("memory-safe") {
                revertedToken := mload(add(reason, 0x24))
            }
            assertEq(address(revertedToken), address(expectedBuyToken), "revert should report buyToken, not sellToken");
        }
    }

    // GMX -> USDC with `recipient == address(0)`.
    // Replays the embedded Renegade v2 call from https://arbiscan.io/tx/0xc8f6bc1f5bdbc0efd76d03de8ca8d7f5d4988f6ab741d4e92d2be843fe192889
    function testSellToRenegade() public {
        _rerunTxn(ARBITRUM_TXN_CALLDATA, ARBITRUM_GMX, ARBITRUM_USDC, ARBITRUM_AMOUNT);
    }

    function testSlippageRevertReportsBuyToken() public {
        bytes memory ahData =
            _buildExecData(ARBITRUM_TXN_CALLDATA, ARBITRUM_GMX, ARBITRUM_USDC, ARBITRUM_AMOUNT, type(uint256).max);
        _expectSlippageRevert(ahData, ARBITRUM_GMX, ARBITRUM_USDC, ARBITRUM_AMOUNT);
    }

    function testSellTokenMustMatchRenegadeOutputToken() public {
        bytes memory ahData = _buildExecData(ARBITRUM_TXN_CALLDATA, ARBITRUM_USDC, ARBITRUM_GMX, 1e6, 0);

        deal(address(ARBITRUM_USDC), address(this), 1e6);
        ARBITRUM_USDC.approve(address(allowanceHolder), 1e6);
        vm.expectRevert(InvalidRenegadeData.selector);
        allowanceHolder.exec(address(settler), address(ARBITRUM_USDC), 1e6, payable(address(settler)), ahData);
    }
}
