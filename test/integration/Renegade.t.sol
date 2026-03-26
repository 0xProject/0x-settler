// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {BASE_SELECTOR} from "src/core/Renegade.sol";
import {BaseSettler} from "src/chains/Base/TakerSubmitted.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";
import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";
import {TooMuchSlippage} from "src/core/SettlerErrors.sol";
import {
    BASE_GAS_SPONSOR,
    BASE_TXN_CALLDATA,
    BASE_TXN_BLOCK,
    BASE_USDC,
    BASE_WETH,
    BASE_AMOUNT,
    BASE_SELL_BASE_CALLDATA,
    BASE_SELL_BASE_BLOCK,
    BASE_SELL_BASE_AMOUNT
} from "./RenegadeTxn.t.sol";

contract RenegadeBaseIntegrationTest is SettlerBasePairTest {
    function setUp() public virtual override {
        super.setUp();
        vm.label(BASE_GAS_SPONSOR, "GasSponsor");
    }

    function settlerInitCode() internal virtual override returns (bytes memory) {
        return bytes.concat(type(BaseSettler).creationCode, abi.encode(bytes20(0)));
    }

    function _testChainId() internal pure virtual override returns (string memory) {
        return "base";
    }

    function _testBlockNumber() internal pure virtual override returns (uint256) {
        return BASE_TXN_BLOCK - 1;
    }

    function fromToken() internal pure virtual override returns (IERC20) {
        return BASE_USDC;
    }

    function toToken() internal pure virtual override returns (IERC20) {
        return BASE_WETH;
    }

    function _testName() internal pure virtual override returns (string memory) {
        return "BASE-RENEGADE";
    }

    function amount() internal pure virtual override returns (uint256) {
        return BASE_AMOUNT;
    }

    function _buildExecData(
        bytes memory txnCalldata,
        bool baseForQuote,
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
                ISettlerBase.AllowedSlippage({
                    recipient: payable(address(this)), buyToken: buyToken, minAmountOut: 0
                }),
                ActionDataBuilder.build(
                    abi.encodeCall(
                        ISettlerActions.TRANSFER_FROM,
                        (
                            address(settler),
                            defaultERC20PermitTransfer(address(sellToken), sellAmount, 0),
                            new bytes(0)
                        )
                    ),
                    abi.encodeCall(
                        ISettlerActions.RENEGADE,
                        (BASE_GAS_SPONSOR, address(sellToken), baseForQuote, _calldata, minBuyAmount)
                    )
                ),
                bytes32(0)
            )
        );
    }

    function _rerunTxn(
        bytes memory txnCalldata,
        bool baseForQuote,
        IERC20 sellToken,
        IERC20 buyToken,
        uint256 sellAmount
    ) internal {
        bytes memory ahData = _buildExecData(txnCalldata, baseForQuote, sellToken, buyToken, sellAmount, 0);

        deal(address(sellToken), address(this), sellAmount);
        sellToken.approve(address(allowanceHolder), sellAmount);
        allowanceHolder.exec(address(settler), address(sellToken), sellAmount, payable(address(settler)), ahData);
    }

    // Sell-quote: USDC -> WETH
    // Replays https://basescan.org/tx/0xbfcb0bcd28de600cbca36a3be9630aeed3b0d44be2e78a21e46f0abc64414085
    function testSellQuote() public {
        _rerunTxn(BASE_TXN_CALLDATA, false, BASE_USDC, BASE_WETH, BASE_AMOUNT);
    }

    // Sell-base: WETH -> USDC
    // Replays https://basescan.org/tx/0xcfe9507e3e591f9340a185a8114cc762c44ba973c22925880f36516f1001e2b2
    function testSellBase() public {
        // Roll to a different block for sell-base calldata; redeploy settler + AllowanceHolder
        vm.rollFork(BASE_SELL_BASE_BLOCK - 1);
        uint256 forkChainId = vm.getChainId();
        vm.chainId(31337);
        bytes memory initCode = settlerInitCode();
        assembly ("memory-safe") {
            let s := create(0x00, add(0x20, initCode), mload(initCode))
            if iszero(s) { revert(0x00, 0x00) }
            sstore(settler.slot, s)
        }
        vm.etch(address(allowanceHolder), vm.getDeployedCode("AllowanceHolder.sol:AllowanceHolder"));
        vm.chainId(forkChainId);

        _rerunTxn(BASE_SELL_BASE_CALLDATA, true, BASE_WETH, BASE_USDC, BASE_SELL_BASE_AMOUNT);
    }

    function _expectSlippageRevert(
        bytes memory ahData,
        IERC20 sellToken,
        IERC20 expectedBuyToken,
        uint256 sellAmount
    ) internal {
        deal(address(sellToken), address(this), sellAmount);
        sellToken.approve(address(allowanceHolder), sellAmount);

        try allowanceHolder.exec(address(settler), address(sellToken), sellAmount, payable(address(settler)), ahData) {
            revert("expected TooMuchSlippage revert");
        } catch (bytes memory reason) {
            assertEq(bytes4(reason), TooMuchSlippage.selector);
            // Decode the token address from the error data (first word after selector)
            IERC20 revertedToken;
            assembly ("memory-safe") {
                revertedToken := mload(add(reason, 0x24))
            }
            assertEq(address(revertedToken), address(expectedBuyToken), "revert should report buyToken, not sellToken");
        }
    }

    // Verify revertTooMuchSlippage reports the correct buyToken (WETH) when selling quote (USDC)
    function testSellQuoteSlippageRevert() public {
        bytes memory ahData = _buildExecData(BASE_TXN_CALLDATA, false, BASE_USDC, BASE_WETH, BASE_AMOUNT, type(uint256).max);
        _expectSlippageRevert(ahData, BASE_USDC, BASE_WETH, BASE_AMOUNT);
    }

    // Verify revertTooMuchSlippage reports the correct buyToken (USDC) when selling base (WETH)
    function testSellBaseSlippageRevert() public {
        vm.rollFork(BASE_SELL_BASE_BLOCK - 1);
        uint256 forkChainId = vm.getChainId();
        vm.chainId(31337);
        bytes memory initCode = settlerInitCode();
        assembly ("memory-safe") {
            let s := create(0x00, add(0x20, initCode), mload(initCode))
            if iszero(s) { revert(0x00, 0x00) }
            sstore(settler.slot, s)
        }
        vm.etch(address(allowanceHolder), vm.getDeployedCode("AllowanceHolder.sol:AllowanceHolder"));
        vm.chainId(forkChainId);

        bytes memory ahData = _buildExecData(BASE_SELL_BASE_CALLDATA, true, BASE_WETH, BASE_USDC, BASE_SELL_BASE_AMOUNT, type(uint256).max);
        _expectSlippageRevert(ahData, BASE_WETH, BASE_USDC, BASE_SELL_BASE_AMOUNT);
    }
}
