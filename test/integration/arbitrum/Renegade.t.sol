// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ARBITRUM_SELECTOR} from "src/core/Renegade.sol";
import {ArbitrumSettler} from "src/chains/Arbitrum/TakerSubmitted.sol";
import {ActionDataBuilder} from "../../utils/ActionDataBuilder.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";
import {SettlerBasePairTest, Shim} from "../SettlerBasePairTest.t.sol";
import {
    ARBITRUM_GAS_SPONSOR,
    ARBITRUM_TXN_CALLDATA,
    ARBITRUM_TXN_BLOCK,
    ABRITRUM_USDC,
    ABRITRUM_WETH,
    ARBITRUM_AMOUNT,
    ARBITRUM_SELL_BASE_CALLDATA,
    ARBITRUM_SELL_BASE_BLOCK,
    ARBITRUM_SELL_BASE_AMOUNT
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
        return ABRITRUM_USDC;
    }

    function toToken() internal pure virtual override returns (IERC20) {
        return ABRITRUM_WETH;
    }

    function _testName() internal pure virtual override returns (string memory) {
        return "ARBITRUM-RENEGADE";
    }

    function amount() internal pure virtual override returns (uint256) {
        return ARBITRUM_AMOUNT;
    }

    function _rerunTxn(
        bytes memory txnCalldata,
        bool baseForQuote,
        IERC20 sellToken,
        IERC20 buyToken,
        uint256 sellAmount
    ) internal {
        bytes memory _calldata = txnCalldata;
        assembly ("memory-safe") {
            let len := mload(_calldata)
            _calldata := add(0x04, _calldata)
            mstore(_calldata, sub(len, 4))
        }

        deal(address(sellToken), address(this), sellAmount);
        sellToken.approve(address(allowanceHolder), sellAmount);
        allowanceHolder.exec(
            address(settler),
            address(sellToken),
            sellAmount,
            payable(address(settler)),
            abi.encodeCall(
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
                            (ARBITRUM_GAS_SPONSOR, address(sellToken), baseForQuote, _calldata, 0)
                        )
                    ),
                    bytes32(0)
                )
            )
        );
    }

    // Sell-quote: USDC -> WETH
    // Replays https://arbiscan.io/tx/0x937b0111b64ce852f1202c324753f6e1066d1137e5aee5d2a076997b3c873dec
    function testSellQuote() public {
        _rerunTxn(ARBITRUM_TXN_CALLDATA, false, ABRITRUM_USDC, ABRITRUM_WETH, ARBITRUM_AMOUNT);
    }

    // Sell-base: WETH -> USDC
    // Replays https://arbiscan.io/tx/0x101b4aca8371f8a98ba112510a4d8c6622f4245c127628396f30b12cdc37faec
    function testSellBase() public {
        vm.rollFork(ARBITRUM_SELL_BASE_BLOCK - 1);
        vm.setEvmVersion("osaka");
        uint256 forkChainId = (new Shim()).chainId();
        vm.chainId(31337);
        bytes memory initCode = settlerInitCode();
        assembly ("memory-safe") {
            let s := create(0x00, add(0x20, initCode), mload(initCode))
            if iszero(s) { revert(0x00, 0x00) }
            sstore(settler.slot, s)
        }
        vm.etch(address(allowanceHolder), vm.getDeployedCode("AllowanceHolder.sol:AllowanceHolder"));
        vm.chainId(forkChainId);

        _rerunTxn(ARBITRUM_SELL_BASE_CALLDATA, true, ABRITRUM_WETH, ABRITRUM_USDC, ARBITRUM_SELL_BASE_AMOUNT);
    }
}
