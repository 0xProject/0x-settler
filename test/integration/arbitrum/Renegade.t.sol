// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ARBITRUM_SELECTOR} from "src/core/Renegade.sol";
import {ArbitrumSettler} from "src/chains/Arbitrum/TakerSubmitted.sol";
import {ActionDataBuilder} from "../../utils/ActionDataBuilder.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {SettlerBasePairTest} from "../SettlerBasePairTest.t.sol";
import {
    ARBITRUM_GAS_SPONSOR,
    ARBITRUM_TXN_CALLDATA,
    ARBITRUM_TXN_BLOCK,
    ABRITRUM_USDC,
    ABRITRUM_WETH,
    ARBITRUM_AMOUNT
} from "../RenegadeTxn.t.sol";

// Sell-quote: USDC -> WETH
// Replays https://arbiscan.io/tx/0x937b0111b64ce852f1202c324753f6e1066d1137e5aee5d2a076997b3c873dec
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

    function testSellQuote() public {
        bytes memory _calldata = ARBITRUM_TXN_CALLDATA;
        assembly ("memory-safe") {
            let len := mload(_calldata)
            _calldata := add(0x04, _calldata)
            mstore(_calldata, sub(len, 4))
        }

        deal(address(fromToken()), address(this), amount());
        fromToken().approve(address(allowanceHolder), amount());
        allowanceHolder.exec(
            address(settler),
            address(fromToken()),
            amount(),
            payable(address(settler)),
            abi.encodeCall(
                settler.execute,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(this)), buyToken: toToken(), minAmountOut: 0
                    }),
                    ActionDataBuilder.build(
                        abi.encodeCall(
                            ISettlerActions.TRANSFER_FROM,
                            (
                                address(settler),
                                defaultERC20PermitTransfer(address(fromToken()), amount(), 0),
                                new bytes(0)
                            )
                        ),
                        abi.encodeCall(
                            ISettlerActions.RENEGADE, (ARBITRUM_GAS_SPONSOR, address(fromToken()), false, 0, _calldata)
                        )
                    ),
                    bytes32(0)
                )
            )
        );
    }
}
