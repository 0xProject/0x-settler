// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {BASE_SELECTOR} from "src/core/Renegade.sol";
import {BaseSettler} from "src/chains/Base/TakerSubmitted.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";
import {Test} from "@forge-std/Test.sol";
import {BASE_GAS_SPONSOR, BASE_USDC, BASE_WETH} from "./RenegadeTxn.t.sol";

/// @dev Mocks Renegade GasSponsor (word 0 = quote, word 1 = base).
///      Uses WETH allowance to infer direction; only valid on fresh deploys.
contract MockGasSponsor {
    IERC20 constant USDC = IERC20(address(BASE_USDC));
    IERC20 constant WETH = IERC20(address(BASE_WETH));

    fallback() external payable {
        uint256 quoteAmount;
        uint256 baseAmount;
        assembly {
            quoteAmount := calldataload(4)
            baseAmount := calldataload(36)
        }

        uint256 wethAllowance = WETH.allowance(msg.sender, address(this));

        if (wethAllowance >= baseAmount && baseAmount > 0) {
            WETH.transferFrom(msg.sender, address(this), baseAmount);
            USDC.transfer(msg.sender, quoteAmount);
        } else {
            USDC.transferFrom(msg.sender, address(this), quoteAmount);
            WETH.transfer(msg.sender, baseAmount);
        }
    }
}

/// @dev Tests sell-base direction (WETH -> USDC) through the RENEGADE action.
///      Uses a mock GasSponsor because no real sell-base tx exists on-chain yet.
///      Replace with a real tx replay (like Renegade.t.sol) once one is available.
contract RenegadeSellBaseTest is SettlerBasePairTest {
    address mockGasSponsor;

    uint256 constant SELL_AMOUNT = 0.01 ether;
    uint256 constant BUY_AMOUNT_USDC = 19_000_000;

    function setUp() public virtual override {
        super.setUp();
        mockGasSponsor = address(new MockGasSponsor());
        deal(address(BASE_USDC), mockGasSponsor, 1_000_000 * 1e6);
    }

    function settlerInitCode() internal virtual override returns (bytes memory) {
        return bytes.concat(type(BaseSettler).creationCode, abi.encode(bytes20(0)));
    }

    function _testChainId() internal pure virtual override returns (string memory) {
        return "base";
    }

    function _testBlockNumber() internal pure virtual override returns (uint256) {
        return 38176523;
    }

    function fromToken() internal pure virtual override returns (IERC20) {
        return BASE_WETH;
    }

    function toToken() internal pure virtual override returns (IERC20) {
        return BASE_USDC;
    }

    function _testName() internal pure virtual override returns (string memory) {
        return "RENEGADE-SELL-BASE";
    }

    function amount() internal pure virtual override returns (uint256) {
        return SELL_AMOUNT;
    }

    function testSellBaseDirection() public {
        bytes memory renegadeData = abi.encode(BUY_AMOUNT_USDC, SELL_AMOUNT, address(0));

        deal(address(fromToken()), address(this), amount());
        fromToken().approve(address(allowanceHolder), amount());

        uint256 usdcBefore = BASE_USDC.balanceOf(address(this));

        allowanceHolder.exec(
            address(settler),
            address(fromToken()),
            amount(),
            payable(address(settler)),
            abi.encodeCall(
                settler.execute,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(this)),
                        buyToken: toToken(),
                        minAmountOut: 0
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
                            ISettlerActions.RENEGADE, (mockGasSponsor, address(fromToken()), true, renegadeData)
                        )
                    ),
                    bytes32(0)
                )
            )
        );

        assertEq(BASE_USDC.balanceOf(address(this)) - usdcBefore, BUY_AMOUNT_USDC);
    }
}
