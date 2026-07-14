// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {Settler} from "src/Settler.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {BnbSettler} from "src/chains/Bnb/TakerSubmitted.sol";
import {squadSwapV3ForkId} from "src/core/univ3forks/SquadSwapV3.sol";

import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";

contract SquadSwapV3Test is SettlerBasePairTest {
    IERC20 private constant USDT = IERC20(0x55d398326f99059fF775485246999027B3197955);
    IERC20 private constant WBNB = IERC20(0xbb4CdB9CBd36B01bD1cBaEBF2De08d9173bc095c);

    function _testName() internal pure override returns (string memory) {
        return "USDT-WBNB";
    }

    function _testChainId() internal pure override returns (string memory) {
        return "bnb";
    }

    function _testBlockNumber() internal pure override returns (uint256) {
        return 66500000;
    }

    function fromToken() internal pure override returns (IERC20) {
        return USDT;
    }

    function toToken() internal pure override returns (IERC20) {
        return WBNB;
    }

    function amount() internal pure override returns (uint256) {
        return 100e18;
    }

    function settlerInitCode() internal pure override returns (bytes memory) {
        return bytes.concat(type(BnbSettler).creationCode, abi.encode(bytes20(0)));
    }

    function setUp() public override {
        super.setUp();

        // FROM has code at this block; clear it across fork rolls so Permit2 uses ecrecover.
        vm.etch(FROM, "");
        vm.makePersistent(FROM);
        safeApproveIfBelow(fromToken(), FROM, address(PERMIT2), amount());
    }

    function testSquadSwapV3VIP() public {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.UNISWAPV3_VIP,
                (
                    FROM,
                    permit,
                    abi.encodePacked(USDT, squadSwapV3ForkId, uint24(500), uint160(4295128740), WBNB),
                    sig,
                    0
                )
            )
        );

        vm.startPrank(FROM);
        snapStartName("settler_squadSwapV3VIP");
        Settler.AllowedSlippage memory slippage;
        Settler(settler).execute(slippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        assertEq(USDT.balanceOf(FROM), 0);
        assertGt(WBNB.balanceOf(FROM), 0);
    }
}
