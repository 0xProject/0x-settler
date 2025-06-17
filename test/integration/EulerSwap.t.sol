// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {Settler} from "src/Settler.sol";

import {IEVC} from "src/core/EulerSwap.sol";

import {AllowanceHolderPairTest} from "./AllowanceHolderPairTest.t.sol";

IEVC constant EVC = IEVC(0x0C9a3dd6b8F28529d72d7f9cE918D493519EE383);

abstract contract EulerSwapTest is AllowanceHolderPairTest {
    function eulerSwapPool() internal view virtual returns (address) {
        return address(0);
    }

    function eulerSwapBlock() internal view virtual returns (uint256) {
        return 0;
    }

    function eulerSwapAmount() internal view virtual returns (uint256) {
        return amount();
    }

    modifier setEulerSwapBlock() {
        uint256 blockNumber = vm.getBlockNumber();
        vm.rollFork(eulerSwapBlock());
        _;
        vm.rollFork(blockNumber);
    }

    function _setEulerSwapLabels() private setEulerSwapBlock {
        vm.label(address(EVC), "EVC");
        vm.label(eulerSwapPool(), string.concat("EulerSwap ", testName(), " pool"));
    }

    function setUp() public virtual override {
        super.setUp();
        if (eulerSwapPool() != address(0)) {
            vm.makePersistent(address(PERMIT2));
            vm.makePersistent(address(allowanceHolder));
            vm.makePersistent(address(settler));
            vm.makePersistent(address(fromToken()));
            vm.makePersistent(address(toToken()));
            _setEulerSwapLabels();
        }
    }

    function testEulerSwap() public skipIf(eulerSwapPool() == address(0)) setEulerSwapBlock {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) =
            _getDefaultFromPermit2(eulerSwapAmount());

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(ISettlerActions.EULERSWAP, (FROM, address(fromToken()), 10_000, eulerSwapPool(), true, 0))
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)),
            buyToken: IERC20(address(0)),
            minAmountOut: 0
        });
        Settler _settler = settler;
        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStartName("settler_eulerSwap");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + eulerSwapAmount(), beforeBalanceFrom);
    }
}
