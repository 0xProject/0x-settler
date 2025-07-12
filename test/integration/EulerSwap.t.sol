// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {Settler} from "src/Settler.sol";

import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";

import {IEVC, IEulerSwap} from "src/core/EulerSwap.sol";

import {AllowanceHolderPairTest} from "./AllowanceHolderPairTest.t.sol";

IEVC constant EVC = IEVC(0x0C9a3dd6b8F28529d72d7f9cE918D493519EE383);

abstract contract EulerSwapTest is AllowanceHolderPairTest {
    using SafeTransferLib for IERC20;

    function eulerSwapPool() internal view virtual returns (address) {
        return address(0);
    }

    function eulerSwapBlock() internal view virtual returns (uint256) {
        return 0;
    }

    function eulerSwapAmount() internal view virtual returns (uint256) {
        return amount();
    }

    function reverseTestName() internal view virtual returns (string memory);

    modifier setEulerSwapBlock() {
        uint256 blockNumber = vm.getBlockNumber();
        vm.rollFork(eulerSwapBlock());
        _;
        vm.rollFork(blockNumber);
    }

    function _setEulerSwapLabels() private setEulerSwapBlock {
        vm.label(address(EVC), "EVC");
        vm.label(eulerSwapPool(), string.concat("EulerSwap ", testName(), " pool"));
        IEulerSwap.Params memory params = IEulerSwap(eulerSwapPool()).getParams();
        vm.label(params.eulerAccount, "Euler Account");
        string memory vault0UnderlyingSymbol = IERC20(params.vault0.asset()).symbol();
        string memory vault1UnderlyingSymbol = IERC20(params.vault1.asset()).symbol();
        vm.label(address(params.vault0), string.concat("Euler Vault ", vault0UnderlyingSymbol));
        vm.label(address(params.vault1), string.concat("Euler Vault ", vault1UnderlyingSymbol));
        vm.label(address(params.vault0.dToken()), string.concat("Euler dToken ", vault0UnderlyingSymbol));
        vm.label(address(params.vault1.dToken()), string.concat("Euler dToken ", vault1UnderlyingSymbol));
    }

    function setUp() public virtual override {
        super.setUp();
        if (eulerSwapPool() != address(0)) {
            vm.makePersistent(address(PERMIT2));
            vm.makePersistent(address(allowanceHolder));
            vm.makePersistent(address(settler));
            vm.makePersistent(address(fromToken()));
            vm.makePersistent(address(toToken()));
            deal(address(toToken()), FROM, eulerSwapAmount());
            vm.prank(FROM, FROM);
            toToken().safeApprove(address(PERMIT2), type(uint256).max);
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

    function testEulerSwapReverse() public skipIf(eulerSwapPool() == address(0)) setEulerSwapBlock {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) =
            _getDefaultFromPermit2(toToken(), eulerSwapAmount());

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(ISettlerActions.EULERSWAP, (FROM, address(toToken()), 10_000, eulerSwapPool(), false, 0))
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)),
            buyToken: IERC20(address(0)),
            minAmountOut: 0
        });
        Settler _settler = settler;
        uint256 beforeBalanceFrom = balanceOf(toToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(fromToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStart(string.concat("settler_eulerSwap_", reverseTestName()));
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = fromToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = toToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + eulerSwapAmount(), beforeBalanceFrom);
    }

    function testEulerSwapCustody() public skipIf(eulerSwapPool() == address(0)) setEulerSwapBlock {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) =
            _getDefaultFromPermit2(eulerSwapAmount());

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (eulerSwapPool(), permit, sig)),
            abi.encodeCall(ISettlerActions.EULERSWAP, (FROM, address(fromToken()), 0, eulerSwapPool(), true, 0))
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
        snapStartName("settler_eulerSwapCustody");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + eulerSwapAmount(), beforeBalanceFrom);
    }
}
