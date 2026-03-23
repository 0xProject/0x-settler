// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

import {Shim} from "./SettlerBasePairTest.t.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {MainnetSettlerMetaTxn as SettlerMetaTxn} from "src/chains/Mainnet/MetaTxn.sol";
import {Settler} from "src/Settler.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";
import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";
import {maverickV2InitHash, maverickV2Factory} from "src/core/MaverickV2.sol";

import {SettlerMetaTxnPairTest} from "./SettlerMetaTxnPairTest.t.sol";

abstract contract MaverickV2PairTest is SettlerMetaTxnPairTest {
    function setUp() public virtual override {
        super.setUp();
        if (maverickV2Salt() != bytes32(0)) {
            vm.makePersistent(address(PERMIT2));
            vm.makePersistent(address(allowanceHolder));
            vm.makePersistent(address(settler));
            vm.makePersistent(address(settlerMetaTxn));
            vm.makePersistent(address(fromToken()));
            vm.makePersistent(address(toToken()));
        }
    }

    function maverickV2BlockNumber() internal view virtual returns (uint256) {
        return 20421077;
    }

    modifier setMaverickV2Block() {
        uint256 blockNumber = (new Shim()).blockNumber();
        vm.rollFork(maverickV2BlockNumber());
        vm.setEvmVersion("osaka");
        _;
        vm.rollFork(blockNumber);
        vm.setEvmVersion("osaka");
    }

    function maverickV2Salt() internal view virtual returns (bytes32) {
        return bytes32(0);
    }

    function maverickV2Pool() internal view returns (address) {
        return AddressDerivation.deriveDeterministicContract(maverickV2Factory, maverickV2Salt(), maverickV2InitHash);
    }

    function maverickV2TokenAIn() internal view virtual returns (bool) {
        return false;
    }

    function maverickV2TickLimit() internal view virtual returns (int32) {
        return maverickV2TokenAIn() ? type(int32).max : type(int32).min;
    }

    function testMaverickV2() public skipIf(maverickV2Salt() == bytes32(0)) setMaverickV2Block {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.MAVERICKV2,
                (FROM, address(fromToken()), 10_000, maverickV2Pool(), maverickV2TokenAIn(), maverickV2TickLimit(), 0)
            )
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
        snapStartName("settler_maverickV2");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }

    function testMaverickV2Custody() public skipIf(maverickV2Salt() == bytes32(0)) setMaverickV2Block {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (maverickV2Pool(), permit, sig)),
            abi.encodeCall(
                ISettlerActions.MAVERICKV2, (FROM, address(fromToken()), 0, maverickV2Pool(), maverickV2TokenAIn(), maverickV2TickLimit(), 0)
            )
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
        snapStartName("settler_maverickV2_custody");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }
}
