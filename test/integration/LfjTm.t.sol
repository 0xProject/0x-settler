// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {ILfjTmMarket} from "src/core/LfjTokenMill.sol";

import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {Settler} from "src/Settler.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";
import {MonadSettler} from "src/chains/Monad/TakerSubmitted.sol";

import {AllowanceHolderPairTest} from "./AllowanceHolderPairTest.t.sol";

abstract contract LfjTmTest is AllowanceHolderPairTest {
    function _testBlockNumber() internal pure virtual override returns (uint256) {
        return 37865992;
    }

    function _testChainId() internal pure virtual override returns (string memory) {
        return "monad";
    }

    function settlerInitCode() internal virtual override returns (bytes memory) {
        return bytes.concat(type(MonadSettler).creationCode, abi.encode(bytes20(0)));
    }

    function _setLfjTmLabels() private {
        vm.label(address(lfjTmPool()), "LfjTokenMillMarket");
    }

    function setUp() public virtual override {
        super.setUp();
        vm.makePersistent(address(allowanceHolder));
        vm.makePersistent(address(settler));
        vm.makePersistent(address(fromToken()));
        vm.makePersistent(address(toToken()));
        if (address(toToken()).code.length != 0) {
            deal(address(toToken()), FROM, amount());
        }
    }

    function lfjTmPool() internal view virtual returns (ILfjTmMarket) {
        return ILfjTmMarket(0xE14d2602E27F2dD779E427D2e33eaf450Fb1e8e0);
    }

    function lfjTmZeroForOne() internal pure virtual returns (bool) {
        return true;
    }

    function fromToken() internal view virtual override returns (IERC20) {
        return IERC20(0x012Dc9b54623C37aEDb6f1b751c568a9995926a9); // launchpad token
    }

    function toToken() internal view virtual override returns (IERC20) {
        return IERC20(0x3bd359C1119dA7Da1D913D1C4D2B7c461115433A); // WMON
    }

    function testLfjTm_zeroForOne() public skipIf(address(lfjTmPool()) == address(0)) {
        if (lfjTmZeroForOne()) {
            assertEq(address(lfjTmPool().getBaseToken()), address(fromToken()));
            assertEq(address(lfjTmPool().getQuoteToken()), address(toToken()));
        } else {
            assertEq(address(lfjTmPool().getBaseToken()), address(toToken()));
            assertEq(address(lfjTmPool().getQuoteToken()), address(fromToken()));
        }
    }

    function testLfjTm() public skipIf(address(lfjTmPool()) == address(0)) {
        uint256 _amount = amount();
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(_fromToken), _amount, 0 /* nonce */ );
        bytes memory sig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(_settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.LFJTM, (FROM, address(_fromToken), 10000, address(lfjTmPool()), lfjTmZeroForOne(), 0)
            )
        );
        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)),
            buyToken: IERC20(address(0)),
            minAmountOut: 0
        });
        IAllowanceHolder _allowanceHolder = allowanceHolder;

        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        uint256 beforeBalanceFrom = balanceOf(_fromToken, FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStartName("allowanceHolder_lfjTm");
        _allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = _fromToken.balanceOf(FROM);
        assertEq(afterBalanceFrom, beforeBalanceFrom - _amount);
    }

    function testLfjTm_custody() public skipIf(address(lfjTmPool()) == address(0)) {
        uint256 _amount = amount();
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(_fromToken), _amount, 0 /* nonce */ );
        bytes memory sig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(lfjTmPool()), permit, sig)),
            abi.encodeCall(
                ISettlerActions.LFJTM, (FROM, address(_fromToken), 0, address(lfjTmPool()), lfjTmZeroForOne(), 0)
            )
        );
        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)),
            buyToken: IERC20(address(0)),
            minAmountOut: 0
        });
        IAllowanceHolder _allowanceHolder = allowanceHolder;

        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        uint256 beforeBalanceFrom = balanceOf(_fromToken, FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStartName("allowanceHolder_lfjTm_custody");
        _allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = _fromToken.balanceOf(FROM);
        assertEq(afterBalanceFrom, beforeBalanceFrom - _amount);
    }

    function testLfjTm_reverse() public skipIf(address(lfjTmPool()) == address(0)) {
        uint256 _amount = amount();
        Settler _settler = settler;
        IERC20 _fromToken = toToken();

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(_fromToken), _amount, 0 /* nonce */ );
        bytes memory sig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(_settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.LFJTM, (FROM, address(_fromToken), 10000, address(lfjTmPool()), !lfjTmZeroForOne(), 0)
            )
        );
        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)),
            buyToken: IERC20(address(0)),
            minAmountOut: 0
        });
        IAllowanceHolder _allowanceHolder = allowanceHolder;

        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        uint256 beforeBalanceFrom = balanceOf(toToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(fromToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStartName("allowanceHolder_lfjTm_reverse");
        _allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = fromToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = toToken().balanceOf(FROM);
        assertEq(afterBalanceFrom, beforeBalanceFrom - _amount);
    }
}
