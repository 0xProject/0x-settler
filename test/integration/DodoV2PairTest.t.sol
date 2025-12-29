// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {BasePairTest} from "./BasePairTest.t.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {MainnetSettler as Settler} from "src/chains/Mainnet/TakerSubmitted.sol";
import {Shim} from "./SettlerBasePairTest.t.sol";

import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";

contract DodoV2PairTest is BasePairTest {
    function _testName() internal pure override returns (string memory) {
        return "USDT-DAI";
    }

    Settler internal settler;
    IAllowanceHolder internal allowanceHolder;
    uint256 private _amount;

    function setUp() public override {
        super.setUp();
        // the pool specified below doesn't have very much liquidity, so we only swap a small amount
        IERC20 sellToken = IERC20(address(fromToken()));
        _amount = 10 ** sellToken.decimals() * 100;
        if (address(fromToken()).code.length != 0) {
            deal(address(fromToken()), FROM, _amount);
            deal(address(fromToken()), MAKER, 1);
            deal(address(fromToken()), BURN_ADDRESS, 1);
        }
        if (address(toToken()).code.length != 0) {
            deal(address(toToken()), MAKER, _amount);
            deal(address(toToken()), BURN_ADDRESS, 1);
        }
        safeApproveIfBelow(fromToken(), FROM, address(PERMIT2), amount());
        warmPermit2Nonce(FROM);

        allowanceHolder = IAllowanceHolder(0x0000000000001fF3684f28c67538d4D072C22734);

        uint256 forkChainId = (new Shim()).chainId();
        vm.chainId(31337);
        settler = new Settler(bytes20(0));
        vm.etch(address(allowanceHolder), vm.getDeployedCode("AllowanceHolder.sol:AllowanceHolder"));
        vm.chainId(forkChainId);

        // USDT is obnoxious about throwing errors, so let's check here before
        // we run into something inscrutable. Do this here to avoid incorrectly
        // warming storage.
        assertGe(fromToken().balanceOf(FROM), amount());
        assertGe(fromToken().allowance(FROM, address(PERMIT2)), amount());
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(0xdAC17F958D2ee523a2206206994597C13D831ec7); // USDT
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(0x6B175474E89094C44Da98b954EedeAC495271d0F); // DAI
    }

    function dodoV2Pool() internal pure returns (address) {
        return 0x3058EF90929cb8180174D74C507176ccA6835D73;
    }

    function amount() internal view override returns (uint256) {
        return _amount;
    }

    function testSettler_dodov2() public skipIf(dodoV2Pool() == address(0)) {
        ISignatureTransfer.PermitTransferFrom memory permit = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: address(fromToken()), amount: amount()}),
            nonce: 1,
            deadline: block.timestamp + 30 seconds
        });
        bytes memory sig = getPermitTransferSignature(permit, address(settler), FROM_PRIVATE_KEY, permit2Domain);
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(ISettlerActions.DODOV2, (FROM, address(fromToken()), 10_000, dodoV2Pool(), true, 0))
        );

        Settler _settler = settler;

        uint256 beforeBalance = balanceOf(toToken(), FROM);
        vm.startPrank(FROM, FROM);
        snapStartName("settler_dodov2");
        _settler.execute(
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0}),
            actions,
            bytes32(0)
        );
        snapEnd();
        uint256 afterBalance = toToken().balanceOf(FROM);

        assertGt(afterBalance, beforeBalance);
    }

    function testSettler_dodov2_custody() public skipIf(dodoV2Pool() == address(0)) {
        ISignatureTransfer.PermitTransferFrom memory permit = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: address(fromToken()), amount: amount()}),
            nonce: 1,
            deadline: block.timestamp + 30 seconds
        });
        bytes memory sig = getPermitTransferSignature(permit, address(settler), FROM_PRIVATE_KEY, permit2Domain);
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (dodoV2Pool(), permit, sig)),
            abi.encodeCall(ISettlerActions.DODOV2, (FROM, address(0), 0, dodoV2Pool(), true, 0))
        );

        Settler _settler = settler;

        uint256 beforeBalance = balanceOf(toToken(), FROM);
        vm.startPrank(FROM, FROM);
        snapStartName("settler_dodov2_custody");
        _settler.execute(
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0}),
            actions,
            bytes32(0)
        );
        snapEnd();
        uint256 afterBalance = toToken().balanceOf(FROM);

        assertGt(afterBalance, beforeBalance);
    }
}
