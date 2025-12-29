// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {BasePairTest} from "./BasePairTest.t.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {BaseSettler as Settler} from "src/chains/Base/TakerSubmitted.sol";
import {Shim} from "./SettlerBasePairTest.t.sol";

import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";

contract VelodromePairTest is BasePairTest {
    function _testName() internal pure override returns (string memory) {
        return "USDT-USDC";
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
        return IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48); // USDC
    }

    function velodromePool() internal pure returns (address) {
        return 0x63A65a174Cc725824188940255aD41c371F28F28; // actually solidlyv2 (velodrome does not exist on mainnet)
    }

    function amount() internal view override returns (uint256) {
        return _amount;
    }

    function testSettler_velodrome() public skipIf(velodromePool() == address(0)) {
        ISignatureTransfer.PermitTransferFrom memory permit = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: address(fromToken()), amount: amount()}),
            nonce: 1,
            deadline: block.timestamp + 30 seconds
        });
        bytes memory sig = getPermitTransferSignature(permit, address(settler), FROM_PRIVATE_KEY, permit2Domain);
        uint24 swapInfo = (2 << 8) | (0 << 1) | (0);
        // fees = 2 bp; internally, solidly uses ppm
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (velodromePool(), permit, sig)),
            abi.encodeCall(ISettlerActions.VELODROME, (FROM, 0, velodromePool(), swapInfo, 0))
        );

        Settler _settler = settler;

        uint256 beforeBalance = balanceOf(toToken(), FROM);
        vm.startPrank(FROM, FROM);
        snapStartName("settler_velodrome");
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
