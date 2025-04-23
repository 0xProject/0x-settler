// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {IAllowanceTransfer} from "@permit2/interfaces/IAllowanceTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

import {
    UNIVERSAL_ROUTER,
    encodePermit2Permit,
    encodeV2Swap,
    encodeUnwrapWeth
} from "src/vendor/IUniswapUniversalRouter.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {Settler} from "src/Settler.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";

import {SettlerPairTest} from "./SettlerPairTest.t.sol";

abstract contract UniswapV2PairTest is SettlerPairTest {
    function testUniswapV2UniversalRouter() public skipIf(uniswapV2Pool() == address(0)) {
        bytes memory commands = new bytes(3);
        bytes[] memory inputs = new bytes[](3);

        IAllowanceTransfer.PermitSingle memory permit =
            defaultERC20PermitSingle(address(fromToken()), PERMIT2_FROM_NONCE);
        bytes memory signature =
            getPermitSingleSignature(permit, address(UNIVERSAL_ROUTER), FROM_PRIVATE_KEY, permit2Domain);

        (commands[0], inputs[0]) = encodePermit2Permit(fromToken(), PERMIT2_FROM_NONCE, signature);
        (commands[1], inputs[1]) =
            encodeV2Swap(address(UNIVERSAL_ROUTER), amount(), 0 wei, fromToken(), toToken(), true);
        (commands[2], inputs[2]) = encodeUnwrapWeth(FROM, 0 wei);

        (bool success,) = FROM.call(""); // touch FROM to warm it; in normal operation this would already be warmed
        require(success);

        vm.startPrank(FROM, FROM);
        snapStartName("universalRouter_uniswapV2");
        UNIVERSAL_ROUTER.execute(commands, inputs, block.timestamp);
        snapEnd();
        vm.stopPrank();
    }

    function testSettler_uniswapV2_toNative()
        public
        skipIf(uniswapV2Pool() == address(0))
        skipIf(toToken() != IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2))
    {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        Settler _settler = settler;

        bool zeroForOne = fromToken() < toToken();
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (uniswapV2Pool(), permit, sig)),
            abi.encodeCall(
                ISettlerActions.UNISWAPV2,
                (
                    address(_settler),
                    address(fromToken()),
                    0,
                    uniswapV2Pool(),
                    uint24((30 << 8) | (zeroForOne ? 1 : 0)),
                    0 wei
                )
            ),
            abi.encodeCall(
                ISettlerActions.BASIC,
                (
                    0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2,
                    10_000,
                    0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2,
                    4,
                    abi.encodeWithSignature("withdraw(uint256)", 0 wei)
                )
            )
        );
        ISettlerBase.AllowedSlippage memory slippage = ISettlerBase.AllowedSlippage({
            recipient: FROM,
            buyToken: IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE),
            minAmountOut: 0 ether
        });

        (bool success,) = FROM.call(""); // touch FROM to warm it; in normal operation this would already be warmed
        require(success);

        vm.startPrank(FROM, FROM);
        snapStartName("settler_uniswapV2_toNative");
        _settler.execute(slippage, actions, bytes32(0));
        snapEnd();
    }
}
