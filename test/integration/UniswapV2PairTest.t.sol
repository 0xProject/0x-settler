// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {IAllowanceTransfer} from "@permit2/interfaces/IAllowanceTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

import {
    UNIVERSAL_ROUTER,
    CONTRACT_BALANCE,
    ALREADY_PAID,
    RECIPIENT_ROUTER,
    RECIPIENT_TAKER,
    encodePermit2Permit,
    encodeV2Swap,
    encodeWrapEth,
    encodeUnwrapWeth
} from "src/vendor/IUniswapUniversalRouter.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {Settler} from "src/Settler.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";

import {SettlerPairTest} from "./SettlerPairTest.t.sol";

abstract contract UniswapV2PairTest is SettlerPairTest {
    function testUniswapV2UniversalRouterToNative()
        public
        skipIf(uniswapV2Pool() == address(0))
        skipIf(toToken() != WETH)
    {
        bytes memory commands = new bytes(3);
        bytes[] memory inputs = new bytes[](3);

        IAllowanceTransfer.PermitSingle memory permit =
            defaultERC20PermitSingle(address(fromToken()), PERMIT2_FROM_NONCE);
        bytes memory signature =
            getPermitSingleSignature(permit, address(UNIVERSAL_ROUTER), FROM_PRIVATE_KEY, permit2Domain);

        (commands[0], inputs[0]) = encodePermit2Permit(fromToken(), PERMIT2_FROM_NONCE, signature);
        (commands[1], inputs[1]) = encodeV2Swap(RECIPIENT_ROUTER, amount(), 0 wei, fromToken(), toToken(), true);
        (commands[2], inputs[2]) = encodeUnwrapWeth(RECIPIENT_TAKER, slippageLimit());

        (bool success,) = FROM.call(""); // touch FROM to warm it; in normal operation this would already be warmed
        require(success);

        vm.startPrank(FROM, FROM);
        snapStartName("universalRouter_uniswapV2");
        UNIVERSAL_ROUTER.execute(commands, inputs, block.timestamp);
        snapEnd();
        vm.stopPrank();
    }

    function testUniswapV2UniversalRouterFromNative()
        public
        skipIf(uniswapV2Pool() == address(0))
        skipIf(fromToken() != WETH)
    {
        bytes memory commands = new bytes(2);
        bytes[] memory inputs = new bytes[](2);

        (commands[0], inputs[0]) = encodeWrapEth(address(uniswapV2Pool()), CONTRACT_BALANCE);
        (commands[1], inputs[1]) =
            encodeV2Swap(RECIPIENT_TAKER, ALREADY_PAID, slippageLimit(), fromToken(), toToken(), false);

        vm.deal(FROM, amount());
        vm.startPrank(FROM, FROM);
        snapStartName("universalRouter_uniswapV2");
        UNIVERSAL_ROUTER.execute{value: amount()}(commands, inputs, block.timestamp);
        snapEnd();
        vm.stopPrank();
    }

    function testSettler_uniswapV2_toNative() public skipIf(uniswapV2Pool() == address(0)) skipIf(toToken() != WETH) {
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
                (address(WETH), 10_000, address(WETH), 4, abi.encodeWithSignature("withdraw(uint256)", 0 wei))
            )
        );
        ISettlerBase.AllowedSlippage memory slippage =
            ISettlerBase.AllowedSlippage({recipient: FROM, buyToken: ETH, minAmountOut: slippageLimit()});

        (bool success,) = FROM.call(""); // touch FROM to warm it; in normal operation this would already be warmed
        require(success);

        vm.startPrank(FROM, FROM);
        snapStartName("settler_uniswapV2_toNative");
        _settler.execute(slippage, actions, bytes32(0));
        snapEnd();
    }

    function testSettler_uniswapV2_fromNative()
        public
        skipIf(uniswapV2Pool() == address(0))
        skipIf(fromToken() != WETH)
    {
        bool zeroForOne = fromToken() < toToken();
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.BASIC,
                (address(ETH), 10_000, address(WETH), 4, bytes.concat(abi.encodeWithSignature("deposit()"), bytes32(0)))
            ),
            abi.encodeCall(
                ISettlerActions.UNISWAPV2,
                (
                    FROM,
                    address(fromToken()),
                    10_000,
                    uniswapV2Pool(),
                    uint24((30 << 8) | (zeroForOne ? 1 : 0)),
                    slippageLimit()
                )
            )
        );
        ISettlerBase.AllowedSlippage memory slippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)),
            buyToken: IERC20(address(0)),
            minAmountOut: 0 ether
        });

        Settler _settler = settler;
        vm.deal(FROM, amount());

        vm.startPrank(FROM, FROM);
        snapStartName("settler_uniswapV2_fromNative");
        _settler.execute{value: amount()}(slippage, actions, bytes32(0));
        snapEnd();
    }
}
