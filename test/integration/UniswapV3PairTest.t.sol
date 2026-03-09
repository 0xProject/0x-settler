// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {IAllowanceTransfer} from "@permit2/interfaces/IAllowanceTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

import {
    UNIVERSAL_ROUTER,
    CONTRACT_BALANCE,
    RECIPIENT_ROUTER,
    RECIPIENT_TAKER,
    encodePermit2Permit,
    encodeV3Swap,
    encodeWrapEth,
    encodeUnwrapWeth
} from "src/vendor/IUniswapUniversalRouter.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {Settler} from "src/Settler.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";

import {SettlerPairTest} from "./SettlerPairTest.t.sol";
import {IUniswapV3Router} from "./vendor/IUniswapV3Router.sol";

abstract contract UniswapV3PairTest is SettlerPairTest {
    IUniswapV3Router private constant UNISWAP_ROUTER = IUniswapV3Router(0xE592427A0AEce92De3Edee1F18E0157C05861564);

    function setUp() public virtual override {
        super.setUp();
        safeApproveIfBelow(fromToken(), FROM, address(UNISWAP_ROUTER), amount());
    }

    function _testBlockNumber() internal pure virtual override returns (uint256) {
        return 22333955;
    }

    function uniswapV3PathCompat() internal view virtual returns (bytes memory);

    function testUniswapRouter() public {
        vm.startPrank(FROM);
        snapStartName("uniswapRouter_uniswapV3");
        UNISWAP_ROUTER.exactInput(
            IUniswapV3Router.ExactInputParams({
                path: uniswapV3PathCompat(),
                recipient: FROM,
                deadline: block.timestamp + 1,
                amountIn: amount(),
                amountOutMinimum: 1
            })
        );
        snapEnd();
    }

    function testUniswapV3UniversalRouterToNative()
        public
        skipIf(uniswapV3PathCompat().length == 0)
        skipIf(toToken() != WETH)
    {
        bytes memory commands = new bytes(3);
        bytes[] memory inputs = new bytes[](3);

        IAllowanceTransfer.PermitSingle memory permit =
            defaultERC20PermitSingle(address(fromToken()), PERMIT2_FROM_NONCE);
        bytes memory signature =
            getPermitSingleSignature(permit, address(UNIVERSAL_ROUTER), FROM_PRIVATE_KEY, permit2Domain);
        bytes memory path = uniswapV3PathCompat();

        (commands[0], inputs[0]) = encodePermit2Permit(fromToken(), PERMIT2_FROM_NONCE, signature);
        (commands[1], inputs[1]) = encodeV3Swap(RECIPIENT_ROUTER, amount(), 0 wei, path, true);
        (commands[2], inputs[2]) = encodeUnwrapWeth(RECIPIENT_TAKER, slippageLimit());

        (bool success,) = FROM.call(""); // touch FROM to warm it; in normal operation this would already be warmed
        require(success);

        vm.startPrank(FROM, FROM);
        snapStartName("universalRouter_uniswapV3");
        UNIVERSAL_ROUTER.execute(commands, inputs, block.timestamp);
        snapEnd();
        vm.stopPrank();
    }

    function testUniswapV3UniversalRouterFromNative()
        public
        skipIf(uniswapV3PathCompat().length == 0)
        skipIf(fromToken() != WETH)
    {
        bytes memory commands = new bytes(2);
        bytes[] memory inputs = new bytes[](2);

        bytes memory path = uniswapV3PathCompat();

        (commands[0], inputs[0]) = encodeWrapEth(RECIPIENT_ROUTER, CONTRACT_BALANCE);
        (commands[1], inputs[1]) = encodeV3Swap(RECIPIENT_TAKER, CONTRACT_BALANCE, slippageLimit(), path, false);

        vm.deal(FROM, amount());

        vm.startPrank(FROM, FROM);
        snapStartName("universalRouter_uniswapV3");
        UNIVERSAL_ROUTER.execute{value: amount()}(commands, inputs, block.timestamp);
        snapEnd();
        vm.stopPrank();
    }

    function testSettler_uniswapV3VIP_toNative() public skipIf(uniswapV3Path().length == 0) skipIf(toToken() != WETH) {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        Settler _settler = settler;

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.UNISWAPV3_VIP, (address(_settler), permit, uniswapV3Path(), sig, 0 wei)),
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
        snapStartName("settler_uniswapV3VIP_toNative");
        _settler.execute(slippage, actions, bytes32(0));
        snapEnd();
    }

    function testSettler_uniswapV3_fromNative()
        public
        skipIf(uniswapV3Path().length == 0)
        skipIf(fromToken() != WETH)
    {
        Settler _settler = settler;

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.BASIC,
                (address(ETH), 10_000, address(WETH), 4, abi.encodeWithSignature("deposit()", 0 wei))
            ),
            abi.encodeCall(ISettlerActions.UNISWAPV3, (FROM, 10_000, uniswapV3Path(), slippageLimit()))
        );
        ISettlerBase.AllowedSlippage memory slippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)),
            buyToken: IERC20(address(0)),
            minAmountOut: 0 ether
        });

        vm.deal(FROM, amount());
        vm.startPrank(FROM, FROM);
        snapStartName("settler_uniswapV3_fromNative");
        _settler.execute{value: amount()}(slippage, actions, bytes32(0));
        snapEnd();
    }
}
