// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IAllowanceTransfer} from "@permit2/interfaces/IAllowanceTransfer.sol";

import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";
import {UNIVERSAL_ROUTER, encodePermit2Permit, encodeV3Swap} from "src/vendor/IUniswapUniversalRouter.sol";

import {BasePairTest} from "./BasePairTest.t.sol";
import {IUniswapV3Router} from "./vendor/IUniswapV3Router.sol";

abstract contract UniswapV3PairTest is BasePairTest {
    using SafeTransferLib for IERC20;

    IUniswapV3Router private constant UNISWAP_ROUTER = IUniswapV3Router(0xE592427A0AEce92De3Edee1F18E0157C05861564);

    function setUp() public virtual override {
        super.setUp();
        safeApproveIfBelow(fromToken(), FROM, address(UNISWAP_ROUTER), amount());
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

    function testUniversalRouter() public {
        bytes memory commands = new bytes(2);
        bytes[] memory inputs = new bytes[](2);

        IAllowanceTransfer.PermitSingle memory permit = defaultERC20PermitSingle(address(fromToken()), PERMIT2_FROM_NONCE);
        bytes memory signature = getPermitSingleSignature(permit, address(UNIVERSAL_ROUTER), FROM_PRIVATE_KEY, permit2Domain);
        bytes memory path = uniswapV3PathCompat();

        (commands[0], inputs[0]) = encodePermit2Permit(fromToken(), PERMIT2_FROM_NONCE, signature);
        (commands[1], inputs[1]) = encodeV3Swap(FROM, amount(), 0, uniswapV3PathCompat(), true);

        UNIVERSAL_ROUTER.execute(commands, inputs, block.timestamp);
    }
}
