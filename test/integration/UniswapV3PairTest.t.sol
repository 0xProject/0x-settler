// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IAllowanceTransfer} from "@permit2/interfaces/IAllowanceTransfer.sol";

import {UNIVERSAL_ROUTER, encodePermit2Permit, encodeV3Swap, encodeUnwrapWeth} from "src/vendor/IUniswapUniversalRouter.sol";

import {BasePairTest} from "./BasePairTest.t.sol";
import {IUniswapV3Router} from "./vendor/IUniswapV3Router.sol";

abstract contract UniswapV3PairTest is BasePairTest {
    IUniswapV3Router private constant UNISWAP_ROUTER = IUniswapV3Router(0xE592427A0AEce92De3Edee1F18E0157C05861564);

    function setUp() public virtual override {
        super.setUp();
        safeApproveIfBelow(fromToken(), FROM, address(UNISWAP_ROUTER), amount());
    }

    function testBlockNumber() internal pure virtual override returns (uint256) {
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

    function testUniswapV3UniversalRouter() public {
        bytes memory commands = new bytes(3);
        bytes[] memory inputs = new bytes[](3);

        IAllowanceTransfer.PermitSingle memory permit = defaultERC20PermitSingle(address(fromToken()), PERMIT2_FROM_NONCE);
        bytes memory signature = getPermitSingleSignature(permit, address(UNIVERSAL_ROUTER), FROM_PRIVATE_KEY, permit2Domain);
        bytes memory path = uniswapV3PathCompat();

        (commands[0], inputs[0]) = encodePermit2Permit(fromToken(), PERMIT2_FROM_NONCE, signature);
        (commands[1], inputs[1]) = encodeV3Swap(address(UNIVERSAL_ROUTER), amount(), 0 wei, path, true);
        (commands[2], inputs[2]) = encodeUnwrapWeth(FROM, 0 wei);

        (bool success, ) = FROM.call(""); // touch FROM to warm it; in normal operation this would already be warmed
        require(success);

        vm.startPrank(FROM, FROM);
        snapStartName("universalRouter_uniswapV3");
        UNIVERSAL_ROUTER.execute(commands, inputs, block.timestamp);
        snapEnd();
        vm.stopPrank();
    }
}
