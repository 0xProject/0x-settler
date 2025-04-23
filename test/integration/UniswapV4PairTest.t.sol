// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IAllowanceTransfer} from "@permit2/interfaces/IAllowanceTransfer.sol";

import {UNIVERSAL_ROUTER, encodePermit2Permit, encodeV4Swap} from "src/vendor/IUniswapUniversalRouter.sol";

import {BasePairTest} from "./BasePairTest.t.sol";

abstract contract UniswapV4PairTest is BasePairTest {
    function testUniswapV4UniversalRouter() public {
        bytes memory commands = new bytes(2);
        bytes[] memory inputs = new bytes[](2);

        IAllowanceTransfer.PermitSingle memory permit = defaultERC20PermitSingle(address(fromToken()), PERMIT2_FROM_NONCE);
        bytes memory signature = getPermitSingleSignature(permit, address(UNIVERSAL_ROUTER), FROM_PRIVATE_KEY, permit2Domain);

        (commands[0], inputs[0]) = encodePermit2Permit(fromToken(), PERMIT2_FROM_NONCE, signature);
        IERC20 toTokenCompat = toToken();
        if (toTokenCompat == IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2)) {
            toTokenCompat = IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);
        }
        IERC20 fromTokenCompat = fromToken();
        if (fromTokenCompat == IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2)) {
            fromTokenCompat = IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);
        }
        (commands[1], inputs[1]) = encodeV4Swap(FROM, amount(), 0 wei, fromTokenCompat, 500, 10, address(0), toTokenCompat);

        (bool success, ) = FROM.call(""); // touch FROM to warm it; in normal operation this would already be warmed
        require(success);

        vm.startPrank(FROM, FROM);
        snapStartName("universalRouter_uniswapV4");
        UNIVERSAL_ROUTER.execute(commands, inputs, block.timestamp);
        snapEnd();
        vm.stopPrank();
    }
}
