// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IAllowanceTransfer} from "@permit2/interfaces/IAllowanceTransfer.sol";

import {UNIVERSAL_ROUTER, encodePermit2Permit, encodeV4Swap} from "src/vendor/IUniswapUniversalRouter.sol";

import {BasePairTest} from "./BasePairTest.t.sol";

abstract contract UniswapV4PairTest is BasePairTest {
    function testUniswapV4UniversalRouter() public {
        bytes memory commands = new bytes(3);
        bytes[] memory inputs = new bytes[](3);

        IAllowanceTransfer.PermitSingle memory permit = defaultERC20PermitSingle(address(fromToken()), PERMIT2_FROM_NONCE);
        bytes memory signature = getPermitSingleSignature(permit, address(UNIVERSAL_ROUTER), FROM_PRIVATE_KEY, permit2Domain);

        (commands[0], inputs[0]) = encodePermit2Permit(fromToken(), PERMIT2_FROM_NONCE, signature);
        (commands[1], inputs[1]) = encodeV4Swap(FROM, amount(), 0 wei, fromToken(), 500, 10, address(0), toToken());

        vm.startPrank(FROM, FROM);
        snapStartName("universalRouter_uniswapV4");
        UNIVERSAL_ROUTER.execute(commands, inputs, block.timestamp);
        snapEnd();
        vm.stopPrank();
    }
}
