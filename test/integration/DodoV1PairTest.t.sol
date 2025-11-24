// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {Settler} from "src/Settler.sol";

abstract contract DodoV1PairTest is SettlerBasePairTest {
    function dodoV1Pool() internal virtual returns (address) {
        return address(0);
    }

    function dodoV1Direction() internal virtual returns (bool) {
        return false;
    }

    function testSettler_dodoV1() public skipIf(dodoV1Pool() == address(0)) {
        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(ISettlerActions.DODOV1, (address(fromToken()), 10_000, dodoV1Pool(), dodoV1Direction(), 0))
        );
        Settler _settler = settler;
        uint256 beforeBalance = balanceOf(toToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStartName("settler_dodoV1");
        _settler.execute(
            ISettlerBase.AllowedSlippage({recipient: FROM, buyToken: toToken(), minAmountOut: 1 wei}),
            actions,
            bytes32(0)
        );
        snapEnd();

        assertGt(toToken().balanceOf(FROM), beforeBalance);
    }
}
