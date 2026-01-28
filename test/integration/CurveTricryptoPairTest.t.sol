// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";

import {Settler} from "src/Settler.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

abstract contract CurveTricryptoPairTest is SettlerBasePairTest {
    function curveV2TricryptoPoolId() internal virtual returns (uint80) {
        return 0;
    }

    function testCurveTricrypto() public skipIf(curveV2TricryptoPoolId() == 0) {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.CURVE_TRICRYPTO_VIP, (FROM, permit, curveV2TricryptoPoolId(), sig, 0))
        );
        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)),
            buyToken: IERC20(address(0)),
            minAmountOut: 0
        });
        Settler _settler = settler;
        vm.startPrank(FROM, FROM);
        snapStartName("settler_curveTricrypto");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
    }
}
