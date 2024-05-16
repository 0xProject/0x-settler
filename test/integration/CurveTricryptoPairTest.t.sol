// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";

import {Settler} from "src/Settler.sol";
import {SettlerBase} from "src/SettlerBase.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

abstract contract CurveTricryptoPairTest is SettlerBasePairTest {
    function curveV2TricryptoPoolId() internal virtual returns (uint80) {
        return 0;
    }

    function testCurveTricrypto() public skipIf(curveV2TricryptoPoolId() == 0) {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.CURVE_TRICRYPTO_VIP, (FROM, curveV2TricryptoPoolId(), permit, sig, 0))
        );
        SettlerBase.AllowedSlippage memory allowedSlippage =
            SettlerBase.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0});
        Settler _settler = settler;
        vm.startPrank(FROM, FROM);
        snapStartName("settler_curveTricrypto");
        _settler.execute(actions, allowedSlippage);
        snapEnd();
    }
}
