// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";

import {Settler} from "src/Settler.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

abstract contract CurveTricryptoPairTest is SettlerBasePairTest {
    function testCurveTricrypto() public {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(
            ISettlerActions.CURVE_TRICRYPTO_VIP,
            (
                FROM,
                bytes.concat(
                    bytes20(address(fromToken())),
                    bytes1(uint8(0)),
                    bytes1(uint8(0)),
                    bytes1(uint8(2)),
                    bytes20(address(toToken()))
                ),
                0,
                permit,
                sig
            )
        );
        Settler.AllowedSlippage memory allowedSlippage =
            Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0});
        Settler _settler = settler;
        vm.startPrank(FROM, FROM);
        snapStartName("settler_curveTricrypto");
        _settler.execute(actions, allowedSlippage);
        snapEnd();
    }
}
