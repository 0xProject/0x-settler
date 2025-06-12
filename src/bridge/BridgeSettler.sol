// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {BridgeSettlerBase} from "./BridgeSettlerBase.sol";
import {revertActionInvalid} from "../core/SettlerErrors.sol";
import {CalldataDecoder} from "../SettlerBase.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "../ISettlerActions.sol";
import {Permit2PaymentTakerSubmitted} from "../core/Permit2Payment.sol";

interface IBridgeSettlerTakerSubmitted {
    function execute(bytes[] calldata, bytes32)
        external
        payable
        returns (bool);
}

abstract contract BridgeSettler is IBridgeSettlerTakerSubmitted, Permit2PaymentTakerSubmitted, BridgeSettlerBase {
    using CalldataDecoder for bytes[];
    using UnsafeMath for uint256;

    function _tokenId() internal pure override returns (uint256) {
        return 5;
    }

    function _dispatchVIP(uint256 action, bytes calldata data) internal virtual returns (bool) {
        if (action == uint32(ISettlerActions.TRANSFER_FROM.selector)) {
            (address recipient, ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) =
                abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom, bytes));
            (ISignatureTransfer.SignatureTransferDetails memory transferDetails,) =
                _permitToTransferDetails(permit, recipient);
            _transferFrom(permit, transferDetails, sig);
        }
        else {
            return false;
        }
        return true;
    }

    function execute(bytes[] calldata actions, bytes32 /* zid & affiliate */ )
        public
        payable
        override
        takerSubmitted
        returns (bool)
    {

        if (actions.length != 0) {
            (uint256 action, bytes calldata data) = actions.decodeCall(0);
            if (!_dispatchVIP(action, data)) {
                if (!_dispatch(0, action, data)) {
                    revertActionInvalid(0, action, data);
                }
            }
        }

        for (uint256 i = 1; i < actions.length; i = i.unsafeInc()) {
            (uint256 action, bytes calldata data) = actions.decodeCall(i);
            if (!_dispatch(i, action, data)) {
                revertActionInvalid(i, action, data);
            }
        }

        return true;
    }

    function _hasMetaTxn() internal pure virtual override returns (bool) {
        return false;
    }
}