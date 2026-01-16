// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {KatanaMixin} from "./Common.sol";
import {Settler} from "../../Settler.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "../../ISettlerActions.sol";
import {FastLogic} from "../../utils/FastLogic.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {SettlerBase} from "../../SettlerBase.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";
import {AbstractContext} from "../../Context.sol";

/// @custom:security-contact security@0x.org
contract KatanaSettler is Settler, KatanaMixin {
    using FastLogic for bool;

    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    function _dispatchVIP(uint256 action, bytes calldata data) internal override DANGEROUS_freeMemory returns (bool) {
        // This does not make use of `super._dispatchVIP`. This chain's Settler is extremely
        // stripped-down and has almost no capabilities
        if (action == uint32(ISettlerActions.TRANSFER_FROM.selector)) {
            (address recipient, ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) =
                abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom, bytes));
            (ISignatureTransfer.SignatureTransferDetails memory transferDetails,) =
                _permitToTransferDetails(permit, recipient);
            _transferFrom(permit, transferDetails, sig);
        } else if (action == uint32(ISettlerActions.TRANSFER_FROM_WITH_PERMIT.selector)) {
            (address recipient, ISignatureTransfer.PermitTransferFrom memory permit, bytes memory permitData) =
                abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom, bytes));
            if (_isRestrictedTarget(permit.permitted.token).or(!_isForwarded())) {
                revertConfusedDeputy();
            }
            _dispatchPermit(permit.permitted.token, permitData);
            (ISignatureTransfer.SignatureTransferDetails memory transferDetails,) =
                _permitToTransferDetails(permit, recipient);
            _transferFrom(permit, transferDetails, new bytes(0), true);
        } else {
            return false;
        }
        return true;
    }

    // Solidity inheritance is stupid
    function _isRestrictedTarget(address target)
        internal
        view
        override(Settler, Permit2PaymentAbstract)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        override(Settler, KatanaMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender() internal view override(Settler, AbstractContext) returns (address) {
        return super._msgSender();
    }
}
