// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {AvalancheSettlerMetaTxn} from "./MetaTxn.sol";
import {SettlerIntent} from "../../SettlerIntent.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "../../ISettlerActions.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {SettlerBase} from "../../SettlerBase.sol";
import {SettlerMetaTxn} from "../../SettlerMetaTxn.sol";
import {SettlerIntent} from "../../SettlerIntent.sol";
import {AbstractContext} from "../../Context.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";
import {Permit2PaymentMetaTxn} from "../../core/Permit2Payment.sol";

/// @custom:security-contact security@0x.org
contract AvalancheSettlerIntent is SettlerIntent, AvalancheSettlerMetaTxn {
    constructor(bytes20 gitCommit) AvalancheSettlerMetaTxn(gitCommit) {}

    // Solidity inheritance is stupid
    function executeMetaTxn(
        AllowedSlippage calldata slippage,
        bytes[] calldata actions,
        bytes32, /* zid & affiliate */
        address msgSender,
        bytes calldata sig
    ) public override(SettlerIntent, SettlerMetaTxn) returns (bool) {
        return super.executeMetaTxn(slippage, actions, bytes32(0), msgSender, sig);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        override(AvalancheSettlerMetaTxn, SettlerBase, SettlerAbstract)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender() internal view override(SettlerIntent, AvalancheSettlerMetaTxn) returns (address) {
        return super._msgSender();
    }

    function _witnessTypeSuffix()
        internal
        pure
        override(SettlerIntent, Permit2PaymentMetaTxn)
        returns (string memory)
    {
        return super._witnessTypeSuffix();
    }

    function _mandatorySlippageCheck() internal pure override(SettlerBase, SettlerIntent) returns (bool) {
        return super._mandatorySlippageCheck();
    }

    function _tokenId() internal pure override(SettlerIntent, SettlerMetaTxn, SettlerAbstract) returns (uint256) {
        return super._tokenId();
    }

    function _dispatchVIP(uint256 action, bytes calldata data, bytes calldata sig)
        internal
        override(AvalancheSettlerMetaTxn, SettlerMetaTxn)
        returns (bool)
    {
        return super._dispatchVIP(action, data, sig);
    }

    function _permitToSellAmount(ISignatureTransfer.PermitTransferFrom memory permit)
        internal
        pure
        override(SettlerIntent, Permit2PaymentAbstract, Permit2PaymentMetaTxn)
        returns (uint256)
    {
        return super._permitToSellAmount(permit);
    }
}
