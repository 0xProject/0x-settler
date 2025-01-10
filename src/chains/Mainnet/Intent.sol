// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {SettlerIntent} from "../../SettlerIntent.sol";
import {MainnetSettlerMetaTxnBase} from "./MetaTxn.sol";

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {SettlerBase} from "../../SettlerBase.sol";
import {SettlerMetaTxnBase} from "../../SettlerMetaTxn.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";
import {Permit2PaymentMetaTxn} from "../../core/Permit2Payment.sol";

/// @custom:security-contact security@0x.org
contract MainnetSettlerIntent is SettlerIntent, MainnetSettlerMetaTxnBase {
    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    // Solidity inheritance is stupid
    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        override(MainnetSettlerMetaTxnBase, SettlerBase, SettlerAbstract)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender() internal view override(SettlerIntent, MainnetSettlerMetaTxnBase) returns (address) {
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

    function _tokenId() internal pure override(SettlerIntent, SettlerAbstract) returns (uint256) {
        return super._tokenId();
    }

    function _dispatchVIP(uint256 action, bytes calldata data, bytes calldata sig)
        internal
        override(MainnetSettlerMetaTxnBase, SettlerMetaTxnBase)
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
