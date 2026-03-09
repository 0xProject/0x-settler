// SPDX-License-Identifier: MIT
pragma solidity =0.8.33;

import {ScrollMixin} from "./Common.sol";
import {SettlerMetaTxn} from "../../SettlerMetaTxn.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "../../ISettlerActions.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {SettlerBase} from "../../SettlerBase.sol";
import {AbstractContext} from "../../Context.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";
import {Permit2PaymentBase} from "../../core/Permit2Payment.sol";
import {uint512} from "../../utils/512Math.sol";

/// @custom:security-contact security@0x.org
contract ScrollSettlerMetaTxn is SettlerMetaTxn, ScrollMixin {
    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    function _dispatchVIP(uint256 action, bytes calldata data, bytes calldata sig)
        internal
        virtual
        override
        DANGEROUS_freeMemory
        returns (bool)
    {
        if (super._dispatchVIP(action, data, sig)) {
            return true;
        } else if (action == uint32(ISettlerActions.METATXN_MAVERICKV2_VIP.selector)) {
            (
                address recipient,
                ISignatureTransfer.PermitTransferFrom memory permit,
                bytes32 salt,
                bool tokenAIn,
                int32 tickLimit,
                uint256 minBuyAmount
            ) = abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom, bytes32, bool, int32, uint256));

            sellToMaverickV2VIP(recipient, salt, tokenAIn, permit, sig, tickLimit, minBuyAmount);
        } else {
            return false;
        }
        return true;
    }

    // Solidity inheritance is stupid
    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        virtual
        override(SettlerAbstract, SettlerBase, ScrollMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _isRestrictedTarget(address target)
        internal
        view
        virtual
        override(SettlerMetaTxn, Permit2PaymentAbstract)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    function _msgSender() internal view virtual override(SettlerMetaTxn, AbstractContext) returns (address) {
        return super._msgSender();
    }

    function _div512to256(uint512 n, uint512 d)
        internal
        view
        virtual
        override(ScrollMixin, SettlerBase, SettlerAbstract)
        returns (uint256)
    {
        return super._div512to256(n, d);
    }
}
