// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {ScrollMixin} from "./Common.sol";
import {Settler} from "../../Settler.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "../../ISettlerActions.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {SettlerBase} from "../../SettlerBase.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";
import {AbstractContext} from "../../Context.sol";
import {uint512} from "../../utils/512Math.sol";

/// @custom:security-contact security@0x.org
contract ScrollSettler is Settler, ScrollMixin {
    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    function _dispatchVIP(uint256 action, bytes calldata data) internal override DANGEROUS_freeMemory returns (bool) {
        if (super._dispatchVIP(action, data)) {
            return true;
        } else if (action == uint32(ISettlerActions.MAVERICKV2_VIP.selector)) {
            (
                address recipient,
                ISignatureTransfer.PermitTransferFrom memory permit,
                bytes32 salt,
                bool tokenAIn,
                bytes memory sig,
                int32 tickLimit,
                uint256 minBuyAmount
            ) = abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom, bytes32, bool, bytes, int32, uint256));

            sellToMaverickV2VIP(recipient, salt, tokenAIn, permit, sig, tickLimit, minBuyAmount);
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
        override(Settler, ScrollMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender() internal view override(Settler, AbstractContext) returns (address) {
        return super._msgSender();
    }

    function _div512to256(uint512 n, uint512 d)
        internal
        view
        override(ScrollMixin, SettlerBase, SettlerAbstract)
        returns (uint256)
    {
        return super._div512to256(n, d);
    }
}
