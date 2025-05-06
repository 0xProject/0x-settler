// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {ScrollMixin} from "./Common.sol";
import {SettlerMetaTxn} from "../../SettlerMetaTxn.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "../../ISettlerActions.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {SettlerBase} from "../../SettlerBase.sol";
import {AbstractContext} from "../../Context.sol";
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
                bytes32 salt,
                bool tokenAIn,
                ISignatureTransfer.PermitTransferFrom memory permit,
                uint256 minBuyAmount
            ) = abi.decode(data, (address, bytes32, bool, ISignatureTransfer.PermitTransferFrom, uint256));

            sellToMaverickV2VIP(recipient, salt, tokenAIn, permit, sig, minBuyAmount);
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
