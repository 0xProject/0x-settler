// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerAbstract} from "./SettlerAbstract.sol";
import {SettlerBase} from "./SettlerBase.sol";
import {SettlerMetaTxnBase} from "./SettlerMetaTxn.sol";

import {Permit2PaymentAbstract} from "./core/Permit2PaymentAbstract.sol";
import {Permit2PaymentIntent, Permit2PaymentMetaTxn, Permit2Payment} from "./core/Permit2Payment.sol";

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

import {Panic} from "./utils/Panic.sol";

library ArraySliceBecauseSolidityIsDumb {
    function slice(bytes[] calldata data, uint256 stop_) internal pure returns (bytes[] calldata rData) {
        if (stop_ > data.length) {
            Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
        }
        assembly ("memory-safe") {
            rData.offset := data.offset
            rData.length := stop_
        }
    }
}

abstract contract SettlerIntent is Permit2PaymentIntent, SettlerMetaTxnBase {
    using ArraySliceBecauseSolidityIsDumb for bytes[];

    function _tokenId() internal pure override returns (uint256) {
        return 4;
    }

    function executeMetaTxn(
        AllowedSlippage calldata slippage,
        bytes[] calldata actions,
        bytes32, /* zid & affiliate */
        address msgSender,
        bytes calldata sig,
        uint256 prefixLen
    )
        external
        metaTx(msgSender, _hashSlippageAnd(SLIPPAGE_AND_CONDITION_TYPEHASH, actions.slice(prefixLen), slippage))
        returns (bool)
    {
        return _executeMetaTxn(slippage, actions, sig, prefixLen);
    }

    // Solidity inheritance is stupid
    function _witnessTypeSuffix()
        internal
        pure
        virtual
        override(Permit2PaymentMetaTxn, Permit2PaymentIntent)
        returns (string memory)
    {
        return super._witnessTypeSuffix();
    }
}
