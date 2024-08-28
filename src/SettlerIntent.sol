// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerAbstract} from "./SettlerAbstract.sol";
import {SettlerBase} from "./SettlerBase.sol";
import {SettlerMetaTxn} from "./SettlerMetaTxn.sol";

import {Permit2PaymentIntent, Permit2PaymentMetaTxn} from "./core/Permit2Payment.sol";

abstract contract SettlerIntent is Permit2PaymentIntent, SettlerMetaTxn {
    function _tokenId() internal pure virtual override(SettlerAbstract, SettlerMetaTxn) returns (uint256) {
        return 4;
    }

    function _msgSender()
        internal
        view
        virtual
        // Solidity inheritance is so stupid
        override(Permit2PaymentMetaTxn, SettlerMetaTxn)
        returns (address)
    {
        return super._msgSender();
    }

    // Solidity inheritance is so stupid
    function _witnessTypeSuffix() internal pure virtual override(Permit2PaymentMetaTxn, Permit2PaymentIntent)  returns (string memory) {
        return super._witnessTypeSuffix();
    }

    function _hashSlippage(AllowedSlippage calldata slippage)
        internal
        pure
        returns (bytes32 result)
    {
        // This function does not check for or clean any dirty bits that might
        // exist in `slippage`. We assume that `slippage` will be used elsewhere
        // in this context and that if there are dirty bits it will result in a
        // revert later.
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, SLIPPAGE_TYPEHASH)
            calldatacopy(add(ptr, 0x20), slippage, 0x60)
            result := keccak256(ptr, 0x80)
        }
    }

    function _executeMetaTxn(
        AllowedSlippage calldata slippage,
        bytes[] calldata actions,
        bytes32, /* zid & affiliate */
        address msgSender,
        bytes calldata sig
    ) public virtual metaTx(msgSender, _hashSlippage(slippage)) returns (bool) {
        return _executeMetaTxn(slippage, actions, sig);
    }
}
