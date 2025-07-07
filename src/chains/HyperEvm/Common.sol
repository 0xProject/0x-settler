// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {SettlerBase} from "../../SettlerBase.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {revertUnknownForkId} from "../../core/SettlerErrors.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";

abstract contract HyperEvmMixin is FreeMemory, SettlerBase {
    constructor() {
        assert(block.chainid == 11155111 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        virtual
        override(/* SettlerAbstract, */ SettlerBase)
        DANGEROUS_freeMemory
        returns (bool)
    {
        if (super._dispatch(i, action, data)) {
            return true;
        } else {
            return false;
        }
        return true;
    }

    function _uniV3ForkInfo(uint8 forkId)
        internal
        pure
        override
        returns (address factory, bytes32 initHash, uint32 callbackSelector)
    {
        revertUnknownForkId(forkId);
    }
}
