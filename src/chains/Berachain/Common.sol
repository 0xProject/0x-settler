// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {SettlerBase} from "../../SettlerBase.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {UnknownForkId} from "../../core/SettlerErrors.sol";

import {kodiakV3Factory, kodiakV3InitHash, kodiakV3ForkId} from "../../core/univ3forks/KodiakV3.sol";
import {IUniswapV3Callback} from "../../core/univ3forks/UniswapV3.sol";
import {bullaFactory, bullaForkId} from "../../core/univ3forks/Bulla.sol";
import {algebraV4InitHash, IAlgebraCallback} from "../../core/univ3forks/Algebra.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";

abstract contract BerachainMixin is FreeMemory, SettlerBase {
    constructor() {
        assert(block.chainid == 80094 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        virtual
        override(/*SettlerAbstract, */SettlerBase)
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
        if (forkId == kodiakV3ForkId) {
            factory = kodiakV3Factory;
            initHash = kodiakV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == bullaForkId) {
            factory = bullaFactory;
            initHash = algebraV4InitHash;
            callbackSelector = uint32(IAlgebraCallback.algebraSwapCallback.selector);
        } else {
            revert UnknownForkId(forkId);
        }
    }
}
