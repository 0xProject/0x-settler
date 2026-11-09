// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {SettlerBase} from "../../SettlerBase.sol";
import {Attest} from "../../core/Attest.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {UniswapV4} from "../../core/UniswapV4.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {revertUnknownForkId} from "../../core/SettlerErrors.sol";

import {
    uniswapV3ElysiumFactory,
    uniswapV3InitHash,
    uniswapV3ForkId,
    IUniswapV3Callback
} from "../../core/univ3forks/UniswapV3.sol";

import {IPoolManager} from "../../core/UniswapV4Types.sol";
import {uniswapV4ElysiumPoolManager, uniswapV4ForkId} from "../../core/univ4forks/UniswapV4.sol";
import {elysPumpV4PoolManager, elysPumpV4ForkId} from "../../core/univ4forks/ElysPumpV4.sol";
import {kleosV4PoolManager, kleosV4ForkId} from "../../core/univ4forks/KleosV4.sol";
import {boxaV4PoolManager, boxaV4ForkId} from "../../core/univ4forks/BoxaV4.sol";
import {elyxaV4PoolManager, elyxaV4ForkId} from "../../core/univ4forks/ElyxaV4.sol";
import {eleosV4PoolManager, eleosV4ForkId} from "../../core/univ4forks/EleosV4.sol";

// Solidity inheritance is stupid
import {SettlerSwapAbstract} from "../../SettlerAbstract.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";

abstract contract ElysiumMixin is FreeMemory, SettlerBase, UniswapV4 {
    constructor() {
        assert(block.chainid == _chainId() || block.chainid == 31337);
    }

    function _chainId() internal pure override returns (uint256) {
        return 99901;
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data, AllowedSlippage memory slippage)
        internal
        virtual
        override(SettlerSwapAbstract, SettlerBase)
        DANGEROUS_freeMemory
        returns (bool)
    {
        if (super._dispatch(i, action, data, slippage)) {
            return true;
        } else if (action == uint32(ISettlerActions.UNISWAPV4.selector)) {
            (
                address recipient,
                IERC20 sellToken,
                uint256 ppm,
                uint8 forkId,
                bool feeOnTransfer,
                uint256 hashMul,
                uint256 hashMod,
                bytes memory fills,
                uint256 amountOutMin
            ) = abi.decode(data, (address, IERC20, uint256, uint8, bool, uint256, uint256, bytes, uint256));

            sellToUniswapV4(recipient, sellToken, ppm, forkId, feeOnTransfer, hashMul, hashMod, fills, amountOutMin);
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
        if (forkId == uniswapV3ForkId) {
            factory = uniswapV3ElysiumFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else {
            revertUnknownForkId(forkId);
        }
    }

    function _uniV4ForkInfo(uint8 forkId) internal pure override returns (IPoolManager poolManager) {
        if (forkId == uniswapV4ForkId) {
            poolManager = uniswapV4ElysiumPoolManager;
        } else if (forkId == elysPumpV4ForkId) {
            poolManager = elysPumpV4PoolManager;
        } else if (forkId == kleosV4ForkId) {
            poolManager = kleosV4PoolManager;
        } else if (forkId == boxaV4ForkId) {
            poolManager = boxaV4PoolManager;
        } else if (forkId == elyxaV4ForkId) {
            poolManager = elyxaV4PoolManager;
        } else if (forkId == eleosV4ForkId) {
            poolManager = eleosV4PoolManager;
        } else {
            revertUnknownForkId(forkId);
        }
    }

    // I hate Solidity inheritance
    function _fallback(bytes calldata data)
        internal
        virtual
        override(Permit2PaymentAbstract, UniswapV4)
        returns (bool success, bytes memory returndata)
    {
        return super._fallback(data);
    }
}

// `Attest` is listed last so that candidate selection sits above the chain actions in the
// linearization; see `Select`.
abstract contract ElysiumCommon is ElysiumMixin, Attest {
    function _dispatch(uint256 i, uint256 action, bytes calldata data, AllowedSlippage memory slippage)
        internal
        virtual
        override(ElysiumMixin, Attest)
        returns (bool)
    {
        return super._dispatch(i, action, data, slippage);
    }

    function _fallback(bytes calldata data)
        internal
        virtual
        override(ElysiumMixin, Attest)
        returns (bool success, bytes memory returndata)
    {
        return super._fallback(data);
    }
}
