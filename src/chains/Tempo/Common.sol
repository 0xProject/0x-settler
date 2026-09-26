// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {SettlerBase} from "../../SettlerBase.sol";
import {BlockTempoSystemContracts} from "./BlockTempoSystemContracts.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";

import {UniswapV4} from "../../core/UniswapV4.sol";
import {IPoolManager} from "../../core/UniswapV4Types.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {revertUnknownForkId, ReceivePolicyBlocked} from "../../core/SettlerErrors.sol";

import {
    uniswapV3TempoFactory,
    uniswapV3InitHash,
    uniswapV3ForkId,
    IUniswapV3Callback
} from "../../core/univ3forks/UniswapV3.sol";

import {TEMPO_POOL_MANAGER} from "../../core/UniswapV4Addresses.sol";

// Solidity inheritance is stupid
import {SettlerBase} from "../../SettlerBase.sol";
import {SettlerSwapAbstract} from "../../SettlerAbstract.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";

interface ITempoAddressRegistry {
    function resolveRecipient(address to) external view returns (address);
}

interface ITempoReceivePolicy {
    function validateReceivePolicy(address token, address sender, address receiver)
        external
        view
        returns (bool authorized, uint8 blockedReason);
}

abstract contract TempoMixin is FreeMemory, SettlerBase, BlockTempoSystemContracts, UniswapV4 {
    address internal constant _TEMPO_ADDRESS_REGISTRY = 0xfDC0000000000000000000000000000000000000;

    constructor() {
        assert(block.chainid == 4217 || block.chainid == 31337);
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
                bool feeOnTransfer,
                uint256 hashMul,
                uint256 hashMod,
                bytes memory fills,
                uint256 amountOutMin
            ) = abi.decode(data, (address, IERC20, uint256, bool, uint256, uint256, bytes, uint256));

            sellToUniswapV4(recipient, sellToken, ppm, feeOnTransfer, hashMul, hashMod, fills, amountOutMin);
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
            factory = uniswapV3TempoFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else {
            revertUnknownForkId(forkId);
        }
    }

    function _POOL_MANAGER() internal pure override returns (IPoolManager) {
        return TEMPO_POOL_MANAGER;
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

    function _isRestrictedTarget(address target)
        internal
        view
        virtual
        override(Permit2PaymentAbstract, BlockTempoSystemContracts)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    // A recipient's TIP-1028 receive policy would send a TIP-20 payout to the ReceivePolicyGuard
    // rather than the recipient. Revert instead.
    function _transferBuyToken(IERC20 buyToken, address recipient, uint256 amountOut)
        internal
        virtual
        override(SettlerSwapAbstract, SettlerBase)
    {
        if (uint160(address(buyToken)) >> 64 == 0x20c000000000000000000000) {
            address resolved = ITempoAddressRegistry(_TEMPO_ADDRESS_REGISTRY).resolveRecipient(recipient);
            (bool authorized,) = ITempoReceivePolicy(_TEMPO_TIP403_REGISTRY)
                .validateReceivePolicy(address(buyToken), address(this), resolved);
            if (!authorized) revert ReceivePolicyBlocked(recipient);
        }
        super._transferBuyToken(buyToken, recipient, amountOut);
    }
}
