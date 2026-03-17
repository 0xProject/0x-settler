// SPDX-License-Identifier: MIT
pragma solidity =0.8.33;

import {SettlerBase} from "../../SettlerBase.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";
import {SafeTransferLib} from "../../vendor/SafeTransferLib.sol";
import {Ternary} from "../../utils/Ternary.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {revertUnknownForkId} from "../../core/SettlerErrors.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";

abstract contract TempoMixin is FreeMemory, SettlerBase {
    using Ternary for bool;
    using SafeTransferLib for IERC20;
    using SafeTransferLib for address payable;

    constructor() {
        assert(block.chainid == 4217 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        virtual
        override(/* SettlerAbstract, */ SettlerBase)
        DANGEROUS_freeMemory
        returns (bool)
    {
        // This does not make use of `super._dispatch`. This chain's Settler is extremely
        // stripped-down and has almost no capabilities
        if (action == uint32(ISettlerActions.BASIC.selector)) {
            (IERC20 sellToken, uint256 bps, address pool, uint256 offset, bytes memory _data) =
                abi.decode(data, (IERC20, uint256, address, uint256, bytes));

            basicSellToPool(sellToken, bps, pool, offset, _data);
        } else if (action == uint32(ISettlerActions.POSITIVE_SLIPPAGE.selector)) {
            (address payable recipient, IERC20 token, uint256 expectedAmount, uint256 maxBps) =
                abi.decode(data, (address, IERC20, uint256, uint256));
            bool isETH = (token == ETH_ADDRESS);
            uint256 balance = isETH ? address(this).balance : token.fastBalanceOf(address(this));
            if (balance > expectedAmount) {
                uint256 cap;
                unchecked {
                    cap = balance * maxBps / BASIS;
                    balance -= expectedAmount;
                }
                balance = (balance > cap).ternary(cap, balance);
                if (isETH) {
                    recipient.safeTransferETH(balance);
                } else {
                    token.safeTransfer(recipient, balance);
                }
            }
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

    // I hate Solidity inheritance
    function _fallback(bytes calldata data)
        internal
        virtual
        override(Permit2PaymentAbstract)
        returns (bool success, bytes memory returndata)
    {
        return super._fallback(data);
    }
}
