// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {ISettlerActions} from "../ISettlerActions.sol";

import {FastLogic} from "../utils/FastLogic.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {FullMath} from "../vendor/FullMath.sol";
import {Ternary} from "../utils/Ternary.sol";

import {revertTooMuchSlippage} from "./SettlerErrors.sol";

import {SettlerAbstract} from "../SettlerAbstract.sol";

interface IBebopSettlement {
    event BebopOrder(uint128 indexed eventId);

    /// @notice Struct for one-to-one trade with one maker
    struct Single {
        uint256 expiry;
        address taker_address;
        address maker_address;
        uint256 maker_nonce;
        IERC20 taker_token;
        IERC20 maker_token;
        uint256 taker_amount;
        uint256 maker_amount;
        address payable receiver;
        uint256 packed_commands;
        uint256 flags; // `hashSingleOrder` doesn't use this field for SingleOrder hash
    }

    /// @notice Taker execution of one-to-one trade with one maker
    /// @param order Single order struct
    /// @param makerSignature Maker's signature for SingleOrder
    /// @param filledTakerAmount Partially filled taker amount, 0 for full fill
    function swapSingle(Single calldata order, ISettlerActions.BebopMakerSignature calldata makerSignature, uint256 filledTakerAmount)
        external
        payable;
}

library FastBebop {
    function fastSwapSingle(
        IBebopSettlement bebop,
        address payable recipient,
        address taker,
        IERC20 sellToken,
        ISettlerActions.BebopOrder memory order,
        ISettlerActions.BebopMakerSignature memory makerSignature,
        uint256 filledTakerAmount
    ) internal {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, 0x4dcebcba)                                                             // IBebopSettlement.swapSingle.selector
            mstore(add(0x20, ptr), mload(order))                                                // expiry
            mstore(add(0x40, ptr), address())                                                   // taker_address
            mcopy(add(0x60, ptr), add(0x20, order), 0x40)                                       // maker_address; maker_nonce
            mstore(add(0xa0, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, sellToken))  // taker_token
            mcopy(add(0xc0, ptr), add(0x60, order), 0x60)                                       // maker_token, taker_amount, maker_amount
            mstore(add(0x120, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, recipient)) // receiver

            let event_id_and_flags := mload(add(0xc0, order))
            mstore(add(0x140, ptr), or(shl(0x60, taker), shr(0xf8, event_id_and_flags)))        // packed_commands
            mstore(add(0x160, ptr), shl(0x80, event_id_and_flags))                              // flags

            mstore(add(0x180, ptr), 0x1a0)                                                      // makerSignature.offset
            mstore(add(0x1a0, ptr), filledTakerAmount)
            mstore(add(0x1c0, ptr), 0x40)                                                       // makerSignature.signatureBytes.offset
            mstore(add(0x1e0, ptr), mload(add(0x20, makerSignature)))                           // makerSignature.flags

            let makerSignatureBytes := mload(makerSignature)
            let makerSignatureBytesLength := mload(makerSignatureBytes)
            mcopy(add(0x200, ptr), makerSignatureBytes, add(0x20, makerSignatureBytesLength))

            if iszero(call(gas(), bebop, 0x00, add(0x1c, ptr), add(0x204, makerSignatureBytesLength), 0x00, 0x00)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
        }
    }
}

abstract contract Bebop is SettlerAbstract {
    using FastLogic for bool;
    using SafeTransferLib for IERC20;
    using Ternary for bool;
    using FullMath for uint256;
    using FastBebop for IBebopSettlement;

    IBebopSettlement internal constant _BEBOP = IBebopSettlement(0xbbbbbBB520d69a9775E85b458C58c648259FAD5F);

    constructor() {
        assert(address(_BEBOP).code.length > 0 || block.chainid == 31337);
    }

    function _isRestrictedTarget(address target) internal view virtual override returns (bool) {
        return (target == address(_BEBOP)).or(super._isRestrictedTarget(target));
    }

    function _logBebopOrder(uint128 eventId, uint128 makerFilledAmount) private {
        assembly ("memory-safe") {
            mstore(0x10, makerFilledAmount)
            mstore(0x00, and(0xffffffffffffffffffffffffffffffff, eventId))
            log0(0x00, 0x30)
        }
    }

    function sellToBebop(
        address payable recipient,
        IERC20 sellToken,
        ISettlerActions.BebopOrder memory order,
        ISettlerActions.BebopMakerSignature memory makerSignature,
        uint256 amountOutMin
    ) internal returns (uint256 makerFilledAmount) {
        uint256 takerFilledAmount = sellToken.fastBalanceOf(address(this));
        {
            uint256 maxTakerAmount = order.taker_amount;
            takerFilledAmount = (takerFilledAmount > maxTakerAmount).ternary(maxTakerAmount, takerFilledAmount);
            makerFilledAmount = order.maker_amount.unsafeMulDiv(takerFilledAmount, maxTakerAmount);
        }
        if (makerFilledAmount < amountOutMin) {
            revertTooMuchSlippage(IERC20(order.maker_token), amountOutMin, makerFilledAmount);
        }

        sellToken.safeApproveIfBelow(address(_BEBOP), takerFilledAmount);
        _BEBOP.fastSwapSingle(recipient, _msgSender(), sellToken, order, makerSignature, takerFilledAmount);

        _logBebopOrder(uint128(order.event_id_and_flags), uint128(makerFilledAmount));
    }
}
