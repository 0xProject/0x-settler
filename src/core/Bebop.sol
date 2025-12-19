// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

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

    struct MakerSignature {
        bytes signatureBytes;
        uint256 flags;
    }

    /// @notice Taker execution of one-to-one trade with one maker
    /// @param order Single order struct
    /// @param makerSignature Maker's signature for SingleOrder
    /// @param filledTakerAmount Partially filled taker amount, 0 for full fill
    function swapSingle(Single calldata order, MakerSignature calldata makerSignature, uint256 filledTakerAmount)
        external
        payable;
}

library FastBebop {
    struct BebopSingleReduced {
        uint256 expiry;
        address maker_address;
        uint256 maker_nonce;
        IERC20 maker_token;
        uint256 taker_amount;
        uint256 maker_amount;
        uint256 flags;
    }

    function fastSwapSingle(
        IBebopSettlement bebop,
        address payable recipient,
        address taker,
        IERC20 sellToken,
        BebopSingleReduced memory order,
        IBebopSettlement.MakerSignature memory makerSignature,
        uint256 filledTakerAmount
    ) internal {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, 0x4dcebcba)
            mstore(add(0x20, ptr), mload(order)) // expiry
            mstore(add(0x40, ptr), address()) // taker_address
            mcopy(add(0x60, ptr), add(0x20, order), 0x40) // maker_address; maker_nonce
            mstore(add(0xa0, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, sellToken)) // taker_token
            mcopy(add(0xc0, ptr), add(0x60, order), 0x60) // maker_token, taker_amount, maker_amount
            mstore(add(0x120, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, recipient)) // receiver
            mstore(add(0x140, ptr), shl(0x60, taker)) // packed_commands // TODO: might want to handle `takerHasNative`, `makerHasNative`, or `takerUsingPermit2` flags
            mstore(add(0x160, ptr), mload(add(0xc0, order))) // flags
            mstore(add(0x180, ptr), 0x1a0) // makerSignature.offset
            mstore(add(0x1a0, ptr), filledTakerAmount)
            mstore(add(0x1c0, ptr), 0x40) // makerSignature.signatureBytes.offset
            mstore(add(0x1e0, ptr), mload(add(0x20, makerSignature))) // makerSignature.flags

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
        assert(block.chainid == 1 || block.chainid == 31337);
    }

    function _isRestrictedTarget(address target) internal pure virtual override returns (bool) {
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
        address sellToken,
        FastBebop.BebopSingleReduced memory order,
        IBebopSettlement.MakerSignature memory makerSignature,
        uint256 amountOutMin
    ) internal returns (uint256 makerFilledAmount) {
        uint256 takerFilledAmount = order.sellToken.fastBalanceOf(address(this));
        {
            uint256 maxTakerAmount = order.taker_amount;
            takerFilledAmount = (takerAmount > maxTakerAmount).ternary(maxTakerAmount, takerAmount);
            makerFilledAmount = order.maker_amount.unsafeMulDiv(takerFilledAmount, maxTakerAmount);
        }
        if (makerFilledAmount < amountOutMin) {
            revertTooMuchSlippage(order.maker_token, amountOutMin, makerFilledAmount);
        }

        _BEBOP.fastSwapSingle(recipient, _msgSender(), sellToken, order, makerSignature, takerFilledAmount);

        _logBebopOrder(uint128(order.flags >> 128), makerFilledAmount);
    }
}
