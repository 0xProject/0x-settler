// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";
import {revertTooMuchSlippage} from "./SettlerErrors.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";

interface IDodoV2 {
    function sellBase(address to) external returns (uint256 receiveQuoteAmount);
    function sellQuote(address to) external returns (uint256 receiveBaseAmount);

    function _BASE_TOKEN_() external view returns (IERC20);
    function _QUOTE_TOKEN_() external view returns (IERC20);
}

library FastDodoV2 {
    function _callAddressReturnUint(IDodoV2 dodo, uint256 sig, address addr) private returns (uint256 r) {
        assembly ("memory-safe") {
            mstore(0x14, addr)
            mstore(0x00, shl(0x60, sig))
            if iszero(call(gas(), dodo, 0x00, 0x10, 0x24, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if iszero(gt(returndatasize(), 0x1f)) { revert(0x00, 0x00) }

            r := mload(0x00)
        }
    }

    function fastSellBase(IDodoV2 dodo, address to) internal returns (uint256 receiveQuoteAmount) {
        return _callAddressReturnUint(dodo, uint32(dodo.sellBase.selector), to);
    }

    function fastSellQuote(IDodoV2 dodo, address to) internal returns (uint256 receiveBaseAmount) {
        return _callAddressReturnUint(dodo, uint32(dodo.sellQuote.selector), to);
    }

    function _get(IDodoV2 dodo, uint256 sig) private view returns (bytes32 r) {
        assembly ("memory-safe") {
            mstore(0x00, sig)
            if iszero(staticcall(gas(), dodo, 0x1c, 0x04, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if iszero(gt(returndatasize(), 0x1f)) { revert(0x00, 0x00) }

            r := mload(0x00)
        }
    }

    function fast_BASE_TOKEN_(IDodoV2 dodo) internal view returns (IERC20) {
        uint256 result = uint256(_get(dodo, uint32(dodo._BASE_TOKEN_.selector)));
        require(result >> 160 == 0);
        return IERC20(address(uint160(result)));
    }

    function fast_QUOTE_TOKEN_(IDodoV2 dodo) internal view returns (IERC20) {
        uint256 result = uint256(_get(dodo, uint32(dodo._QUOTE_TOKEN_.selector)));
        require(result >> 160 == 0);
        return IERC20(address(uint160(result)));
    }
}

abstract contract DodoV2 is SettlerAbstract {
    using UnsafeMath for uint256;
    using SafeTransferLib for IERC20;
    using FastDodoV2 for IDodoV2;

    function sellToDodoV2(
        address recipient,
        IERC20 sellToken,
        uint256 bps,
        IDodoV2 dodo,
        bool quoteForBase,
        uint256 minBuyAmount
    ) internal returns (uint256 buyAmount) {
        if (bps != 0) {
            uint256 sellAmount;
            unchecked {
                sellAmount = (sellToken.fastBalanceOf(address(this)) * bps).unsafeDiv(BASIS);
            }
            sellToken.safeTransfer(address(dodo), sellAmount);
        }
        if (quoteForBase) {
            buyAmount = dodo.fastSellQuote(recipient);
            if (buyAmount < minBuyAmount) {
                revertTooMuchSlippage(dodo.fast_BASE_TOKEN_(), minBuyAmount, buyAmount);
            }
        } else {
            buyAmount = dodo.fastSellBase(recipient);
            if (buyAmount < minBuyAmount) {
                revertTooMuchSlippage(dodo.fast_QUOTE_TOKEN_(), minBuyAmount, buyAmount);
            }
        }
    }
}
