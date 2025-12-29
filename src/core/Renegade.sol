// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {FullMath} from "../vendor/FullMath.sol";

// selector for `sponsorMalleableAtomicMatchSettleWithRefundOptions(uint256,uint256,address,bytes,bytes,bytes,bytes,address,uint256,bool,uint256,bytes)`
uint32 constant ARBITRUM_SELECTOR = 0x0f977971;
// selector for `sponsorMalleableAtomicMatchSettle(uint256,uint256,address,(((uint256,uint256,uint256)),(uint256,uint256,uint256)),((address,address,(uint256),uint256,uint256,uint8),((uint256),(uint256)),((uint256),(uint256)),uint256[],address),(((uint256,uint256)[5],(uint256,uint256),(uint256,uint256)[5],(uint256,uint256),(uint256,uint256),uint256[5],uint256[4],uint256),((uint256,uint256)[5],(uint256,uint256),(uint256,uint256)[5],(uint256,uint256),(uint256,uint256),uint256[5],uint256[4],uint256),((uint256,uint256)[5],(uint256,uint256),(uint256,uint256)[5],(uint256,uint256),(uint256,uint256),uint256[5],uint256[4],uint256)),(((uint256,uint256),(uint256,uint256)),((uint256,uint256),(uint256,uint256))),address,bool,uint256,uint256,bytes)`
uint32 constant BASE_SELECTOR = 0x322ef840;

abstract contract Renegade is SettlerAbstract {
    using SafeTransferLib for IERC20;
    using FullMath for uint256;

    constructor() {
        uint32 selector = _renegadeSelector();
        assert(
            (block.chainid == 42161 && selector == ARBITRUM_SELECTOR)
                || (block.chainid == 8453 && selector == BASE_SELECTOR) || block.chainid == 31337
        );
    }

    function _renegadeSelector() internal pure virtual returns (uint32);

    function sellToRenegade(address target, IERC20 baseToken, bytes memory data) internal returns (uint256 buyAmount) {
        uint256 newBaseAmount;
        uint256 value;
        if (baseToken == ETH_ADDRESS) {
            value = address(this).balance;
            newBaseAmount = value;
        } else {
            newBaseAmount = baseToken.fastBalanceOf(address(this));
            baseToken.safeApproveIfBelow(address(target), newBaseAmount);
        }

        uint256 originalBaseAmount;
        uint256 originalQuoteAmount;
        assembly ("memory-safe") {
            // baseAmount and quoteAmount are the first and second parameters in ARBITRUM_SELECTOR and BASE_SELECTOR
            originalBaseAmount := mload(add(0x20, data))
            originalQuoteAmount := mload(add(0x40, data))
        }
        // scale quoteAmount using newBaseAmount
        buyAmount = originalQuoteAmount.mulDiv(newBaseAmount, originalBaseAmount);

        uint32 selector = _renegadeSelector();
        assembly ("memory-safe") {
            // override baseAmount and quoteAmount
            mstore(add(0x20, data), newBaseAmount)
            mstore(add(0x40, data), buyAmount)

            let len := mload(data)
            // temporarily clobber `data` size memory area
            mstore(data, selector)
            // Allowed selectors don't clash with any relevant function of restricted targets so we can skip checking `target`
            if iszero(call(gas(), target, value, add(0x1c, data), add(0x04, len), 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            // restore clobbered memory
            mstore(data, len)
        }
    }
}
