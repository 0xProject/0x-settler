// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SettlerSwapAbstract} from "../SettlerAbstract.sol";
import {IDeepstateV1} from "../interfaces/IDeepstateV1.sol";
import {tmp} from "../utils/512Math.sol";
import {FastLogic} from "../utils/FastLogic.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {revertInvalidDeepstateRoute, revertNonStandardDeepstateToken} from "./SettlerErrors.sol";
import "./Constants.sol" as Constants;

IDeepstateV1 constant ROBINHOOD_DEEPSTATE = IDeepstateV1(0x6cf19308C22FC82ea620Fa0B3E94948d20f27B96);

abstract contract Deepstate is SettlerSwapAbstract {
    using SafeTransferLib for IERC20;
    using SafeTransferLib for address payable;
    using FastLogic for bool;
    using UnsafeMath for uint256;

    constructor() {
        assert(address(ROBINHOOD_DEEPSTATE).code.length > 0 || block.chainid == 31337);
    }

    function _isRestrictedTarget(address target) internal view virtual override returns (bool) {
        return (target == address(ROBINHOOD_DEEPSTATE)).or(super._isRestrictedTarget(target));
    }

    /// @dev Executes a direct self-funded route against the canonical Robinhood Chain deployment.
    /// Unmatched selected input is returned to `recipient`; unselected input remains available to later actions.
    function sellToDeepstate(
        address payable recipient,
        IERC20 sellToken,
        IERC20 buyToken,
        uint256 ppm,
        IDeepstateV1.FillParams[] memory fills
    ) internal {
        address engineSellToken = _deepstateAsset(sellToken);
        address engineBuyToken = _deepstateAsset(buyToken);
        if (fills.length == 0 || engineSellToken == engineBuyToken) revertInvalidDeepstateRoute();

        for (uint256 i; i < fills.length;) {
            IDeepstateV1.FillParams memory fill = fills[i];
            address inputAsset = fill.isBid ? fill.token1 : fill.token0;
            address outputAsset = fill.isBid ? fill.token0 : fill.token1;
            if (fill.token0 >= fill.token1 || inputAsset != engineSellToken || outputAsset != engineBuyToken) {
                revertInvalidDeepstateRoute();
            }
            fills[i].noRest = true;

            unchecked {
                ++i;
            }
        }

        uint256 balanceBefore = _balanceOf(sellToken, address(this));
        uint256 maxSellAmount = tmp().omul(balanceBefore, ppm).unsafeDiv(Constants.BASIS);
        uint256 consumed;
        if (address(sellToken) == Constants.ETH_ADDRESS) {
            unchecked {
                // `ppm > BASIS` is caller-supplied GIGO, consistent with other self-funded actions.
                ROBINHOOD_DEEPSTATE.fillRoute{value: maxSellAmount}(fills);
                uint256 balanceAfter = address(this).balance;
                if (balanceAfter > balanceBefore) revertNonStandardDeepstateToken(sellToken);
                consumed = balanceBefore - balanceAfter;
            }
        } else {
            uint256 engineBalanceBefore = sellToken.fastBalanceOf(address(ROBINHOOD_DEEPSTATE));

            sellToken.safeApprove(address(ROBINHOOD_DEEPSTATE), 0);
            sellToken.safeApprove(address(ROBINHOOD_DEEPSTATE), maxSellAmount);
            ROBINHOOD_DEEPSTATE.fillRoute(fills);
            sellToken.safeApprove(address(ROBINHOOD_DEEPSTATE), 0);

            uint256 balanceAfter = sellToken.fastBalanceOf(address(this));
            uint256 engineBalanceAfter = sellToken.fastBalanceOf(address(ROBINHOOD_DEEPSTATE));
            if (balanceAfter > balanceBefore || engineBalanceAfter < engineBalanceBefore) {
                revertNonStandardDeepstateToken(sellToken);
            }
            unchecked {
                consumed = balanceBefore - balanceAfter;
            }
            if (engineBalanceAfter - engineBalanceBefore != consumed) revertNonStandardDeepstateToken(sellToken);
        }

        if (consumed > maxSellAmount) revertNonStandardDeepstateToken(sellToken);
        uint256 refund;
        unchecked {
            refund = maxSellAmount - consumed;
        }
        if (refund != 0 && recipient != address(this)) {
            if (address(sellToken) == Constants.ETH_ADDRESS) {
                recipient.safeTransferETH(refund);
            } else {
                uint256 recipientBalanceBefore = sellToken.fastBalanceOf(recipient);
                sellToken.safeTransfer(recipient, refund);
                uint256 recipientBalanceAfter = sellToken.fastBalanceOf(recipient);
                if (
                    recipientBalanceAfter < recipientBalanceBefore
                        || recipientBalanceAfter - recipientBalanceBefore != refund
                ) {
                    revertNonStandardDeepstateToken(sellToken);
                }
            }
        }
    }

    function _deepstateAsset(IERC20 token) private pure returns (address asset) {
        asset = address(token);
        if (asset == Constants.ETH_ADDRESS) return address(0);
        if (asset == address(0)) revertInvalidDeepstateRoute();
    }

    function _balanceOf(IERC20 token, address account) private view returns (uint256) {
        return address(token) == Constants.ETH_ADDRESS ? account.balance : token.fastBalanceOf(account);
    }
}
