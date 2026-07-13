// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SettlerSwapAbstract} from "../SettlerAbstract.sol";
import {CalldataDecoder} from "../SettlerBase.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {FastLogic} from "../utils/FastLogic.sol";
import {revertActionInvalid, Measured} from "./SettlerErrors.sol";

/// @notice Candidate-route selection by revertable self-call measurement.
abstract contract Select is SettlerSwapAbstract {
    using SafeTransferLib for IERC20;
    using UnsafeMath for uint256;
    using CalldataDecoder for bytes[];
    using FastLogic for bool;

    function _dispatchVIP(uint256, bytes calldata) internal virtual returns (bool) {
        return false;
    }

    function _balanceOfOrZero(IERC20 token) private view returns (uint256) {
        return address(token) == address(0) ? 0 : token.fastBalanceOf(address(this));
    }

    /// @notice Self-call entrypoint for one candidate. `tag`'s high bit dispatches action 0 VIP.
    function executeSelected(bytes[] calldata actions, IERC20 token, uint256 minOut, bytes32 tag) external {
        require(msg.sender == address(this));
        uint256 balBefore = _balanceOfOrZero(token);
        _runActions(actions, uint256(tag) >> 255 != 0);
        uint256 score = _balanceOfOrZero(token) - balBefore;
        if (score < minOut) revert Measured(score, tag);
    }

    function _select(bytes calldata data, bool vip) internal {
        uint256 measuredSelector = uint32(Measured.selector);
        uint256 tagFlag = vip.toUint() << 255;
        bytes4 selector = this.executeSelected.selector;
        assembly ("memory-safe") {
            function measured(ret_, tag_, sel_) -> s_ {
                if eq(returndatasize(), 0x44) {
                    returndatacopy(ret_, 0x00, 0x44)
                    if eq(shr(0xe0, mload(ret_)), sel_) {
                        if eq(mload(add(0x24, ret_)), tag_) { s_ := mload(add(0x04, ret_)) }
                    }
                }
            }
            function blob(base_, n_, end_, i_) -> start_, len_ {
                start_ := add(base_, calldataload(add(base_, shl(0x05, i_))))
                let e_ := end_
                let j_ := add(0x01, i_)
                if lt(j_, n_) { e_ := add(base_, calldataload(add(base_, shl(0x05, j_)))) }
                len_ := sub(e_, start_)
            }

            let gasCap := calldataload(data.offset)
            let token := and(0xffffffffffffffffffffffffffffffffffffffff, calldataload(add(0x20, data.offset)))
            let targetsData := add(0x20, add(data.offset, calldataload(add(0x40, data.offset))))
            let base := add(data.offset, calldataload(add(0x60, data.offset)))
            let n := calldataload(base)
            let candsData := add(0x20, base)
            let dataEnd := add(data.offset, data.length)
            if or(iszero(n), lt(calldataload(sub(targetsData, 0x20)), n)) {
                revert(0x00, 0x00)
            }

            let nets := mload(0x40)
            let tags := add(nets, shl(0x05, n))
            let ret := add(tags, shl(0x05, n))
            let cd := add(0x60, ret)
            mstore(cd, selector)
            mstore(add(0x04, cd), 0x80)
            mstore(add(0x24, cd), token)
            let dst := add(0x84, cd)
            let tagMask := shl(0xff, 0x01)

            let attemptedCommit
            let anyScore
            let measuredCount
            for {} lt(measuredCount, n) { measuredCount := add(0x01, measuredCount) } {
                // Preserve a commit reserve once at least one candidate has measured positive.
                if and(and(iszero(iszero(gasCap)), anyScore), lt(gas(), add(add(gasCap, gasCap), 0x10000))) {
                    break
                }
                let start, len := blob(candsData, n, dataEnd, measuredCount)
                calldatacopy(dst, start, len)
                let tag := or(and(keccak256(dst, len), not(tagMask)), tagFlag)
                mstore(add(0x44, cd), calldataload(add(targetsData, shl(0x05, measuredCount))))
                mstore(add(0x64, cd), tag)
                let g := gasCap
                if or(iszero(g), and(iszero(anyScore), eq(measuredCount, sub(n, 0x01)))) { g := gas() }
                if call(g, address(), 0x00, cd, add(0x84, len), 0x00, 0x00) {
                    attemptedCommit := 0x01
                    break
                }
                let score := measured(ret, tag, measuredSelector)
                anyScore := or(anyScore, gt(score, 0x00))
                mstore(add(nets, shl(0x05, measuredCount)), score)
                // Cache the hash and use its high bit as the attempted-candidate marker.
                mstore(add(tags, shl(0x05, measuredCount)), or(tag, tagMask))
            }

            if iszero(attemptedCommit) {
                for {} 0x01 {} {
                    let best := measuredCount
                    let bestNet := shl(0xff, 0x01)
                    for { let i := 0x00 } lt(i, measuredCount) { i := add(0x01, i) } {
                        if mload(add(tags, shl(0x05, i))) {
                            let net := mload(add(nets, shl(0x05, i)))
                            if or(eq(best, measuredCount), sgt(net, bestNet)) {
                                best := i
                                bestNet := net
                            }
                        }
                    }
                    if eq(best, measuredCount) {
                        returndatacopy(ret, 0x00, returndatasize())
                        revert(ret, returndatasize())
                    }

                    let start, len := blob(candsData, n, dataEnd, best)
                    calldatacopy(dst, start, len)
                    mstore(add(0x44, cd), mload(add(nets, shl(0x05, best))))
                    mstore(add(0x64, cd), or(and(mload(add(tags, shl(0x05, best))), not(tagMask)), tagFlag))
                    if call(gas(), address(), 0x00, cd, add(0x84, len), 0x00, 0x00) {
                        break
                    }

                    mstore(add(tags, shl(0x05, best)), 0x00)
                }
            }
        }
    }

    function _runActions(bytes[] calldata actions, bool vip) internal {
        AllowedSlippage memory noSlippage;
        uint256 it;
        assembly ("memory-safe") {
            it := actions.offset
        }
        for (uint256 i; i < actions.length; (i, it) = (i.unsafeInc(), it.unsafeAdd(32))) {
            (uint256 action, bytes calldata data) = actions.decodeCall(it);
            // `decodeCall` underflows short actions.
            assembly ("memory-safe") {
                if gt(data.length, not(0x04)) {
                    let ptr := mload(0x40)
                    mstore(ptr, 0x3c74eed6)
                    mstore(add(0x20, ptr), i)
                    mstore(add(0x40, ptr), shl(0xe0, action))
                    mstore(add(0x60, ptr), 0x60)
                    mstore(add(0x80, ptr), 0x00)
                    revert(add(0x1c, ptr), 0x84)
                }
            }
            if (vip.and(i == 0) ? !_dispatchVIP(action, data) : !_dispatch(i, action, data, noSlippage)) {
                revertActionInvalid(i, action, data);
            }
        }
    }
}
