// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SettlerSwapAbstract} from "../SettlerAbstract.sol";
import {CalldataDecoder} from "../SettlerBase.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {revertActionInvalid, Measured} from "./SettlerErrors.sol";

/// @notice Candidate-route selection by revertable self-call measurement.
abstract contract Select is SettlerSwapAbstract {
    using SafeTransferLib for IERC20;
    using UnsafeMath for uint256;
    using CalldataDecoder for bytes[];

    function _balanceOfOrZero(IERC20 token) private view returns (uint256) {
        return address(token) == address(0) ? 0 : token.fastBalanceOf(address(this));
    }

    /// @notice Self-call entrypoint for one candidate.
    function executeSelected(bytes[] calldata actions, IERC20 token, uint256 minOut, bytes32 tag) external {
        if (msg.sender != address(this)) revert();
        uint256 balBefore = _balanceOfOrZero(token);
        _runActions(actions);
        uint256 score = _balanceOfOrZero(token) - balBefore;
        if (score < minOut) {
            // revert Measured(score, tag); -- in assembly because a left-padded selector constant
            // is smaller bytecode than Solidity's right-padded `bytes4`
            assembly ("memory-safe") {
                mstore(0x00, 0x56c925b8) // selector for `Measured(uint256,bytes32)`
                mstore(0x20, score)
                mstore(0x40, tag)
                revert(0x1c, 0x44)
            }
        }
    }

    function _select(bytes calldata data) internal {
        uint256 measuredSelector = uint32(Measured.selector);
        uint256 selector = uint32(this.executeSelected.selector);
        assembly ("memory-safe") {
            function measured(ret_, tag_, sel_) -> score_, valid_ {
                if eq(returndatasize(), 0x44) {
                    returndatacopy(ret_, 0x00, 0x44)
                    if and(eq(shr(0xe0, mload(ret_)), sel_), eq(mload(add(0x24, ret_)), tag_)) {
                        score_ := mload(add(0x04, ret_))
                        valid_ := 0x01
                    }
                }
            }
            function blob(base_, n_, end_, i_) -> start_, len_ {
                start_ := add(base_, calldataload(add(base_, shl(0x05, i_))))
                let e_ := end_
                let j_ := add(0x01, i_)
                if lt(j_, n_) { e_ := add(base_, calldataload(add(base_, shl(0x05, j_)))) }
                // Keep each candidate inside the SELECT action. Meta-txn witnesses hash only the
                // declared outer action bytes, so escaped offsets would read unsigned trailing data.
                if or(or(lt(start_, base_), gt(e_, end_)), gt(start_, e_)) { revert(0x00, 0x00) }
                len_ := sub(e_, start_)
            }
            // Shared by the trial and commit loops (one bytecode copy). Recomputing the keccak
            // tag on commit yields the identical value that the trial cached.
            function attempt(base_, n_, end_, i_, cd_, minOut_, gas_) -> ok_, tag_ {
                let start_, len_ := blob(base_, n_, end_, i_)
                let dst_ := add(0x84, cd_)
                calldatacopy(dst_, start_, len_)
                tag_ := keccak256(dst_, len_)
                mstore(add(0x44, cd_), minOut_)
                mstore(add(0x64, cd_), tag_)
                ok_ := call(gas_, address(), 0x00, cd_, add(0x84, len_), 0x00, 0x00)
            }

            // EIP-150: trials get min(gasCap, 63/64 of remaining). Provision ~2*gasCap or early
            // candidates starve. gasCap == 0 lets one trial starve the rest.
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

            let scores := mload(0x40)
            let valids := add(scores, shl(0x05, n))
            let ret := add(valids, shl(0x05, n))
            let cd := add(0x60, ret)
            mstore(cd, selector)
            mstore(add(0x20, cd), 0x80)
            mstore(add(0x40, cd), token)
            // `selector` is left-padded; calldata starts at its first byte
            cd := add(0x1c, cd)

            let attemptedCommit
            let anyMeasured
            let measuredCount
            for {} lt(measuredCount, n) { measuredCount := add(0x01, measuredCount) } {
                // Preserve a commit reserve once at least one candidate has measured.
                // gasCap >> 0x05 covers the commit call's 63/64 shave.
                if and(
                    and(iszero(iszero(gasCap)), anyMeasured),
                    lt(gas(), add(add(gasCap, gasCap), add(shr(0x05, gasCap), 0x10000)))
                ) { break }
                let g := gasCap
                if or(iszero(g), and(iszero(anyMeasured), eq(measuredCount, sub(n, 0x01)))) { g := gas() }
                let ok, tag :=
                    attempt(
                        candsData,
                        n,
                        dataEnd,
                        measuredCount,
                        cd,
                        calldataload(add(targetsData, shl(0x05, measuredCount))),
                        g
                    )
                if ok {
                    attemptedCommit := 0x01
                    break
                }
                let score, valid := measured(ret, tag, measuredSelector)
                anyMeasured := or(anyMeasured, valid)
                mstore(add(scores, shl(0x05, measuredCount)), score)
                mstore(add(valids, shl(0x05, measuredCount)), valid)
            }

            if iszero(attemptedCommit) {
                for {} 0x01 {} {
                    let best := measuredCount
                    let bestScore
                    for { let i := 0x00 } lt(i, measuredCount) { i := add(0x01, i) } {
                        if mload(add(valids, shl(0x05, i))) {
                            let score := mload(add(scores, shl(0x05, i)))
                            if or(eq(best, measuredCount), gt(score, bestScore)) {
                                best := i
                                bestScore := score
                            }
                        }
                    }
                    if eq(best, measuredCount) {
                        returndatacopy(ret, 0x00, returndatasize())
                        revert(ret, returndatasize())
                    }

                    let ok, tag := attempt(candsData, n, dataEnd, best, cd, bestScore, gas())
                    if ok { break }

                    mstore(add(valids, shl(0x05, best)), 0x00)
                }
            }
        }
    }

    function _runActions(bytes[] calldata actions) internal {
        AllowedSlippage memory noSlippage;
        uint256 it;
        assembly ("memory-safe") {
            it := actions.offset
        }
        for (uint256 i; i < actions.length; (i, it) = (i.unsafeInc(), it.unsafeAdd(32))) {
            (uint256 action, bytes calldata data) = actions.decodeCall(it);
            bool tooShort;
            assembly ("memory-safe") {
                tooShort := gt(data.length, not(0x04))
                if tooShort { data.length := 0x00 }
            }
            // `||` (not `FastLogic.or`) so a too-short action is never dispatched; single
            // `revertActionInvalid` call site keeps its body from being inlined twice.
            if (tooShort || !_dispatch(i, action, data, noSlippage)) {
                revertActionInvalid(i, action, data);
            }
        }
    }
}
