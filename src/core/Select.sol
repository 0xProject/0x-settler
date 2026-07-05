// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SettlerSwapAbstract} from "../SettlerAbstract.sol";
import {CalldataDecoder} from "../SettlerBase.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {revertActionInvalid, Measured} from "./SettlerErrors.sol";

/// @notice Runs candidate routes in revertable self-calls and commits one, scored by `token`'s
///         balance delta. The first candidate meeting its own target commits directly with no fee.
///         If no candidate clears its target, SELECT commits the highest measured score net of
///         hurdles at its measured score, degrading to the next-best candidate if a measurement was
///         false. `token = 0` and zero targets is pure fallback; descending targets form a ladder;
///         `targets[0] = belief` and `targets[1..] = type(uint256).max` is best-of-N.
abstract contract Select is SettlerSwapAbstract {
    using SafeTransferLib for IERC20;
    using UnsafeMath for uint256;
    using CalldataDecoder for bytes[];

    /// todo: set proper address. Hard-coded so a calldata receiver cannot strip the fee.
    address internal constant _IMPROVEMENT_FEE_RECEIVER = 0x23030a6124E871F4744Cb9bc14D519b1f033FFe3;

    /// @notice Runs one candidate, which must deliver `token` here (zero `token` scores 0, native
    ///         ETH must route into WETH). Commits if the score meets `minOut`, else reverts
    ///         `Measured(score, tag)`. Self-call only.
    function executeSelected(bytes[] calldata actions, IERC20 token, uint256 minOut, bytes32 tag) external {
        require(msg.sender == address(this));
        uint256 balBefore = address(token) == address(0) ? 0 : token.fastBalanceOf(address(this));
        _runActions(actions);
        uint256 score = address(token) == address(0) ? 0 : token.fastBalanceOf(address(this)) - balBefore;
        if (score < minOut) revert Measured(score, tag);
    }

    /// @dev `SELECT` body. `data` is abi.encode(uint256 shareBps, uint256 candidateGasLimit,
    ///      address token, uint256[] targets, uint256[] hurdles, bytes[][] candidates). Candidate
    ///      sub-encodings forward straight from calldata into `executeSelected` self-calls.
    ///      `candidateGasLimit` (0 = uncapped) bounds every attempt; commit-phase calls are uncapped.
    function _select(bytes calldata data) internal {
        bytes4 selector = this.executeSelected.selector;
        uint256 measuredSelector = uint32(Measured.selector);
        IERC20 token;
        uint256 shareBps;
        int256 committedNet;
        int256 runnerUpNet = type(int256).min; // stays min, and the fee unreachable, unless a runner-up remains
        uint256 committedScore;
        // Hand-build executeSelected calls from candidate sub-encodings in calldata and retain each
        // failed attempt's measured score/net. Solidity pseudocode:
        // for each candidate: if selfCall(targets[i], cappedGas) succeeds return; else save score/net.
        // while no commit: try the highest non-dropped net uncapped at its score; drop false measurements.
        assembly ("memory-safe") {
            // reads the last self-call's Measured(score, tag) revert. Returns 0 unless selector and tag match
            function measured(ret_, tag_, sel_) -> s_ {
                if eq(returndatasize(), 0x44) {
                    returndatacopy(ret_, 0x00, 0x44)
                    if eq(shr(0xe0, mload(ret_)), sel_) {
                        if eq(mload(add(0x24, ret_)), tag_) { s_ := mload(add(0x04, ret_)) }
                    }
                }
            }
            // candidate i's `bytes[]` sub-encoding within calldata: [start, start+len)
            function blob(base_, n_, end_, i_) -> start_, len_ {
                start_ := add(base_, calldataload(add(base_, shl(0x05, i_))))
                let e_ := end_
                let j_ := add(0x01, i_)
                if lt(j_, n_) { e_ := add(base_, calldataload(add(base_, shl(0x05, j_)))) }
                len_ := sub(e_, start_)
            }

            shareBps := calldataload(data.offset)
            let gasCap := calldataload(add(0x20, data.offset))
            token := and(0xffffffffffffffffffffffffffffffffffffffff, calldataload(add(0x40, data.offset)))
            let targetsData := add(0x20, add(data.offset, calldataload(add(0x60, data.offset))))
            let hurdlesData := add(0x20, add(data.offset, calldataload(add(0x80, data.offset))))
            let base := add(data.offset, calldataload(add(0xa0, data.offset)))
            let n := calldataload(base)
            let candsData := add(0x20, base)
            let dataEnd := add(data.offset, data.length)
            // input guards: at least one candidate, and per-candidate targets/hurdles present
            if or(
                iszero(n),
                or(lt(calldataload(sub(targetsData, 0x20)), n), lt(calldataload(sub(hurdlesData, 0x20)), n))
            ) {
                revert(0x00, 0x00)
            }

            let scores := mload(0x40)
            let nets := add(scores, shl(0x05, n))
            let dropped := add(nets, shl(0x05, n))
            let ret := add(dropped, shl(0x05, n)) // 0x44-byte returndata scratch
            let cd := add(0x60, ret) // call scratch: selector, head (0x80), token, minOut, tag, candidate tail
            mstore(cd, selector)
            mstore(add(0x04, cd), 0x80)
            mstore(add(0x24, cd), token)
            let dst := add(0x84, cd)

            let attemptedCommit
            for { let i := 0x00 } lt(i, n) { i := add(0x01, i) } {
                let start, len := blob(candsData, n, dataEnd, i)
                calldatacopy(dst, start, len)
                let tag := keccak256(dst, len)
                mstore(add(0x44, cd), calldataload(add(targetsData, shl(0x05, i))))
                mstore(add(0x64, cd), tag)
                let g := gasCap
                if iszero(g) { g := gas() }
                if call(g, address(), 0x00, cd, add(0x84, len), 0x00, 0x00) {
                    attemptedCommit := 0x01
                    break
                }
                let score := measured(ret, tag, measuredSelector)
                mstore(add(scores, shl(0x05, i)), score)
                // wrapping sub == int256 net. Absurd scores or hurdles revert in the checked fee
                // math below (fail closed)
                mstore(add(nets, shl(0x05, i)), sub(score, calldataload(add(hurdlesData, shl(0x05, i)))))
                mstore(add(dropped, shl(0x05, i)), 0x00)
            }

            if iszero(attemptedCommit) {
                let failedCommits
                for {} 0x01 {} {
                    let best := n
                    let bestNet := shl(0xff, 0x01) // int256 min
                    for { let i := 0x00 } lt(i, n) { i := add(0x01, i) } {
                        if iszero(mload(add(dropped, shl(0x05, i)))) {
                            let net := mload(add(nets, shl(0x05, i)))
                            if or(eq(best, n), sgt(net, bestNet)) {
                                best := i
                                bestNet := net
                            }
                        }
                    }

                    // commit the current highest-net candidate at its measured score
                    let start, len := blob(candsData, n, dataEnd, best)
                    calldatacopy(dst, start, len)
                    mstore(add(0x44, cd), mload(add(scores, shl(0x05, best))))
                    mstore(add(0x64, cd), keccak256(dst, len))
                    if call(gas(), address(), 0x00, cd, add(0x84, len), 0x00, 0x00) {
                        committedNet := bestNet
                        committedScore := mload(add(scores, shl(0x05, best)))
                        let second := shl(0xff, 0x01) // int256 min
                        for { let j := 0x00 } lt(j, n) { j := add(0x01, j) } {
                            if and(iszero(eq(j, best)), iszero(mload(add(dropped, shl(0x05, j))))) {
                                let net := mload(add(nets, shl(0x05, j)))
                                if sgt(net, second) { second := net }
                            }
                        }
                        runnerUpNet := second
                        break
                    }

                    failedCommits := add(failedCommits, 0x01)
                    mstore(add(dropped, shl(0x05, best)), 0x01)
                    if eq(failedCommits, n) {
                        returndatacopy(ret, 0x00, returndatasize())
                        revert(ret, returndatasize())
                    }
                }
            }
        }
        // fee on the committed candidate's measured edge over the runner-up, clamped to its score
        // and to held balance. Only reachable when the commit phase finds a real runner-up.
        if (runnerUpNet != type(int256).min && committedNet > runnerUpNet && address(token) != address(0)) {
            if (shareBps > BASIS) shareBps = BASIS;
            uint256 improvement = uint256(committedNet - runnerUpNet);
            if (improvement > committedScore) improvement = committedScore;
            uint256 fee = improvement * shareBps / BASIS;
            uint256 held = token.fastBalanceOf(address(this));
            if (fee > held) fee = held;
            if (fee != 0) token.safeTransfer(_IMPROVEMENT_FEE_RECEIVER, fee);
        }
    }

    /// @dev The shared candidate-execution loop.
    function _runActions(bytes[] calldata actions) internal {
        AllowedSlippage memory noSlippage;
        uint256 it;
        assembly ("memory-safe") {
            it := actions.offset
        }
        for (uint256 i; i < actions.length; (i, it) = (i.unsafeInc(), it.unsafeAdd(32))) {
            (uint256 action, bytes calldata data) = actions.decodeCall(it);
            // `decodeCall` strips 4 selector bytes unchecked, so a shorter action underflows
            // `data.length` and `revertActionInvalid` would OOG. Catch it here.
            assembly ("memory-safe") {
                if gt(data.length, not(0x04)) {
                    let ptr := mload(0x40)
                    mstore(ptr, 0x3c74eed6) // selector for `ActionInvalid(uint256,bytes4,bytes)`
                    mstore(add(0x20, ptr), i)
                    mstore(add(0x40, ptr), shl(0xe0, action)) // align as `bytes4`
                    mstore(add(0x60, ptr), 0x60) // offset to the length slot of `data`
                    mstore(add(0x80, ptr), 0x00) // report `data` as empty, its true length underflowed
                    revert(add(0x1c, ptr), 0x84)
                }
            }
            if (!_dispatch(i, action, data, noSlippage)) {
                revertActionInvalid(i, action, data);
            }
        }
    }
}
