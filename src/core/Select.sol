// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SettlerSwapAbstract} from "../SettlerAbstract.sol";
import {CalldataDecoder} from "../SettlerBase.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {revertActionInvalid, Measured} from "./SettlerErrors.sol";

/// @notice Runs candidate routes in revertable self-calls and commits one, scored by `token`'s
///         balance delta: the first candidate meeting its own target, else the best measurement
///         re-run at its measured score (fail closed), degrading to the runner-up on divergence.
///         Full semantics on `ISettlerActions.SELECT`.
abstract contract Select is SettlerSwapAbstract {
    using SafeTransferLib for IERC20;
    using UnsafeMath for uint256;
    using CalldataDecoder for bytes[];

    function _dispatchVIP(uint256, bytes calldata) internal virtual returns (bool) {
        return false;
    }

    /// @notice Runs one candidate, which must deliver `token` here (zero `token` scores 0, native
    ///         ETH must route into WETH). Commits if the score meets `minOut`, else reverts
    ///         `Measured(score, tag)`. `tag`'s high bit dispatches action 0 VIP. Self-call only.
    function executeSelected(bytes[] calldata actions, IERC20 token, uint256 minOut, bytes32 tag) external {
        require(msg.sender == address(this));
        uint256 balBefore = address(token) == address(0) ? 0 : token.fastBalanceOf(address(this));
        _runActions(actions, uint256(tag) >> 255 != 0);
        uint256 score = address(token) == address(0) ? 0 : token.fastBalanceOf(address(this)) - balBefore;
        if (score < minOut) revert Measured(score, tag);
    }

    /// @dev `SELECT`/`SELECT_VIP` body. `data` is the action's arguments, abi.encoded. Candidate
    ///      sub-encodings forward straight from calldata into `executeSelected` self-calls.
    function _select(bytes calldata data, bool vip) internal {
        uint256 measuredSelector = uint32(Measured.selector);
        uint256 tagFlag;
        assembly ("memory-safe") {
            tagFlag := shl(0xff, vip)
        }
        bytes4 selector = this.executeSelected.selector;
        // Hand-built executeSelected self-calls, forwarded from calldata. Pseudocode:
        // for each candidate: if selfCall(targets[i], cappedGas) succeeds return; else save score/net
        //   (breaking early once a score exists and gas nears the commit reserve);
        // while no commit: try the highest live net uncapped at its score; drop false measurements.
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

            let gasCap := calldataload(data.offset)
            let token := and(0xffffffffffffffffffffffffffffffffffffffff, calldataload(add(0x20, data.offset)))
            let targetsData := add(0x20, add(data.offset, calldataload(add(0x40, data.offset))))
            let hurdlesData := add(0x20, add(data.offset, calldataload(add(0x60, data.offset))))
            let base := add(data.offset, calldataload(add(0x80, data.offset)))
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
            let alive := add(nets, shl(0x05, n))
            // the gas guard can skip candidates, and memory above the free pointer is not
            // necessarily zero (`DANGEROUS_freeMemory`), so `alive` must be zeroed explicitly
            calldatacopy(alive, calldatasize(), shl(0x05, n))
            let ret := add(alive, shl(0x05, n)) // 0x44-byte returndata scratch
            let cd := add(0x60, ret) // call scratch: selector, head (0x80), token, minOut, tag, candidate tail
            mstore(cd, selector)
            mstore(add(0x04, cd), 0x80)
            mstore(add(0x24, cd), token)
            let dst := add(0x84, cd)
            let tagMask := shl(0xff, 0x01)

            let attemptedCommit
            let anyScore
            for { let i := 0x00 } lt(i, n) { i := add(0x01, i) } {
                // once a real score exists, stop measuring when gas nears the reserve for one
                // capped commit run plus post-processing (heuristic; the cap must be sane)
                if and(and(iszero(iszero(gasCap)), anyScore), lt(gas(), add(add(gasCap, gasCap), 0x10000))) {
                    break
                }
                let start, len := blob(candsData, n, dataEnd, i)
                calldatacopy(dst, start, len)
                let tag := or(and(keccak256(dst, len), not(tagMask)), tagFlag)
                mstore(add(0x44, cd), calldataload(add(targetsData, shl(0x05, i))))
                mstore(add(0x64, cd), tag)
                let g := gasCap
                if or(iszero(g), and(iszero(anyScore), eq(i, sub(n, 0x01)))) { g := gas() }
                if call(g, address(), 0x00, cd, add(0x84, len), 0x00, 0x00) {
                    attemptedCommit := 0x01
                    break
                }
                let score := measured(ret, tag, measuredSelector)
                anyScore := or(anyScore, gt(score, 0x00))
                mstore(add(scores, shl(0x05, i)), score)
                // wrapping sub == int256 net; the solver keeps hurdles inside sane int256 bounds
                mstore(add(nets, shl(0x05, i)), sub(score, calldataload(add(hurdlesData, shl(0x05, i)))))
                mstore(add(alive, shl(0x05, i)), 0x01)
            }

            if iszero(attemptedCommit) {
                for {} 0x01 {} {
                    let best := n
                    let bestNet := shl(0xff, 0x01) // int256 min
                    for { let i := 0x00 } lt(i, n) { i := add(0x01, i) } {
                        if mload(add(alive, shl(0x05, i))) {
                            let net := mload(add(nets, shl(0x05, i)))
                            if or(eq(best, n), sgt(net, bestNet)) {
                                best := i
                                bestNet := net
                            }
                        }
                    }
                    if eq(best, n) {
                        returndatacopy(ret, 0x00, returndatasize())
                        revert(ret, returndatasize())
                    }

                    // commit the current highest-net candidate at its measured score
                    let start, len := blob(candsData, n, dataEnd, best)
                    calldatacopy(dst, start, len)
                    mstore(add(0x44, cd), mload(add(scores, shl(0x05, best))))
                    mstore(add(0x64, cd), or(and(keccak256(dst, len), not(tagMask)), tagFlag))
                    if call(gas(), address(), 0x00, cd, add(0x84, len), 0x00, 0x00) {
                        break
                    }

                    mstore(add(alive, shl(0x05, best)), 0x00)
                }
            }
        }
    }

    /// @dev The shared candidate-execution loop. When `vip`, action 0 must be VIP.
    function _runActions(bytes[] calldata actions, bool vip) internal {
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
            if (vip && i == 0 ? !_dispatchVIP(action, data) : !_dispatch(i, action, data, noSlippage)) {
                revertActionInvalid(i, action, data);
            }
        }
    }
}
