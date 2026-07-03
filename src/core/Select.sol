// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SettlerSwapAbstract} from "../SettlerAbstract.sol";
import {CalldataDecoder} from "../SettlerBase.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {revertActionInvalid, Measured} from "./SettlerErrors.sol";

/// @notice The JIT selection combinator (scalar). Candidates are non-VIP action lists over held
///         balance; each runs in a disposable self-call frame (a reverting sub-call is the EVM's only
///         atomic undo) and is scored by `token`'s balance delta (`token == 0` scores bare success).
///         CASCADE commits the first candidate clearing its own target (a fallback at targets 0, a
///         descending-floor ladder otherwise). BEST commits candidate 0 if it clears `targets[0]`,
///         else measures all (rolling each back) and re-runs the argmax of score − hurdle AT ITS
///         MEASURED SCORE — so a forged measurement (the tag only rejects accidental look-alikes)
///         fails closed. A candidate may itself be a SELECT (per-hop candidate sets). Funded once;
///         the trailing `CHECK_SLIPPAGE` is the taker's real backstop.
abstract contract Select is SettlerSwapAbstract {
    using SafeTransferLib for IERC20;
    using CalldataDecoder for bytes[];

    /// @dev Placeholder for the demo. Production: 0x's fee wallet, HARD-CODED by decision
    ///      (protocol call 2026-06-29) — an in-calldata receiver invites fee-stripping.
    address internal constant _IMPROVEMENT_FEE_RECEIVER = 0x23030a6124E871F4744Cb9bc14D519b1f033FFe3;

    /// @notice Run one candidate in an isolated frame, scoring `token`'s balance delta (0 when
    ///         `token == 0`). COMMIT if `score >= minOut`, else revert `Measured(score, tag)`.
    ///         `onlySelf`. The candidate must deliver `token` to this contract (native ETH via WETH +
    ///         a later unwrap); the echoed `tag` (keccak of the candidate) rejects accidental
    ///         Measured-shaped reverts.
    function executeSelected(bytes[] calldata actions, IERC20 token, uint256 minOut, bytes32 tag) external {
        require(msg.sender == address(this));
        uint256 balBefore = address(token) == address(0) ? 0 : token.fastBalanceOf(address(this));
        _runActions(actions);
        uint256 score = address(token) == address(0) ? 0 : token.fastBalanceOf(address(this)) - balBefore;
        if (score < minOut) revert Measured(score, tag);
        // else: return -> committed
    }

    /// @dev `SELECT` body. `data` = abi.encode(uint256 fold, uint256 shareBps, uint256
    ///      candidateGasLimit, address token, uint256[] targets, uint256[] hurdles, bytes[][]
    ///      candidates). Assembly forwards each candidate's self-contained `bytes[]` sub-encoding
    ///      straight from calldata into an `executeSelected` self-call — no decode/re-encode, and the
    ///      measurement returndata is read at the exact 0x44-byte `Measured` payload. `candidateGasLimit`
    ///      (0 = uncapped) caps every attempt except the one that must finish (CASCADE's last,
    ///      BEST's commit), so a stalling candidate can't starve the rest (EIP-150). The fee is
    ///      computed in Solidity below. Scores/hurdles are token amounts far below 2^255, so the
    ///      signed netting can't overflow.
    function _select(bytes calldata data) internal {
        bytes4 selector = this.executeSelected.selector;
        uint256 measuredSelector = uint32(Measured.selector);
        IERC20 token;
        uint256 shareBps;
        int256 bestNet;
        int256 secondNet = type(int256).min; // stays min unless BEST finds a runner-up -> no fee
        uint256 bestScore;
        assembly ("memory-safe") {
            // decode the last self-call's `Measured(score, tag)` revert: nonzero iff shape+selector+tag match
            function measured(ret_, tag_, sel_) -> s_ {
                if eq(returndatasize(), 0x44) {
                    returndatacopy(ret_, 0x00, 0x44)
                    if eq(shr(0xe0, mload(ret_)), sel_) { if eq(mload(add(ret_, 0x24)), tag_) { s_ := mload(add(ret_, 0x04)) } }
                }
            }
            // candidate i's `bytes[]` sub-encoding within calldata: [start, start+len)
            function blob(base_, n_, end_, i_) -> start_, len_ {
                start_ := add(base_, calldataload(add(base_, shl(0x05, i_))))
                let e_ := end_
                let j_ := add(i_, 0x01)
                if lt(j_, n_) { e_ := add(base_, calldataload(add(base_, shl(0x05, j_)))) }
                len_ := sub(e_, start_)
            }

            let fold := calldataload(data.offset)
            shareBps := calldataload(add(data.offset, 0x20))
            let gasCap := calldataload(add(data.offset, 0x40))
            token := and(calldataload(add(data.offset, 0x60)), 0xffffffffffffffffffffffffffffffffffffffff)
            let targetsData := add(add(data.offset, calldataload(add(data.offset, 0x80))), 0x20)
            let hurdlesData := add(add(data.offset, calldataload(add(data.offset, 0xa0))), 0x20)
            let base := add(data.offset, calldataload(add(data.offset, 0xc0)))
            let n := calldataload(base)
            let candsData := add(base, 0x20)
            let dataEnd := add(data.offset, data.length)
            // input guards: at least one candidate, and per-candidate targets/hurdles present
            if or(iszero(n), or(lt(calldataload(sub(targetsData, 0x20)), n), lt(calldataload(sub(hurdlesData, 0x20)), n))) {
                revert(0x00, 0x00)
            }

            let ret := mload(0x40) // 0x44-byte returndata scratch
            let cd := add(ret, 0x60) // call scratch: selector ‖ head(0x80) ‖ token ‖ minOut ‖ tag ‖ candidate
            mstore(cd, selector)
            mstore(add(cd, 0x04), 0x80)
            mstore(add(cd, 0x24), token)
            let dst := add(cd, 0x84)

            switch fold
            case 0 {
                // CASCADE: commit the first candidate clearing its own target
                let last := sub(n, 0x01)
                for { let i := 0x00 } iszero(gt(i, last)) { i := add(i, 0x01) } {
                    let start, len := blob(candsData, n, dataEnd, i)
                    calldatacopy(dst, start, len)
                    mstore(add(cd, 0x44), calldataload(add(targetsData, shl(0x05, i))))
                    mstore(add(cd, 0x64), keccak256(dst, len))
                    let g := gasCap
                    if or(iszero(g), eq(i, last)) { g := gas() } // last must be able to finish
                    if call(g, address(), 0x00, cd, add(0x84, len), 0x00, 0x00) { break }
                    if eq(i, last) {
                        returndatacopy(0x00, 0x00, returndatasize())
                        revert(0x00, returndatasize())
                    }
                }
            }
            default {
                // BEST: candidate 0's target attempt doubles as its measurement
                let start, len := blob(candsData, n, dataEnd, 0x00)
                calldatacopy(dst, start, len)
                let tag := keccak256(dst, len)
                mstore(add(cd, 0x44), calldataload(targetsData))
                mstore(add(cd, 0x64), tag)
                let g0 := gasCap
                if iszero(g0) { g0 := gas() }
                if iszero(call(g0, address(), 0x00, cd, add(0x84, len), 0x00, 0x00)) {
                    let bs := measured(ret, tag, measuredSelector)
                    let bn := sub(bs, calldataload(hurdlesData)) // wrapping sub == int256 net
                    let sn := shl(0xff, 0x01) // int256 min
                    let best := 0x00
                    mstore(add(cd, 0x44), not(0x00)) // minOut = MAX -> pure measurement
                    for { let i := 0x01 } lt(i, n) { i := add(i, 0x01) } {
                        start, len := blob(candsData, n, dataEnd, i)
                        calldatacopy(dst, start, len)
                        tag := keccak256(dst, len)
                        mstore(add(cd, 0x64), tag)
                        let gi := gasCap
                        if iszero(gi) { gi := gas() }
                        pop(call(gi, address(), 0x00, cd, add(0x84, len), 0x00, 0x00))
                        let s := measured(ret, tag, measuredSelector)
                        let net := sub(s, calldataload(add(hurdlesData, shl(0x05, i))))
                        switch sgt(net, bn)
                        case 1 { sn := bn  bn := net  best := i  bs := s }
                        default { if sgt(net, sn) { sn := net } }
                    }
                    // commit the winner at its measured score; bubble on any divergence (fail-closed)
                    start, len := blob(candsData, n, dataEnd, best)
                    calldatacopy(dst, start, len)
                    mstore(add(cd, 0x44), bs)
                    mstore(add(cd, 0x64), keccak256(dst, len))
                    if iszero(call(gas(), address(), 0x00, cd, add(0x84, len), 0x00, 0x00)) {
                        returndatacopy(0x00, 0x00, returndatasize())
                        revert(0x00, returndatasize())
                    }
                    bestNet := bn
                    secondNet := sn
                    bestScore := bs
                }
            }
        }
        // fee on demonstrated improvement only: the winner's measured edge over the runner-up,
        // clamped to the winner's score and to held balance, paid in `token`. Reached only on a
        // BEST degraded commit with a runner-up.
        if (secondNet != type(int256).min && bestNet > secondNet && address(token) != address(0)) {
            if (shareBps > BASIS) shareBps = BASIS;
            uint256 improvement = uint256(bestNet - secondNet);
            if (improvement > bestScore) improvement = bestScore;
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
        for (uint256 i; i < actions.length;) {
            (uint256 action, bytes calldata data) = actions.decodeCall(it);
            // `decodeCall` strips a 4-byte selector via unchecked subtraction; a sub-4-byte encoded
            // length underflows `data.length`, which would make `revertActionInvalid`'s calldatacopy
            // OOG instead of reverting cleanly. Catch it (no analogous guard exists on the top-level
            // dispatch loops yet — worth a follow-up there).
            assembly ("memory-safe") {
                if gt(data.length, sub(0, 5)) {
                    mstore(0x00, 0x3c74eed6) // selector for `ActionInvalid(uint256,bytes4,bytes)`
                    mstore(0x20, i)
                    mstore(0x40, shl(0xe0, action))
                    mstore(0x60, 0x60)
                    mstore(0x80, 0x00)
                    revert(0x1c, 0x84)
                }
            }
            if (!_dispatch(i, action, data, noSlippage)) {
                revertActionInvalid(i, action, data);
            }
            unchecked {
                ++i;
                it += 0x20;
            }
        }
    }
}
