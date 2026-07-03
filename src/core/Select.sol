// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SettlerSwapAbstract} from "../SettlerAbstract.sol";
import {CalldataDecoder} from "../SettlerBase.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {revertActionInvalid, Measured} from "./SettlerErrors.sol";

/// @notice Runs candidate routes in revertable self-calls and commits one, scored by `token`'s
///         balance delta. CASCADE commits the first candidate meeting its own target. BEST measures
///         every candidate and re-runs the best net of hurdles at its measured score, so a faked
///         measurement cannot profit.
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

    /// @dev `SELECT` body. `data` is abi.encode(uint256 fold, uint256 shareBps, uint256
    ///      candidateGasLimit, address token, uint256[] targets, uint256[] hurdles, bytes[][]
    ///      candidates). Candidate sub-encodings forward straight from calldata into
    ///      `executeSelected` self-calls. `candidateGasLimit` (0 = uncapped) bounds every attempt
    ///      except the one that must finish, CASCADE's last and BEST's commit.
    function _select(bytes calldata data) internal {
        bytes4 selector = this.executeSelected.selector;
        uint256 measuredSelector = uint32(Measured.selector);
        IERC20 token;
        uint256 shareBps;
        int256 bestNet;
        int256 secondNet = type(int256).min; // stays min, and the fee unreachable, unless BEST finds a runner-up
        uint256 bestScore;
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

            let fold := calldataload(data.offset)
            shareBps := calldataload(add(0x20, data.offset))
            let gasCap := calldataload(add(0x40, data.offset))
            token := and(0xffffffffffffffffffffffffffffffffffffffff, calldataload(add(0x60, data.offset)))
            let targetsData := add(0x20, add(data.offset, calldataload(add(0x80, data.offset))))
            let hurdlesData := add(0x20, add(data.offset, calldataload(add(0xa0, data.offset))))
            let base := add(data.offset, calldataload(add(0xc0, data.offset)))
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

            let ret := mload(0x40) // 0x44-byte returndata scratch
            let cd := add(0x60, ret) // call scratch: selector, head (0x80), token, minOut, tag, candidate tail
            mstore(cd, selector)
            mstore(add(0x04, cd), 0x80)
            mstore(add(0x24, cd), token)
            let dst := add(0x84, cd)

            switch fold
            case 0 {
                // CASCADE: commit the first candidate clearing its own target
                let last := sub(n, 0x01)
                for { let i := 0x00 } iszero(gt(i, last)) { i := add(0x01, i) } {
                    let start, len := blob(candsData, n, dataEnd, i)
                    calldatacopy(dst, start, len)
                    mstore(add(0x44, cd), calldataload(add(targetsData, shl(0x05, i))))
                    mstore(add(0x64, cd), keccak256(dst, len))
                    let g := gasCap
                    if or(iszero(g), eq(i, last)) { g := gas() } // last must be able to finish
                    if call(g, address(), 0x00, cd, add(0x84, len), 0x00, 0x00) { break }
                    if eq(i, last) {
                        returndatacopy(ret, 0x00, returndatasize())
                        revert(ret, returndatasize())
                    }
                }
            }
            default {
                // BEST: candidate 0's target attempt doubles as its measurement
                let start, len := blob(candsData, n, dataEnd, 0x00)
                calldatacopy(dst, start, len)
                let tag := keccak256(dst, len)
                mstore(add(0x44, cd), calldataload(targetsData))
                mstore(add(0x64, cd), tag)
                let g0 := gasCap
                if iszero(g0) { g0 := gas() }
                if iszero(call(g0, address(), 0x00, cd, add(0x84, len), 0x00, 0x00)) {
                    let bs := measured(ret, tag, measuredSelector)
                    let bn := sub(bs, calldataload(hurdlesData)) // wrapping sub == int256 net. Absurd scores or hurdles revert in the checked fee math below (fail closed)
                    let sn := shl(0xff, 0x01) // int256 min
                    let best := 0x00
                    mstore(add(0x44, cd), not(0x00)) // minOut of MAX makes every attempt a pure measurement
                    for { let i := 0x01 } lt(i, n) { i := add(0x01, i) } {
                        start, len := blob(candsData, n, dataEnd, i)
                        calldatacopy(dst, start, len)
                        tag := keccak256(dst, len)
                        mstore(add(0x64, cd), tag)
                        let gi := gasCap
                        if iszero(gi) { gi := gas() }
                        pop(call(gi, address(), 0x00, cd, add(0x84, len), 0x00, 0x00))
                        let s := measured(ret, tag, measuredSelector)
                        let net := sub(s, calldataload(add(hurdlesData, shl(0x05, i))))
                        switch sgt(net, bn)
                        case 1 {
                            sn := bn
                            bn := net
                            best := i
                            bs := s
                        }
                        default { if sgt(net, sn) { sn := net } }
                    }
                    // commit the winner at its measured score, bubbling any divergence (fail closed)
                    start, len := blob(candsData, n, dataEnd, best)
                    calldatacopy(dst, start, len)
                    mstore(add(0x44, cd), bs)
                    mstore(add(0x64, cd), keccak256(dst, len))
                    if iszero(call(gas(), address(), 0x00, cd, add(0x84, len), 0x00, 0x00)) {
                        returndatacopy(ret, 0x00, returndatasize())
                        revert(ret, returndatasize())
                    }
                    bestNet := bn
                    secondNet := sn
                    bestScore := bs
                }
            }
        }
        // fee on the winner's measured edge over the runner-up, clamped to its score and to held
        // balance. Only reachable on a BEST degraded commit with a runner-up.
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
