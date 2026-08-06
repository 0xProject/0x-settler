// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SettlerSwapAbstract} from "../SettlerAbstract.sol";
import {CalldataDecoder} from "../SettlerBase.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {revertActionInvalid} from "./SettlerErrors.sol";

/// @notice Ordered candidate-route selection by revertable self-calls.
abstract contract Select is SettlerSwapAbstract {
    using SafeTransferLib for IERC20;
    using UnsafeMath for uint256;
    using CalldataDecoder for bytes[];

    /// @notice Candidates per SELECT action. The last candidate is the reliable fallback, so a
    /// lot needs two and a middle rung needs three; deeper ladders only widen the decoder.
    uint256 private constant MAX_CANDIDATES = 3;

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
            // A left-padded selector constant is smaller than Solidity's right-padded `bytes4`.
            // Equivalent Solidity: `revert Measured(score, tag)`.
            assembly ("memory-safe") {
                mstore(0x00, 0x56c925b8) // selector for `Measured(uint256,bytes32)`
                mstore(0x20, score)
                mstore(0x40, tag)
                revert(0x1c, 0x44)
            }
        }
        // Logs in reverted frames are discarded, so this survives exactly when this candidate
        // commits -- receipt-level attribution of the committed candidate and its score.
        // Equivalent Solidity pseudocode: `emit Selected(tag, score)`.
        assembly ("memory-safe") {
            mstore(0x00, score)
            log1(0x00, 0x20, tag)
        }
    }

    function _select(bytes calldata data) internal {
        bytes4 selector = this.executeSelected.selector;
        // Assembly keeps candidate validation, slicing, self-call construction, and revert
        // bubbling compact. Equivalent Solidity: validate a canonical in-frame targets prefix
        // and one-to-three strictly ordered candidate frames; require the last frame's ABI
        // encoding to consume the action exactly; then call candidates in order with their
        // targets and commit the first success, bubbling the final failure. Before each non-final
        // call, reserve enough gas for every remaining allocation: for r candidates, gasleft()
        // must be at least r * candidateGasLimit + floor(r * candidateGasLimit / 0x20) + 0x10000.
        // A multi-candidate action therefore requires a nonzero cap; the last candidate gets gas().
        assembly ("memory-safe") {
            function attempt(start_, len_, cd_, minOut_, gasCap_, remaining_) -> ok_ {
                let dst_ := add(0x84, cd_)
                calldatacopy(dst_, start_, len_)
                mstore(add(0x44, cd_), minOut_)
                mstore(add(0x64, cd_), keccak256(dst_, len_))

                let g_ := gas()
                if remaining_ {
                    if or(iszero(gasCap_), gt(gasCap_, div(g_, remaining_))) { revert(0x00, 0x00) }
                    let totalCap_ := mul(gasCap_, remaining_)
                    if lt(g_, add(add(totalCap_, shr(0x05, totalCap_)), 0x10000)) {
                        revert(0x00, 0x00)
                    }
                    g_ := gasCap_
                }
                ok_ := call(g_, address(), 0x00, cd_, add(0x84, len_), 0x00, 0x00)
            }

            let dataStart := data.offset
            let dataEnd := add(dataStart, data.length)
            if or(lt(data.length, 0x80), or(lt(dataEnd, dataStart), gt(dataEnd, calldatasize()))) {
                revert(0x00, 0x00)
            }

            let gasCap := calldataload(dataStart)
            let token := and(0xffffffffffffffffffffffffffffffffffffffff, calldataload(add(0x20, dataStart)))
            let dynamicStart := add(dataStart, 0x80)
            let targetsBase := add(dataStart, calldataload(add(0x40, dataStart)))
            let base := add(dataStart, calldataload(add(0x60, dataStart)))
            if or(
                or(lt(targetsBase, dynamicStart), gt(targetsBase, sub(dataEnd, 0x20))),
                or(lt(base, dynamicStart), gt(base, sub(dataEnd, 0x20)))
            ) { revert(0x00, 0x00) }

            let n := calldataload(base)
            if or(iszero(n), gt(n, MAX_CANDIDATES)) { revert(0x00, 0x00) }

            let targetsData := add(0x20, targetsBase)
            let candsData := add(0x20, base)
            let targetsEnd := add(targetsData, shl(0x05, n))
            let candidatesBody := add(candsData, shl(0x05, n))
            if or(lt(calldataload(targetsBase), n), or(gt(targetsEnd, base), gt(candidatesBody, dataEnd))) {
                revert(0x00, 0x00)
            }

            let previous
            for { let i := 0x00 } lt(i, n) { i := add(0x01, i) } {
                let start_ := add(candsData, calldataload(add(candsData, shl(0x05, i))))
                if or(lt(start_, candidatesBody), gt(start_, dataEnd)) { revert(0x00, 0x00) }
                if and(i, iszero(gt(start_, previous))) { revert(0x00, 0x00) }
                previous := start_
            }

            // The last candidate's final bytes element must end at the action boundary. Solidity's
            // decoder accepts trailing calldata, so this exact-span check is performed explicitly.
            let lastData := add(previous, 0x20)
            if gt(lastData, dataEnd) { revert(0x00, 0x00) }
            let lastLength := calldataload(previous)
            if gt(lastLength, shr(0x05, sub(dataEnd, lastData))) { revert(0x00, 0x00) }
            let encodedEnd := lastData
            if lastLength {
                let lastTableEnd := add(lastData, shl(0x05, lastLength))
                let lastElement := add(lastData, calldataload(add(lastData, shl(0x05, sub(lastLength, 0x01)))))
                if or(lt(lastElement, lastTableEnd), gt(lastElement, sub(dataEnd, 0x20))) {
                    revert(0x00, 0x00)
                }
                let elementData := add(lastElement, 0x20)
                let elementLength := calldataload(lastElement)
                if gt(elementLength, sub(dataEnd, elementData)) { revert(0x00, 0x00) }
                encodedEnd := add(elementData, and(add(elementLength, 0x1f), not(0x1f)))
            }
            if iszero(eq(encodedEnd, dataEnd)) { revert(0x00, 0x00) }

            let cd := mload(0x40)
            mstore(cd, selector)
            mstore(add(0x04, cd), 0x80)
            mstore(add(0x24, cd), token)

            for { let i := 0x00 } lt(i, n) { i := add(0x01, i) } {
                let start_ := add(candsData, calldataload(add(candsData, shl(0x05, i))))
                let next_ := dataEnd
                let remaining_ := 0x00
                if lt(add(i, 0x01), n) {
                    next_ := add(candsData, calldataload(add(candsData, shl(0x05, add(i, 0x01)))))
                    remaining_ := sub(n, i)
                }
                if attempt(
                    start_,
                    sub(next_, start_),
                    cd,
                    calldataload(add(targetsData, shl(0x05, i))),
                    gasCap,
                    remaining_
                ) { break }
                if eq(add(i, 0x01), n) {
                    returndatacopy(cd, 0x00, returndatasize())
                    revert(cd, returndatasize())
                }
            }
        }
    }

    function _runActions(bytes[] calldata actions) internal {
        AllowedSlippage memory noSlippage;
        uint256 it;
        // Read the calldata array cursor without copying it to memory.
        // Equivalent Solidity: `it = actions.offset`.
        assembly ("memory-safe") {
            it := actions.offset
        }
        for (uint256 i; i < actions.length; (i, it) = (i.unsafeInc(), it.unsafeAdd(32))) {
            (uint256 action, bytes calldata data) = actions.decodeCall(it);
            bool tooShort;
            // Detect the lax decoder's underflow sentinel without copying the nested action.
            // Equivalent Solidity: `tooShort = data.length > type(uint256).max - 4; if
            // (tooShort) data = bytes("")`.
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
