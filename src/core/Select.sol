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

    /// @notice Nest the uncapped fallback to exceed three candidates.
    uint256 private constant MAX_CANDIDATES = 3;

    event Selected(bytes32 indexed candidateHash, uint256 score) anonymous;

    function _balanceOfOrZero(IERC20 token) private view returns (uint256) {
        return address(token) == address(0) ? 0 : token.fastBalanceOf(address(this));
    }

    /// @notice Self-call entrypoint for one candidate.
    function executeSelected(bytes[] calldata actions, IERC20 token, uint256 minOut, bytes32 candidateHash) external {
        if (msg.sender != address(this)) revert();
        uint256 balBefore = _balanceOfOrZero(token);
        _runActions(actions);
        uint256 score = _balanceOfOrZero(token) - balBefore;
        if (score < minOut) {
            // A left-padded selector constant is smaller than Solidity's right-padded `bytes4`.
            // Equivalent Solidity: `revert Shortfall(score, candidateHash)`.
            assembly ("memory-safe") {
                mstore(0x00, 0x463e8fcd) // selector for `Shortfall(uint256,bytes32)`
                mstore(0x20, score)
                mstore(0x40, candidateHash)
                revert(0x1c, 0x44)
            }
        }
        // Reverted trials discard this log. Equivalent Solidity emits Selected(candidateHash, score).
        assembly ("memory-safe") {
            mstore(0x00, score)
            log1(0x00, 0x20, candidateHash)
        }
    }

    function _select(bytes calldata data) internal {
        bytes4 selector = this.executeSelected.selector;
        // Assembly keeps validation and self-calls compact. Equivalent Solidity validates both ABI
        // tables and their exact span before trying candidates. With r candidates left, a trial
        // requires r * trialGasLimit + floor(r * trialGasLimit / 0x20) + 0x10000 gas. The final
        // call is uncapped and bubbles failure.
        assembly ("memory-safe") {
            let dataStart := data.offset
            let dataEnd := add(dataStart, data.length)
            if or(or(lt(data.length, 0x80), lt(dataEnd, dataStart)), gt(dataEnd, calldatasize())) {
                revert(0x00, 0x00)
            }

            let gasCap := calldataload(dataStart)
            let token := and(0xffffffffffffffffffffffffffffffffffffffff, calldataload(add(0x20, dataStart)))
            let dynamicStart := add(dataStart, 0x80)
            let targetsBase := add(dataStart, calldataload(add(0x40, dataStart)))
            let base := add(dataStart, calldataload(add(0x60, dataStart)))
            // Nonzero lengths, ordered starts, and the terminal bound also contain both tables.
            if or(lt(targetsBase, dynamicStart), lt(base, dynamicStart)) { revert(0x00, 0x00) }

            let n := calldataload(base)
            if or(iszero(n), gt(n, MAX_CANDIDATES)) { revert(0x00, 0x00) }

            let targetsData := add(0x20, targetsBase)
            let candsData := add(0x20, base)
            let targetsEnd := add(targetsData, shl(0x05, n))
            let candidatesBody := add(candsData, shl(0x05, n))
            if or(lt(calldataload(targetsBase), n), gt(targetsEnd, base)) { revert(0x00, 0x00) }

            let previous := sub(candidatesBody, 0x01)
            for { let i := 0x00 } lt(i, n) { i := add(0x01, i) } {
                let start_ := add(candsData, calldataload(add(candsData, shl(0x05, i))))
                if iszero(gt(start_, previous)) { revert(0x00, 0x00) }
                previous := start_
            }

            // The last candidate's final bytes element must end at the action boundary. Solidity's
            // decoder accepts trailing calldata, so this exact-span check is performed explicitly.
            if gt(previous, sub(dataEnd, 0x20)) { revert(0x00, 0x00) }
            let lastData := add(previous, 0x20)
            let lastLength := calldataload(previous)
            if gt(lastLength, shr(0x05, sub(dataEnd, lastData))) { revert(0x00, 0x00) }
            switch lastLength
            case 0x00 { if iszero(eq(lastData, dataEnd)) { revert(0x00, 0x00) } }
            default {
                let lastTableEnd := add(lastData, shl(0x05, lastLength))
                let lastElement := add(lastData, calldataload(add(lastData, shl(0x05, sub(lastLength, 0x01)))))
                if or(lt(lastElement, lastTableEnd), gt(lastElement, sub(dataEnd, 0x20))) {
                    revert(0x00, 0x00)
                }
                let elementData := add(lastElement, 0x20)
                let elementLength := calldataload(lastElement)
                if gt(elementLength, sub(dataEnd, elementData)) { revert(0x00, 0x00) }
                if iszero(eq(add(elementData, and(add(elementLength, 0x1f), not(0x1f))), dataEnd)) {
                    revert(0x00, 0x00)
                }
            }

            let cd := mload(0x40)
            mstore(cd, selector)
            mstore(add(0x04, cd), 0x80)
            mstore(add(0x24, cd), token)

            for { let i := 0x00 } lt(i, n) { i := add(0x01, i) } {
                let start_ := add(candsData, calldataload(add(candsData, shl(0x05, i))))
                let next_ := dataEnd
                let remaining_ := sub(n, i)
                let later_ := sub(remaining_, 0x01)
                if later_ {
                    next_ := add(candsData, calldataload(add(candsData, shl(0x05, add(i, 0x01)))))
                }
                let len_ := sub(next_, start_)
                let dst_ := add(0x84, cd)
                calldatacopy(dst_, start_, len_)
                mstore(add(0x44, cd), calldataload(add(targetsData, shl(0x05, i))))
                mstore(add(0x64, cd), keccak256(dst_, len_))

                let g_ := gas()
                if later_ {
                    let totalCap_ := mul(gasCap, remaining_)
                    if or(
                        or(iszero(gasCap), gt(gasCap, div(g_, remaining_))),
                        lt(g_, add(add(totalCap_, shr(0x05, totalCap_)), 0x10000))
                    ) {
                        revert(0x00, 0x00)
                    }
                    g_ := gasCap
                }
                if call(g_, address(), 0x00, cd, add(0x84, len_), 0x00, 0x00) { break }
                if iszero(later_) {
                    returndatacopy(cd, 0x00, returndatasize())
                    revert(cd, returndatasize())
                }
            }
        }
    }

    function _runActions(bytes[] calldata actions) internal {
        AllowedSlippage memory noSlippage;
        uint256 it;
        // Read the array cursor without a memory copy. Equivalent Solidity: `it = actions.offset`.
        assembly ("memory-safe") {
            it := actions.offset
        }
        for (uint256 i; i < actions.length; (i, it) = (i.unsafeInc(), it.unsafeAdd(32))) {
            (uint256 action, bytes calldata data) = actions.decodeCall(it);
            bool tooShort;
            // Equivalent Solidity replaces decoder underflow with empty bytes.
            assembly ("memory-safe") {
                tooShort := gt(data.length, not(0x04))
                if tooShort { data.length := 0x00 }
            }
            // Short-circuit malformed data. One revert site avoids duplicated inlining.
            if (tooShort || !_dispatch(i, action, data, noSlippage)) {
                revertActionInvalid(i, action, data);
            }
        }
    }
}
