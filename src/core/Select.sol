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

    // uint32(bytes4(keccak256("executeSelected(bytes[],address,uint256)")))
    uint32 private constant _EXECUTE_SELECTED_SELECTOR = 0x1bbdbb47;

    // Adding one failing empty candidate measured 3,603 gas (solc 0.8.34 via-IR, 2026-08-31).  The
    // shared buffer makes per-trial overhead input-independent; 0x2000 is more than double the
    // measurement and is rechecked per capped trial.
    uint256 private constant _SELECT_OVERHEAD_GAS = 8192;

    function _executeSelected(bytes calldata data) private returns (bytes memory) {
        bytes[] calldata actions;
        IERC20 token;
        uint256 minOut;
        // Read the internally constructed callback head without writing memory:
        //     [0x00 actions offset][0x20 token][0x40 minOut][actions length][offsets/actions]
        // `select` built the head and copied the complete candidate region once. Reads past the end
        // of the trial calldata return zero. A failing action reverts only this trial.
        assembly ("memory-safe") {
            actions.offset := add(data.offset, calldataload(data.offset))
            actions.length := calldataload(actions.offset)
            actions.offset := add(0x20, actions.offset)
            token := calldataload(add(0x20, data.offset))
            minOut := calldataload(add(0x40, data.offset))
        }
        // A candidate can meet its target by liquidating unexpected assets or unexpected amounts of
        // assets held by Settler.  This is outside SELECT's threat model. Final slippage still
        // enforces the taker's minimum.
        // See https://web.archive.org/web/20240913184335/https://kebabsec.xyz/posts/critical_vulnerability_in_uniswapx/
        uint256 balBefore = token.fastBalanceOf(address(this));
        _runActions(actions);
        uint256 score = token.fastBalanceOf(address(this)) - balBefore;
        if (score < minOut) {
            assembly ("memory-safe") {
                mstore(0x00, 0xa55fee2e) // selector for `Shortfall(uint256)`
                mstore(0x20, score)
                revert(0x1c, 0x24)
            }
        }
        return new bytes(0);
    }

    function select(bytes calldata data) internal {
        uint256 gasCap;
        address token;
        uint256 targetsData;
        uint256 candsData;
        uint256 candsLength;
        uint256 n;
        bytes memory callData;
        // Follow and bound both top-level array offsets. The candidate region is copied once after
        // the private callback head, preserving every valid relative candidate offset.  A zero or
        // dirty `token` reverts.
        assembly ("memory-safe") {
            let dataStart := data.offset
            let dataEnd := add(dataStart, data.length)
            let err := lt(dataEnd, dataStart)
            err := or(gt(0x80, data.length), err)
            gasCap := calldataload(dataStart)
            err := or(or(shr(0x40, gasCap), iszero(gasCap)), err)
            token := calldataload(add(0x20, dataStart))
            err := or(or(shr(0xa0, token), iszero(token)), err)

            let targetsOffset := calldataload(add(0x40, dataStart))
            err := or(gt(targetsOffset, sub(data.length, 0x20)), err) // can't be `gt(add(0x20, targetsOffset), data.length)` due to risk of overflow
            let targetsBase := add(targetsOffset, dataStart)
            n := calldataload(targetsBase)
            targetsData := add(0x20, targetsBase)
            err := or(or(iszero(n), gt(n, shr(0x05, sub(dataEnd, targetsData)))), err)

            let candidatesOffset := calldataload(add(0x60, dataStart))
            err := or(gt(candidatesOffset, sub(data.length, 0x20)), err)
            let candidatesBase := add(candidatesOffset, dataStart)
            candsData := add(0x20, candidatesBase)
            // `targets` and `candidates` must be the same length. Unequal lengths are valid ABI but
            // meaningless here.
            err := or(xor(calldataload(candidatesBase), n), err)
            err := or(gt(n, shr(0x05, sub(dataEnd, candsData))), err)
            if err { revert(0x00, 0x00) }

            candsLength := sub(dataEnd, candsData)
            callData := mload(0x40)
            let dst := add(0x84, callData)
            calldatacopy(dst, candsData, candsLength)
            mstore(add(0x44, callData), token)
            mstore(add(0x04, callData), _EXECUTE_SELECTED_SELECTOR)
            mstore(callData, add(0x64, candsLength))
            mstore(0x40, add(dst, candsLength))
        }

        for (uint256 i; i < n; i = i.unsafeInc()) {
            uint256 gasLimit;
            bool isLast;
            // Select one candidate in the shared callback buffer by changing only its dynamic
            // offset and target. The token, selector, length, and copied region remain unchanged.
            assembly ("memory-safe") {
                let offset := calldataload(add(shl(0x05, i), candsData))
                if gt(offset, sub(candsLength, 0x20)) { revert(0x00, 0x00) }
                mstore(add(0x24, callData), add(0x60, offset))
                mstore(add(0x64, callData), calldataload(add(shl(0x05, i), targetsData)))

                let remaining := sub(n, i)
                let later := lt(0x01, remaining)
                isLast := iszero(later)

                gasLimit := gas()
                if later {
                    // Reserve every remaining trial's cap plus `_SELECT_OVERHEAD_GAS` of loop
                    // overhead before capping this trial. The `gasCap/63` term covers EIP-150's
                    // retained sixty-fourth on the final uncapped call: `C + floor(C/63)` forwards
                    // exactly `C`. Capped trials need no retention term because `remaining >= 2`
                    // makes 63/64 of `gasLimit` exceed `gasCap`. The check re-runs before every
                    // capped trial and reverts if the reserve no longer fits.
                    let totalCap := mul(gasCap, remaining)
                    if gt(add(_SELECT_OVERHEAD_GAS, add(totalCap, div(gasCap, 0x3f))), gasLimit) {
                        revert(0x00, 0x00)
                    }
                    gasLimit := gasCap
                }
            }

            if (_setOperatorAndTryCall(gasLimit, address(this), callData, _EXECUTE_SELECTED_SELECTOR, _executeSelected))
            {
                break;
            }
            if (isLast) {
                // Copy final-trial returndata to `[ptr, ptr + returndatasize())` and bubble it
                // unchanged.  The temporary free-memory buffer cannot cross back into Solidity
                // because this path reverts.
                assembly ("memory-safe") {
                    let ptr := mload(0x40)
                    returndatacopy(ptr, 0x00, returndatasize())
                    revert(ptr, returndatasize())
                }
            }
        }
    }

    function _runActions(bytes[] calldata actions) internal {
        // A nested `CHECK_SLIPPAGE` no-ops against this zeroed struct in taker-submitted Settler.
        // The other flavors do not dispatch it, so there it reverts only its own trial.
        AllowedSlippage memory noSlippage;
        uint256 it;
        assembly ("memory-safe") {
            it := actions.offset
        }
        for (uint256 i; i < actions.length; (i, it) = (i.unsafeInc(), it.unsafeAdd(32))) {
            (uint256 action, bytes calldata data) = actions.decodeCall(it);
            bool tooShort;
            // A length that wrapped in `decodeCall`'s selector slice has upper bits set.
            assembly ("memory-safe") {
                tooShort := shr(0x40, data.length)
                data.length := mul(data.length, iszero(tooShort))
            }
            // Not `FastLogic.or`: `_dispatch` must not run on the cleared length.
            if (tooShort || !_dispatch(i, action, data, noSlippage)) {
                revertActionInvalid(i, action, data);
            }
        }
    }
}
