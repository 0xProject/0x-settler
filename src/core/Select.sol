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

    // bytes4(keccak256("executeSelected(bytes[],address,uint256)"))
    uint32 private constant _EXECUTE_SELECTED_SELECTOR = 0x1bbdbb47;

    // Adding one failing empty candidate measured 8,426 gas (solc 0.8.34 via-IR, 2026-08-26).
    // 0x10000 leaves 57,110 gas for input-dependent copy cost and is rechecked per capped trial.
    uint256 private constant _SELECT_OVERHEAD_GAS = 0x10000;

    function _executeSelected(bytes calldata data) private returns (bytes memory) {
        bytes[] calldata actions;
        IERC20 token;
        uint256 minOut;
        // Read the trusted callback body without writing memory:
        // `[0x00 actions=0x60][0x20 token][0x40 minOut][0x60 actions length][0x80 offsets/frames]`.
        // `select` built this payload with the fixed `0x60` head and a verified-clean `token`,
        // and copied only this candidate's frame. Reads past the end of the trial calldata
        // return zero. A failing action reverts only this trial.
        assembly ("memory-safe") {
            actions.length := calldataload(add(0x60, data.offset))
            actions.offset := add(0x80, data.offset)
            token := calldataload(add(0x20, data.offset))
            minOut := calldataload(add(0x40, data.offset))
        }
        // A candidate can meet its target by liquidating unexpected assets or unexpected amounts of assets held by Settler.
        // This is outside SELECT's threat model; final slippage still enforces the taker's minimum.
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
        uint256 dataEnd;
        uint256 n;
        // Ignore the dynamic offset words and decode the fixed packed layout:
        // `[0x00 gasCap][0x20 token][0x40, 0x60 ignored][0x80 n][0xa0 targets]`
        // `[candidates length/table/frames]`. A zero or dirty `token` reverts.
        assembly ("memory-safe") {
            let dataStart := data.offset
            dataEnd := add(dataStart, data.length)
            let err := or(lt(calldatasize(), dataEnd), lt(dataEnd, dataStart))
            gasCap := calldataload(dataStart)
            token := calldataload(add(0x20, dataStart))
            err := or(or(shr(0xa0, token), iszero(token)), err)
            n := calldataload(add(0x80, dataStart))
            let tableSize := shl(0x05, n)
            let candidatesOffset := add(0xa0, tableSize)
            let base := add(candidatesOffset, dataStart)
            candsData := add(0x20, base)
            err := or(or(iszero(n), lt(shr(0x05, data.length), n)), err)
            err := or(xor(calldataload(base), n), err)
            err := or(gt(add(tableSize, candsData), dataEnd), err)
            // The first frame starts at the offset-table end, so every byte belongs to the head,
            // a table, or exactly one frame. Strict ordering bounds each later start below.
            // The upper bound on the last start then bounds them all.
            err := or(xor(calldataload(candsData), tableSize), err)

            // Entry zero is already pinned to `tableSize` and bounded by the table-fit check above.
            let previous := tableSize
            for { let i := 0x01 } lt(i, n) { i := add(0x01, i) } {
                let offset := calldataload(add(shl(0x05, i), candsData))
                err := or(iszero(gt(offset, previous)), err)
                previous := offset
            }
            err := or(gt(previous, sub(dataEnd, candsData)), err)
            if err { revert(0x00, 0x00) }

            targetsData := add(0xa0, dataStart)
        }

        for (uint256 i; i < n; i = i.unsafeInc()) {
            bytes memory callData;
            uint256 gasLimit;
            bool isLast;
            // Allocate one callback buffer per trial. Memory layout:
            // `[0x00 len=0x64+frame][0x20 selector][0x24 actions=0x60][0x44 token]`
            // `[0x64 target][0x84 frame]`. Writing the length last overwrites the selector
            // word's 28-byte zero prefix, avoiding a selector `PUSH32`.
            assembly ("memory-safe") {
                let start := add(calldataload(add(shl(0x05, i), candsData)), candsData)
                let next := dataEnd
                let remaining := sub(n, i)
                let later := lt(0x01, remaining)
                isLast := iszero(later)
                if later {
                    next := add(calldataload(add(shl(0x05, add(0x01, i)), candsData)), candsData)
                }
                let len := sub(next, start)
                callData := mload(0x40)
                let dst := add(0x84, callData)
                calldatacopy(dst, start, len)
                mstore(add(0x64, callData), calldataload(add(shl(0x05, i), targetsData)))
                mstore(add(0x44, callData), token)
                mstore(add(0x24, callData), 0x60)
                mstore(add(0x04, callData), _EXECUTE_SELECTED_SELECTOR)
                mstore(callData, add(0x64, len))
                mstore(0x40, add(dst, len))

                gasLimit := gas()
                if later {
                    // Reserve every remaining trial's cap plus `_SELECT_OVERHEAD_GAS` of loop
                    // overhead before capping this trial. The `gasCap/63` term covers EIP-150's
                    // retained sixty-fourth on the final uncapped call: `C + floor(C/63)` forwards
                    // exactly `C`. Capped trials need no retention term because `remaining >= 2`
                    // makes 63/64 of `gasLimit` exceed `gasCap`. The check re-runs before every
                    // capped trial and reverts if the reserve no longer fits. The division in the
                    // first test cannot overflow and passing it bounds `totalCap` by `gasLimit`,
                    // so the `mul` cannot overflow either.
                    let totalCap := mul(gasCap, remaining)
                    if or(
                        or(iszero(gasCap), gt(gasCap, div(gasLimit, remaining))),
                        lt(gasLimit, add(add(totalCap, div(gasCap, 0x3f)), _SELECT_OVERHEAD_GAS))
                    ) {
                        revert(0x00, 0x00)
                    }
                    gasLimit := gasCap
                }
            }

            if (_setOperatorAndTryCall(address(this), gasLimit, callData, _EXECUTE_SELECTED_SELECTOR, _executeSelected))
            {
                break;
            }
            if (isLast) {
                // Copy final-trial returndata to `[ptr, ptr + returndatasize())` and bubble it unchanged.
                // The temporary free-memory buffer cannot cross back into Solidity because this path reverts.
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
                tooShort := shr(0xe0, data.length)
                data.length := mul(data.length, iszero(tooShort))
            }
            // Not `FastLogic.or`: `_dispatch` must not run on the cleared length.
            if (tooShort || !_dispatch(i, action, data, noSlippage)) {
                revertActionInvalid(i, action, data);
            }
        }
    }
}
