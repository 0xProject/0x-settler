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

    function _balanceOfOrZero(IERC20 token) private view returns (uint256) {
        return address(token) == address(0) ? 0 : token.fastBalanceOf(address(this));
    }

    function _executeSelected(bytes calldata data) private returns (bytes memory) {
        bytes[] calldata actions;
        IERC20 token;
        uint256 minOut;
        // Read the trusted callback body without writing memory:
        // `[0x00 actions=0x60][0x20 token][0x40 minOut][0x60 actions length][0x80 offsets/frames]`.
        // `select` built this payload with the fixed `0x60` head, a verified-clean `token`, and
        // copied only this frame. Forward reads past the trial calldata return zero; a failing action
        // reverts only this trial.
        assembly ("memory-safe") {
            actions.length := calldataload(add(0x60, data.offset))
            actions.offset := add(0x80, data.offset)
            token := calldataload(add(0x20, data.offset))
            minOut := calldataload(add(0x40, data.offset))
        }
        uint256 balBefore = _balanceOfOrZero(token);
        _runActions(actions);
        uint256 score = _balanceOfOrZero(token) - balBefore;
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
        // Validate the canonical outer SELECT head and candidate-frame table without writing memory:
        // `[0x00 gasCap][0x20 token][0x40 targets=0x80][0x60 candidates=0xa0+0x20*n]`, then
        // `[0x80 n][0xa0 targets][candidates length/table/frames]`. Dirty upper bits in `token` throw.
        assembly ("memory-safe") {
            let dataStart := data.offset
            dataEnd := add(dataStart, data.length)
            let err := or(lt(dataEnd, dataStart), gt(dataEnd, calldatasize()))
            gasCap := calldataload(dataStart)
            token := calldataload(add(0x20, dataStart))
            err := or(shr(0xa0, token), err)
            n := calldataload(add(dataStart, 0x80))
            let tableSize := shl(0x05, n)
            let candidatesOffset := add(0xa0, tableSize)
            let base := add(dataStart, candidatesOffset)
            candsData := add(0x20, base)
            err := or(xor(0x80, calldataload(add(0x40, dataStart))), err)
            err := or(xor(calldataload(add(0x60, dataStart)), candidatesOffset), err)
            err := or(or(iszero(n), gt(n, div(data.length, 0x20))), err)
            err := or(xor(calldataload(base), n), err)
            err := or(gt(add(candsData, tableSize), dataEnd), err)
            // The first frame starts at the offset-table end, so every byte belongs to the head,
            // a table, or exactly one frame. Strict ordering then bounds each later start below;
            // `maxOffset` bounds it above.
            err := or(xor(calldataload(candsData), tableSize), err)

            // Entry zero is already pinned to `tableSize` and bounded by the table-fit check above.
            let previous := tableSize
            let maxOffset := sub(dataEnd, candsData)
            for { let i := 0x01 } and(iszero(err), lt(i, n)) { i := add(0x01, i) } {
                let offset := calldataload(add(candsData, shl(0x05, i)))
                err := or(or(gt(offset, maxOffset), iszero(gt(offset, previous))), err)
                previous := offset
            }
            if err { revert(0x00, 0x00) }

            targetsData := add(dataStart, 0xa0)
        }

        for (uint256 i; i < n; i = i.unsafeInc()) {
            bytes memory callData;
            uint256 gasLimit;
            bool isLast;
            // Allocate one callback buffer per trial. Memory layout:
            // `[0x00 len=0x64+frame][0x20 selector][0x24 actions=0x60][0x44 token]`
            // `[0x64 target][0x84 frame]`. Reserve through the rounded frame end
            // before the trial call crosses into Solidity.
            assembly ("memory-safe") {
                let start := add(candsData, calldataload(add(candsData, shl(0x05, i))))
                let next := dataEnd
                let remaining := sub(n, i)
                let later := sub(remaining, 0x01)
                isLast := iszero(later)
                if later {
                    next := add(candsData, calldataload(add(candsData, shl(0x05, add(i, 0x01)))))
                }
                let len := sub(next, start)
                callData := mload(0x40)
                let cd := add(0x20, callData)
                mstore(callData, add(0x64, len))
                mstore(cd, shl(0xe0, _EXECUTE_SELECTED_SELECTOR))
                mstore(add(0x04, cd), 0x60)
                mstore(add(0x24, cd), token)
                let dst := add(0x64, cd)
                calldatacopy(dst, start, len)
                mstore(add(0x44, cd), calldataload(add(targetsData, shl(0x05, i))))
                mstore(0x40, and(add(add(dst, len), 0x1f), not(0x1f)))

                gasLimit := gas()
                if later {
                    // Reserve every remaining trial's cap plus loop overhead before capping this
                    // trial. The `gasCap/63` term covers EIP-150's retained sixty-fourth on the
                    // final uncapped call: `C + floor(C/63)` forwards exactly `C`. Capped trials
                    // need no retention term because `remaining >= 2` makes 63/64 of `gasLimit`
                    // exceed `gasCap`. The check re-runs before every capped trial and fails closed.
                    let totalCap := mul(gasCap, remaining)
                    if or(
                        or(iszero(gasCap), gt(gasCap, div(gasLimit, remaining))),
                        lt(gasLimit, add(add(totalCap, div(gasCap, 0x3f)), 0x10000))
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
        // A zeroed slippage struct makes a nested `CHECK_SLIPPAGE` a no-op (it takes the
        // `minAmountOut == 0 && buyToken == 0` early return and transfers nothing), except under a
        // mandatory slippage check, where it reverts only the trial.
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
                tooShort := iszero(iszero(shr(0xe0, data.length)))
                data.length := mul(data.length, iszero(tooShort))
            }
            // Not `FastLogic.or`: `_dispatch` must not run on the cleared length.
            if (tooShort || !_dispatch(i, action, data, noSlippage)) {
                revertActionInvalid(i, action, data);
            }
        }
    }
}
