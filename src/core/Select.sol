// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SettlerSwapAbstract} from "../SettlerAbstract.sol";
import {CalldataDecoder} from "../SettlerBase.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {TransientStorage} from "./Permit2Payment.sol";
import {revertActionInvalid} from "./SettlerErrors.sol";

/// @notice Ordered candidate-route selection by revertable self-calls.
abstract contract Select is SettlerSwapAbstract {
    using SafeTransferLib for IERC20;
    using UnsafeMath for uint256;
    using CalldataDecoder for bytes[];

    // selector for `executeSelected(bytes[],address,uint256)`
    uint32 private constant _SELECT_CALLBACK_SELECTOR = 0x1bbdbb47;

    function _balanceOfOrZero(IERC20 token) private view returns (uint256) {
        return address(token) == address(0) ? 0 : token.fastBalanceOf(address(this));
    }

    function _tryCall(bytes memory data, uint256 gasLimit) private returns (bool success) {
        TransientStorage.setOperatorAndCallback(address(this), _SELECT_CALLBACK_SELECTOR, _executeSelected);
        // Avoid copying returndata so the caller can copy only the final failed trial.
        assembly ("memory-safe") {
            success := call(gasLimit, address(), 0x00, add(0x20, data), mload(data), 0x00, 0x00)
        }
        if (success) {
            TransientStorage.checkSpentOperatorAndCallback();
        } else {
            TransientStorage.clearOperatorAndCallback();
        }
    }

    function _executeSelected(bytes calldata data) private returns (bytes memory) {
        bytes[] calldata actions;
        IERC20 token;
        uint256 minOut;
        // Read the trusted callback body without writing memory:
        // `[0x00 actions=0x60][0x20 token][0x40 minOut][0x60 actions length][0x80 offsets/frames]`.
        // `_select` built this payload with the fixed `0x60` head, cleared `token`'s upper bits, and
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
        assembly ("memory-safe") {
            return(0x00, 0x00)
        }
    }

    function _select(bytes calldata data) internal {
        uint256 gasCap_;
        address token_;
        uint256 targetsData_;
        uint256 candsData_;
        uint256 dataEnd_;
        uint256 n_;
        // Validate the canonical outer SELECT head and candidate-frame table without writing memory:
        // `[0x00 gasCap][0x20 token][0x40 targets=0x80][0x60 candidates=0xa0+0x20*n]`, then
        // `[0x80 n][0xa0 targets][candidates length/table/frames]`. Mask token at the calldata boundary.
        assembly ("memory-safe") {
            let dataStart := data.offset
            let dataEnd := add(dataStart, data.length)
            let err := or(lt(dataEnd, dataStart), gt(dataEnd, calldatasize()))
            gasCap_ := calldataload(dataStart)
            token_ := and(0xffffffffffffffffffffffffffffffffffffffff, calldataload(add(0x20, dataStart)))
            let n := calldataload(add(dataStart, 0x80))
            let tableSize := shl(0x05, n)
            let candidatesOffset := add(0xa0, tableSize)
            let base := add(dataStart, candidatesOffset)
            let candsData := add(0x20, base)
            err := or(err, iszero(eq(calldataload(add(0x40, dataStart)), 0x80)))
            err := or(err, iszero(eq(calldataload(add(0x60, dataStart)), candidatesOffset)))
            err := or(err, or(iszero(n), gt(n, div(data.length, 0x20))))
            err := or(err, iszero(eq(calldataload(base), n)))
            err := or(err, gt(add(candsData, tableSize), dataEnd))
            // The first frame starts at the offset-table end, so every byte belongs to the head,
            // a table, or exactly one frame. Strict ordering then bounds each later start below;
            // `maxOffset` bounds it above.
            err := or(err, iszero(eq(calldataload(candsData), tableSize)))

            // Entry zero is already pinned to `tableSize` and bounded by the table-fit check above.
            let previous := tableSize
            let maxOffset := sub(dataEnd, candsData)
            for { let i := 0x01 } and(iszero(err), lt(i, n)) { i := add(0x01, i) } {
                let offset := calldataload(add(candsData, shl(0x05, i)))
                err := or(err, or(gt(offset, maxOffset), iszero(gt(offset, previous))))
                previous := offset
            }
            if err { revert(0x00, 0x00) }

            targetsData_ := add(dataStart, 0xa0)
            candsData_ := candsData
            dataEnd_ := dataEnd
            n_ := n
        }

        for (uint256 i; i < n_; i = i.unsafeInc()) {
            bytes memory callData;
            uint256 gasLimit;
            bool isLast;
            // Allocate one callback buffer per trial. Memory layout:
            // `[0x00 len=0x84+frame][0x20 selector][0x24 actions=0x80][0x44 token]`
            // `[0x64 target][0x84 frame]`. Reserve through the rounded frame end
            // before `_tryCall` crosses into Solidity.
            assembly ("memory-safe") {
                let start := add(candsData_, calldataload(add(candsData_, shl(0x05, i))))
                let next := dataEnd_
                let remaining := sub(n_, i)
                let later := sub(remaining, 0x01)
                isLast := iszero(later)
                if later {
                    next := add(candsData_, calldataload(add(candsData_, shl(0x05, add(i, 0x01)))))
                }
                let len := sub(next, start)
                callData := mload(0x40)
                let cd := add(0x20, callData)
                mstore(callData, add(0x64, len))
                mstore(cd, shl(0xe0, _SELECT_CALLBACK_SELECTOR))
                mstore(add(0x04, cd), 0x60)
                mstore(add(0x24, cd), token_)
                let dst := add(0x64, cd)
                calldatacopy(dst, start, len)
                mstore(add(0x44, cd), calldataload(add(targetsData_, shl(0x05, i))))
                mstore(0x40, and(add(add(dst, len), 0x1f), not(0x1f)))

                gasLimit := gas()
                if later {
                    // Reserve every remaining trial's cap, EIP-150 63/64 headroom (1/32 is a safe
                    // overestimate), and loop overhead, so no trial can starve a later one.
                    let totalCap := mul(gasCap_, remaining)
                    if or(
                        or(iszero(gasCap_), gt(gasCap_, div(gasLimit, remaining))),
                        lt(gasLimit, add(add(totalCap, shr(0x05, totalCap)), 0x10000))
                    ) {
                        revert(0x00, 0x00)
                    }
                    gasLimit := gasCap_
                }
            }

            if (_tryCall(callData, gasLimit)) {
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
        AllowedSlippage memory noSlippage;
        uint256 it;
        assembly ("memory-safe") {
            it := actions.offset
        }
        for (uint256 i; i < actions.length; (i, it) = (i.unsafeInc(), it.unsafeAdd(32))) {
            (uint256 action, bytes calldata data) = actions.decodeCall(it);
            bool tooShort;
            // Clear a length that wrapped in `decodeCall`'s selector slice.
            assembly ("memory-safe") {
                tooShort := gt(data.length, not(0x04))
                data.length := mul(data.length, iszero(tooShort))
            }
            // Not `FastLogic.or`: `_dispatch` must not run on the cleared length.
            if (tooShort || !_dispatch(i, action, data, noSlippage)) {
                revertActionInvalid(i, action, data);
            }
        }
    }
}
