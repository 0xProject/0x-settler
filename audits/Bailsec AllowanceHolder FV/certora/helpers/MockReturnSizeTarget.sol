// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

// models a `maybeERC20` target whose `balanceOf(address)` returns a CONTROLLABLE 
// number of returndata bytes (and can either succeed or revert), so a
// rule can exercise the REAL CheckCall returndata-size semantics across the
// 32-byte boundary.

contract MockReturnSizeTarget {
    uint256 private retLen;
    bool private callSucceeds;

    function setRetLen(uint256 _retLen) external {
        retLen = _retLen;
    }

    function setCallSucceeds(bool _callSucceeds) external {
        callSucceeds = _callSucceeds;
    }

    // balanceOf(address): on success returns exactly `retLen` bytes of returndata;
    // otherwise reverts with `retLen` bytes. Reached only via the staticcall inside
    // CheckCall.checkCallSolidity, hence `view`.
    function balanceOf(address) external view {
        uint256 len = retLen;
        bool ok = callSucceeds;
        assembly ("memory-safe") {
            switch len
            case 0x00 {
                if ok { return(0x00, 0x00) }
                revert(0x00, 0x00)
            }
            case 0x01 {
                if ok { return(0x00, 0x01) }
                revert(0x00, 0x01)
            }
            case 0x1f {
                if ok { return(0x00, 0x1f) }
                revert(0x00, 0x1f)
            }
            case 0x20 {
                if ok { return(0x00, 0x20) }
                revert(0x00, 0x20)
            }
            default {
                if ok { return(0x00, 0x21) }
                revert(0x00, 0x21)
            }
        }
    }
}
