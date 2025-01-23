// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Panic} from "src/utils/Panic.sol";

library SlowMath {
    function fullMul(uint256 a, uint256 b) internal pure returns (uint256 r0, uint256 r1) {
        uint256 mask = 0xffffffffffffffffffffffffffffffff;
        uint256 shift = 0x80;
        // Split in groups of 128 bit
        uint256 a0 = a & mask;
        uint256 a1 = a >> shift;
        uint256 b0 = b & mask;
        uint256 b1 = b >> shift;

        // Compute 256 bit intermediate products
        uint256 i00 = a0 * b0;
        uint256 i01 = a0 * b1;
        uint256 i10 = a1 * b0;
        uint256 i11 = a1 * b1;

        // Split results in (shifted) groups of 128 bit
        uint256 i010 = i01 << shift;
        uint256 i011 = i01 >> shift;
        uint256 i100 = i10 << shift;
        uint256 i101 = i10 >> shift;

        // Add all intermediate terms, taking care of overflow
        r0 = i00;
        r1 = i11 + i011 + i101;
        unchecked {
            r0 += i010;
        }
        if (r0 < i010) {
            r1 += 1;
        }
        unchecked {
            r0 += i100;
        }
        if (r0 < i100) {
            r1 += 1;
        }
    }

    function fullMul(uint256 aLo, uint256 aHi, uint256 bLo, uint256 bHi)
        internal
        pure
        returns (uint256 r0, uint256 r1)
    {
        (r0, r1) = fullMul(aLo, bLo);
        unchecked {
            r1 += aHi * bLo;
            r1 += bHi * aLo;
        }
    }

    function fullAdd(uint256 lLo, uint256 lHi, uint256 rLo, uint256 rHi)
        internal
        pure
        returns (uint256 lo, uint256 hi)
    {
        unchecked {
            lo = lLo + rLo;
        }
        unchecked {
            hi = lHi + rHi;
        }
        if (lo < lLo) {
            unchecked {
                hi++;
            }
        }
    }

    function fullSub(uint256 lLo, uint256 lHi, uint256 rLo, uint256 rHi)
        internal
        pure
        returns (uint256 lo, uint256 hi)
    {
        // we don't check that l >= r; that is assumed
        unchecked {
            lo = lLo - rLo;
        }
        unchecked {
            // can't underflow
            hi = lHi - rHi;
        }
        if (lo > lLo) {
            unchecked {
                // can't underflow
                hi--;
            }
        }
    }

    function _div256(uint256 a) private pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := add(div(sub(0x00, a), a), 0x01)
        }
    }

    function _mod256(uint256 a) private pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := mod(sub(0x00, a), a)
        }
    }

    function fullDiv(uint256 n0, uint256 n1, uint256 d) internal pure returns (uint256, uint256) {
        // Stolen from https://2π.com/17/512-bit-division/
        if (d == 0) {
            Panic.panic(Panic.DIVISION_BY_ZERO);
        }
        if (d == 1) {
            return (n0, n1);
        }
        uint256 q = _div256(d);
        uint256 r = _mod256(d);
        uint256 x0;
        uint256 x1;
        for (uint256 i; i < 1024; i++) {
            if (n1 == 0) {
                return fullAdd(x0, x1, n0 / d, 0);
            }
            (uint256 t0, uint256 t1) = fullMul(n1, q);
            (x0, x1) = fullAdd(x0, x1, t0, t1);
            (t0, t1) = fullMul(n1, r);
            (n0, n1) = fullAdd(t0, t1, n0, 0);
        }
        revert("Not converged");
    }
}
