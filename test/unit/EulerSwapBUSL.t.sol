// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity ^0.8.24;

import {Test} from "@forge-std/Test.sol";
import {console} from "@forge-std/console.sol";
import {IEulerSwap} from "@eulerswap/interfaces/IEulerSwap.sol";
import {CurveLib} from "src/core/EulerSwapBUSL.sol";
import {CurveLib as CurveLibReference} from "@eulerswap/libraries/CurveLib.sol";

contract CurveLibTest is Test {
    function test_fInverse() public pure {
        // Params
        uint256 px = 1e18;
        uint256 py = 1e18;
        uint256 x0 = 1e14;
        uint256 y0 = 1e14;
        uint256 cx = 1e18;

        // Use CurveLib.f to get a valid y
        uint256 x = 1;
        console.log("x    ", x);
        uint256 y = CurveLib.f(x, px, py, x0, y0, cx);
        console.log("y    ", y);
        uint256 xCalc = CurveLib.fInverse(y, px, py, x0, y0, cx);
        console.log("xCalc", xCalc);
        uint256 yCalc = CurveLib.f(xCalc, px, py, x0, y0, cx);
        console.log("yCalc", yCalc);
    }

    function test_fuzzF(uint256 x, uint256 px, uint256 py, uint256 x0, uint256 y0, uint256 cx, uint256 cy) public pure {
        // Params
        px = bound(px, 1, 1e25);
        py = bound(py, 1, 1e25);
        x0 = bound(x0, 0, 1e28);
        y0 = bound(y0, 0, 1e28);
        cx = bound(cx, 0, 1e18);
        cy = bound(cy, 0, 1e18);
        console.log("px", px);
        console.log("py", py);
        console.log("x0", x0);
        console.log("y0", y0);
        console.log("cx", cx);
        console.log("cy", cy);

        IEulerSwap.Params memory p = IEulerSwap.Params({
            vault0: address(0),
            vault1: address(0),
            eulerAccount: address(0),
            equilibriumReserve0: uint112(x0),
            equilibriumReserve1: uint112(y0),
            priceX: px,
            priceY: py,
            concentrationX: cx,
            concentrationY: cy,
            fee: 0,
            protocolFee: 0,
            protocolFeeRecipient: address(0)
        });

        x = bound(x, 0, x0);
        console.log("x    ", x);

        uint256 yBin = binSearchY(x, x0, y0, px, py, cx, cy);
        uint256 yCalc = CurveLib.f(x, px, py, x0, y0, cx);
        console.log("yBin ", yBin);
        console.log("yCalc", yCalc);

        vm.assume(yBin >> 112 == 0);

        assertGe(yCalc, yBin);

        assertTrue(CurveLib.verify(x, yBin, x0, y0, px, py, cx, cy), "binary search verification failed");
        if (yBin != 0) {
            assertFalse(CurveLib.verify(x, yBin - 1, x0, y0, px, py, cx, cy), "binary search not smallest");
        }
        assertTrue(CurveLib.verify(x, yCalc, x0, y0, px, py, cx, cy), "verification failed");

        // `yCalc` is computed with only a single division, so it can be off by at most 1 wei
        //assertLe(yCalc - yBin, 1, "y margin of error");

        if (x != 0) {
            // the reference implementation of `f` sometimes returns 0, even though it's not a valid input
            uint256 yRef = CurveLibReference.f(x, px, py, x0, y0, cx);
            console.log("yRef ", yRef);
            assertLe(yCalc, yRef);

            // the reference implementation of `verify` does not handle zero as an input correctly
            if (yCalc == 0) {
                yCalc++;
            }
            assertTrue(CurveLibReference.verify(p, x, yCalc), "reference verification failed");
            if (yBin == 0) {
                yBin++;
            }
            assertTrue(CurveLibReference.verify(p, x, yBin), "binary search reference verification failed");
        }
    }

    function test_fuzzFInverse(uint256 x, uint256 px, uint256 py, uint256 x0, uint256 y0, uint256 cx, uint256 cy)
        public
        pure
    {
        // Params
        px = bound(px, 1, 1e25);
        py = bound(py, 1, 1e25);
        x0 = bound(x0, 0, 1e28);
        y0 = bound(y0, 0, 1e28);
        cx = bound(cx, 0, 1e18);
        cy = bound(cy, 0, 1e18);
        console.log("px", px);
        console.log("py", py);
        console.log("x0", x0);
        console.log("y0", y0);
        console.log("cx", cx);
        console.log("cy", cy);

        IEulerSwap.Params memory p = IEulerSwap.Params({
            vault0: address(0),
            vault1: address(0),
            eulerAccount: address(0),
            equilibriumReserve0: uint112(x0),
            equilibriumReserve1: uint112(y0),
            priceX: px,
            priceY: py,
            concentrationX: cx,
            concentrationY: cy,
            fee: 0,
            protocolFee: 0,
            protocolFeeRecipient: address(0)
        });

        x = bound(x, 0, x0);

        uint256 y = binSearchY(x, x0, y0, px, py, cx, cy);

        vm.assume(y >> 112 == 0);

        console.log("x    ", x);
        console.log("y    ", y);

        uint256 xBin = binSearchX(y, x0, y0, px, py, cx, cy);
        console.log("xBin ", xBin);

        vm.assume(xBin >> 112 == 0);

        uint256 xCalc = CurveLib.fInverse(y, px, py, x0, y0, cx);
        console.log("xCalc", xCalc);
        assertGe(xCalc, xBin);

        assertTrue(CurveLib.verify(xBin, y, x0, y0, px, py, cx, cy), "binary search verification failed");
        if (xBin != 0) {
            assertFalse(CurveLib.verify(xBin - 1, y, x0, y0, px, py, cx, cy), "binary search not smallest");
        }
        assertTrue(CurveLib.verify(xCalc, y, x0, y0, px, py, cx, cy), "verification failed");

        uint256 xBinRef = binSearchXRef(y, x0, y0, px, py, cx);
        console.log("xBinRef", xBinRef);
        if (xCalc == 0) {
            assertLe(xBinRef, 2);
        } else {
            assertLe(xCalc - xBinRef, 3);
        }
        // the computation of `xCalc` involves two divisions with rounding. because of the
        // double rounding, we can be off by up to 2 wei
        //assertLe(xCalc - xBin, 2, "x margin of error");

        if (y != 0) {
            // the reference implementation of `fInverse` sometimes returns 0, even though it's not a valid input
            if (cx != 0) {
                // the reference implementation of `fInverse` does not correctly handle `cx == 0`
                uint256 xRef = CurveLibReference.fInverse(y, px, py, x0, y0, cx);
                console.log("xRef ", xRef);
                if (xCalc > xRef) {
                    // due to double rounding in the optimized implementation, it is very rarely 1 wei more than the reference
                    assertEq(xCalc, xRef + 1);
                } else {
                    assertLe(xCalc, xRef);
                }
            }

            // the reference implementation of `verify` does not handle zero as an input correctly
            if (xCalc == 0) {
                xCalc++;
            }
            assertTrue(CurveLibReference.verify(p, xCalc, y), "reference verification failed");
            if (xBin == 0) {
                xBin++;
            }
            assertTrue(CurveLibReference.verify(p, xBin, y), "reference verification failed");
        }
    }

    function test_fuzzFEquillibrium(uint256 px, uint256 py, uint256 x0, uint256 y0, uint256 cx, uint256 cy)
        public
        pure
    {
        // Params
        px = bound(px, 1, 1e25);
        py = bound(py, 1, 1e25);
        x0 = bound(x0, 0, 1e28);
        y0 = bound(y0, 0, 1e28);
        cx = bound(cx, 0, 1e18);
        cy = bound(cy, 0, 1e18);

        uint256 y = CurveLib.f(x0, px, py, x0, y0, cx);
        uint256 x = CurveLib.f(y0, py, px, y0, x0, cy);

        assertEq(y, y0);
        assertEq(x, x0);
    }

    function binSearchX(uint256 newReserve1, uint256 equilibriumReserve0, uint256 equilibriumReserve1, uint256 priceX, uint256 priceY, uint256 concentrationX, uint256 concentrationY) internal pure returns (uint256) {
        uint256 xMax = 1 << 112;
        uint256 xMin = 0;
        while (xMin < xMax) {
            uint256 xMid = (xMin + xMax) / 2;
            if (CurveLib.verify(xMid, newReserve1, equilibriumReserve0, equilibriumReserve1, priceX, priceY, concentrationX, concentrationY)) {
                xMax = xMid;
            } else {
                xMin = xMid + 1;
            }
        }
        return xMax;
    }

    function binSearchY(uint256 newReserve0, uint256 equilibriumReserve0, uint256 equilibriumReserve1, uint256 priceX, uint256 priceY, uint256 concentrationX, uint256 concentrationY) internal pure returns (uint256) {
        uint256 yMax = 1 << 112;
        uint256 yMin = 0;
        while (yMin < yMax) {
            uint256 yMid = (yMin + yMax) / 2;
            if (CurveLib.verify(newReserve0, yMid, equilibriumReserve0, equilibriumReserve1, priceX, priceY, concentrationX, concentrationY)) {
                yMax = yMid;
            } else {
                yMin = yMid + 1;
            }
        }
        return yMax;
    }

    function binSearchXRef(uint256 newReserve1, uint256 equilibriumReserve0, uint256 equilibriumReserve1, uint256 priceX, uint256 priceY, uint256 concentrationX)
        internal
        pure
        returns (uint256)
    {
        uint256 xMax = equilibriumReserve0;
        uint256 xMin = 1;
        while (xMin < xMax) {
            uint256 xMid = (xMin + xMax) / 2;
            uint256 fxMid =
                CurveLib.f(xMid, priceX, priceY, equilibriumReserve0, equilibriumReserve1, concentrationX);
            if (newReserve1 >= fxMid) {
                xMax = xMid;
            } else {
                xMin = xMid + 1;
            }
        }
        if (
            newReserve1
                < CurveLib.f(xMin, priceX, priceY, equilibriumReserve0, equilibriumReserve1, concentrationX)
        ) {
            xMin += 1;
        }
        return xMin;
    }
}
