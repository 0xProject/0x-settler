// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity ^0.8.24;

import {Test} from "@forge-std/Test.sol";
import {console} from "@forge-std/console.sol";
import {IEulerSwap} from "@eulerswap/interfaces/IEulerSwap.sol";
import {CurveLib} from "src/core/EulerSwapBUSL.sol";
import {CurveLib as CurveLibReference} from "@eulerswap/libraries/CurveLib.sol";
import {Panic} from "src/utils/Panic.sol";

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

    function test_validation() public view {
        uint112 equilibriumReserve0 = 0x0000000000000000000000000000000000000000000000807101361354552724;
        uint112 equilibriumReserve1 = 0x0000000000000000000000000000000000000000000000dad81da87296f77c31;
        uint256 priceX = 0x00000000000000000000000000000000000000000000000010bf9f38b14a3e00;
        uint256 priceY = 0x0000000000000000000000000000000000000000000000000de0b6b3a7640000;
        uint256 concentrationX = 0x0000000000000000000000000000000000000000000000000de0893a1f26e000;
        uint256 concentrationY = 0x0000000000000000000000000000000000000000000000000de0893a1f26e000;
        uint256 fee = 0x00000000000000000000000000000000000000000000000000005af3107a4000;
        uint256 reserve0 = 1056676627945319924227;
        uint256 reserve1 = 5621243280384200185656;

        bool zeroForOne = true; // this is backwards of what it was in the test; see commented-out `referenceAmountOut`
        uint256 amountIn = 10000000000000000;
        amountIn -= amountIn * fee / 1e18;
        uint256 referenceAmountOut = 12069806184391508;
        //uint256 referenceAmountOut = 8283480201573472;

        uint256 amountOut;
        if (zeroForOne) {
            // swap X in and Y out
            uint256 xNew = reserve0 + amountIn;
            uint256 yNew = xNew <= equilibriumReserve0
                // remain on f()
                ? CurveLib.saturatingF(xNew, priceX, priceY, equilibriumReserve0, equilibriumReserve1, concentrationX)
                // move to g()
                : CurveLib.fInverse(xNew, priceY, priceX, equilibriumReserve1, equilibriumReserve0, concentrationY);
            if (yNew == 0) {
                yNew++;
            }
            amountOut = reserve1 - yNew;
        } else {
            uint256 yNew = reserve1 + amountIn;
            uint256 xNew = yNew <= equilibriumReserve1
                // remain on g()
                ? CurveLib.saturatingF(yNew, priceY, priceX, equilibriumReserve1, equilibriumReserve0, concentrationY)
                // move to f()
                : CurveLib.fInverse(yNew, priceX, priceY, equilibriumReserve0, equilibriumReserve1, concentrationX);
            if (xNew == 0) {
                xNew++;
            }
            amountOut = reserve0 - xNew;
        }
        assertEq(amountOut, referenceAmountOut);
    }

    function test_extremeF0(uint256 px, uint256 py, uint256 x0, uint256 y0, uint256 cx) public view {
        uint256 x = 0;
        x0 = bound(x0, 0, type(uint112).max);
        cx = bound(cx, 0, 1e18 - 1);

        try this.f(x, px, py, x0, y0, cx) returns (uint256) {
            revert("succeeded unexpectedly");
        } catch {
            assertEq(CurveLib.saturatingF(x, px, py, x0, y0, cx), type(uint256).max);
        }
    }

    function test_extremeF1(uint256 px, uint256 py, uint256 y0) public pure {
        uint256 x = 0;
        uint256 x0 = 0;
        uint256 cx = 1e18;

        assertEq(CurveLib.f(x, px, py, x0, y0, cx), CurveLib.saturatingF(x, px, py, x0, y0, cx));
    }

    function test_fuzzF(uint256 x, uint256 px, uint256 py, uint256 x0, uint256 y0, uint256 cx, uint256 cy)
        public
        pure
    {
        // Params
        px = bound(px, 1, 1e25);
        py = bound(py, 1, 1e25);
        cx = bound(cx, 0, 1e18);
        cy = bound(cy, 0, 1e18);
        if (cx == 1e18) {
            x0 = bound(x0, 0, type(uint112).max);
        } else {
            x0 = bound(x0, 1, type(uint112).max);
        }
        if (cy == 1e18) {
            y0 = bound(y0, 0, type(uint112).max);
        } else {
            y0 = bound(y0, 1, type(uint112).max);
        }
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

        if (cx == 1e18) {
            x = bound(x, 0, x0);
        } else {
            x = bound(x, 1, x0);
        }
        console.log("x    ", x);

        uint256 yBin = binSearchY(x, x0, y0, px, py, cx, cy);
        console.log("yBin ", yBin);

        vm.assume(yBin >> 112 == 0);

        assertTrue(CurveLib.verify(x, yBin, x0, y0, px, py, cx, cy), "binary search verification failed");
        if (yBin != 0) {
            assertFalse(CurveLib.verify(x, yBin - 1, x0, y0, px, py, cx, cy), "binary search not smallest");
        }

        uint256 yCalc = CurveLib.f(x, px, py, x0, y0, cx);
        console.log("yCalc", yCalc);
        assertLe(y0, yCalc, "out of range (violates natspec)");

        assertEq(yCalc, yBin, "CurveLib.f solution not exact");

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
        }
    }

    function test_fuzzSaturatingF(uint256 x, uint256 px, uint256 py, uint256 x0, uint256 y0, uint256 cx) public view {
        // Params
        px = bound(px, 1, 1e25);
        py = bound(py, 1, 1e25);
        cx = bound(cx, 0, 1e18);
        if (cx == 1e18) {
            x0 = bound(x0, 0, type(uint112).max);
        } else {
            x0 = bound(x0, 1, type(uint112).max);
        }
        console.log("px", px);
        console.log("py", py);
        console.log("x0", x0);
        console.log("y0", y0);
        console.log("cx", cx);

        if (cx == 1e18) {
            x = bound(x, 0, x0);
        } else {
            x = bound(x, 1, x0);
        }

        // ugh. stack-too-deep
        bool success;
        bytes memory returndata;
        uint256 expected;
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, 0x5eb69a95) // this.f.selector
            mstore(add(0x20, ptr), x)
            mstore(add(0x40, ptr), px)
            mstore(add(0x60, ptr), py)
            mstore(add(0x80, ptr), x0)
            mstore(add(0xa0, ptr), y0)
            mstore(add(0xc0, ptr), cx)
            success := staticcall(gas(), address(), add(0x1c, ptr), 0xc4, 0x00, 0x20)
            switch success
            case 0 {
                returndata := ptr
                mstore(returndata, returndatasize())
                returndatacopy(add(0x20, returndata), 0x00, returndatasize())
                mstore(0x40, add(returndatasize(), add(0x20, returndata)))
            }
            default { expected := mload(0x00) }
        }
        if (success) {
            uint256 actual = CurveLib.saturatingF(x, px, py, x0, y0, cx);
            assertEq(expected, actual);
        } else {
            assertEq(returndata.length, 36);
            assertEq(uint32(bytes4(returndata)), 0x4e487b71);
            uint256 arg;
            assembly ("memory-safe") {
                arg := mload(add(0x24, returndata))
            }
            assertTrue(arg == Panic.ARITHMETIC_OVERFLOW || arg == Panic.DIVISION_BY_ZERO);
            uint256 actual = CurveLib.saturatingF(x, px, py, x0, y0, cx);
            assertEq(actual, type(uint256).max);
        }
    }

    function binSearchY(
        uint256 newReserve0,
        uint256 equilibriumReserve0,
        uint256 equilibriumReserve1,
        uint256 priceX,
        uint256 priceY,
        uint256 concentrationX,
        uint256 concentrationY
    ) internal pure returns (uint256) {
        uint256 yMax = 1 << 112;
        uint256 yMin = 0;
        while (yMin < yMax) {
            uint256 yMid = (yMin + yMax) / 2;
            if (
                CurveLib.verify(
                    newReserve0,
                    yMid,
                    equilibriumReserve0,
                    equilibriumReserve1,
                    priceX,
                    priceY,
                    concentrationX,
                    concentrationY
                )
            ) {
                yMax = yMid;
            } else {
                yMin = yMid + 1;
            }
        }
        return yMax;
    }

    function f(uint256 x, uint256 px, uint256 py, uint256 x0, uint256 y0, uint256 cx) external pure returns (uint256) {
        return CurveLib.f(x, px, py, x0, y0, cx);
    }

    function test_fuzzFInverse(uint256 x, uint256 px, uint256 py, uint256 x0, uint256 y0, uint256 cx, uint256 cy)
        public
        view
    {
        // Params
        px = bound(px, 1, 1e25);
        py = bound(py, 1, 1e25);
        cx = bound(cx, 0, 1e18);
        cy = bound(cy, 0, 1e18);
        if (cx == 1e18) {
            x0 = bound(x0, 0, type(uint112).max);
        } else {
            x0 = bound(x0, 1, type(uint112).max);
        }
        if (cy == 1e18) {
            y0 = bound(y0, 0, type(uint112).max);
        } else {
            y0 = bound(y0, 1, type(uint112).max);
        }
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

        if (cx == 1e18) {
            x = bound(x, 0, x0);
        } else {
            x = bound(x, 1, x0);
        }

        uint256 y = binSearchY(x, x0, y0, px, py, cx, cy);

        vm.assume(y >> 112 == 0);

        console.log("x    ", x);
        console.log("y    ", y);

        uint256 xBin = binSearchX(y, x0, y0, px, py, cx, cy);
        console.log("xBin ", xBin);

        vm.assume(xBin >> 112 == 0);

        uint256 xCalc = CurveLib.fInverse(y, px, py, x0, y0, cx);
        console.log("xCalc", xCalc);
        assertLe(xCalc, x0, "out of range (violates natspec)");
        // double rounding in `fInverse`, compared to the exact computation in `verify` (and
        // consequently `binSearchX`) can result in substantial amounts of error compared to
        // `xBin`. all we can do is assert that the approximate closed-form solution is greater than
        // (valid) the exact solution
        assertGe(xCalc, xBin);
        // the computation of `xCalc` involves four lossy operations with rounding. because we
        // multiply in between, the rounding error may be substantial.
        assertLe(xCalc - xBin, 1, "x margin of error");

        assertTrue(CurveLib.verify(xBin, y, x0, y0, px, py, cx, cy), "binary search verification failed");
        if (xBin != 0) {
            assertFalse(CurveLib.verify(xBin - 1, y, x0, y0, px, py, cx, cy), "binary search not smallest");
        }
        assertTrue(CurveLib.verify(xCalc, y, x0, y0, px, py, cx, cy), "verification failed");

        // work around stack-too-deep
        {
            uint256 xBinRef = type(uint256).max;
            assembly ("memory-safe") {
                let ptr := mload(0x40)
                mstore(ptr, 0xf626f3ed) // this.binSearchXRef.selector
                mstore(add(0x20, ptr), y)
                mcopy(add(0x40, ptr), add(0x60, p), 0x40)
                mcopy(add(0x80, ptr), add(0xa0, p), 0x40)
                mstore(add(0xa0, ptr), mload(add(0xe0, p)))
                switch staticcall(gas(), address(), add(0x1c, ptr), 0xc4, 0x00, 0x40)
                case 0 {
                    if iszero(
                        or(
                            and(eq(0x04, returndatasize()), eq(0x35278d12, shr(0xe0, mload(0x00)))), // CurveLibReference.Overflow.selector
                            and(
                                and(eq(0x24, returndatasize()), eq(0x4e487b71, shr(0xe0, mload(0x00)))), // Panic.selector
                                eq(0x12, mload(0x04))
                            )
                        )
                    ) { revert(0x00, 0x00) }
                }
                default { xBinRef := mload(0x00) }
            }
            console.log("xBinRef", xBinRef);
            if (xBinRef < xBin) {
                assertFalse(CurveLib.verify(xBinRef, y, x0, y0, px, py, cx, cy), "reference quoted better");
            }
        }

        if (y != 0) {
            // the reference implementation of `fInverse` sometimes returns 0, even though it's not a valid input
            if (cx != 0) {
                // the reference implementation of `fInverse` does not correctly handle `cx == 0`
                uint256 xRef = CurveLibReference.fInverse(y, px, py, x0, y0, cx);
                console.log("xRef ", xRef);
                assertLe(xCalc, xRef + 1, "x reference margin of error");
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

    function binSearchX(
        uint256 newReserve1,
        uint256 equilibriumReserve0,
        uint256 equilibriumReserve1,
        uint256 priceX,
        uint256 priceY,
        uint256 concentrationX,
        uint256 concentrationY
    ) internal pure returns (uint256) {
        uint256 xMax = 1 << 112;
        uint256 xMin = 0;
        while (xMin < xMax) {
            uint256 xMid = (xMin + xMax) / 2;
            if (
                CurveLib.verify(
                    xMid,
                    newReserve1,
                    equilibriumReserve0,
                    equilibriumReserve1,
                    priceX,
                    priceY,
                    concentrationX,
                    concentrationY
                )
            ) {
                xMax = xMid;
            } else {
                xMin = xMid + 1;
            }
        }
        return xMax;
    }

    function binSearchXRef(
        uint256 newReserve1,
        uint256 equilibriumReserve0,
        uint256 equilibriumReserve1,
        uint256 priceX,
        uint256 priceY,
        uint256 concentrationX
    ) external pure returns (uint256) {
        uint256 xMax = equilibriumReserve0;
        uint256 xMin = 1;
        while (xMin < xMax) {
            uint256 xMid = (xMin + xMax) / 2;
            uint256 fxMid =
                CurveLibReference.f(xMid, priceX, priceY, equilibriumReserve0, equilibriumReserve1, concentrationX);
            if (newReserve1 >= fxMid) {
                xMax = xMid;
            } else {
                xMin = xMid + 1;
            }
        }
        if (
            newReserve1
                < CurveLibReference.f(xMin, priceX, priceY, equilibriumReserve0, equilibriumReserve1, concentrationX)
        ) {
            xMin += 1;
        }
        return xMin;
    }

    function test_fuzzFEquilibrium(uint256 px, uint256 py, uint256 x0, uint256 y0, uint256 cx, uint256 cy)
        public
        pure
    {
        // Params
        px = bound(px, 1, 1e25);
        py = bound(py, 1, 1e25);
        cx = bound(cx, 0, 1e18);
        cy = bound(cy, 0, 1e18);
        if (cx == 1e18) {
            x0 = bound(x0, 0, type(uint112).max);
        } else {
            x0 = bound(x0, 1, type(uint112).max);
        }
        if (cy == 1e18) {
            y0 = bound(y0, 0, type(uint112).max);
        } else {
            y0 = bound(y0, 1, type(uint112).max);
        }

        uint256 y = CurveLib.f(x0, px, py, x0, y0, cx);
        uint256 x = CurveLib.f(y0, py, px, y0, x0, cy);

        assertEq(y, y0);
        assertEq(x, x0);
    }
}
