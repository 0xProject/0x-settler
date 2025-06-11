// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerAbstract} from "../SettlerAbstract.sol";
import {CurveLib} from "./EulerSwapBUSL.sol";

import {Ternary} from "../utils/Ternary.sol";

interface IEulerSwap {
    /// @dev Immutable pool parameters. Passed to the instance via proxy trailing data.
    struct Params {
        // Entities
        address vault0;
        address vault1;
        address eulerAccount;
        // Curve
        uint112 equilibriumReserve0;
        uint112 equilibriumReserve1;
        uint256 priceX;
        uint256 priceY;
        uint256 concentrationX;
        uint256 concentrationY;
        // Fees
        uint256 fee;
        uint256 protocolFee;
        address protocolFeeRecipient;
    }

    /// @notice Retrieves the current reserves from storage, along with the pool's lock status.
    /// @return reserve0 The amount of asset0 in the pool
    /// @return reserve1 The amount of asset1 in the pool
    /// @return status The status of the pool (0 = unactivated, 1 = unlocked, 2 = locked)
    function getReserves() external view returns (uint112 reserve0, uint112 reserve1, uint32 status);

    /// @notice Optimistically sends the requested amounts of tokens to the `to`
    /// address, invokes `eulerSwapCall` callback on `to` (if `data` was provided),
    /// and then verifies that a sufficient amount of tokens were transferred to
    /// satisfy the swapping curve invariant.
    function swap(uint256 amount0Out, uint256 amount1Out, address to, bytes calldata data) external;
}

library ParamsLib {
    // This type is exactly the same as `IEulerSwap.Params`, but memory is managed manually because
    // solc is shit at it.
    type Params is uint256;

    function getParams(IEulerSwap eulerSwap) internal view returns (Params p) {
        assembly ("memory-safe") {
            p := mload(0x40)
            mstore(0x40, add(0x180, p))
            extcodecopy(eulerSwap, p, 0x36, 0x180)
        }
    }

    function vault0(Params p) internal pure returns (address r) {
        assembly ("memory-safe") {
            r := mload(p)
        }
    }

    function vault1(Params p) internal pure returns (address r) {
        assembly ("memory-safe") {
            r := mload(add(0x20, p))
        }
    }

    function eulerAccount(Params p) internal pure returns (address r) {
        assembly ("memory-safe") {
            r := mload(add(0x40, p))
        }
    }

    function equilibriumReserve0(Params p) internal pure returns (uint112 r) {
        assembly ("memory-safe") {
            r := mload(add(0x60, p))
        }
    }

    function equilibriumReserve1(Params p) internal pure returns (uint112 r) {
        assembly ("memory-safe") {
            r := mload(add(0x80, p))
        }
    }

    function priceX(Params p) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := mload(add(0xa0, p))
        }
    }

    function priceY(Params p) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := mload(add(0xc0, p))
        }
    }

    function concentrationX(Params p) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := mload(add(0xe0, p))
        }
    }

    function concentrationY(Params p) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := mload(add(0x100, p))
        }
    }

    function fee(Params p) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := mload(add(0x120, p))
        }
    }

    function protocolFee(Params p) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := mload(add(0x140, p))
        }
    }

    function protocolFeeRecipient(Params p) internal pure returns (address r) {
        assembly ("memory-safe") {
            r := mload(add(0x160, p))
        }
    }
}

abstract contract EulerSwap is SettlerAbstract {
    using Ternary for bool;
    using ParamsLib for ParamsLib.Params;
    using ParamsLib for IEulerSwap;

    error SwapLimitExceeded();

    function findCurvePoint(IEulerSwap eulerSwap, uint256 amount, bool asset0IsInput)
        internal
        view
        returns (uint256)
    {
        ParamsLib.Params p = eulerSwap.getParams();
        uint256 px = p.priceX();
        uint256 py = p.priceY();
        uint256 x0 = p.equilibriumReserve0();
        uint256 y0 = p.equilibriumReserve1();
        uint256 fee = p.fee();
        (uint112 reserve0, uint112 reserve1,) = eulerSwap.getReserves();

        unchecked {
            amount = amount - (amount * fee / 1e18);
        }

        if (asset0IsInput) {
            // swap X in and Y out
            uint256 xNew = reserve0 + amount;
            uint256 yNew;
            if (xNew <= x0) {
                // remain on f()
                yNew = CurveLib.f(xNew, px, py, x0, y0, p.concentrationX());
            } else {
                // move to g()
                yNew = CurveLib.fInverse(xNew, py, px, y0, x0, p.concentrationY());
            }
            return (reserve1 > yNew).ternary(reserve1 - yNew, 0);
        } else {
            // swap Y in and X out
            uint256 xNew;
            uint256 yNew = reserve1 + amount;
            if (yNew <= y0) {
                // remain on g()
                xNew = CurveLib.f(yNew, py, px, y0, x0, p.concentrationY());
            } else {
                // move to f()
                xNew = CurveLib.fInverse(yNew, px, py, x0, y0, p.concentrationX());
            }
            return (reserve0 > xNew).ternary(reserve0 - xNew, 0);
        }
    }

}
