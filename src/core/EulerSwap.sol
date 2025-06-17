// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC4626} from "@forge-std/interfaces/IERC4626.sol";

import {InvalidEulerSwapPoolStatus} from "./SettlerErrors.sol";

import {SettlerAbstract} from "../SettlerAbstract.sol";
import {CurveLib} from "./EulerSwapBUSL.sol";

import {Ternary} from "../utils/Ternary.sol";

interface IEVC {
    /// @notice Returns whether a given operator has been authorized for a given account.
    /// @param account The address of the account whose operator is being checked.
    /// @param operator The address of the operator that is being checked.
    /// @return authorized A boolean value that indicates whether the operator is authorized for the account.
    function isAccountOperatorAuthorized(address account, address operator) external view returns (bool authorized);
}

interface IEVault is IERC4626 {
    /// @notice Sum of all outstanding debts, in underlying units (increases as interest is accrued)
    /// @return The total borrows in asset units
    function totalBorrows() external view returns (uint256);

    /// @notice Balance of vault assets as tracked by deposits/withdrawals and borrows/repays
    /// @return The amount of assets the vault tracks as current direct holdings
    function cash() external view returns (uint256);

    /// @notice Debt owed by a particular account, in underlying units
    /// @param account Address to query
    /// @return The debt of the account in asset units
    function debtOf(address account) external view returns (uint256);

    /// @notice Retrieves supply and borrow caps in AmountCap format
    /// @return supplyCap The supply cap in AmountCap format
    /// @return borrowCap The borrow cap in AmountCap format
    function caps() external view returns (uint16 supplyCap, uint16 borrowCap);
}

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

    IEVC internal constant _EVC = IEVC(0x0C9a3dd6b8F28529d72d7f9cE918D493519EE383);

    function _revertInvalidStatus(uint32 status) private pure {
        assembly ("memory-safe") {
            mstore(0x00, 0x215f0a29) // selector for `InvalidEulerSwapPoolStatus(uint32)`
            mstore(0x20, and(0xffffffff, status))
            revert(0x1c, 0x24)
        }
    }

    function _foo(IEulerSwap eulerSwap, uint112 amount, bool zeroForOne) internal {
        ParamsLib.Params p = eulerSwap.getParams();
        (uint112 reserve0, uint112 reserve1, uint32 status) = eulerSwap.getReserves();
        if (status != 1) {
            // TODO: maybe just abort silently?
            _revertInvalidStatus(status);
        }
        if (!_EVC.isAccountOperatorAuthorized(p.eulerAccount(), address(eulerSwap))) {
            // TODO: maybe just abort silently?
            _revertInvalidStatus(0);
        }
        (uint256 inLimit, uint256 outLimit) = calcLimits(zeroForOne, p, reserve0, reserve1);
        if (amount > inLimit) {
            // TODO:
        }
        uint256 amountOut = findCurvePoint(amount, zeroForOne, p, reserve0, reserve1);
        if (amountOut > outLimit) {
            // TODO:
        }
    }

    function findCurvePoint(uint112 amount, bool zeroForOne, ParamsLib.Params p, uint112 reserve0, uint112 reserve1)
        private
        pure
        returns (uint256)
    {
        uint256 px = p.priceX();
        uint256 py = p.priceY();
        uint256 x0 = p.equilibriumReserve0();
        uint256 y0 = p.equilibriumReserve1();
        uint256 fee = p.fee();

        unchecked {
            uint256 amountWithFee = amount - (uint256(amount) * fee / 1e18);
            if (zeroForOne) {
                // swap X in and Y out
                uint256 xNew = reserve0 + amountWithFee;
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
                uint256 yNew = reserve1 + amountWithFee;
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

    /// @notice Calculates the maximum input and output amounts for a swap based on protocol constraints
    /// @dev Determines limits by checking multiple factors:
    ///      1. Supply caps and existing debt for the input token
    ///      2. Available reserves in the EulerSwap for the output token
    ///      3. Available cash and borrow caps for the output token
    ///      4. Account balances in the respective vaults
    /// @param p The EulerSwap params
    /// @param zeroForOne Boolean indicating whether asset0 (true) or asset1 (false) is the input token
    /// @return inLimit Maximum amount of input token that can be deposited
    /// @return outLimit Maximum amount of output token that can be withdrawn
        function calcLimits(bool zeroForOne, ParamsLib.Params p, uint112 reserve0, uint112 reserve1) private view returns (uint256 inLimit, uint256 outLimit) {
        inLimit = type(uint112).max;
        outLimit = type(uint112).max;

        address eulerAccount = p.eulerAccount();
        (IEVault vault0, IEVault vault1) = (IEVault(p.vault0()), IEVault(p.vault1()));
        // Supply caps on input
        {
            IEVault vault = (zeroForOne ? vault0 : vault1);
            uint256 maxDeposit = vault.debtOf(eulerAccount) + vault.maxDeposit(eulerAccount);
            if (maxDeposit < inLimit) inLimit = maxDeposit;
        }

        // Remaining reserves of output
        {
            uint112 reserveLimit = zeroForOne ? reserve1 : reserve0;
            if (reserveLimit < outLimit) outLimit = reserveLimit;
        }

        // Remaining cash and borrow caps in output
        {
            IEVault vault = (zeroForOne ? vault1 : vault0);

            uint256 cash = vault.cash();
            if (cash < outLimit) outLimit = cash;

            (, uint16 borrowCap) = vault.caps();
            uint256 maxWithdraw = decodeCap(uint256(borrowCap));
            maxWithdraw = vault.totalBorrows() > maxWithdraw ? 0 : maxWithdraw - vault.totalBorrows();
            if (maxWithdraw < outLimit) {
                maxWithdraw += vault.convertToAssets(vault.balanceOf(eulerAccount));
                if (maxWithdraw < outLimit) outLimit = maxWithdraw;
            }
        }
    }

    /// @notice Decodes a compact-format cap value to its actual numerical value
    /// @dev The cap uses a compact-format where:
    ///      - If amountCap == 0, there's no cap (returns max uint256)
    ///      - Otherwise, the lower 6 bits represent the exponent (10^exp)
    ///      - The upper bits (>> 6) represent the mantissa
    ///      - The formula is: (10^exponent * mantissa) / 100
    /// @param amountCap The compact-format cap value to decode
    /// @return The actual numerical cap value (type(uint256).max if uncapped)
    /// @custom:security Uses unchecked math for gas optimization as calculations cannot overflow:
    ///                  maximum possible value 10^(2^6-1) * (2^10-1) ≈ 1.023e+66 < 2^256
    function decodeCap(uint256 amountCap) private pure returns (uint256) {
        if (amountCap == 0) return type(uint256).max;

        unchecked {
            // Cannot overflow because this is less than 2**256:
            //   10**(2**6 - 1) * (2**10 - 1) = 1.023e+66
            return 10 ** (amountCap & 63) * (amountCap >> 6) / 100;
        }
    }

}
