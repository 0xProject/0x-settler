// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC4626} from "@forge-std/interfaces/IERC4626.sol";

import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

import {revertTooMuchSlippage} from "./SettlerErrors.sol";

import {SettlerAbstract} from "../SettlerAbstract.sol";
import {CurveLib} from "./EulerSwapBUSL.sol";

import {FastLogic} from "../utils/FastLogic.sol";
import {Ternary} from "../utils/Ternary.sol";
import {UnsafeMath, Math} from "../utils/UnsafeMath.sol";

interface IEVC {
    /// @notice Returns whether a given operator has been authorized for a given account.
    /// @param account The address of the account whose operator is being checked.
    /// @param operator The address of the operator that is being checked.
    /// @return authorized A boolean value that indicates whether the operator is authorized for the account.
    function isAccountOperatorAuthorized(address account, address operator) external view returns (bool authorized);

    /// @notice Returns an array of collaterals enabled for an account.
    /// @dev A collateral is a vault for which an account's balances are under the control of the currently enabled
    /// controller vault.
    /// @param account The address of the account whose collaterals are being queried.
    /// @return An array of addresses that are enabled collaterals for the account.
    function getCollaterals(address account) external view returns (address[] memory);

    /// @notice Returns an array of enabled controllers for an account.
    /// @dev A controller is a vault that has been chosen for an account to have special control over the account's
    /// balances in enabled collaterals vaults. A user can have multiple controllers during a call execution, but at
    /// most one can be selected when the account status check is performed.
    /// @param account The address of the account whose controllers are being queried.
    /// @return An array of addresses that are the enabled controllers for the account.
    function getControllers(address account) external view returns (address[] memory);
}

library FastEvc {
    function fastIsAccountOperatorAuthorized(IEVC evc, address account, address operator)
        internal
        view
        returns (bool authorized)
    {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            mstore(0x40, operator)
            mstore(0x2c, shl(0x60, account)) // clears `operator`'s padding
            mstore(0x0c, 0x1647292a000000000000000000000000) // selector for `isAccountOperatorAuthorized(address,address)` with `account`'s padding
            if iszero(staticcall(gas(), evc, 0x1c, 0x44, 0x00, 0x20)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
            authorized := mload(0x00)
            mstore(0x40, ptr)
        }
    }

    function fastGetCollaterals(IEVC evc, address account) internal view returns (address[] memory collaterals) {
        assembly ("memory-safe") {
            mstore(0x14, account)
            mstore(0x00, 0xa4d25d1e000000000000000000000000) // selector for `getCollaterals(address)` with `evc`'s padding

            if iszero(staticcall(gas(), evc, 0x00, 0x24, 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }

            let size := returndatasize()
            collaterals := mload(0x40)
            returndatacopy(collaterals, 0x00, size)
            mstore(0x40, add(collaterals, size))
        }
    }

    function fastGetControllers(IEVC evc, address account) internal view returns (address[] memory controllers) {
        assembly ("memory-safe") {
            mstore(0x14, account)
            mstore(0x00, 0xfd6046d7000000000000000000000000) // selector for `getControllers(address)` with `evc`'s padding

            if iszero(staticcall(gas(), evc, 0x00, 0x24, 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }

            let size := returndatasize()
            controllers := mload(0x40)
            returndatacopy(controllers, 0x00, size)
            mstore(0x40, add(controllers, size))
        }
    }
}

interface IOracle {
    /// @notice Two-sided price: How much quote token you would get/spend for selling/buying inAmount of base token.
    /// @param inAmount The amount of `base` to convert.
    /// @param base The token that is being priced.
    /// @param quote The token that is the unit of account.
    /// @return bidOutAmount The amount of `quote` you would get for selling `inAmount` of `base`.
    /// @return askOutAmount The amount of `quote` you would spend for buying `inAmount` of `base`.
    /// @dev `base` and `quote` can be either underlying assets or they can be themselves EVaults,
    ///      in which case `inAmount` is interpreted as an amount of shares and the corresponding
    ///      amount of the underlying is resolved recursively.
    function getQuotes(uint256 inAmount, IERC20 base, IERC20 quote)
        external
        view
        returns (uint256 bidOutAmount, uint256 askOutAmount);
    // for computing liability value, use `askOutAmount`
    // for computing collateral value, use `bidOutAmount`
}

library FastOracle {
    function fastGetQuote(IOracle oracle, uint256 inAmount, IERC20 base, IERC20 quote) internal view returns (uint256 bidOutAmount, uint256 askOutAmount) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            mstore(ptr, 0x0902f1ac) // selector for `getQuotes(uint256,address,address)`
            mstore(add(0x20, ptr), inAmount)
            mstore(add(0x40, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, base))
            mstore(add(0x60, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, quote))
            if iszero(staticcall(gas(), oracle, 0x1c, 0x64, 0x00, 0x40)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
            bidOutAmount := mload(0x00)
            askOutAmount := mload(0x20)
        }
    }
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

    /// @notice Returns an address of the sidecar DToken
    /// @return The address of the DToken
    function dToken() external view returns (IERC20);

    /// @notice Retrieves a reference asset used for liquidity calculations
    /// @return The address of the reference asset
    function unitOfAccount() external view returns (IERC20);

    /// @notice Retrieves the borrow LTV of the collateral, which is used to determine if the account is healthy during
    /// account status checks.
    /// @param collateral The address of the collateral to query
    /// @return Borrowing LTV in 1e4 scale
    function LTVBorrow(IEVault collateral) external view returns (uint16);

    /// @notice Retrieves the address of the oracle contract
    /// @return The address of the oracle
    function oracle() external view returns (IOracle);
}

IERC20 constant UNIT_OF_ACCOUNT_USD = IERC20(0x0000000000000000000000000000000000000348);

library FastEvault {
    function fastAsset(IERC4626 vault) internal view returns (IERC20 asset) {
        assembly ("memory-safe") {
            mstore(0x00, 0x38d52e0f) // selector for `asset()`
            if iszero(staticcall(gas(), vault, 0x1c, 0x04, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            asset := mload(0x00)
            if or(gt(0x20, returndatasize()), shr(0xa0, asset)) { revert(0x00, 0x00) }
        }
    }

    function fastMaxDeposit(IERC4626 vault, address receiver) internal view returns (uint256 maxAssets) {
        assembly ("memory-safe") {
            mstore(0x14, receiver)
            mstore(0x00, 0x402d267d000000000000000000000000) // selector for `maxDeposit(address)` with `receiver`'s padding
            if iszero(staticcall(gas(), vault, 0x10, 0x24, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if gt(0x20, returndatasize()) { revert(0x00, 0x00) }
            maxAssets := mload(0x00)
        }
    }

    function fastConvertToAssets(IERC4626 vault, uint256 shares) internal view returns (uint256 assets) {
        assembly ("memory-safe") {
            mstore(0x20, shares)
            mstore(0x00, 0x07a2d13a) // selector for `convertToAssets(uint256)`
            if iszero(staticcall(gas(), vault, 0x1c, 0x24, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if gt(0x20, returndatasize()) { revert(0x00, 0x00) }
            assets := mload(0x00)
        }
    }

    function fastTotalBorrows(IEVault vault) internal view returns (uint256 r) {
        assembly ("memory-safe") {
            mstore(0x00, 0x47bd3718) // selector for `totalBorrows()`
            if iszero(staticcall(gas(), vault, 0x1c, 0x04, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if gt(0x20, returndatasize()) { revert(0x00, 0x00) }
            r := mload(0x00)
        }
    }

    function fastCash(IEVault vault) internal view returns (uint256 r) {
        assembly ("memory-safe") {
            mstore(0x00, 0x961be391) // selector for `cash()`
            if iszero(staticcall(gas(), vault, 0x1c, 0x04, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if gt(0x20, returndatasize()) { revert(0x00, 0x00) }
            r := mload(0x00)
        }
    }

    function fastDebtOf(IEVault vault, address account) internal view returns (uint256 r) {
        assembly ("memory-safe") {
            mstore(0x14, account)
            mstore(0x00, 0xd283e75f000000000000000000000000) // selector for `debtOf(address)` with `account`'s padding
            if iszero(staticcall(gas(), vault, 0x10, 0x24, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if gt(0x20, returndatasize()) { revert(0x00, 0x00) }
            r := mload(0x00)
        }
    }

    // Caps are returned as `uint256` for efficiency, but they are checked to ensure that they do not overflow a `uint16`.
    function fastCaps(IEVault vault) internal view returns (uint256 supplyCap, uint256 borrowCap) {
        assembly ("memory-safe") {
            mstore(0x00, 0x18e22d98) // selector for `caps()`
            if iszero(staticcall(gas(), vault, 0x1c, 0x04, 0x00, 0x40)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            supplyCap := mload(0x00)
            borrowCap := mload(0x20)
            if or(gt(0x40, returndatasize()), or(shr(0x10, supplyCap), shr(0x10, borrowCap))) { revert(0x00, 0x00) }
        }
    }

    function fastOracle(IEVault vault) internal view returns (IOracle oracle) {
        assembly ("memory-safe") {
            mstore(0x00, 0x7dc0d1d0) // selector for `oracle()`
            if iszero(staticcall(gas(), vault, 0x1c, 0x04, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            oracle := mload(0x00)
            if or(gt(0x20, returndatasize()), shr(0xa0, oracle)) { revert(0x00, 0x00) }
        }
    }

    function fastUnitOfAccount(IEVault vault) internal view returns (IERC20 unitOfAccount) {
        assembly ("memory-safe") {
            mstore(0x00, 0x3e833364) // selector for `unitOfAccount()`
            if iszero(staticcall(gas(), vault, 0x1c, 0x04, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            unitOfAccount := mload(0x00)
            if or(gt(0x20, returndatasize()), shr(0xa0, unitOfAccount)) { revert(0x00, 0x00) }
        }
    }

    // LTV is returned as `uint256` for efficiency, but they are checked to ensure that they do not overflow a `uint16`.
    function fastLTVBorrow(IEVault vault, IEVault collateral) internal view returns (uint256 ltv) {
        assembly ("memory-safe") {
            mstore(0x14, collateral)
            mstore(0x00, 0xbf58094d000000000000000000000000) // selector for `LTVBorrow(address)` with `collateral`'s padding
            if iszero(staticcall(gas(), vault, 0x10, 0x24, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            ltv := mload(0x00)
            if or(gt(0x20, returndatasize()), shr(0x10, ltv)) { revert(0x00, 0x00) }
        }
    }
}

interface IEulerSwap {
    /// @dev Immutable pool parameters. Passed to the instance via proxy trailing data.
    struct Params {
        // Entities
        IEVault vault0;
        IEVault vault1;
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

    /// @notice Retrieves the pool's immutable parameters.
    function getParams() external view returns (Params memory);

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

library FastEulerSwap {
    // Reserves are returned as `uint256` for efficiency, but they are checked to ensure that they do not overflow a `uint112`.
    function fastGetReserves(IEulerSwap pool) internal view returns (uint256 reserve0, uint256 reserve1) {
        assembly ("memory-safe") {
            mstore(0x00, 0x0902f1ac) // selector for `getReserves()`
            if iszero(staticcall(gas(), pool, 0x1c, 0x04, 0x00, 0x40)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            reserve0 := mload(0x00)
            reserve1 := mload(0x20)
            if or(gt(0x60, returndatasize()), or(shr(0x70, reserve1), shr(0x70, reserve0))) { revert(0x00, 0x00) }
        }
    }

    function fastSwap(IEulerSwap pool, bool zeroForOne, uint256 amountOut, address to) internal {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, 0x022c0d9f) // selector for `swap(uint256,uint256,address,bytes)`
            {
                zeroForOne := shl(0x05, zeroForOne)
                let amountsStart := add(0x20, ptr)
                let amountWord := add(amountsStart, zeroForOne)
                let zeroWord := add(xor(0x20, zeroForOne), amountsStart)
                mstore(amountWord, amountOut)
                mstore(zeroWord, 0x00)
            }
            mstore(add(0x60, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, to))
            mstore(add(0x80, ptr), 0x80)
            mstore(add(0xa0, ptr), 0x00)
            if iszero(call(gas(), pool, 0x00, add(0x1c, ptr), 0xa4, 0x00, 0x00)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
        }
    }
}

library ParamsLib {
    // This type is exactly the same as `IEulerSwap.Params`, but memory is managed manually because
    // solc is shit at it.
    type Params is uint256;

    function fastGetParams(IEulerSwap pool) internal view returns (Params p) {
        assembly ("memory-safe") {
            p := mload(0x40)
            mstore(0x40, add(0x180, p))
            extcodecopy(pool, p, 0x36, 0x180)
        }
    }

    function vault0(Params p) internal pure returns (IEVault r) {
        assembly ("memory-safe") {
            r := mload(p)
        }
    }

    function vault1(Params p) internal pure returns (IEVault r) {
        assembly ("memory-safe") {
            r := mload(add(0x20, p))
        }
    }

    function eulerAccount(Params p) internal pure returns (address r) {
        assembly ("memory-safe") {
            r := mload(add(0x40, p))
        }
    }

    // The result is a `uint256` for efficiency. EulerSwap's ABI states that this is a `uint112`. Overflow is not checked.
    function equilibriumReserve0(Params p) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := mload(add(0x60, p))
        }
    }

    // The result is a `uint256` for efficiency. EulerSwap's ABI states that this is a `uint112`. Overflow is not checked.
    function equilibriumReserve1(Params p) internal pure returns (uint256 r) {
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

library EulerSwapLib {
    using UnsafeMath for uint256;
    using Math for uint256;
    using Ternary for bool;
    using SafeTransferLib for IEVault;
    using ParamsLib for ParamsLib.Params;
    using FastEvc for IEVC;
    using FastEvault for IEVault;
    using FastOracle for IOracle;

    function findCurvePoint(uint256 amount, bool zeroForOne, ParamsLib.Params p, uint256 reserve0, uint256 reserve1)
        internal
        pure
        returns (uint256)
    {
        uint256 px = p.priceX();
        uint256 py = p.priceY();
        uint256 x0 = p.equilibriumReserve0();
        uint256 y0 = p.equilibriumReserve1();

        unchecked {
            uint256 amountWithFee = amount - (amount * p.fee() / 1e18);
            if (zeroForOne) {
                // swap X in and Y out
                uint256 xNew = reserve0 + amountWithFee;
                uint256 yNew = xNew <= x0
                    // remain on f()
                    ? CurveLib.saturatingF(xNew, px, py, x0, y0, p.concentrationX())
                    // move to g()
                    : CurveLib.fInverse(xNew, py, px, y0, x0, p.concentrationY());
                yNew = yNew.unsafeInc(yNew == 0);
                return reserve1.saturatingSub(yNew);
            } else {
                // swap Y in and X out
                uint256 yNew = reserve1 + amountWithFee;
                uint256 xNew = yNew <= y0
                    // remain on g()
                    ? CurveLib.saturatingF(yNew, py, px, y0, x0, p.concentrationY())
                    // move to f()
                    : CurveLib.fInverse(yNew, px, py, x0, y0, p.concentrationX());
                xNew = xNew.unsafeInc(xNew == 0);
                return reserve0.saturatingSub(xNew);
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
    function calcLimits(IEVC evc, IEulerSwap pool, bool zeroForOne, ParamsLib.Params p, uint256 reserve0, uint256 reserve1)
        internal
        view
        returns (uint256 inLimit, uint256 outLimit)
    {
        IEVault sellVault;
        IEVault buyVault;
        {
            (address sellVault_, address buyVault_) = zeroForOne.maybeSwap(address(p.vault1()), address(p.vault0()));
            sellVault = IEVault(sellVault_);
            buyVault = IEVault(buyVault_);
        }
        address ownerAccount = p.eulerAccount();

        // Supply caps on input
        unchecked {
            inLimit = sellVault.fastDebtOf(ownerAccount) + sellVault.fastMaxDeposit(ownerAccount);
            inLimit = evc.fastIsAccountOperatorAuthorized(ownerAccount, address(pool)).orZero(inLimit);
        }

        // Remaining reserves of output
        outLimit = zeroForOne.ternary(reserve1, reserve0);

        // Remaining cash and borrow caps in output
        {
            uint256 cash = buyVault.fastCash();
            outLimit = (cash < outLimit).ternary(cash, outLimit);

            (, uint256 borrowCap) = buyVault.fastCaps();
            uint256 maxWithdraw = decodeCap(borrowCap).saturatingSub(buyVault.fastTotalBorrows());
            if (maxWithdraw < outLimit) {
                unchecked {
                    maxWithdraw += buyVault.fastConvertToAssets(buyVault.fastBalanceOf(ownerAccount));
                }
                outLimit = (maxWithdraw >= outLimit).ternary(outLimit, maxWithdraw);
            }
        }

        uint256 inLimitFromOutLimit;
        {
            uint256 px = p.priceX();
            uint256 py = p.priceY();
            uint256 x0 = p.equilibriumReserve0();
            uint256 y0 = p.equilibriumReserve1();

            if (zeroForOne) {
                // swap Y out and X in
                uint256 yNew = reserve1.saturatingSub(outLimit);
                uint256 xNew = yNew <= y0
                    // remain on g()
                    ? CurveLib.saturatingF(yNew, py, px, y0, x0, p.concentrationY())
                    // move to f()
                    : CurveLib.fInverse(yNew, px, py, x0, y0, p.concentrationX());
                inLimitFromOutLimit = xNew.saturatingSub(reserve0);
            } else {
                // swap X out and Y in
                uint256 xNew = reserve0.saturatingSub(outLimit);
                uint256 yNew = xNew <= x0
                    // remain on f()
                    ? CurveLib.saturatingF(xNew, px, py, x0, y0, p.concentrationX())
                    // move to g()
                    : CurveLib.fInverse(xNew, py, px, y0, x0, p.concentrationY());
                inLimitFromOutLimit = yNew.saturatingSub(reserve1);
            }
        }

        unchecked {
            inLimit = (inLimitFromOutLimit < inLimit).ternary(inLimitFromOutLimit, inLimit);
            inLimit = (inLimit * 1e18).unsafeDiv(1e18 - p.fee());
        }
    }

    /// @notice Decodes a compact-format cap value to its actual numerical value
    /// @dev The cap uses a compact-format where:
    ///      - If amountCap == 0, there's no cap (returns type(uint112).max)
    ///      - Otherwise, the lower 6 bits represent the exponent (10^exp)
    ///      - The upper bits (>> 6) represent the mantissa
    ///      - The formula is: (10^exponent * mantissa) / 100
    /// @param amountCap The compact-format cap value to decode
    /// @return The actual numerical cap value (type(uint112).max if uncapped)
    /// @custom:security Uses unchecked math for gas optimization as calculations cannot overflow:
    ///                  maximum possible value 10^(2^6-1) * (2^10-1) ≈ 1.023e+66 < 2^256
    function decodeCap(uint256 amountCap) internal pure returns (uint256) {
        unchecked {
            // Cannot overflow because this is less than 2**256:
            //   10**(2**6 - 1) * (2**10 - 1) = 1.023e+66
            return (amountCap == 0).ternary(type(uint112).max, 10 ** (amountCap & 63) * (amountCap >> 6) / 100);
        }
    }

    function checkSolvency(
        IEVC evc,
        address account,
        address vault0,
        address vault1,
        bool zeroForOne,
        uint256 amountIn, 
        uint256 amountOut
    ) internal view returns (bool) {
        address[] memory collaterals = evc.fastGetCollaterals(account);
        IEVault debtVault;
        uint256 debt;

        {
            address[] memory controllers = evc.fastGetControllers(account);

            if(controllers.length > 1) return false;
            if(controllers.length == 1) {
                debtVault = IEVault(controllers[0]);
                debt = debtVault.fastDebtOf(account);
            }
        }

        IEVault sellVault;
        IEVault buyVault;
        {
            (address sellVault_, address buyVault_) = zeroForOne.maybeSwap(vault1, vault0);
            sellVault = IEVault(sellVault_);
            buyVault = IEVault(buyVault_);
        }
        
        uint256 newDebt;
        uint256 soldCollateral;
        uint256 newCollateral;

        // compute new debt in buyVault
        {
            uint256 collateralBalance = buyVault.fastBalanceOf(account);
            if(collateralBalance < amountOut) {
                newDebt = amountOut - collateralBalance;
                soldCollateral = collateralBalance;
            }
            else {
                soldCollateral = amountOut;
            }
        }

        // check sellVault debt
        if(debtVault == sellVault) {
            // debt repayment
            if(amountIn < debt) {
                // collateral in buyVault must be able to cover the amountOut
                // to ensure there is only one controller at the end
                if(newDebt != 0) return false;
                debt -= amountIn;
            }
            else {
                newCollateral = amountIn - debt;
                debt = 0; // debt was repaid
            }
        } else {
            newCollateral = amountIn;
        }

        // if there is new debt in buyVault, check that the controller is buyVault
        // or debt was repaid to ensure there is only one controller at the end
        if(newDebt != 0) {
            if(debt != 0 && debtVault != buyVault) return false;
            if(address(debtVault) == address(0)) debtVault = buyVault;
            debt += newDebt;
        }
    
        // check for solvency if there is any debt
        if(debt != 0) {
            IOracle oracle = debtVault.fastOracle();
            IERC20 unitOfAccount = debtVault.fastUnitOfAccount();

            (, debt) = oracle.fastGetQuote(debt, debtVault.fastAsset(), unitOfAccount);   
            // adjust precision to avoid divisions when adjusting LTVBorrow bps of collateral.
            // All amounts in EulerSwap are lower than uint112 so there should not be overflow errors.
            debt *= 1e4;
            if(soldCollateral != 0) {
                // adjust inequality to avoid substraction
                // collateral + newCollateral - soldCollateral >= debt
                // is changed to 
                // collateral + newCollateral >= debt + soldCollateral
                (uint256 value,) = oracle.fastGetQuote(soldCollateral, buyVault.fastAsset(), unitOfAccount);
                debt += (value * debtVault.fastLTVBorrow(buyVault));
            }
            uint256 collateral;
            if(newCollateral != 0) {
                (uint256 value,) = oracle.fastGetQuote(newCollateral, sellVault.fastAsset(), unitOfAccount);
                collateral = (value * debtVault.fastLTVBorrow(sellVault));
            }
            for(uint256 i = 0; i < collaterals.length; i++) {
                IEVault collateralVault = IEVault(collaterals[i]);
                (uint256 value,) = oracle.fastGetQuote(collateralVault.fastBalanceOf(account), collateralVault.fastAsset(), unitOfAccount);   

                collateral += (value * debtVault.fastLTVBorrow(collateralVault));
                if(collateral >= debt) {
                    return true;
                }
            }
        }

        return false;
    }
}

abstract contract EulerSwap is SettlerAbstract {
    using Ternary for bool;
    using SafeTransferLib for IERC20;
    using ParamsLib for ParamsLib.Params;
    using ParamsLib for IEulerSwap;
    using FastEvault for IEVault;
    using FastEulerSwap for IEulerSwap;

    function _EVC() internal view virtual returns (IEVC);

    function _revertTooMuchSlippage(
        bool zeroForOne,
        ParamsLib.Params p,
        uint256 expectedBuyAmount,
        uint256 actualBuyAmount
    ) private view {
        revertTooMuchSlippage(
            IEVault(zeroForOne.ternary(address(p.vault1()), address(p.vault0()))).fastAsset(),
            expectedBuyAmount,
            actualBuyAmount
        );
    }

    function sellToEulerSwap(
        address recipient,
        IERC20 sellToken,
        uint256 bps,
        IEulerSwap pool,
        bool zeroForOne,
        uint256 amountOutMin
    ) internal {
        // Doing this first violates the general rule that we ought to interact with the token
        // before checking the state of the pool. However, this is safe because Euler doesn't admit
        // badly-behaved tokens, and a token must be available on Euler before it can be added to
        // EulerSwap.
        ParamsLib.Params p = pool.fastGetParams();
        (uint256 reserve0, uint256 reserve1) = pool.fastGetReserves();
        (uint256 inLimit,) = EulerSwapLib.calcLimits(_EVC(), pool, zeroForOne, p, reserve0, reserve1);

        uint256 sellAmount;
        if (bps != 0) {
            unchecked {
                sellAmount = sellToken.fastBalanceOf(address(this)) * bps / BASIS;
            }
            // TODO: Comment for what happens with excess here.
            // 1. Excess is absorbed by other sources
            // 2. Ultimatelly donated as fee, which might result in a slippage revert? Double check.
            sellAmount = (sellAmount > inLimit).ternary(inLimit, sellAmount);
            sellToken.safeTransfer(address(pool), sellAmount);
        }
        if (sellAmount == 0) {
            sellAmount = sellToken.fastBalanceOf(address(pool));
            // If the sell amount is over the limit, the excess is donated. Obviously, this may
            // result in a slippage revert.
            sellAmount = (sellAmount > inLimit).ternary(inLimit, sellAmount);
        }

        // solve the constant function
        uint256 amountOut = EulerSwapLib.findCurvePoint(sellAmount, zeroForOne, p, reserve0, reserve1);

        // check slippage before swapping to save some sad-path gas
        if (amountOut < amountOutMin) {
            _revertTooMuchSlippage(zeroForOne, p, amountOutMin, amountOut);
        }

        // Because the reference implementation of `verify` for the EulerSwap trading function is
        // non-monotonic, it may be possible to have an `amountOut` of one, even if `sellAmount` is
        // zero. Because this is likely triggered by a failure of the `isAccountOperatorAuthorized`
        // check, we skip calling `swap` because it's probably going to revert. If you set
        // `amountOutMin` to one and this catches you off guard, I'm sorry, but that was dumb.
        if (amountOut > 1) {
            pool.fastSwap(zeroForOne, amountOut, recipient);
        }
    }
}
