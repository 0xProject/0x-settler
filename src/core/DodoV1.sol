// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";
import {revertTooMuchSlippage} from "./SettlerErrors.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {Ternary} from "../utils/Ternary.sol";

interface IDodoV1 {
    function sellBaseToken(uint256 amount, uint256 minReceiveQuote, bytes calldata data) external returns (uint256);

    function buyBaseToken(uint256 amount, uint256 maxPayQuote, bytes calldata data) external returns (uint256);

    function _R_STATUS_() external view returns (uint8);

    function _QUOTE_BALANCE_() external view returns (uint256);

    function _BASE_BALANCE_() external view returns (uint256);

    function _K_() external view returns (uint256);

    function _MT_FEE_RATE_() external view returns (uint256);

    function _LP_FEE_RATE_() external view returns (uint256);

    function getExpectedTarget() external view returns (uint256 baseTarget, uint256 quoteTarget);

    function getOraclePrice() external view returns (uint256);

    function _BASE_TOKEN_() external view returns (IERC20);

    function _QUOTE_TOKEN_() external view returns (IERC20);
}

library FastDodoV1 {
    function _callAddressUintEmptyBytesReturnUint(IDodoV1 dodo, uint256 sig, uint256 a, uint256 b)
        private
        returns (uint256 r)
    {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, sig)
            mstore(add(0x20, ptr), a)
            mstore(add(0x40, ptr), b)
            mstore(add(0x60, ptr), 0x60)
            mstore(add(0x80, ptr), 0x00)

            if iszero(call(gas(), dodo, 0x00, add(0x1c, ptr), 0x84, 0x00, 0x20)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
            if iszero(gt(returndatasize(), 0x1f)) { revert(0x00, 0x00) }

            r := mload(0x00)
        }
    }

    function fastSellBaseToken(IDodoV1 dodo, uint256 amount, uint256 minReceiveQuote) internal returns (uint256) {
        return _callAddressUintEmptyBytesReturnUint(dodo, uint32(dodo.sellBaseToken.selector), amount, minReceiveQuote);
    }

    function fastBuyBaseToken(IDodoV1 dodo, uint256 amount, uint256 maxPayQuote) internal returns (uint256) {
        return _callAddressUintEmptyBytesReturnUint(dodo, uint32(dodo.buyBaseToken.selector), amount, maxPayQuote);
    }

    function _get(IDodoV1 dodo, uint256 sig) private view returns (bytes32 r) {
        assembly ("memory-safe") {
            mstore(0x00, sig)
            if iszero(staticcall(gas(), dodo, 0x1c, 0x04, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if iszero(gt(returndatasize(), 0x1f)) { revert(0x00, 0x00) }

            r := mload(0x00)
        }
    }

    function fast_R_STATUS_(IDodoV1 dodo) internal view returns (uint8) {
        uint256 result = uint256(_get(dodo, uint32(dodo._R_STATUS_.selector)));
        require(result >> 8 == 0);
        return uint8(result);
    }

    function fast_QUOTE_BALANCE_(IDodoV1 dodo) internal view returns (uint256) {
        return uint256(_get(dodo, uint32(dodo._QUOTE_BALANCE_.selector)));
    }

    function fast_BASE_BALANCE_(IDodoV1 dodo) internal view returns (uint256) {
        return uint256(_get(dodo, uint32(dodo._BASE_BALANCE_.selector)));
    }

    function fast_K_(IDodoV1 dodo) internal view returns (uint256) {
        return uint256(_get(dodo, uint32(dodo._K_.selector)));
    }

    function fast_MT_FEE_RATE_(IDodoV1 dodo) internal view returns (uint256) {
        return uint256(_get(dodo, uint32(dodo._MT_FEE_RATE_.selector)));
    }

    function fast_LP_FEE_RATE_(IDodoV1 dodo) internal view returns (uint256) {
        return uint256(_get(dodo, uint32(dodo._LP_FEE_RATE_.selector)));
    }

    function fastGetExpectedTarget(IDodoV1 dodo) internal view returns (uint256 baseTarget, uint256 quoteTarget) {
        assembly ("memory-safe") {
            mstore(0x00, 0xffa64225)
            if iszero(staticcall(gas(), dodo, 0x1c, 0x04, 0x00, 0x40)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if iszero(gt(returndatasize(), 0x3f)) { revert(0x00, 0x00) }

            baseTarget := mload(0x00)
            quoteTarget := mload(0x20)
        }
    }

    function fastGetOraclePrice(IDodoV1 dodo) internal view returns (uint256) {
        return uint256(_get(dodo, uint32(dodo.getOraclePrice.selector)));
    }

    function fast_BASE_TOKEN_(IDodoV1 dodo) internal view returns (IERC20) {
        uint256 result = uint256(_get(dodo, uint32(dodo._BASE_TOKEN_.selector)));
        require(result >> 160 == 0);
        return IERC20(address(uint160(result)));
    }

    function fast_QUOTE_TOKEN_(IDodoV1 dodo) internal view returns (IERC20) {
        uint256 result = uint256(_get(dodo, uint32(dodo._QUOTE_TOKEN_.selector)));
        require(result >> 160 == 0);
        return IERC20(address(uint160(result)));
    }
}

library Math {
    using UnsafeMath for uint256;

    function sqrt(uint256 x) internal pure returns (uint256 y) {
        unchecked {
            uint256 z = x / 2 + 1;
            y = x;
            while (z < y) {
                y = z;
                z = (x.unsafeDiv(z) + z) / 2;
            }
        }
    }
}

library DecimalMath {
    using UnsafeMath for uint256;
    using Math for uint256;

    uint256 constant ONE = 10 ** 18;

    function mul(uint256 target, uint256 d) internal pure returns (uint256) {
        unchecked {
            return target * d / ONE;
        }
    }

    function mulCeil(uint256 target, uint256 d) internal pure returns (uint256) {
        unchecked {
            return (target * d).unsafeDivUp(ONE);
        }
    }

    function divFloor(uint256 target, uint256 d) internal pure returns (uint256) {
        unchecked {
            return (target * ONE).unsafeDiv(d);
        }
    }

    function divCeil(uint256 target, uint256 d) internal pure returns (uint256) {
        unchecked {
            return (target * ONE).unsafeDivUp(d);
        }
    }
}

library DodoMath {
    using UnsafeMath for uint256;
    using Math for uint256;

    /*
        Integrate dodo curve fron V1 to V2
        require V0>=V1>=V2>0
        res = (1-k)i(V1-V2)+ikV0*V0(1/V2-1/V1)
        let V1-V2=delta
        res = i*delta*(1-k+k(V0^2/V1/V2))
    */
    function _GeneralIntegrate(uint256 V0, uint256 V1, uint256 V2, uint256 i, uint256 k)
        internal
        pure
        returns (uint256)
    {
        unchecked {
            uint256 fairAmount = DecimalMath.mul(i, V1 - V2); // i*delta
            uint256 V0V0V1V2 = DecimalMath.divCeil((V0 * V0).unsafeDiv(V1), V2);
            uint256 penalty = DecimalMath.mul(k, V0V0V1V2); // k(V0^2/V1/V2)
            return DecimalMath.mul(fairAmount, DecimalMath.ONE - k + penalty);
        }
    }

    /*
        The same with integration expression above, we have:
        i*deltaB = (Q2-Q1)*(1-k+kQ0^2/Q1/Q2)
        Given Q1 and deltaB, solve Q2
        This is a quadratic function and the standard version is
        aQ2^2 + bQ2 + c = 0, where
        a=1-k
        -b=(1-k)Q1-kQ0^2/Q1+i*deltaB
        c=-kQ0^2
        and Q2=(-b+sqrt(b^2+4(1-k)kQ0^2))/2(1-k)
        note: another root is negative, abondan
        if deltaBSig=true, then Q2>Q1
        if deltaBSig=false, then Q2<Q1
    */
    function _SolveQuadraticFunctionForTrade(uint256 Q0, uint256 Q1, uint256 ideltaB, bool deltaBSig, uint256 k)
        internal
        pure
        returns (uint256)
    {
        unchecked {
            // calculate -b value and sig
            // -b = (1-k)Q1-kQ0^2/Q1+i*deltaB
            uint256 kQ02Q1 = (DecimalMath.mul(k, Q0) * Q0).unsafeDiv(Q1); // kQ0^2/Q1
            uint256 b = DecimalMath.mul(DecimalMath.ONE - k, Q1); // (1-k)Q1
            bool minusbSig = true;
            if (deltaBSig) {
                b += ideltaB; // (1-k)Q1+i*deltaB
            } else {
                kQ02Q1 += ideltaB; // i*deltaB+kQ0^2/Q1
            }
            if (b >= kQ02Q1) {
                b -= kQ02Q1;
                minusbSig = true;
            } else {
                b = kQ02Q1 - b;
                minusbSig = false;
            }

            // calculate sqrt
            uint256 squareRoot = DecimalMath.mul((DecimalMath.ONE - k) * 4, DecimalMath.mul(k, Q0) * Q0); // 4(1-k)kQ0^2
            squareRoot = (b * b + squareRoot).sqrt(); // sqrt(b*b+4(1-k)kQ0*Q0)

            // final res
            uint256 denominator = (DecimalMath.ONE - k) * 2; // 2(1-k)
            uint256 numerator;
            if (minusbSig) {
                numerator = b + squareRoot;
            } else {
                numerator = squareRoot - b;
            }

            if (deltaBSig) {
                return DecimalMath.divFloor(numerator, denominator);
            } else {
                return DecimalMath.divCeil(numerator, denominator);
            }
        }
    }

    /*
        Start from the integration function
        i*deltaB = (Q2-Q1)*(1-k+kQ0^2/Q1/Q2)
        Assume Q2=Q0, Given Q1 and deltaB, solve Q0
        let fairAmount = i*deltaB
    */
    function _SolveQuadraticFunctionForTarget(uint256 V1, uint256 k, uint256 fairAmount)
        internal
        pure
        returns (uint256 V0)
    {
        unchecked {
            // V0 = V1+V1*(sqrt-1)/2k
            uint256 sqrt = DecimalMath.divCeil(DecimalMath.mul(k, fairAmount) * 4, V1);
            sqrt = ((sqrt + DecimalMath.ONE) * DecimalMath.ONE).sqrt();
            uint256 premium = DecimalMath.divCeil(sqrt - DecimalMath.ONE, k * 2);
            // V0 is greater than or equal to V1 according to the solution
            return DecimalMath.mul(V1, DecimalMath.ONE + premium);
        }
    }
}

abstract contract DodoSellHelper {
    using Math for uint256;
    using FastDodoV1 for IDodoV1;
    using Ternary for bool;

    enum RStatus {
        ONE,
        ABOVE_ONE,
        BELOW_ONE
    }

    function dodoQuerySellQuoteToken(IDodoV1 dodo, uint256 amount) internal view returns (uint256) {
        (uint256 baseTarget, uint256 quoteTarget) = dodo.fastGetExpectedTarget();
        RStatus rStatus = RStatus(dodo.fast_R_STATUS_());
        uint256 oraclePrice = dodo.fastGetOraclePrice();
        uint256 B = dodo.fast_BASE_BALANCE_();
        uint256 K = dodo.fast_K_();

        unchecked {
            uint256 boughtAmount;
            uint256 i = DecimalMath.divFloor(DecimalMath.ONE, oraclePrice);
            // Determine the status (RStatus) and calculate the amount based on the
            // state
            if (rStatus == RStatus.BELOW_ONE) {
                uint256 Q = dodo.fast_QUOTE_BALANCE_();
                uint256 backOneBase = B - baseTarget;
                uint256 backOneQuote = quoteTarget - Q;
                if (amount <= backOneQuote) {
                    uint256 Q1 = Q + amount;
                    boughtAmount = DodoMath._GeneralIntegrate(quoteTarget, Q1, Q, i, K);
                } else {
                    boughtAmount = backOneBase + _SellQuoteToken(amount - backOneQuote, i, baseTarget, baseTarget, K);
                }
            } else {
                uint256 Q1 = (rStatus == RStatus.ONE).ternary(baseTarget, B);
                boughtAmount = _SellQuoteToken(amount, i, baseTarget, Q1, K);
            }
            // Calculate fees
            return DecimalMath.divFloor(
                boughtAmount, DecimalMath.ONE + dodo.fast_MT_FEE_RATE_() + dodo.fast_LP_FEE_RATE_()
            );
        }
    }

    function _SellQuoteToken(uint256 amount, uint256 i, uint256 Q0, uint256 Q1, uint256 K)
        private
        pure
        returns (uint256 receiveBaseToken)
    {
        unchecked {
            return Q1 - DodoMath._SolveQuadraticFunctionForTrade(Q0, Q1, DecimalMath.mul(i, amount), false, K);
        }
    }
}

abstract contract DodoV1 is SettlerAbstract, DodoSellHelper {
    using UnsafeMath for uint256;
    using SafeTransferLib for IERC20;
    using FastDodoV1 for IDodoV1;

    function sellToDodoV1(IERC20 sellToken, uint256 bps, IDodoV1 dodo, bool quoteForBase, uint256 minBuyAmount)
        internal
    {
        uint256 sellAmount;
        unchecked {
            sellAmount = (sellToken.fastBalanceOf(address(this)) * bps).unsafeDiv(BASIS);
        }
        sellToken.safeApproveIfBelow(address(dodo), sellAmount);
        if (quoteForBase) {
            uint256 buyAmount = dodoQuerySellQuoteToken(dodo, sellAmount);
            if (buyAmount < minBuyAmount) {
                revertTooMuchSlippage(dodo.fast_BASE_TOKEN_(), minBuyAmount, buyAmount);
            }
            dodo.fastBuyBaseToken(buyAmount, sellAmount);
        } else {
            dodo.fastSellBaseToken(sellAmount, minBuyAmount);
        }
    }
}
