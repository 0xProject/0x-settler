// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.25;

import {IERC20} from "forge-std/interfaces/IERC20.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";
import {TooMuchSlippage} from "./SettlerErrors.sol";
import {FullMath} from "../vendor/FullMath.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

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
}

library Math {
    function divCeil(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 quotient = a / b;
        unchecked {
            uint256 remainder = a - quotient * b;
            if (remainder > 0) {
                return quotient + 1;
            } else {
                return quotient;
            }
        }
    }

    function sqrt(uint256 x) internal pure returns (uint256 y) {
        unchecked {
            uint256 z = x / 2 + 1;
            y = x;
            while (z < y) {
                y = z;
                z = (x / z + z) / 2;
            }
        }
    }
}

library DecimalMath {
    using Math for uint256;

    uint256 constant ONE = 10 ** 18;

    function mul(uint256 target, uint256 d) internal pure returns (uint256) {
        unchecked {
            return target * d / ONE;
        }
    }

    function mulCeil(uint256 target, uint256 d) internal pure returns (uint256) {
        unchecked {
            return (target * d).divCeil(ONE);
        }
    }

    function divFloor(uint256 target, uint256 d) internal pure returns (uint256) {
        unchecked {
            return target * ONE / d;
        }
    }

    function divCeil(uint256 target, uint256 d) internal pure returns (uint256) {
        unchecked {
            return (target * ONE).divCeil(d);
        }
    }
}

library DodoMath {
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
            uint256 V0V0V1V2 = DecimalMath.divCeil(V0 * V0 / V1, V2);
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
            uint256 kQ02Q1 = DecimalMath.mul(k, Q0) * Q0 / Q1; // kQ0^2/Q1
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

    enum RStatus {
        ONE,
        ABOVE_ONE,
        BELOW_ONE
    }

    struct DodoState {
        uint256 oraclePrice;
        uint256 K;
        uint256 B;
        uint256 Q;
        uint256 baseTarget;
        uint256 quoteTarget;
        RStatus rStatus;
    }

    function dodoQuerySellQuoteToken(IDodoV1 dodo, uint256 amount) internal view returns (uint256) {
        DodoState memory state;
        (state.baseTarget, state.quoteTarget) = dodo.getExpectedTarget();
        state.rStatus = RStatus(dodo._R_STATUS_());
        state.oraclePrice = dodo.getOraclePrice();
        state.Q = dodo._QUOTE_BALANCE_();
        state.B = dodo._BASE_BALANCE_();
        state.K = dodo._K_();

        unchecked {
            uint256 boughtAmount;
            // Determine the status (RStatus) and calculate the amount based on the
            // state
            if (state.rStatus == RStatus.ONE) {
                boughtAmount = _ROneSellQuoteToken(amount, state);
            } else if (state.rStatus == RStatus.ABOVE_ONE) {
                boughtAmount = _RAboveSellQuoteToken(amount, state);
            } else {
                uint256 backOneBase = state.B - state.baseTarget;
                uint256 backOneQuote = state.quoteTarget - state.Q;
                if (amount <= backOneQuote) {
                    boughtAmount = _RBelowSellQuoteToken(amount, state);
                } else {
                    boughtAmount = backOneBase + _ROneSellQuoteToken(amount - backOneQuote, state);
                }
            }
            // Calculate fees
            return DecimalMath.divFloor(boughtAmount, DecimalMath.ONE + dodo._MT_FEE_RATE_() + dodo._LP_FEE_RATE_());
        }
    }

    function _ROneSellQuoteToken(uint256 amount, DodoState memory state)
        private
        pure
        returns (uint256 receiveBaseToken)
    {
        unchecked {
            uint256 i = DecimalMath.divFloor(DecimalMath.ONE, state.oraclePrice);
            uint256 B2 = DodoMath._SolveQuadraticFunctionForTrade(
                state.baseTarget, state.baseTarget, DecimalMath.mul(i, amount), false, state.K
            );
            return state.baseTarget - B2;
        }
    }

    function _RAboveSellQuoteToken(uint256 amount, DodoState memory state)
        private
        pure
        returns (uint256 receieBaseToken)
    {
        unchecked {
            uint256 i = DecimalMath.divFloor(DecimalMath.ONE, state.oraclePrice);
            uint256 B2 = DodoMath._SolveQuadraticFunctionForTrade(
                state.baseTarget, state.B, DecimalMath.mul(i, amount), false, state.K
            );
            return state.B - B2;
        }
    }

    function _RBelowSellQuoteToken(uint256 amount, DodoState memory state)
        private
        pure
        returns (uint256 receiveBaseToken)
    {
        unchecked {
            uint256 Q1 = state.Q + amount;
            uint256 i = DecimalMath.divFloor(DecimalMath.ONE, state.oraclePrice);
            return DodoMath._GeneralIntegrate(state.quoteTarget, Q1, state.Q, i, state.K);
        }
    }
}

abstract contract DodoV1 is SettlerAbstract, DodoSellHelper {
    using FullMath for uint256;
    using SafeTransferLib for IERC20;

    function sellToDodoV1(IERC20 sellToken, uint256 bps, IDodoV1 dodo, bool quoteForBase, uint256 minBuyAmount)
        internal
    {
        uint256 sellAmount = sellToken.balanceOf(address(this)).mulDiv(bps, BASIS);
        sellToken.safeApproveIfBelow(address(dodo), sellAmount);
        if (quoteForBase) {
            uint256 buyAmount = dodoQuerySellQuoteToken(dodo, sellAmount);
            if (buyAmount < minBuyAmount) {
                revert TooMuchSlippage(sellToken, minBuyAmount, buyAmount);
            }
            dodo.buyBaseToken(buyAmount, sellAmount, new bytes(0));
        } else {
            dodo.sellBaseToken(sellAmount, minBuyAmount, new bytes(0));
        }
    }
}
