#!/usr/bin/env python3
"""Monotonicity certificate for `Ln.lnWad` (src/vendor/Ln.sol).

The claim: x1 < x2 implies lnWad(x1) <= lnWad(x2) over the whole domain
x in [1, 2**255).

Proof structure
===============

Write m for the Q103 mantissa and k for the exponent (x ~ m * 2**k with m in
[2**103, 2**104)). Adjacent inputs either share (m, k) (identical result),
advance m by one within an octave, or cross a clz seam from
(m = 2**104 - 2**(104-t), k) to (m = 2**103, k + 1) at x = 2**t. The
correction `+ eq(x, 10**18)` raises the single point x = 10**18 from -1 to 0,
which preserves order against both neighbors (checked exactly below).

Within an octave, the result is `sar(72, X1 * 5**27 + k*LN2 + BIAS)` with
X1 = sdiv(p(u) * z, q(u)); `sar` and the exact affine map preserve order, so
it suffices that X1 is nondecreasing in m. That follows from this chain:

1.  z = sdiv((S - m) << 100, m + S) is nonincreasing in m, stepping by 0 or -1
    per unit of m. The real argument zeta = (S - m)*2**100/(m + S) has
    d(zeta)/dm = -2*S*2**100/(m + S)**2, which is negative and (checked below)
    less than 1 in magnitude, and `sdiv` truncation toward zero is a monotone
    function of zeta.
2.  u = (z*z) >> 104 changes by at most 1 per unit step of z, because
    2*|z| + 1 < 2**104 (checked below).
3.  X1 = trunc(A(z)) with A(z) = p(u(z))*z/q(u(z)), and truncation toward zero
    is monotone, so it suffices that A is antitone in the integer z. Per unit
    step of z,
        A(z-1) - A(z) = R(u') + z*(R(u') - R(u)),   R = p/(-q),
    where u' = u(z-1) differs from u by at most 1. Splitting R into the
    real-coefficient rational R_real plus per-point truncation jitter,
    R(u') - R(u) = [R_real(u') - R_real(u)] + jitter, the real part has the
    helpful sign (R_real is nondecreasing -- checked below by exact interval
    subdivision -- and the sign of the u-step matches the sign of z), so
        A(z-1) - A(z) >= R_min - z_max * 2*J > 0
    where R_min is a lower bound for R on the domain (from exact integer
    interval propagation of the Horner stages, including truncation slop) and
    J bounds |R - R_real| at any point: each Horner stage truncation theta_i
    in [0, 1) at stage basis b_i, followed by j more multiplies by u,
    perturbs the final Q94 polynomial by less than 2**(94 - b_i) * u_max**j,
    so J <= (slop_p + R_max * slop_q) / |q|_min.

The clz seams do not satisfy a useful one-sided bound (the rational's error
at u_max enters both seam endpoints with the same sign and no cancellation),
so all 254 of them are verified exactly. The certified sign of the error at
u_max (negative, about -0.32 ulp weighted) is what makes them pass with slack
rather than by luck; this script re-derives the seam results from the EVM
mirror rather than trusting that analysis.

Everything here is exact integer/rational arithmetic -- no floating point.
"""

from __future__ import annotations

import sys
from fractions import Fraction

from formal.python.ln.check_ln_counterexample import (
    _BIAS,
    _C0,
    _K,
    _LN2,
    _P1,
    _P2,
    _P3,
    _P4,
    _Q1,
    _Q2,
    _Q3,
    _Q4,
    _S,
    WAD,
    ln_wad_evm,
)

# Stage layout mirrored from src/vendor/Ln.sol: (coefficient, basis, remaining
# multiplies by u after the coefficient is added). Signs follow the p~ = -p,
# z~ = -z convention used by the implementation.
W = 103
P_COEFFS = ((_P4, 68, 4), (-_P3, 80, 3), (_P2, 86, 2), (-_P1, 93, 1), (_C0, 94, 0))
Q_COEFFS = ((-_Q4, 96, 4), (_Q3, 87, 3), (-_Q2, 85, 2), (_Q1, 93, 1), (-_C0, 94, 0))
FINAL_BASIS = 94
Z_BASIS = 100
U_BASIS = 96


def _domain() -> tuple[int, int]:
    """Largest |z| over m in [2**W, 2**(W+1)) and largest u, as integers."""
    two_w = 1 << W
    z_lo = Fraction(((_S - two_w) << Z_BASIS), two_w + _S)
    z_hi = Fraction(((2 * two_w - 1 - _S) << Z_BASIS), 2 * two_w - 1 + _S)
    zmax = max(int(z_lo), int(-z_hi), int(-z_lo), int(z_hi))
    umax = (zmax * zmax) >> (2 * Z_BASIS - U_BASIS)
    return zmax, umax + 1


def _stage_intervals(coeffs, umax_int, monic_first):
    """Exact integer interval propagation of the Horner stages, including the
    [0, 1) truncation slop of each renormalizing shift. Returns the list of
    per-stage (lo, hi) bounds."""
    (c0, b0, _), rest = coeffs[0], coeffs[1:]
    if monic_first:
        lo, hi = c0, umax_int + c0
    else:
        lo = hi = c0
    prev_basis = U_BASIS if monic_first else b0
    out = [(lo, hi)]
    for c, b, _ in rest:
        shift = prev_basis + U_BASIS - b
        cands = (0, lo * umax_int, hi * umax_int)
        lo = min(cands) // (1 << shift) - 1 + c
        hi = max(cands) // (1 << shift) + c
        assert max(abs(lo * umax_int), abs(hi * umax_int)).bit_length() < 255, "mul overflow"
        prev_basis = b
        out.append((lo, hi))
    return out


def _slop(coeffs, umax_int) -> Fraction:
    """Bound, in final-basis units, on |integer Horner value - real-coefficient
    polynomial * 2**FINAL_BASIS|: the sum over stages of the truncation range
    [0, 1) scaled by 2**(FINAL_BASIS - basis) and u_max**j."""
    u = Fraction(umax_int, 1 << U_BASIS)
    total = Fraction(0)
    for _, b, j in coeffs[1:]:
        total += Fraction(1 << FINAL_BASIS, 1 << b) * u**j
    return total


def _poly_coeffs(coeffs):
    """Real-coefficient polynomial as exact rationals, low order first."""
    out = [Fraction(0)] * 6
    for c, b, j in coeffs:
        out[j] += Fraction(c, 1 << b)
    return out


def _poly_mul(a, b):
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def _poly_deriv(a):
    return [i * c for i, c in enumerate(a)][1:]


def _interval_horner(coeffs, lo: Fraction, hi: Fraction) -> tuple[Fraction, Fraction]:
    vlo = vhi = coeffs[-1]
    for c in reversed(coeffs[:-1]):
        cands = (vlo * lo, vlo * hi, vhi * lo, vhi * hi)
        vlo, vhi = min(cands) + c, max(cands) + c
    return vlo, vhi


def _certify_positive(coeffs, lo: Fraction, hi: Fraction, depth: int = 0) -> bool:
    """Certify min of the polynomial over [lo, hi] is nonnegative by exact
    interval bisection."""
    blo, _ = _interval_horner(coeffs, lo, hi)
    if blo >= 0:
        return True
    if depth >= 40:
        return False
    mid = (lo + hi) / 2
    return _certify_positive(coeffs, lo, mid, depth + 1) and _certify_positive(coeffs, mid, hi, depth + 1)


def main() -> int:
    zmax, umax_int = _domain()

    # (1) the mantissa -> z map is antitone with unit steps.
    two_w = 1 << W
    assert 2 * _S << Z_BASIS < (two_w + _S) ** 2, "|d(zeta)/dm| >= 1"

    # (2) u steps by at most one per unit step of z.
    assert 2 * zmax + 1 < 1 << (2 * Z_BASIS - U_BASIS), "u step > 1"

    # (3a) integer interval propagation: p > 0, q < 0, and R = p/(-q) bounds.
    pst = _stage_intervals(P_COEFFS, umax_int, monic_first=False)
    qst = _stage_intervals(Q_COEFFS, umax_int, monic_first=True)
    p_lo, p_hi = pst[-1]
    q_lo, q_hi = qst[-1]
    assert p_lo > 0, "p not positive"
    assert q_hi < 0, "q not negative"
    r_min = Fraction(p_lo, -q_lo)
    r_max = Fraction(p_hi, -q_hi)

    # (3b) truncation jitter bound J and the step inequality.
    slop_p = _slop(P_COEFFS, umax_int)
    slop_q = _slop(Q_COEFFS, umax_int)
    jitter = (slop_p + r_max * slop_q) / (-q_hi)
    step_margin = r_min - zmax * 2 * jitter
    assert step_margin > 0, f"within-octave step margin not positive: {float(step_margin)}"

    # (3c) the real-coefficient rational is nondecreasing on [0, u_max]:
    # N(u) = P'(u) * (-Q(u)) + P(u) * Q'(u) >= 0.
    pr = _poly_coeffs(P_COEFFS)
    qr = _poly_coeffs(Q_COEFFS) + []
    qr.append(Fraction(0))
    qr[5] += 1  # monic u**5 term
    n_poly = [a + b for a, b in zip(_poly_mul(_poly_deriv(pr), [-c for c in qr]),
                                    _poly_mul(pr, _poly_deriv(qr)))]
    u_hi = Fraction(umax_int, 1 << U_BASIS)
    assert _certify_positive(n_poly, Fraction(0), u_hi), "R_real not monotone"

    # clz seams: verified exactly, one pair per exponent.
    for t in range(1, 255):
        assert ln_wad_evm(1 << t) >= ln_wad_evm((1 << t) - 1), f"seam at 2**{t}"

    # the x == 10**18 correction point and its neighbors.
    assert ln_wad_evm(WAD) == 0
    assert ln_wad_evm(WAD - 1) <= 0 <= ln_wad_evm(WAD + 1)

    print("within-octave step margin:", float(step_margin))
    print("R in [", float(r_min), ",", float(r_max), "]")
    print("slop_p =", float(slop_p), " slop_q =", float(slop_q), " z_max*2J =", float(zmax * 2 * jitter))
    print("all 254 clz seams monotone; lnWad(10**18) == 0")
    print("monotonicity certificate: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
