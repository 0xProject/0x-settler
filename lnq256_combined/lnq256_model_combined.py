"""Combined floor(ln(x) * 2**256) model for 512-bit positive integers.

Stage 1: Q216 Remez-optimal [6/7] rational + G=24 guard bits
Stage 2: One-shared-2-bucket micro reduction + adaptive odd atanh series

Stage 1 (fast path, ~99.965% of inputs)
----------------------------------------
- Normalize with CLZ / msb.
- 16-bucket coarse reduction r0 = n / 32.
- Fast kernel:
      ln(1 + u) = 2 z + (2/3) z^3 + (2/5) z^5 + (2/7) z^7 + z^9 * R(w)
  where z = u / (2 + u), w = z^2.
- R is a Remez-optimal [6/7] rational, Q0 = 1 implicit, coefficients in Q216.
- Guard bits: G_FAST = 24 (Q280 working precision).
- Per-bucket additive bias FAST_BIAS_Q[bucket] in Q(256 + 24).
- Per-bucket certified radius FAST_RADIUS_Q[bucket] in Q(256 + 24).

Stage 2 (fallback, ~0.035% of inputs)
--------------------------------------
When the fast-path same-floor test is ambiguous, the fallback resolves the
boundary decision exactly.

Micro reduction uses 1 shared 2-bucket profile in |z|:
- lower bucket: c0 = 0 (free -- no constant needed)
- upper bucket: c1 = 1/64 (dyadic -- encoded as a shift)
- boundary: 1/128 (dyadic -- encoded as a comparison shift)
- only 1 nonzero additive constant: A64_Q256 = floor(2 * atanh(1/64) * 2^256)

This saves ~128 bytes of stage-2 constants compared to the prior 2-bucket
design with arbitrary Q255 centers.

After micro reduction, the adaptive odd atanh series certifies the sign:
    2*atanh(t) = 2*(t + t^3/3 + t^5/5 + ...)
with remainder bound: R_m <= 2*|t|^(2m+3) / ((2m+3)*(1 - t^2)).

Because c1 = 1/64 is smaller than the prior arbitrary centers, the reduced
|t| can be slightly larger for inputs in the upper micro bucket, requiring
~8-9% more series terms on average when fallback runs.  At a 0.035% fallback
rate this is negligible.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Tuple, List
import mpmath as mp

# ---------------------------------------------------------------------------
# Stage 1 hyperparameters
# ---------------------------------------------------------------------------

N0 = [31, 29, 28, 26, 25, 24, 23, 22, 21, 20, 19, 19, 18, 17, 17, 16]

COEFF_BITS = 216
G_FAST = 24
SCALE = 1 << 256
SCALE_FAST = 1 << (256 + G_FAST)

# Per-bucket bias and certified radius in Q(256 + 24).
# Calibrated on 6-seed battery (seeds 1..6), validated on seeds 7..15.
FAST_BIAS_Q = [-150, -862, 1222, -348, 42, 196, 188, 154, 42, 2, -250, 1356, 33, -1140, 104, -179]
FAST_RADIUS_Q = [1199, 5810, 6293, 3502, 148, 907, 1518, 891, 150, 103, 3382, 6313, 44, 5792, 514, 1162]

# ---------------------------------------------------------------------------
# Remez-optimal [6/7] rational for the atanh residual, Q216 coefficients
# ---------------------------------------------------------------------------
#
# Approximates R(w) where:
#   2*atanh(z) = 2z + (2/3)z^3 + (2/5)z^5 + (2/7)z^7 + z^9 * R(z^2)
#
# R(w) = P(w) / Q(w), with Q(w) = 1 + q1*w + ... + q7*w^7
# Minimax approximation error: 5.2e-67
# Horner quantization error at Q216: 1.2e-65 in R(w)
# Max Horner product: 464 bits (48-bit headroom under EVM's 512-bit limit)

FAST_P = [
    23402731481901597043981783929704540515310021200122024723180217230,
    -79147257707505802445321067591641956191893173416852452736772062152,
    105567710592264149655895345681626059811476843737297988261266061719,
    -70280975374256110316161633634422318148227266301984626622229992403,
    24260002286396336386066722552550012983868598792106518362024927003,
    -4031542932217000284709476574733749729411078599780997370963274225,
    244504971595928297752455626929162943780014968997496095305629633,
]

FAST_Q = [
    -442327261958050172847695917721755520215342540249012582887183524330,
    764050311468718105200385962090128619260907774191827731723142005680,
    -698357271234189264361221256846859697717152049975428562654123141828,
    361238115265142525912392094197617069095853073482781560893409836147,
    -104363990572981334424492003201115405883168394510253602517671885198,
    15307805589224505617810266544830173595922016396186463802374189830,
    -855788182002653539265473379773190817088756284166928459588115371,
]

# ---------------------------------------------------------------------------
# Q280 constants for the fast path
# ---------------------------------------------------------------------------

LN2_FAST = 1346555465407776362904412453392572616323996772503848637639390270677811788899942905974

C0_FAST = [
    61677208584394585267140784167174339638468744344880990964782714436880008665083258087,
    191236467202741381933332167506278261044529067668350527406150496492711399858009013218,
    259407282587240253532356295726101822527956106840500618120985309764070011176522172389,
    403374534756206312556061437411144855760105463110602808283916896951274278480683415796,
    479567394129994369684562583036504416766865764150359794367809843154523408843592209188,
    558871013003103184669805819209418693351264500369407928464301894881121645102383815017,
    641550251999619637945331520863360863304390452700127000539092042511911805344223288136,
    727905308350582535288450863281468740092713293384218459274701694181471001815119603305,
    818278295590343438202162114935520515879220607209908546585287204645191656278905987406,
    913061429768885366294487518214538516545431268327104216003600056916167598871767557581,
    1012707317155356367346065177301600422978381312071798613877787687735746954663336476024,
    1012707317155356367346065177301600422978381312071798613877787687735746954663336476024,
    1117742026006206369339611638418837386702529000738815856928603789762243290204767630035,
    1228781898502039120320684340066093177251806363932778194372749743871656510080269305244,
    1228781898502039120320684340066093177251806363932778194372749743871656510080269305244,
    1346555465407776362904412453392572616323996772503848637639390270677811788899942905974,
]

# ---------------------------------------------------------------------------
# Stage 2: one-shared-2-bucket micro reduction
# ---------------------------------------------------------------------------
#
# Lower bucket: c0 = 0                  (free)
# Upper bucket: c1 = 64/4096 = 1/64     (shift-encoded)
# Boundary:     b  = 32/4096 = 1/128    (shift-encoded)
#
# Only 1 nonzero additive constant: floor(2 * atanh(1/64) * 2^256)
# Total stage-2 constant payload: 32 bytes (vs ~160 bytes in prior design)

STAGE2_DEN_BITS = 12
STAGE2_DEN = 1 << STAGE2_DEN_BITS
CENTER0_NUM = 0
CENTER1_NUM = 64
BOUND_NUM = 32

A64_Q256 = 3618797306320365907038389356091966445740960606432524368886479476623023988535
FALLBACK_EXTRA_BITS = 40

MAX_SERIES_TERMS = 80

# High-precision working precision.
MP_DPS = 420
mp.mp.dps = MP_DPS
MP_TWO_POW_256 = mp.mpf(2) ** 256
MP_TWO_POW_320 = mp.mpf(2) ** 320
LN2_Q256 = mp.log(2) * MP_TWO_POW_256
LN2_Q256_FLOOR = int(mp.floor(LN2_Q256))
LN2_Q320_FLOOR = int(mp.floor(mp.log(2) * MP_TWO_POW_320))

CENTER0 = mp.mpf(CENTER0_NUM) / STAGE2_DEN
CENTER1 = mp.mpf(CENTER1_NUM) / STAGE2_DEN
BOUND_STAGE2 = mp.mpf(BOUND_NUM) / STAGE2_DEN
A_MICRO_STAGE2 = [
    2 * mp.atanh(CENTER0) * MP_TWO_POW_256,  # = 0 exactly
    2 * mp.atanh(CENTER1) * MP_TWO_POW_256,
]

# Exact Q256-scale coarse constants for the fallback correction path.
C0_EXACT_Q256 = [-mp.log(mp.mpf(n) / 32) * MP_TWO_POW_256 for n in N0]
C0_EXACT_Q256_FLOOR = [int(mp.floor(v)) for v in C0_EXACT_Q256]
C0_EXACT_Q320_FLOOR = [int(mp.floor(v * (1 << 64))) for v in C0_EXACT_Q256]
A64_Q320_FLOOR = int(mp.floor(A_MICRO_STAGE2[1] * (1 << 64)))

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _round_div(num: int, den: int) -> int:
    if den <= 0:
        raise ValueError("den must be positive")
    if num >= 0:
        return (num + den // 2) // den
    return -(((-num) + den // 2) // den)


def _ceil_div(num: int, den: int) -> int:
    if den <= 0:
        raise ValueError("den must be positive")
    return -(-num // den)


def _floor_div_pow2_signed(x: int, shift: int) -> int:
    if x >= 0:
        return x >> shift
    return -(((-x) + (1 << shift) - 1) >> shift)


def _mulshr_round(a: int, b: int, shift: int) -> int:
    prod = a * b
    if prod >= 0:
        return (prod + (1 << (shift - 1))) >> shift
    return -(((-prod) + (1 << (shift - 1))) >> shift)


def _mulshr_floor(a: int, b: int, shift: int) -> int:
    prod = a * b
    if prod >= 0:
        return prod >> shift
    return -(((-prod) + (1 << shift) - 1) >> shift)


def _qmul_coeff(a_qc: int, b_q256: int) -> int:
    return _mulshr_round(a_qc, b_q256, 256)


def _mulg_fast(a: int, b: int) -> int:
    return _mulshr_round(a, b, 256 + G_FAST)


# ---------------------------------------------------------------------------
# Stage 1: fast path
# ---------------------------------------------------------------------------


def _eval_fast_rational(w_q256: int) -> int:
    """Evaluate R(w) via Horner at Q216 precision."""
    num = FAST_P[-1]
    for c in reversed(FAST_P[:-1]):
        num = _qmul_coeff(num, w_q256) + c

    den = FAST_Q[-1]
    for c in reversed(FAST_Q[:-1]):
        den = _qmul_coeff(den, w_q256) + c
    den = _qmul_coeff(den, w_q256) + (1 << COEFF_BITS)

    return _round_div(num << COEFF_BITS, den)


@dataclass(frozen=True)
class CoarseState:
    exponent: int
    bucket: int
    coarse_num: int
    u_num: int
    z_den: int


def extract_state(x: int) -> CoarseState:
    if x <= 0:
        raise ValueError("x must be positive")
    e = x.bit_length() - 1
    j = ((x << (4 - e)) & 0xF) if e < 4 else ((x >> (e - 4)) & 0xF)
    n = N0[j]
    u_num = n * x - (1 << (e + 5))
    z_den = (1 << (e + 6)) + u_num
    return CoarseState(e, j, n, u_num, z_den)


def fast_eval_state(state: CoarseState) -> int:
    """Evaluate the fast path using Solidity-style truncation points.

    The EVM implementation keeps the Horner chain rounded, but its Q280 power
    chain and residual accumulation truncate on right shifts. It also rounds
    the initial z division only when the denominator fits in one word.
    """
    z_num = abs(state.u_num) * SCALE_FAST
    if state.z_den < SCALE:
        z_hi = _round_div(z_num, state.z_den)
    else:
        z_hi = z_num // state.z_den

    w_hi = _mulshr_floor(z_hi, z_hi, 256 + G_FAST)
    w_q256 = w_hi >> G_FAST

    r_qc = _eval_fast_rational(w_q256)

    z3_hi = _mulshr_floor(z_hi, w_hi, 256 + G_FAST)
    z5_hi = _mulshr_floor(z3_hi, w_hi, 256 + G_FAST)
    z7_hi = _mulshr_floor(z5_hi, w_hi, 256 + G_FAST)
    z9_hi = _mulshr_floor(z7_hi, w_hi, 256 + G_FAST)

    term3_hi = _round_div(z3_hi * 2, 3)
    term5_hi = _round_div(z5_hi * 2, 5)
    term7_hi = _round_div(z7_hi * 2, 7)
    resid_hi = _mulshr_floor(z9_hi, r_qc, COEFF_BITS)

    local_hi = (z_hi << 1) + term3_hi + term5_hi + term7_hi + resid_hi
    prefix_hi = state.exponent * LN2_FAST + C0_FAST[state.bucket]

    q_fast = prefix_hi - local_hi if state.u_num < 0 else prefix_hi + local_hi
    return q_fast + FAST_BIAS_Q[state.bucket]


def _fast_interval_floor(q_fast: int, bucket: int) -> Tuple[int, int]:
    rad = FAST_RADIUS_Q[bucket]
    lo = _floor_div_pow2_signed(q_fast - rad, G_FAST)
    hi = _floor_div_pow2_signed(q_fast + rad, G_FAST)
    return lo, hi


# ---------------------------------------------------------------------------
# Stage 2: one-profile micro reduction + adaptive odd atanh series
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ResidualInfo:
    micro_bucket: int
    sign_z: int
    sign_t: int
    z_q256: int
    t_q256: int
    terms_used: int


def _micro_reduce_from_state(state: CoarseState) -> Tuple[mp.mpf, int, int, mp.mpf, mp.mpf]:
    """One shared 2-bucket micro reduction in exact arithmetic."""
    z = mp.mpf(state.u_num) / mp.mpf(state.z_den)
    sign_z = -1 if z < 0 else 1
    a = -z if z < 0 else z
    k = 0 if a < BOUND_STAGE2 else 1
    c_abs = CENTER0 if k == 0 else CENTER1
    c = c_abs * sign_z
    t = (z - c) / (1 - z * c)
    return z, k, sign_z, c, t


def _micro_reduce_q256_from_state(state: CoarseState) -> Tuple[int, int, int, int, int]:
    """One shared 2-bucket micro reduction using Q256 integer arithmetic.

    Returns (z_q256, micro_bucket, sign_z, sign_t, t_q256_abs).
    """
    z_q256 = abs(state.u_num) * SCALE // state.z_den
    sign_z = -1 if state.u_num < 0 else 1
    if z_q256 < (1 << 249):
        return z_q256, 0, sign_z, sign_z, z_q256

    c_q256 = 1 << 250
    # 1 - z*c in Q256 is 2^256 - ceil(z / 64) because c = 1/64 exactly.
    t_den_q256 = SCALE - ((z_q256 + 63) >> 6)
    diff = z_q256 - c_q256
    if diff >= 0:
        sign_t = sign_z
        t_q256_abs = (diff << 256) // t_den_q256
    else:
        sign_t = -sign_z
        t_q256_abs = ((-diff) << 256) // t_den_q256
    return z_q256, 1, sign_z, sign_t, t_q256_abs


def _micro_reduce_q280_bounds_from_state(
    state: CoarseState,
) -> Tuple[int, int, int, int, int, int]:
    """Return a Q280 interval for the reduced |t| and its sign.

    Returns:
        (micro_bucket, sign_z, sign_t, z_lo_q280, t_lo_q280, t_hi_q280)
    """
    z_lo_q280 = abs(state.u_num) * SCALE_FAST // state.z_den
    sign_z = -1 if state.u_num < 0 else 1

    if z_lo_q280 < (1 << (249 + G_FAST)):
        return 0, sign_z, sign_z, z_lo_q280, z_lo_q280, z_lo_q280 + 1

    z_hi_q280 = z_lo_q280 + 1
    c_q280 = 1 << (250 + G_FAST)

    if z_lo_q280 < c_q280:
        sign_t = -sign_z
        num_lo = c_q280 - z_hi_q280
        den_lo = SCALE_FAST - (z_hi_q280 >> 6)
        t_lo_q280 = 0 if num_lo == 0 else (num_lo * SCALE_FAST) // den_lo

        num_hi = c_q280 - z_lo_q280
        den_hi = SCALE_FAST - ((z_lo_q280 + 63) >> 6)
        t_hi_q280 = 0 if num_hi == 0 else _ceil_div(num_hi * SCALE_FAST, den_hi)
    else:
        sign_t = sign_z
        num_lo = z_lo_q280 - c_q280
        den_lo = SCALE_FAST - (z_lo_q280 >> 6)
        t_lo_q280 = 0 if num_lo == 0 else (num_lo * SCALE_FAST) // den_lo

        num_hi = z_hi_q280 - c_q280
        den_hi = SCALE_FAST - ((z_hi_q280 + 63) >> 6)
        t_hi_q280 = 0 if num_hi == 0 else _ceil_div(num_hi * SCALE_FAST, den_hi)

    return 1, sign_z, sign_t, z_lo_q280, t_lo_q280, t_hi_q280


def accurate_resolve_state(
    state: CoarseState,
    q_fast: int,
    q_lo: int,
    q_hi: int,
    *,
    max_terms: int = MAX_SERIES_TERMS,
) -> Tuple[int, ResidualInfo]:
    """Resolve an ambiguous fast-path case with a direct Q320 certification.

    The fallback reconstructs the exact coarse prefix at Q320 and certifies the
    remaining local 2*atanh(t) term using Q280 bounds for |t| together with a
    Q320 odd-series accumulation. The extra 40 bits prevent the per-term
    round-up slack from growing enough to flip the final floor decision.
    """
    z_q256, _, _, _, t_q256_abs = _micro_reduce_q256_from_state(state)
    k, sign_z, sign_t, _, t_lo_q280, t_hi_q280 = _micro_reduce_q280_bounds_from_state(state)

    prefix_lo_q320 = state.exponent * LN2_Q320_FLOOR + C0_EXACT_Q320_FLOOR[state.bucket]
    prefix_hi_q320 = prefix_lo_q320 + state.exponent + 1

    micro_lo_q320 = 0
    micro_hi_q320 = 0
    if k != 0:
        if sign_z > 0:
            micro_lo_q320 = A64_Q320_FLOOR
            micro_hi_q320 = A64_Q320_FLOOR + 1
        else:
            micro_lo_q320 = -(A64_Q320_FLOOR + 1)
            micro_hi_q320 = -A64_Q320_FLOOR

    target_q320 = q_hi << (G_FAST + FALLBACK_EXTRA_BITS)
    a2_lo_q280 = (t_lo_q280 * t_lo_q280) >> (256 + G_FAST)
    a2_hi_q280 = _ceil_div(t_hi_q280 * t_hi_q280, SCALE_FAST)
    pow_lo_q280 = t_lo_q280
    pow_hi_q280 = t_hi_q280
    partial_lo_q320 = 0
    partial_hi_q320 = 0

    for m in range(max_terms):
        odd = 2 * m + 1
        partial_lo_q320 += ((2 * pow_lo_q280) << FALLBACK_EXTRA_BITS) // odd
        partial_hi_q320 += _ceil_div((2 * pow_hi_q280) << FALLBACK_EXTRA_BITS, odd)

        next_pow_lo_q280 = (pow_lo_q280 * a2_lo_q280) >> (256 + G_FAST)
        next_pow_hi_q280 = _ceil_div(pow_hi_q280 * a2_hi_q280, SCALE_FAST)
        den_q560 = (SCALE_FAST - a2_hi_q280) * (odd + 2)
        rem_hi_q320 = _ceil_div(next_pow_hi_q280 << (G_FAST + FALLBACK_EXTRA_BITS + 257), den_q560)

        tail_lo_q320 = partial_lo_q320
        tail_hi_q320 = partial_hi_q320 + rem_hi_q320

        if sign_t > 0:
            lo_q320 = prefix_lo_q320 + micro_lo_q320 + tail_lo_q320
            hi_q320 = prefix_hi_q320 + micro_hi_q320 + tail_hi_q320
        else:
            lo_q320 = prefix_lo_q320 + micro_lo_q320 - tail_hi_q320
            hi_q320 = prefix_hi_q320 + micro_hi_q320 - tail_lo_q320

        if hi_q320 < target_q320:
            result = q_lo
            terms_used = m + 1
            break
        if lo_q320 >= target_q320:
            result = q_hi
            terms_used = m + 1
            break

        pow_lo_q280 = next_pow_lo_q280
        pow_hi_q280 = next_pow_hi_q280
    else:
        raise RuntimeError("anchored interval fallback exhausted max_terms before certifying")

    info = ResidualInfo(
        micro_bucket=k,
        sign_z=sign_z,
        sign_t=sign_t,
        z_q256=z_q256,
        t_q256=t_q256_abs,
        terms_used=terms_used,
    )
    return result, info


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------


def floor_ln_q256(
    x: int,
    *,
    max_terms: int = MAX_SERIES_TERMS,
) -> Tuple[int, bool, int]:
    """Return floor(ln(x) * 2^256).

    Returns (result, used_fallback, terms_used).
    """
    if x <= 0:
        raise ValueError("x must be positive")
    if x == 1:
        return 0, False, 0

    state = extract_state(x)
    q_fast = fast_eval_state(state)
    q_lo, q_hi = _fast_interval_floor(q_fast, state.bucket)
    if q_lo == q_hi:
        return q_lo, False, 0

    result, info = accurate_resolve_state(
        state, q_fast, q_lo, q_hi, max_terms=max_terms
    )
    return result, True, info.terms_used


# ---------------------------------------------------------------------------
# Truth / diagnostics
# ---------------------------------------------------------------------------


def true_floor_ln_q256(x: int) -> int:
    if x <= 0:
        raise ValueError("x must be positive")
    if x == 1:
        return 0
    last = None
    for dps in (220, 320, 420):
        mp.mp.dps = dps
        cur = int(mp.floor(mp.log(mp.mpf(x)) * (mp.mpf(2) ** 256)))
        if cur == last:
            mp.mp.dps = MP_DPS
            return cur
        last = cur
    mp.mp.dps = MP_DPS
    return last


def hard_boundary_family() -> List[int]:
    """Inputs engineered to sit near Q256 integer boundaries."""
    saved = mp.mp.dps
    mp.mp.dps = max(saved, 420)
    out: List[int] = []
    seen = set()
    for b in range(279, 512):
        n = int(mp.nint(mp.mpf(b) * mp.log(2) * (mp.mpf(2) ** 256)))
        x = int(mp.nint(mp.e ** (mp.mpf(n) / (mp.mpf(2) ** 256))))
        if x not in seen:
            out.append(x)
            seen.add(x)
    mp.mp.dps = saved
    return out


def smoke() -> None:
    samples = [1, 2, 3, 7, 8, 9, (1 << 255) - 19, 1 << 255, (1 << 512) - 1]
    for x in samples:
        got, used_fb, terms = floor_ln_q256(x)
        truth = true_floor_ln_q256(x)
        print(f"x={x}")
        print(f"  got   = {got}")
        print(f"  truth = {truth}")
        print(f"  match = {got == truth}")
        print(f"  fallback={used_fb}, terms={terms}")
        print()


if __name__ == "__main__":
    smoke()
