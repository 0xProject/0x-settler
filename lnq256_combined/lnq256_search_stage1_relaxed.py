"""Search harness for relaxed stage-1 lnQ256 bounds.

The contract target is no longer exact floor(2^256 * ln(x)). Instead, we seek
one shared stage-1 skeleton that can produce:

- lower in [floor(y) - 1, floor(y)]
- upper in [ceil(y), ceil(y) + 1]

where y = 2^256 * ln(x).

The search space keeps the same structure as the existing fast path:

- 16-bucket coarse reduction
- z = u / (2 + u), w = z^2
- a few explicit odd powers of z
- one residual approximant in w
- either per-bucket or shared additive bias and symmetric radius

This script explores whether the relaxed contract lets us shrink:

- the number of explicit z powers
- the numerator / denominator degrees of the residual approximant
- coefficient precision
- guard bits

All validation uses mpmath.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
import sys
from typing import Dict, Iterable, List, Sequence, Tuple

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from lnq256_case_battery import build_battery, merge_batteries
from lnq256_common import N0, SCALE, _mulshr_floor, _qmul_coeff, _round_div, extract_state, hard_boundary_family
from lnq256_stage1_q216_reference import C0_FAST, FAST_P, FAST_Q, G_FAST, LN2_FAST
from remez_rational import W_MAX, rational_remez

mp.mp.dps = 420
MP_TWO_POW_256 = mp.mpf(2) ** 256

# First broad-random counterexample for the over-aggressive z^5/[6/7]/Q218/G9 point.
RELAXED_RANDOM_REGRESSIONS: Tuple[int, ...] = (
    6083672293606572322187875092284454538431936916431621235759156166353632673526038496710872370707557598536064321330255323916722534270660992310761560636054157,
)


@dataclass(frozen=True)
class KernelSpec:
    name: str
    explicit_max_odd: int
    numer_degree: int
    denom_degree: int
    coeff_bits: int
    guard_bits: int
    defer_residual_division: bool = False
    deferred_division_mode: str = "round"


@dataclass
class CaseData:
    x: int
    truth_floor: int
    truth_ceil: int
    log_q256: mp.mpf
    bucket: int
    state: object


@dataclass
class CandidateResult:
    spec: KernelSpec
    calibration_mode: str
    ok: bool
    lower_bad: int
    upper_bad: int
    lower_exact: int
    lower_minus1: int
    upper_exact: int
    upper_plus1: int
    max_radius: int
    max_abs_bias: int
    coeff_bytes: int
    table_bytes: int
    mulshr_count: int
    horner_mults: int
    division_count: int
    biases: List[int]
    radii: List[int]


def _ceil_div_pow2_signed(x: int, shift: int) -> int:
    return -((-x) >> shift)


def q_boundary_shift_pm64() -> List[int]:
    ln2 = mp.log(2)
    cases: List[int] = []
    for b in range(279, 512):
        center_q = int(mp.nint(ln2 * b * MP_TWO_POW_256))
        for dq in range(-64, 65):
            t = mp.mpf(center_q + dq) / MP_TWO_POW_256
            x = int(mp.nint(mp.e**t))
            if 1 <= x < (1 << 512):
                cases.append(x)
    seen = set()
    uniq: List[int] = []
    for x in cases:
        if x not in seen:
            uniq.append(x)
            seen.add(x)
    return uniq


def build_search_battery(random_cases: int, boundary_cases: int, seeds: Sequence[int]) -> List[int]:
    batteries = [build_battery(random_cases, boundary_cases, seed) for seed in seeds]
    batteries.append(hard_boundary_family())
    batteries.append(q_boundary_shift_pm64())
    batteries.append(list(RELAXED_RANDOM_REGRESSIONS))
    return merge_batteries(batteries)


def precompute_case_data(cases: Sequence[int]) -> List[CaseData]:
    data: List[CaseData] = []
    for x in cases:
        log_q256 = mp.log(x) * MP_TWO_POW_256
        truth_floor = int(mp.floor(log_q256))
        truth_ceil = int(mp.ceil(log_q256))
        state = extract_state(x)
        data.append(CaseData(x, truth_floor, truth_ceil, log_q256, state.bucket, state))
    return data


def residual_limit(explicit_max_odd: int) -> mp.mpf:
    return mp.mpf(2) / (explicit_max_odd + 2)


def residual_function(explicit_max_odd: int):
    def f(w: mp.mpf) -> mp.mpf:
        if w == 0:
            return residual_limit(explicit_max_odd)
        s = mp.sqrt(w)
        series = s
        odd = 3
        while odd <= explicit_max_odd:
            series += s**odd / odd
            odd += 2
        return 2 * (mp.atanh(s) - series) / (s ** (explicit_max_odd + 2))

    return f


@lru_cache(maxsize=None)
def real_remez_coeffs(explicit_max_odd: int, numer_degree: int, denom_degree: int) -> Tuple[Tuple[mp.mpf, ...], Tuple[mp.mpf, ...]]:
    f = residual_function(explicit_max_odd)
    p_coeffs, q_coeffs, _ = rational_remez(
        f,
        mp.mpf(0),
        W_MAX,
        numer_degree,
        denom_degree,
        max_iter=40,
        grid_size=6000,
        verbose=False,
    )
    return tuple(p_coeffs), tuple(q_coeffs)


@lru_cache(maxsize=None)
def quantized_coeffs(explicit_max_odd: int, numer_degree: int, denom_degree: int, coeff_bits: int) -> Tuple[Tuple[int, ...], Tuple[int, ...]]:
    if (explicit_max_odd, numer_degree, denom_degree, coeff_bits) == (7, 6, 7, 216):
        return tuple(FAST_P), tuple(FAST_Q)
    p_real, q_real = real_remez_coeffs(explicit_max_odd, numer_degree, denom_degree)
    scale = mp.mpf(1 << coeff_bits)
    p_int = tuple(int(mp.nint(c * scale)) for c in p_real)
    q_int = tuple(int(mp.nint(c * scale)) for c in q_real)
    return p_int, q_int


@lru_cache(maxsize=None)
def fast_constants(guard_bits: int) -> Tuple[int, Tuple[int, ...]]:
    if guard_bits == G_FAST:
        return LN2_FAST, tuple(C0_FAST)
    scale = mp.mpf(2) ** (256 + guard_bits)
    ln2_fast = int(mp.floor(mp.log(2) * scale))
    c0_fast = tuple(int(mp.floor(-mp.log(mp.mpf(n) / 32) * scale)) for n in N0)
    return ln2_fast, c0_fast


def eval_quantized_rational_parts(
    w_q256: int,
    p_int: Sequence[int],
    q_int: Sequence[int],
    coeff_bits: int,
) -> Tuple[int, int]:
    num = p_int[-1]
    for c in reversed(p_int[:-1]):
        num = _qmul_coeff(num, w_q256) + c

    if not q_int:
        return num, 1

    den = q_int[-1]
    for c in reversed(q_int[:-1]):
        den = _qmul_coeff(den, w_q256) + c
    den = _qmul_coeff(den, w_q256) + (1 << coeff_bits)
    return num, den


def eval_quantized_rational(w_q256: int, p_int: Sequence[int], q_int: Sequence[int], coeff_bits: int) -> int:
    num, den = eval_quantized_rational_parts(w_q256, p_int, q_int, coeff_bits)
    if not q_int:
        return num
    return _round_div(num << coeff_bits, den)


def eval_candidate_raw(state, spec: KernelSpec, p_int: Sequence[int], q_int: Sequence[int], ln2_fast: int, c0_fast: Sequence[int]) -> int:
    scale_fast = 1 << (256 + spec.guard_bits)
    z_num = abs(state.u_num) * scale_fast
    if state.z_den < SCALE:
        z_hi = _round_div(z_num, state.z_den)
    else:
        z_hi = z_num // state.z_den

    w_hi = _mulshr_floor(z_hi, z_hi, 256 + spec.guard_bits)
    w_q256 = w_hi >> spec.guard_bits if spec.guard_bits else w_hi
    if spec.defer_residual_division and q_int:
        r_num, r_den = eval_quantized_rational_parts(w_q256, p_int, q_int, spec.coeff_bits)
    else:
        r_qc = eval_quantized_rational(w_q256, p_int, q_int, spec.coeff_bits)

    powers: Dict[int, int] = {1: z_hi}
    current = z_hi
    for odd in range(3, spec.explicit_max_odd + 3, 2):
        current = _mulshr_floor(current, w_hi, 256 + spec.guard_bits)
        powers[odd] = current

    local_hi = z_hi << 1
    for odd in range(3, spec.explicit_max_odd + 1, 2):
        local_hi += _round_div(powers[odd] * 2, odd)

    tail_hi = powers[spec.explicit_max_odd + 2]
    if spec.defer_residual_division and q_int:
        if spec.deferred_division_mode == "round":
            resid_hi = _round_div(tail_hi * r_num, r_den)
        elif spec.deferred_division_mode == "floor":
            resid_hi = (tail_hi * r_num) // r_den
        else:
            raise ValueError(f"unsupported deferred_division_mode={spec.deferred_division_mode}")
    else:
        resid_hi = _mulshr_floor(tail_hi, r_qc, spec.coeff_bits)
    local_hi += resid_hi

    prefix_hi = state.exponent * ln2_fast + c0_fast[state.bucket]
    return prefix_hi - local_hi if state.u_num < 0 else prefix_hi + local_hi


def calibrate_tables(spec: KernelSpec, cases: Sequence[CaseData]) -> Tuple[List[int], List[int]]:
    p_int, q_int = quantized_coeffs(spec.explicit_max_odd, spec.numer_degree, spec.denom_degree, spec.coeff_bits)
    ln2_fast, c0_fast = fast_constants(spec.guard_bits)

    errors_by_bucket: List[List[int]] = [[] for _ in range(16)]
    scale = mp.mpf(1 << spec.guard_bits)
    for case in cases:
        q_raw = eval_candidate_raw(case.state, spec, p_int, q_int, ln2_fast, c0_fast)
        exact_scaled = int(mp.floor(case.log_q256 * scale))
        errors_by_bucket[case.bucket].append(q_raw - exact_scaled)

    biases: List[int] = []
    radii: List[int] = []
    for errs in errors_by_bucket:
        if not errs:
            biases.append(0)
            radii.append(0)
            continue
        lo = min(errs)
        hi = max(errs)
        bias = -_round_div(lo + hi, 2)
        radius = max(abs(err + bias) for err in errs)
        biases.append(bias)
        radii.append(radius)
    return biases, radii


def calibrate_global_table(spec: KernelSpec, cases: Sequence[CaseData]) -> Tuple[List[int], List[int]]:
    p_int, q_int = quantized_coeffs(spec.explicit_max_odd, spec.numer_degree, spec.denom_degree, spec.coeff_bits)
    ln2_fast, c0_fast = fast_constants(spec.guard_bits)

    scale = mp.mpf(1 << spec.guard_bits)
    lo = 0
    hi = 0
    initialized = False
    for case in cases:
        q_raw = eval_candidate_raw(case.state, spec, p_int, q_int, ln2_fast, c0_fast)
        exact_scaled = int(mp.floor(case.log_q256 * scale))
        err = q_raw - exact_scaled
        if not initialized:
            lo = hi = err
            initialized = True
        else:
            lo = min(lo, err)
            hi = max(hi, err)

    if not initialized:
        return [0] * 16, [0] * 16

    bias = -_round_div(lo + hi, 2)
    radius = max(abs(lo + bias), abs(hi + bias))
    return [bias] * 16, [radius] * 16


def validate_candidate(
    spec: KernelSpec,
    train_cases: Sequence[CaseData],
    test_cases: Sequence[CaseData],
    calibration_mode: str = "per_bucket",
) -> CandidateResult:
    p_int, q_int = quantized_coeffs(spec.explicit_max_odd, spec.numer_degree, spec.denom_degree, spec.coeff_bits)
    ln2_fast, c0_fast = fast_constants(spec.guard_bits)
    if calibration_mode == "per_bucket":
        biases, radii = calibrate_tables(spec, train_cases)
    elif calibration_mode == "global":
        biases, radii = calibrate_global_table(spec, train_cases)
    else:
        raise ValueError(f"unsupported calibration_mode={calibration_mode}")

    lower_bad = 0
    upper_bad = 0
    lower_exact = 0
    lower_minus1 = 0
    upper_exact = 0
    upper_plus1 = 0

    for case in test_cases:
        q_raw = eval_candidate_raw(case.state, spec, p_int, q_int, ln2_fast, c0_fast) + biases[case.bucket]
        rad = radii[case.bucket]
        lower = q_raw - rad
        upper = q_raw + rad
        lower_q256 = lower >> spec.guard_bits if spec.guard_bits else lower
        upper_q256 = _ceil_div_pow2_signed(upper, spec.guard_bits) if spec.guard_bits else upper

        if lower_q256 == case.truth_floor:
            lower_exact += 1
        elif lower_q256 == case.truth_floor - 1:
            lower_minus1 += 1
        else:
            lower_bad += 1

        if upper_q256 == case.truth_ceil:
            upper_exact += 1
        elif upper_q256 == case.truth_ceil + 1:
            upper_plus1 += 1
        else:
            upper_bad += 1

    def literal_bytes(v: int) -> int:
        bits = abs(v).bit_length()
        if bits == 0:
            return 1
        return (bits + 7) // 8

    coeff_bytes = sum(literal_bytes(v) for v in p_int) + sum(literal_bytes(v) for v in q_int)
    max_abs_bias = max(abs(b) for b in biases)
    max_radius = max(radii)
    bias_bits = max(1, max_abs_bias.bit_length() + 1)
    radius_bits = max(1, max_radius.bit_length())
    table_entries = 1 if calibration_mode == "global" else 16
    table_bytes = table_entries * (((bias_bits + 7) // 8) + ((radius_bits + 7) // 8))
    mulshr_count = 1 + ((spec.explicit_max_odd + 1) // 2)
    horner_mults = spec.numer_degree + spec.denom_degree
    division_count = 1 if spec.denom_degree else 0

    return CandidateResult(
        spec=spec,
        calibration_mode=calibration_mode,
        ok=(lower_bad == 0 and upper_bad == 0),
        lower_bad=lower_bad,
        upper_bad=upper_bad,
        lower_exact=lower_exact,
        lower_minus1=lower_minus1,
        upper_exact=upper_exact,
        upper_plus1=upper_plus1,
        max_radius=max_radius,
        max_abs_bias=max_abs_bias,
        coeff_bytes=coeff_bytes,
        table_bytes=table_bytes,
        mulshr_count=mulshr_count,
        horner_mults=horner_mults,
        division_count=division_count,
        biases=biases,
        radii=radii,
    )


DEFAULT_CANDIDATES: Tuple[KernelSpec, ...] = (
    KernelSpec("baseline_z7_r67_q216_g24", 7, 6, 7, 216, 24),
    KernelSpec("same_kernel_q192_g8", 7, 6, 7, 192, 8),
    KernelSpec("same_kernel_q160_g0", 7, 6, 7, 160, 0),
    KernelSpec("smaller_rational_z7_r44_q160_g0", 7, 4, 4, 160, 0),
    KernelSpec("smaller_rational_z5_r44_q160_g0", 5, 4, 4, 160, 0),
    KernelSpec("polynomial_z7_p4_q160_g0", 7, 4, 0, 160, 0),
)


def format_result(result: CandidateResult, total_cases: int) -> str:
    s = result.spec
    status = "PASS" if result.ok else "FAIL"
    return (
        f"{status:4}  {s.name:28}  "
        f"{result.calibration_mode:10}  "
        f"lower exact/-1 {result.lower_exact}/{result.lower_minus1}  "
        f"upper exact/+1 {result.upper_exact}/{result.upper_plus1}  "
        f"bad {result.lower_bad + result.upper_bad}  "
        f"coeff {result.coeff_bytes}B  tables {result.table_bytes}B  "
        f"mulshr {result.mulshr_count}  horner {result.horner_mults}  div {result.division_count}  "
        f"max|bias| {result.max_abs_bias}  maxrad {result.max_radius}"
    )


def main() -> int:
    ap = argparse.ArgumentParser(description="Search relaxed stage-1 lnQ256 kernels with mpmath validation")
    ap.add_argument("--train-random", type=int, default=4000)
    ap.add_argument("--train-boundary", type=int, default=1000)
    ap.add_argument("--train-seeds", type=int, nargs="+", default=[1, 2])
    ap.add_argument("--test-random", type=int, default=4000)
    ap.add_argument("--test-boundary", type=int, default=1000)
    ap.add_argument("--test-seeds", type=int, nargs="+", default=[3, 4])
    args = ap.parse_args()

    train_cases = build_search_battery(args.train_random, args.train_boundary, args.train_seeds)
    test_cases = build_search_battery(args.test_random, args.test_boundary, args.test_seeds)

    train_data = precompute_case_data(train_cases)
    test_data = precompute_case_data(test_cases)

    print(f"train cases: {len(train_data)}")
    print(f"test cases:  {len(test_data)}")
    print()

    for spec in DEFAULT_CANDIDATES:
        result = validate_candidate(spec, train_data, test_data)
        print(format_result(result, len(test_data)))
        if result.ok:
            print(f"      biases={result.biases}")
            print(f"      radii ={result.radii}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
