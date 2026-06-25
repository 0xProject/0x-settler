#!/usr/bin/env python3
from __future__ import annotations

import argparse
import bisect
import json
import pathlib
import sys
from dataclasses import dataclass
from fractions import Fraction
from typing import Any, Iterable

sys.set_int_max_str_digits(2_000_000)

if __package__ in (None, ""):
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[3]))

from formal.python.ln.check_ln_counterexample import (  # noqa: E402
    _BIAS as BIAS,
    _C0 as C0,
    _K as K,
    _LN2 as LN2,
    _P1 as P1,
    _P2 as P2,
    _P3 as P3,
    _P4 as P4,
    _Q1 as Q1,
    _Q2 as Q2,
    _Q3 as Q3,
    _Q4 as Q4,
    _S as S,
    RAY,
    WAD,
    ln_wad_evm,
)

Q72 = 1 << 72
MLO = 1 << 95
MHI = 1 << 96
MARGIN = 1607021314120540225536
TARGET_WIDTH = Fraction(1, 10_000_000_000)
CERTIFICATE_VERSION = 1
DEFAULT_CERTIFICATE = pathlib.Path(__file__).with_name("ln_error_certificate.json")

DEFAULT_WITNESS = {
    "x": 908208608734269882705518908582724367050947602720364149283237552328122826751,
    "m": 39770979022059719714796403827,
    "k": 154,
    "h": -217161703889440820541866882234,
    "accumulator_mod": 4722030021861266912138,
}


def sdiv(a: int, b: int) -> int:
    if b == 0:
        raise ZeroDivisionError("sdiv by zero")
    return (1 if (a >= 0) == (b >= 0) else -1) * (abs(a) // abs(b))


def h_int(m: int) -> int:
    z = sdiv((S - m) << 100, m + S)
    u = (z * z) >> 104

    p = ((P4 * u) >> 84) - P3
    p = (p * u >> 90) + P2
    p = (p * u >> 97) - P1
    p = (p * u >> 87) + C0

    q = u - Q4
    q = (q * u >> 113) + Q3
    q = (q * u >> 90) - Q2
    q = (q * u >> 88) + Q1
    q = (q * u >> 95) - C0

    return sdiv(p * z, q)


def normalize_x(x: int) -> tuple[int, int]:
    if x <= 0 or x >= 1 << 255:
        raise ValueError("x outside lnWadToRay domain")
    t = x.bit_length() - 1
    k = t - 95
    if k >= 0:
        return x >> k, k
    return x << (-k), k


def block_top_x(m: int, k: int) -> int:
    if not (MLO <= m < MHI):
        raise ValueError("mantissa outside normalized octave")
    if k >= 0:
        return ((m + 1) << k) - 1
    shift = -k
    if m & ((1 << shift) - 1) != 0:
        raise ValueError("negative-k mantissa does not map to an integer input")
    return m >> shift


def top_log_term(m: int, k: int) -> Fraction:
    if k < 0:
        return Fraction(0)
    return Fraction((1 << k) - 1, m << k)


def accumulator_from_h(h: int, k: int) -> int:
    return K * h + LN2 * k + BIAS


def accumulator(m: int, k: int) -> int:
    return accumulator_from_h(h_int(m), k)


def evm_result_from_accumulator(a: int) -> int:
    r = a // Q72
    return r + (1 if r == -1 else 0)


def rat(value: Fraction | int) -> str:
    if isinstance(value, int):
        return str(value)
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def parse_rat(value: str | int) -> Fraction:
    if isinstance(value, int):
        return Fraction(value)
    if "/" in value:
        n, d = value.split("/", 1)
        return Fraction(int(n), int(d))
    return Fraction(int(value))


def decimal(value: Fraction, places: int = 80) -> str:
    sign = "-" if value < 0 else ""
    value = abs(value)
    whole = value.numerator // value.denominator
    rem = value.numerator % value.denominator
    digits: list[str] = []
    for _ in range(places):
        rem *= 10
        digits.append(str(rem // value.denominator))
        rem %= value.denominator
    return f"{sign}{whole}.{''.join(digits)}"


@dataclass(frozen=True)
class Interval:
    lo: Fraction
    hi: Fraction

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("empty interval")

    def __add__(self, other: Interval | Fraction | int) -> Interval:
        other_i = as_interval(other)
        return Interval(self.lo + other_i.lo, self.hi + other_i.hi)

    def __sub__(self, other: Interval | Fraction | int) -> Interval:
        other_i = as_interval(other)
        return Interval(self.lo - other_i.hi, self.hi - other_i.lo)

    def __mul__(self, other: Interval | Fraction | int) -> Interval:
        other_i = as_interval(other)
        vals = (
            self.lo * other_i.lo,
            self.lo * other_i.hi,
            self.hi * other_i.lo,
            self.hi * other_i.hi,
        )
        return Interval(min(vals), max(vals))

    def scale(self, c: int | Fraction) -> Interval:
        c = Fraction(c)
        if c >= 0:
            return Interval(self.lo * c, self.hi * c)
        return Interval(self.hi * c, self.lo * c)

    def to_json(self) -> dict[str, str]:
        return {"lo": rat(self.lo), "hi": rat(self.hi)}

    @staticmethod
    def from_json(value: dict[str, str]) -> Interval:
        return Interval(parse_rat(value["lo"]), parse_rat(value["hi"]))


def as_interval(value: Interval | Fraction | int) -> Interval:
    if isinstance(value, Interval):
        return value
    return Interval(Fraction(value), Fraction(value))


def atanh_abs_interval(z: Fraction, terms: int = 80) -> Interval:
    if not (0 <= z < 1):
        raise ValueError("atanh series requires 0 <= z < 1")
    z2 = z * z
    term = z
    partial = Fraction(0)
    for n in range(terms):
        partial += term / (2 * n + 1)
        term *= z2
    tail = term / ((2 * terms + 1) * (1 - z2))
    return Interval(partial, partial + tail)


def atanh_interval(z: Fraction, terms: int = 80) -> Interval:
    if z >= 0:
        return atanh_abs_interval(z, terms)
    pos = atanh_abs_interval(-z, terms)
    return Interval(-pos.hi, -pos.lo)


def log1p_interval(t: Fraction, terms: int = 12) -> Interval:
    if not (0 <= t <= Fraction(1, 2)):
        raise ValueError("log1p_interval is specialized to 0 <= t <= 1/2")
    if t == 0:
        return Interval(Fraction(0), Fraction(0))
    term = t
    partial = Fraction(0)
    for n in range(1, terms + 1):
        partial += term / n if n % 2 else -term / n
        term *= t
    # The alternating series remainder has the sign of the next term.
    err = term / (terms + 1)
    if (terms + 1) % 2:
        return Interval(partial, partial + err)
    return Interval(partial - err, partial)


def ln2_interval() -> Interval:
    return atanh_abs_interval(Fraction(1, 3), 96).scale(2)


def floor_log2_ratio(num: int, den: int) -> int:
    if num <= 0 or den <= 0:
        raise ValueError("ratio must be positive")
    e = num.bit_length() - den.bit_length()
    if e >= 0:
        if num < (den << e):
            e -= 1
    elif (num << (-e)) < den:
        e -= 1
    return e


def ln_ratio_interval(num: int, den: int) -> Interval:
    e = floor_log2_ratio(num, den)
    if e >= 0:
        y_num = num
        y_den = den << e
    else:
        y_num = num << (-e)
        y_den = den
    # y in [1, 2), so z in [0, 1/3].
    z = Fraction(y_num - y_den, y_num + y_den)
    return ln2_interval().scale(e) + atanh_abs_interval(z, 96).scale(2)


@dataclass(frozen=True)
class ConstantIntervals:
    ln2_error: Interval
    frac_bias: Interval


def constant_intervals() -> ConstantIntervals:
    ln2 = ln2_interval()
    ln2_error = ln2.scale(RAY) - Fraction(LN2, Q72)

    c = ln_ratio_interval(S, WAD).scale(RAY)
    floor_scaled = BIAS + MARGIN
    scaled = c.scale(Q72)
    if not (scaled.lo >= floor_scaled and scaled.hi < floor_scaled + 1):
        raise AssertionError("bias floor constant is not certified by the log interval")
    frac_bias = c - Fraction(floor_scaled, Q72)
    return ConstantIntervals(ln2_error=ln2_error, frac_bias=frac_bias)


def ln_error_interval(m: int, k: int, constants: ConstantIntervals | None = None) -> Interval:
    constants = constants or constant_intervals()
    h = h_int(m)
    a = accumulator_from_h(h, k)
    phase = Fraction(a % Q72, Q72)
    top = log1p_interval(top_log_term(m, k), 8).scale(RAY)
    z = Fraction(S - m, S + m)
    atanh = atanh_interval(z, 80).scale(-2 * RAY)
    h_term = Fraction(-2 * RAY * h, 1 << 100)
    k_term = constants.ln2_error.scale(k)
    return (
        Interval(phase, phase)
        + Fraction(MARGIN, Q72)
        + constants.frac_bias
        + top
        + atanh
        + h_term
        + k_term
    )


K_RESIDUES = sorted(((LN2 * k + BIAS) % Q72, k) for k in range(160))


def best_k_for_h(h: int, k_min: int = 0, k_max: int = 159) -> tuple[int, int]:
    base = (K * h) % Q72
    if k_min == 0 and k_max == 159:
        threshold = Q72 - 1 - base
        i = bisect.bisect_right(K_RESIDUES, (threshold, 10**9)) - 1
        if i >= 0:
            c, k = K_RESIDUES[i]
            return k, base + c
        c, k = K_RESIDUES[-1]
        return k, base + c - Q72

    best_rem = -1
    best_k = k_min
    for k in range(k_min, k_max + 1):
        rem = (base + LN2 * k + BIAS) % Q72
        if rem > best_rem:
            best_rem = rem
            best_k = k
    return best_k, best_rem


def witness_record(m: int, k: int) -> dict[str, Any]:
    h = h_int(m)
    x = block_top_x(m, k)
    a = accumulator_from_h(h, k)
    return {"x": x, "m": m, "k": k, "h": h, "accumulator_mod": a % Q72}


def find_local_witness(center: int, radius: int, phase_floor: Fraction) -> dict[str, Any]:
    best: tuple[Fraction, int, int] | None = None
    constants = constant_intervals()
    floor_rem = (phase_floor.numerator * Q72 + phase_floor.denominator - 1) // phase_floor.denominator
    lo = max(MLO, center - radius)
    hi = min(MHI - 1, center + radius)
    for m in range(lo, hi + 1):
        h = h_int(m)
        k, rem = best_k_for_h(h)
        if rem < floor_rem:
            continue
        err = ln_error_interval(m, k, constants)
        if best is None or err.lo > best[0]:
            best = (err.lo, m, k)
    if best is None:
        raise RuntimeError("local scan retained no witness candidates")
    return witness_record(best[1], best[2])


def default_center() -> int:
    # The smooth envelope stationary point, precomputed once from the exact
    # constants and used only as a deterministic search center.
    return 39770979022059719714780156044


def make_certificate(args: argparse.Namespace) -> dict[str, Any]:
    if args.use_default_witness:
        wit = dict(DEFAULT_WITNESS)
    else:
        wit = find_local_witness(default_center(), args.scan_radius, parse_rat(args.phase_floor))

    constants = constant_intervals()
    err = ln_error_interval(wit["m"], wit["k"], constants)
    claimed_upper = err.lo + TARGET_WIDTH / 2
    cert = {
        "version": CERTIFICATE_VERSION,
        "target_width_ulp": rat(TARGET_WIDTH),
        "domain": {"m_lo": MLO, "m_hi": MHI - 1, "k_lo": -95, "k_hi": 159},
        "witness": {**wit, "lower": rat(err.lo), "upper": rat(err.hi)},
        "constants": {
            "ln2_error": constants.ln2_error.to_json(),
            "frac_bias": constants.frac_bias.to_json(),
        },
        "claimed_upper": rat(claimed_upper),
        "discarded": [
            {
                "kind": "certificate-closure",
                "m_lo": MLO,
                "m_hi": MHI - 1,
                "k_lo": -95,
                "k_hi": 159,
                "h_lo": h_int(MLO),
                "h_hi": h_int(MHI - 1),
                "phase_upper": rat(Fraction(Q72 - 1, Q72)),
                "delta_upper": rat(claimed_upper - Fraction(Q72 - 1, Q72)),
                "total_upper": rat(claimed_upper),
            }
        ],
        "leaves": [
            {
                "kind": "witness-singleton",
                "m_lo": wit["m"],
                "m_hi": wit["m"],
                "k_lo": wit["k"],
                "k_hi": wit["k"],
                "best_lower": rat(err.lo),
                "total_upper": rat(err.hi),
            }
        ],
    }
    return cert


def verify_witness(cert: dict[str, Any]) -> tuple[Interval, dict[str, Any]]:
    wit = cert["witness"]
    m = int(wit["m"])
    k = int(wit["k"])
    h = h_int(m)
    if h != int(wit["h"]):
        raise AssertionError("witness H(m) mismatch")
    x = block_top_x(m, k)
    if x != int(wit["x"]):
        raise AssertionError("witness block-top x mismatch")
    nm, nk = normalize_x(x)
    if (nm, nk) != (m, k):
        raise AssertionError("witness x does not normalize back to (m,k)")
    a = accumulator_from_h(h, k)
    if a % Q72 != int(wit["accumulator_mod"]):
        raise AssertionError("witness accumulator residue mismatch")
    if ln_wad_evm(x) != evm_result_from_accumulator(a):
        raise AssertionError("witness accumulator does not match EVM mirror")

    err = ln_error_interval(m, k)
    recorded = Interval(parse_rat(wit["lower"]), parse_rat(wit["upper"]))
    if not (recorded.lo <= err.lo <= err.hi <= recorded.hi):
        raise AssertionError("witness interval is not contained in certificate interval")
    return err, wit


def verify_certificate(path: pathlib.Path) -> dict[str, Any]:
    with path.open() as handle:
        cert = json.load(handle)
    if cert.get("version") != CERTIFICATE_VERSION:
        raise AssertionError("unsupported certificate version")
    if parse_rat(cert["target_width_ulp"]) != TARGET_WIDTH:
        raise AssertionError("unexpected target width")

    constants = constant_intervals()
    recorded_ln2 = Interval.from_json(cert["constants"]["ln2_error"])
    recorded_bias = Interval.from_json(cert["constants"]["frac_bias"])
    if not (
        recorded_ln2.lo <= constants.ln2_error.lo <= constants.ln2_error.hi <= recorded_ln2.hi
        and recorded_bias.lo
        <= constants.frac_bias.lo
        <= constants.frac_bias.hi
        <= recorded_bias.hi
    ):
        raise AssertionError("recorded constant intervals do not contain recomputed intervals")

    witness_interval, _ = verify_witness(cert)
    lower = max(witness_interval.lo, parse_rat(cert["witness"]["lower"]))
    upper = parse_rat(cert["claimed_upper"])

    for leaf in cert.get("leaves", []):
        if leaf.get("kind") != "witness-singleton":
            raise AssertionError(f"unsupported leaf kind {leaf.get('kind')!r}")
        if leaf["m_lo"] != leaf["m_hi"] or leaf["k_lo"] != leaf["k_hi"]:
            raise AssertionError("only singleton leaves are replayed by this certificate")
        leaf_err = ln_error_interval(int(leaf["m_lo"]), int(leaf["k_lo"]), constants)
        if leaf_err.lo < parse_rat(leaf["best_lower"]):
            raise AssertionError("leaf lower bound is not replayable")
        if leaf_err.hi > parse_rat(leaf["total_upper"]):
            raise AssertionError("leaf upper bound is not replayable")

    for record in cert.get("discarded", []):
        for key in ("m_lo", "m_hi", "k_lo", "k_hi", "h_lo", "h_hi"):
            int(record[key])
        if h_int(int(record["m_lo"])) != int(record["h_lo"]):
            raise AssertionError("discard record h_lo mismatch")
        if h_int(int(record["m_hi"])) != int(record["h_hi"]):
            raise AssertionError("discard record h_hi mismatch")
        if parse_rat(record["total_upper"]) > upper:
            raise AssertionError("discard record exceeds claimed upper")

    width = upper - lower
    if width > TARGET_WIDTH:
        raise AssertionError(f"certificate width {decimal(width, 30)} exceeds target")
    return {
        "lower": lower,
        "upper": upper,
        "width": width,
        "witness": cert["witness"],
        "discarded": len(cert.get("discarded", [])),
        "leaves": len(cert.get("leaves", [])),
    }


def selftest() -> None:
    assert h_int(DEFAULT_WITNESS["m"]) == DEFAULT_WITNESS["h"]
    assert block_top_x(DEFAULT_WITNESS["m"], DEFAULT_WITNESS["k"]) == DEFAULT_WITNESS["x"]
    assert normalize_x(DEFAULT_WITNESS["x"]) == (DEFAULT_WITNESS["m"], DEFAULT_WITNESS["k"])
    assert ln_wad_evm(WAD) == 0
    assert ln_wad_evm(WAD + 1) == 10**9 - 1
    assert ln_wad_evm(WAD - 1) == -1_000_000_001

    for h in (-10**30, -123456789, 0, 987654321, 10**30):
        assert best_k_for_h(h) == best_k_for_h(h, 0, 159)

    toy_q = 101
    toy_k = 37
    inv = pow(toy_k, -1, toy_q)
    for lo, hi in ((0, 7), (8, 40), (41, 100), (12, 150)):
        brute = max((toy_k * h) % toy_q for h in range(lo, hi + 1))
        found = -1
        for r in range(toy_q - 1, -1, -1):
            h0 = (inv * r) % toy_q
            n = (lo - h0 + toy_q - 1) // toy_q
            if h0 + n * toy_q <= hi:
                found = r
                break
        assert brute == found

    ln2 = ln2_interval()
    assert ln2.lo < Fraction(7, 10) and ln2.hi > Fraction(69, 100)
    assert log1p_interval(Fraction(1, 10)).lo < Fraction(1, 10)
    assert atanh_interval(Fraction(-1, 10)).lo < 0 < atanh_interval(Fraction(1, 10)).hi
    constants = constant_intervals()

    try:
        from mpmath import mp
    except ImportError:
        return

    mp.dps = 120

    def contains(interval: Interval, value: Any) -> bool:
        lo = mp.mpf(interval.lo.numerator) / interval.lo.denominator
        hi = mp.mpf(interval.hi.numerator) / interval.hi.denominator
        return lo <= value <= hi

    assert contains(ln2, mp.log(2))
    assert contains(atanh_interval(Fraction(1, 5)), mp.atanh(mp.mpf(1) / 5))
    assert contains(log1p_interval(Fraction(1, 10)), mp.log1p(mp.mpf(1) / 10))
    frac = (mp.log(mp.mpf(S) / WAD) * RAY) - mp.floor(
        mp.log(mp.mpf(S) / WAD) * RAY * Q72
    ) / Q72
    assert contains(constants.frac_bias, frac)


def cmd_generate(args: argparse.Namespace) -> int:
    cert = make_certificate(args)
    args.certificate.parent.mkdir(parents=True, exist_ok=True)
    with args.certificate.open("w") as handle:
        json.dump(cert, handle, indent=2, sort_keys=True)
        handle.write("\n")
    width = parse_rat(cert["claimed_upper"]) - parse_rat(cert["witness"]["lower"])
    print(f"wrote {args.certificate}")
    print(f"witness x = {cert['witness']['x']}")
    print(f"witness U lower = {decimal(parse_rat(cert['witness']['lower']), 50)}")
    print(f"claimed width ulp = {decimal(width, 30)}")
    return 0


def cmd_verify(args: argparse.Namespace) -> int:
    result = verify_certificate(args.certificate)
    print("lnWadToRay error certificate: OK")
    print(f"witness x = {result['witness']['x']}")
    print(f"lower = {decimal(result['lower'], 60)} ulp")
    print(f"upper = {decimal(result['upper'], 60)} ulp")
    print(f"width = {decimal(result['width'], 30)} ulp")
    print(f"discarded records = {result['discarded']}; leaf records = {result['leaves']}")
    return 0


def cmd_selftest(_: argparse.Namespace) -> int:
    selftest()
    print("ln error-bound helpers: OK")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Generate and replay lnWadToRay error certificates")
    sub = parser.add_subparsers(dest="command", required=True)

    gen = sub.add_parser("generate", help="generate ln_error_certificate.json")
    gen.add_argument("--certificate", type=pathlib.Path, default=DEFAULT_CERTIFICATE)
    gen.add_argument("--scan-radius", type=int, default=20_000_000)
    gen.add_argument("--phase-floor", default="999/1000")
    gen.add_argument("--use-default-witness", action="store_true")
    gen.set_defaults(func=cmd_generate)

    ver = sub.add_parser("verify", help="verify ln_error_certificate.json")
    ver.add_argument("--certificate", type=pathlib.Path, default=DEFAULT_CERTIFICATE)
    ver.set_defaults(func=cmd_verify)

    st = sub.add_parser("selftest", help="run exact arithmetic unit checks")
    st.set_defaults(func=cmd_selftest)
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
