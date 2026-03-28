"""Rational Remez algorithm for the lnQ256 fast-kernel residual.

Finds the minimax [6/7] rational approximation R(w) on [0, w_max] where:
  2*atanh(z) = 2z + (2/3)z^3 + (2/5)z^5 + (2/7)z^7 + z^9 * R(z^2)

Uses the exchange (Remez) algorithm with linearized systems.
"""
import mpmath as mp
from mpmath import mpf, matrix, lu_solve, pi, cos, sqrt, atanh, log, floor, nint

DPS = 200
mp.mp.dps = DPS

# ── Target function ──────────────────────────────────────────────────────

N0 = [31, 29, 28, 26, 25, 24, 23, 22, 21, 20, 19, 19, 18, 17, 17, 16]

def compute_w_max():
    """Maximum w = z^2 across all 16 coarse buckets."""
    wm = mpf(0)
    for j in range(16):
        n = N0[j]
        for y in [mpf(16 + j) / 16, mpf(16 + j + 1) / 16]:
            u = n * y / 32 - 1
            z = u / (2 + u)
            wm = max(wm, z * z)
    return wm

W_MAX = compute_w_max()

def R_true(w):
    """Target function: the atanh tail after explicit terms through z^7."""
    if w == 0:
        return mpf(2) / 9
    s = sqrt(w)
    return 2 * (atanh(s) - s - s**3/3 - s**5/5 - s**7/7) / s**9


# ── Rational Remez ───────────────────────────────────────────────────────

def chebyshev_nodes(a, b, n):
    """n Chebyshev nodes on [a, b]."""
    return sorted([(a + b)/2 + (b - a)/2 * cos(pi * k / (n - 1)) for k in range(n)])


def eval_poly(coeffs, x):
    """Evaluate polynomial with coefficients [c0, c1, ..., cd]."""
    val = mpf(0)
    xpow = mpf(1)
    for c in coeffs:
        val += c * xpow
        xpow *= x
    return val


def eval_rational(p_coeffs, q_coeffs, x):
    """Evaluate P(x) / Q(x) where Q has implicit leading 1."""
    P = eval_poly(p_coeffs, x)
    Q = mpf(1) + eval_poly(q_coeffs, x) * x  # q_coeffs = [q1, ..., qn], multiply by x
    return P / Q


def build_system(f, refs, m, n):
    """Build the linearized Remez system.

    f(xi) - P(xi)/Q(xi) = (-1)^i * h
    Rewritten as: f(xi)*Q(xi) - P(xi) = (-1)^i * h
    With Q(x) = 1 + q1*x + ... + qn*x^n, this is linear in {p_j, q_j, h}.

    Unknowns: p0,...,pm, q1,...,qn, h  (total m+1+n+1 = m+n+2)
    """
    N = len(refs)
    assert N == m + n + 2

    A = matrix(N, N)
    b = matrix(N, 1)

    for i in range(N):
        xi = refs[i]
        fi = f(xi)

        # p0, p1*x, ..., pm*x^m  (coefficients: -1, -x, ..., -x^m)
        xpow = mpf(1)
        for j in range(m + 1):
            A[i, j] = -xpow
            xpow *= xi

        # q1*x, q2*x^2, ..., qn*x^n  (coefficients: fi*x, fi*x^2, ..., fi*x^n)
        xpow = xi
        for j in range(n):
            A[i, m + 1 + j] = fi * xpow
            xpow *= xi

        # h  (coefficient: -(-1)^i)
        A[i, m + 1 + n] = -((-1) ** i)

        b[i] = -fi

    return A, b


def find_extrema(errs, N_target):
    """Find N_target alternating extrema from a dense error sample.

    errs: list of (x, e(x)) sorted by x.
    Returns: list of x values at alternating extrema.
    """
    # Find all local extrema
    extrema = []
    for i in range(1, len(errs) - 1):
        _, e_prev = errs[i - 1]
        _, e_cur = errs[i]
        _, e_next = errs[i + 1]
        if (e_cur >= e_prev and e_cur >= e_next) or (e_cur <= e_prev and e_cur <= e_next):
            extrema.append(errs[i])

    # Include endpoints
    extrema = [errs[0]] + extrema + [errs[-1]]

    # Remove duplicates and sort
    seen = set()
    unique = []
    for x, e in extrema:
        if x not in seen:
            unique.append((x, e))
            seen.add(x)
    unique.sort(key=lambda t: t[0])
    extrema = unique

    if len(extrema) < N_target:
        # Fall back: pick equally spaced among largest-error points
        extrema_by_err = sorted(extrema, key=lambda t: -abs(t[1]))
        result = sorted(extrema_by_err[:N_target], key=lambda t: t[0])
        return [x for x, _ in result]

    # Select N_target extrema with alternating signs and maximum deviation
    # Greedy: pick the largest |error| extremum, then alternating neighbors
    best = select_alternating(extrema, N_target)
    return [x for x, _ in best]


def select_alternating(extrema, N):
    """Select N alternating extrema maximizing minimum |error|."""
    # Dynamic programming is overkill; use a simple greedy approach.
    # First, group consecutive extrema by sign.
    if len(extrema) <= N:
        return extrema

    # Try starting with the largest positive and negative, alternating
    best_set = None
    best_min_err = mpf(-1)

    for start_sign in [1, -1]:
        selected = []
        sign = start_sign
        remaining = list(extrema)

        for _ in range(N):
            # Find the extremum with the right sign and largest |error|
            candidates = [(i, x, e) for i, (x, e) in enumerate(remaining)
                          if (e > 0) == (sign > 0) or (e == 0 and sign > 0)]
            if not candidates:
                # Try the other sign or any remaining
                candidates = [(i, x, e) for i, (x, e) in enumerate(remaining)]
            if not candidates:
                break

            best_idx, best_x, best_e = max(candidates, key=lambda t: abs(t[2]))
            selected.append((best_x, best_e))
            remaining.pop(best_idx)
            sign = -sign

        if len(selected) == N:
            selected.sort(key=lambda t: t[0])
            min_err = min(abs(e) for _, e in selected)
            if min_err > best_min_err:
                best_min_err = min_err
                best_set = selected

    if best_set is None:
        # Fallback: just pick the N with largest |error|
        by_err = sorted(extrema, key=lambda t: -abs(t[1]))
        best_set = sorted(by_err[:N], key=lambda t: t[0])

    return best_set


def rational_remez(f, a, b, m, n, max_iter=60, grid_size=20000, verbose=True):
    """Compute the minimax [m/n] rational approximation of f on [a, b].

    P(x) = p0 + p1*x + ... + pm*x^m
    Q(x) = 1 + q1*x + ... + qn*x^n

    Returns: (p_coeffs, q_coeffs, max_error)
    """
    N = m + n + 2  # number of reference points

    # Initial reference: Chebyshev nodes
    refs = chebyshev_nodes(a, b, N)

    prev_max_err = None

    for it in range(max_iter):
        # Solve linearized system
        A, rhs = build_system(f, refs, m, n)
        sol = lu_solve(A, rhs)

        p_coeffs = [sol[j] for j in range(m + 1)]
        q_coeffs = [sol[m + 1 + j] for j in range(n)]
        h = sol[m + 1 + n]

        # Evaluate error on dense grid
        grid = [a + (b - a) * mpf(i) / grid_size for i in range(grid_size + 1)]
        errs = []
        max_err = mpf(0)
        for x in grid:
            r = eval_rational(p_coeffs, q_coeffs, x)
            e = f(x) - r
            errs.append((x, e))
            if abs(e) > max_err:
                max_err = abs(e)

        if verbose:
            print(f"  iter {it}: |h| = {float(abs(h)):.6e}, max_grid_err = {float(max_err):.6e}, ratio = {float(max_err/abs(h)):.6f}")

        # Check convergence
        if prev_max_err is not None:
            rel_change = abs(max_err - prev_max_err) / max_err
            if rel_change < mpf(10) ** (-(DPS // 3)):
                if verbose:
                    print(f"  Converged at iteration {it}")
                break
        prev_max_err = max_err

        # Update reference points
        new_refs = find_extrema(errs, N)
        if len(new_refs) == N:
            refs = new_refs
        else:
            if verbose:
                print(f"  Warning: found only {len(new_refs)} extrema, keeping old refs")

    return p_coeffs, q_coeffs, max_err


def quantize_and_measure(p_real, q_real, bits, f, a, b, grid_size=50000):
    """Quantize coefficients to Q{bits} and measure the Horner evaluation error."""
    scale = mpf(2) ** bits

    p_q = [int(nint(c * scale)) for c in p_real]
    q_q = [int(nint(c * scale)) for c in q_real]

    def horner_eval(p_int, q_int, w_q256, coeff_bits):
        """Simulate the fixed-point Horner evaluation."""
        # Numerator
        num = p_int[-1]
        for c in reversed(p_int[:-1]):
            prod = num * w_q256
            if prod >= 0:
                num = (prod + (1 << 255)) >> 256
            else:
                num = -(((-prod) + (1 << 255)) >> 256)
            num += c

        # Denominator (with implicit Q0 = 2^coeff_bits)
        den = q_int[-1]
        for c in reversed(q_int[:-1]):
            prod = den * w_q256
            if prod >= 0:
                den = (prod + (1 << 255)) >> 256
            else:
                den = -(((-prod) + (1 << 255)) >> 256)
            den += c
        # Final step: den * w + Q0
        prod = den * w_q256
        if prod >= 0:
            den = (prod + (1 << 255)) >> 256
        else:
            den = -(((-prod) + (1 << 255)) >> 256)
        den += (1 << coeff_bits)

        # Division: num << coeff_bits / den, rounded
        shifted = num * (1 << coeff_bits)
        if den > 0:
            if shifted >= 0:
                return (shifted + den // 2) // den
            else:
                return -(((-shifted) + den // 2) // den)
        else:
            raise ValueError("Denominator is non-positive")

    grid = [a + (b - a) * mpf(i) / grid_size for i in range(grid_size + 1)]
    max_err_q256 = mpf(0)
    max_err_real = mpf(0)

    for x in grid:
        f_true = f(x)

        # Real-valued evaluation (to measure approximation error alone)
        P = eval_poly([mpf(c) / scale for c in p_q], x)
        Q = mpf(1) + eval_poly([mpf(c) / scale for c in q_q], x) * x
        r_real = P / Q
        err_real = abs(f_true - r_real)
        max_err_real = max(max_err_real, err_real)

        # Fixed-point Horner evaluation (to measure total error)
        w_q256 = int(nint(x * (mpf(2) ** 256)))
        r_qc = horner_eval(p_q, q_q, w_q256, bits)
        r_from_horner = mpf(r_qc) / scale
        err_horner = abs(f_true - r_from_horner)
        max_err_q256 = max(max_err_q256, err_horner)

    return p_q, q_q, float(max_err_real), float(max_err_q256)


# ── Main ─────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    print(f"w_max = {float(W_MAX):.10e}")
    print(f"R(0) = {float(R_true(0)):.15f} (should be 2/9 = {float(mpf(2)/9):.15f})")
    print(f"R(w_max) = {float(R_true(W_MAX)):.15f}")
    print()

    print("Running rational Remez [6/7] on [0, w_max]...")
    p_real, q_real, minimax_err = rational_remez(R_true, mpf(0), W_MAX, 6, 7)

    print(f"\nMinimax approximation error: {float(minimax_err):.6e}")
    print()

    # Quantize and measure at Q212 and Q216
    for bits in [212, 216, 220, 224, 240, 248]:
        p_q, q_q, err_real, err_horner = quantize_and_measure(
            p_real, q_real, bits, R_true, mpf(0), W_MAX
        )
        # Convert R(w) error to contribution in final ln(x) result
        # The rational error gets multiplied by z^9 and contributes to the Q256 result
        # z_max^9 ≈ (0.01916)^9
        z9_max = float(W_MAX ** mpf(4.5))
        err_ln_q256 = err_horner * z9_max
        print(f"Q{bits:3d}: real_err={err_real:.4e}  horner_err={err_horner:.4e}  "
              f"-> z^9*err = {err_ln_q256:.4e} Q256 ulps  max_coeff_bits={max(c.bit_length() for c in p_q + q_q)}")

    print("\n--- Existing Q212 coefficients for comparison ---")
    from lnq256_model_stage1_bucketbias import FAST_P as OLD_P, FAST_Q as OLD_Q
    _, _, old_err_real, old_err_horner = quantize_and_measure(
        [mpf(c) / (mpf(2)**212) for c in OLD_P],  # "unquantize" to real
        [mpf(c) / (mpf(2)**212) for c in OLD_Q],
        212, R_true, mpf(0), W_MAX
    )
    z9_max = float(W_MAX ** mpf(4.5))
    print(f"Old Q212: real_err={old_err_real:.4e}  horner_err={old_err_horner:.4e}  "
          f"-> z^9*err = {old_err_horner * z9_max:.4e} Q256 ulps")
