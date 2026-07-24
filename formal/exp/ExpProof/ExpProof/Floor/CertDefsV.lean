import Common.Foundation.ShiftCert

/-!
# The v-form reduced-argument rational target and its cut / denominator-floor certificates

The runtime forms `r0 = ⌊scaleQ67·ê_v(t)⌋` with the **v-form** rational

```
ê_v(t) = (evNumV(v) · 2^111 + t · odNumV(v)) / (evNumV(v) · 2^111 − t · odNumV(v)),   v = t²/2^135,
```

built from the exact integer even/odd Horner polynomials `evNumV`/`odNumV` (defined in
`Floor/R0Bound.lean` as functions of the integer `v = vTree x`). The runtime's truncation bridge
lands on this representation, so the floor layer needs a cut certificate phrased on `ê_v`, not on the
t-form `ê_t = numExp/denExp`. `ê_v` and `ê_t` are equal as reals but differ as integer
polynomials (different shift-clearing), so this module re-derives the cut against `ê_v` directly.

Here `v = t²` is carried symbolically (each Horner stage multiplies by `t²` via `mulT2`, with the
runtime per-stage shift cleared into the per-stage scale): `evNumVPoly` accumulates `Ev` to the
cleared scale `2^1201` and `odNumVPoly` accumulates `Od` to `2^1048`; `t·Od` (lifted by `2^24`) joins
`Ev` at the common `2^1201`. The shared scale cancels in `ê_v = NUM/DEN`. As a polynomial in `t` the
numerator/denominator are degree 10.

Two certificate shapes are declared:

* the Taylor cut, the standard `Common.Exp.capUB_of_partial`/`capLB` shape at depth `K = 27`,
  nudging the rational by a dyadic margin (`yUB/wUB = ê_v·(1 + 2⁻¹³²)`, `yLB/wLB = ê_v·(1 − 2⁻¹³²)`);
  the realized envelope `2¹²⁶·|ê_v − exp(t/2¹²⁸)| ≤ 0.0075` ulp is inside those margins with 2.1× slack;
* the **denominator floors** over the integer `v`-grid: the parameterized shapes
  `certDOverP`/`certDUnderP` pin `Ev(v)·2^111 ∓ T·Od(v)` above explicit constants, instantiated
  once globally (`certDOver`, at the domain edge `T = H129` over all of `[0, vmaxV + 1]`) and once
  per granularity piece (32 pieces, each with its own `t`-cap `T` and floor constant over its
  `v`-range); the argument-granularity link divides one `v`-grid step of `ê_v` by the piece floors.
-/

namespace ExpCertV

open Common.Poly

/-! ## The reduced-argument denominator and the cert domain -/

/-- The reduced-argument denominator `tDen = 2^128`: the runtime carries `t` in Q128. -/
def Qexp : Nat := 2 ^ 129

/-- The cert variable upper bound `H129 = ⌊ln2/2 · 2^128⌋`. -/
def H129 : Nat := 235865763225513294137944142764154484399

/-! ## Exact integer `ê_v(t) = NUM(t)/DEN(t)` from the implementation coefficients

The even/odd Horner accumulators evaluated as exact polynomials in `t` with `v = t²/2^135`, each
runtime per-stage shift cleared into the stage scale. `evNumVPoly` is `evNumV(t²)` cleared so its
evaluation is `Ev·2^1201` (`= evNumV(v)·2^675` at grid points `t² = 2^135·v`); `odNumVPoly`
evaluates to `Od·2^1048` (`= odNumV(v)·2^540` at grid points); `t·Od` (lifted by `2^24` to the
common `2^1201`) joins `Ev`. The shared `2^1201` cancels in `ê_v = NUM/DEN`. -/

/-- `t²·P` at the polynomial level (one Horner `·v` stage, with the runtime per-stage shift cleared
into the per-stage constant scale). -/
def mulT2 (P : List Int) : List Int := 0 :: 0 :: P

/-- The even Horner accumulator `Ev` (evaluation `Ev·2^1201`; `evNumV(v)·2^675` at grid points).
The per-stage constants are the even coefficients `A0..A4` lifted by the cleared stage scale; the
innermost monic `v` stage clears to `[A4·2^133, 0, 1]` (A4 is carried at v's own Q123 basis). -/
def evNumVPoly : List Int :=
  polyAdd [0x1385291795942d41ba5fd317688e18710 * 2 ^ 1201]
    (mulT2 (polyAdd [0x93f11e650dd6c64b96ce79065cdf80f4 * 2 ^ 941]
      (mulT2 (polyAdd [0x9064d9657e9a21fc16bb69331b81ae1e * 2 ^ 677]
        (mulT2 (polyAdd [0x9a036222841f47c6ed6fc3f7599445 * 2 ^ 419]
          (mulT2 [0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 135, 0, 1])))))))

/-- The odd Horner accumulator `Od` (evaluation `Od·2^1048`; `odNumV(v)·2^540` at grid points). -/
def odNumVPoly : List Int :=
  polyAdd [0x9c2948bcaca16a0dd2fe98bb4470c388 * 2 ^ 1048]
    (mulT2 (polyAdd [0xaf566247c05753b42892f77b67a6b7c7 * 2 ^ 785]
      (mulT2 (polyAdd [0xad4506af99be27419341e181693281 * 2 ^ 528]
        (mulT2 [0xc926ddbecdeeb42e68cd16db7ed378 * 2 ^ 261, 0, 0xdc07aff8276bde9a361278df6a10])))))

/-- `t·Od` lifted to the common scale `2^1201` (`= 2^24 · t · odNumVPoly`). -/
def todNumV : List Int := polyScale (2 ^ 24) (0 :: odNumVPoly)

/-- `ê_v`-numerator `NUM(t) = Ev(t) + t·Od(t)` (scale `2^1201`). -/
def numExpV : List Int := polyAdd evNumVPoly todNumV

/-- `ê_v`-denominator `DEN(t) = Ev(t) − t·Od(t)` (scale `2^1201`). -/
def denExpV : List Int := polySub evNumVPoly todNumV

/-! ## Taylor partial-sum numerator at the cut argument -/

/-- Polynomial-level depth-27 partial-sum numerator at argument `t/Qexp`. -/
def expN27 : List Int := expPolyNum [0, 1] [(Qexp : Int)] 27

/-! ## Margin-nudged rational targets

`yUB/wUB = ê_v·(1 + 2⁻¹³²)` and `yLB/wLB = ê_v·(1 − 2⁻¹³²)`. The tight `2⁻¹³²` margins keep the
`2¹²⁶·(ê_v − exp)` contribution to the runtime over/under budget below `2¹²⁶·exp·2⁻¹³² ≈ 0.022` ulp,
inside the `MARGIN`; the realized envelope `2¹²⁶·|ê_v − exp(t/2¹²⁹)| ≤ 0.0075` ulp leaves slack. -/

def yUB : List Int := polyScale (2 ^ 132 + 1) numExpV
def wUB : List Int := polyScale (2 ^ 132) denExpV
def yLB : List Int := polyScale (2 ^ 132 - 1) numExpV
def wLB : List Int := polyScale (2 ^ 132) denExpV

/-! ## The cut certificate polynomials -/

/-- `28! · Qexp^28`. -/
def fact28Q28 : Int := 304888344611713860501504000000 * (Qexp : Int) ^ 28

/-- `27! · Qexp^27`. -/
def fact27Q27 : Int := 10888869450418352160768000000 * (Qexp : Int) ^ 27

/-- The `capUB_of_partial` tail polynomial `expN27·(28·Qexp) + 2·t²⁸`. -/
def tailUp : List Int :=
  polyAdd (polyScale (28 * (Qexp : Int)) expN27) (polyScale 2 (polyPow [0, 1] 28))

def certExpUp : List Int := polySub (polyScale fact28Q28 yUB) (polyMul tailUp wUB)

def certExpLo : List Int := polySub (polyMul expN27 wLB) (polyScale fact27Q27 yLB)

/-- `DEN(t) − 1`: nonnegativity over the domain certifies `1 ≤ DEN(t)`. -/
def certDenM1 : List Int := polyAdd denExpV [-1]

/-! ## The v-grid denominator floors

The argument-granularity link works on the integer `v`-grid: with `Ev(v)`/`Od(v)` the exact integer
Horner polynomials (cleared scales `2^528`/`2^510`; `Floor/R0Bound.lean`), the aligned rational is
`ê_v = (Ev·2^111 + t·Od) / (Ev·2^111 − t·Od)` and one grid step of it is bounded by dividing the
`K`-identity numerator by the two floors below. The grid never leaves `[0, vmaxV + 1]`
(`v = ⌊t²/2^135⌋ ≤ vmaxV` for `|t| ≤ H129`, and the step looks one cell ahead). -/

/-- The top of the `v`-grid: `vmaxV = ⌊H129²/2^133⌋`. -/
def vmaxV : Nat := 1277263193518626341050532535110179582

/-- The even integer Horner polynomial `Ev` in `v` (degree 5, monic, cleared scale `2^528`):
coefficient list of `evNumV` (`Floor/R0Bound.lean`). -/
def evVPoly : List Int :=
  [0x1385291795942d41ba5fd317688e18710 * 2 ^ 526,
   0x93f11e650dd6c64b96ce79065cdf80f4 * 2 ^ 401,
   0x9064d9657e9a21fc16bb69331b81ae1e * 2 ^ 272,
   0x9a036222841f47c6ed6fc3f7599445 * 2 ^ 149,
   0xb9aacfacf3c10b378435f8e22adf48500e,
   1]

/-- The odd integer Horner polynomial `Od` in `v` (degree 4, cleared scale `2^510`). -/
def odVPoly : List Int :=
  [0x9c2948bcaca16a0dd2fe98bb4470c388 * 2 ^ 508,
   0xaf566247c05753b42892f77b67a6b7c7 * 2 ^ 380,
   0xad4506af99be27419341e181693281 * 2 ^ 258,
   0xc926ddbecdeeb42e68cd16db7ed378 * 2 ^ 126,
   0xdc07aff8276bde9a361278df6a10]

/-- Over-half denominator floor shape: `Ev(v)·2^111 − T·Od(v) − D·2^725 ≥ 0`. Nonnegativity over a
`v`-range gives `DEN(v, t) ≥ D·2^725` there for every `0 ≤ t ≤ T` (the floor constant is `2^725`
times a real-scale minimum). -/
def certDOverP (T D : Int) : List Int :=
  polyAdd (polySub (polyScale (2 ^ 111) evVPoly) (polyScale T odVPoly)) [-(D * 2 ^ 725)]

/-- Under-half (`t = −T`) denominator floor shape: `Ev(v)·2^111 + T·Od(v) − D·2^725 ≥ 0`. The
granularity lift is monotone in `|t|`, so the single cap evaluation floors a whole piece's
negative half. -/
def certDUnderP (T D : Int) : List Int :=
  polyAdd (polyAdd (polyScale (2 ^ 111) evVPoly) (polyScale T odVPoly)) [-(D * 2 ^ 725)]

/-- The global over-half floor at the domain edge: `DEN(v, t) ≥ 1108965543718·2^725` on all of
`[0, vmaxV + 1]` for every `0 ≤ t ≤ H129` (real-scale minimum `≈ 1.1090·10¹²`, attained interior). -/
def certDOver : List Int := certDOverP (H129 : Int) 1108965543718

end ExpCertV
