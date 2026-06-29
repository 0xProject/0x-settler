import Common.Foundation.ShiftCert

/-!
# The v-form reduced-argument rational target and its Taylor cut certificates

The runtime forms `r0 = ⌊ê_v(t)·2^126⌋` with the **v-form** rational

```
ê_v(t) = (evNumV(v) · 2^105 + t · odNumV(v)) / (evNumV(v) · 2^105 − t · odNumV(v)),   v = t²/2^128,
```

built from the exact integer even/odd Horner polynomials `evNumV`/`odNumV` (defined in
`Floor/R0Bound.lean` as functions of the integer `v = vTree x`). The runtime's truncation bridge
lands on this representation, so the floor layer needs a cut certificate phrased on `ê_v`, not on the
t-form `ê_t = numExp/denExp`. `ê_v` and `ê_t` are equal as reals but differ as integer
polynomials (different shift-clearing), so this module re-derives the cut against `ê_v` directly.

Here `v = t²` is carried symbolically (each Horner stage multiplies by `t²` via `mulT2`, with the
runtime per-stage `>>128` cleared into the per-stage scale): `evNumVPoly` accumulates `Ev` to the
cleared scale `2^1193` and `odNumVPoly` accumulates `Od` to `2^1042`; `t·Od` (lifted by `2^23`) joins
`Ev` at the common `2^1193`. The shared scale cancels in `ê_v = NUM/DEN`. As a polynomial in `t` the
numerator/denominator are degree 10.

The cut is the standard `Common.Exp.capUB_of_partial`/`capLB` shape at Taylor depth `K = 27`, nudging
the rational by a dyadic margin (`yUB/wUB = ê_v·(1 + 2⁻¹²⁰)`, `yLB/wLB = ê_v·(1 − 2⁻¹²⁶)`); the
verified envelope `2¹²⁶·|ê_v − exp(t/2¹²⁸)| ≤ 0.057` ulp is far inside those margins.
-/

namespace ExpCertV

open Common.Poly

/-! ## The reduced-argument denominator and the cert domain -/

/-- The reduced-argument denominator `tDen = 2^128`: the runtime carries `t` in Q128. -/
def Qexp : Nat := 2 ^ 128

/-- The cert variable upper bound `H128 = ⌊ln2/2 · 2^128⌋`. -/
def H128 : Nat := 117932881612756647068972071382077242199

/-! ## Exact integer `ê_v(t) = NUM(t)/DEN(t)` from the implementation coefficients

The even/odd Horner accumulators evaluated as exact polynomials in `t` with `v = t²/2^128`, each
runtime per-stage `>>128` cleared into the stage scale. `evNumVPoly` is `evNumV(t²)` cleared to scale
`2^640` (so its evaluation is `Ev·2^1193`); `odNumVPoly` is `odNumV(t²)` cleared to scale `2^512`
(evaluation `Od·2^1042`); `t·Od` (lifted by `2^23` to the common `2^1193`) joins `Ev`. The shared
`2^1193` cancels in `ê_v = NUM/DEN`. -/

/-- `t²·P` at the polynomial level (one Horner `·v` stage, with the runtime `>>128` cleared into the
per-stage constant scale). -/
def mulT2 (P : List Int) : List Int := 0 :: 0 :: P

/-- The even Horner accumulator `Ev`, cleared to scale `2^640` (evaluation `Ev·2^1193`). The
per-stage constants are the even coefficients `A0..A4` lifted by the cleared stage scale; the
innermost monic `v` stage clears to `[A4·2^157, 0, 1]`. -/
def evNumVPoly : List Int :=
  polyAdd [0x4e14a45e8ec305e233e11b4174e214ac * 2 ^ 1193]
    (mulT2 (polyAdd [0x93f11e65781741b92fa7fc4f4fffcca2 * 2 ^ 933]
      (mulT2 (polyAdd [0x9064d965e1c4863b73604e0ddbec53f9 * 2 ^ 671]
        (mulT2 (polyAdd [0x9a036222e11aee18465042f8ea64c8 * 2 ^ 415]
          (mulT2 [0xb9aacfad41060587203a79af0ebc * 2 ^ 157, 0, 1])))))))

/-- The odd Horner accumulator `Od`, cleared to scale `2^512` (evaluation `Od·2^1042`). -/
def odNumVPoly : List Int :=
  polyAdd [0x270a522f476182f119f08da0ba710a56 * 2 ^ 1042]
    (mulT2 (polyAdd [0xaf5662483c4ce783a9ef5fe025f42e9e * 2 ^ 779]
      (mulT2 (polyAdd [0xad4506b00b1246c7e5b4fd33e1201b * 2 ^ 524]
        (mulT2 [0xc926ddbf3830ca5561cc01585402d0 * 2 ^ 259, 0, 0xdc07aff85e5bb5629d0fb64a84bb])))))

/-- `t·Od` lifted to the common scale `2^1193` (`= 2^23 · t · odNumVPoly`). -/
def todNumV : List Int := polyScale (2 ^ 23) (0 :: odNumVPoly)

/-- `ê_v`-numerator `NUM(t) = Ev(t) + t·Od(t)` (scale `2^1193`). -/
def numExpV : List Int := polyAdd evNumVPoly todNumV

/-- `ê_v`-denominator `DEN(t) = Ev(t) − t·Od(t)` (scale `2^1193`). -/
def denExpV : List Int := polySub evNumVPoly todNumV

/-! ## Taylor partial-sum numerator at the cut argument -/

/-- Polynomial-level depth-27 partial-sum numerator at argument `t/Qexp`. -/
def expN27 : List Int := expPolyNum [0, 1] [(Qexp : Int)] 27

/-! ## Margin-nudged rational targets

`yUB/wUB = ê_v·(1 + 2⁻¹²⁰)` and `yLB/wLB = ê_v·(1 − 2⁻¹²⁶)`. -/

def yUB : List Int := polyScale (2 ^ 120 + 1) numExpV
def wUB : List Int := polyScale (2 ^ 120) denExpV
def yLB : List Int := polyScale (2 ^ 126 - 1) numExpV
def wLB : List Int := polyScale (2 ^ 126) denExpV

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

end ExpCertV
