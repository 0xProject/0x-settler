import Common.Foundation.ShiftCert

/-!
# The reduced-argument rational target and its Taylor cut certificates

The runtime forms `r0 = ⌊ê(t)·2^126⌋` with `ê(t) = (Ev(v) + t·Od(v))/(Ev(v) − t·Od(v))`,
`v = t²`, the reciprocal-symmetric rational of the even/odd Horner accumulators. The Taylor certificates
sandwich this rational by `exp(t)` within the runtime margin: they
establishes, over the reduced domain `t ∈ [0, H128]` (the cert variable `t` is the Q128
reduced argument, `tDen = 2^128`), the two bare-argument Taylor caps

* never-over `exp(t) ≤ yUB(t)/wUB(t)` (`capUB`), and
* not-two-below `yLB(t)/wLB(t) ≤ exp(t)` (`capLB`),

where the targets are the *exact* rational `ê(t) = NUM(t)/DEN(t)` (built here from the
implementation's even/odd coefficients, with the common `2^1193` scale cancelling) nudged by a
dyadic margin: `yUB/wUB = ê·(1 + 2⁻¹²⁰)` and `yLB/wLB = ê·(1 − 2⁻¹²⁶)`. The negative-`t` branch
reuses these via the reciprocal bridge; the octave `2^k` fold is handled by the `*_of_fold` lemmas.

`NUM`/`DEN` are derived from the same `A0..A4`/`B0..B4` even/odd coefficients and per-stage shifts
that `Mono/Tree.lean` reads off the compiled `_expRayToWad`, with every `>>` cleared to an exact
integer scale (`Ev` to `2^1193`, `t·Od` to `2^1170`, then both lifted to the common `2^1193`). The
cert polynomials are the standard `Common.Exp.capUB_of_partial` / `capLB` shapes at Taylor depth
`K = 27` (the depth that resolves `exp(t)` to below the rational's `~2⁻¹³⁰` accuracy on
`|t| ≤ ln2/2`).
-/

namespace ExpCert

open Common.Poly

/-! ## The reduced-argument denominator and the cert domain -/

/-- The reduced-argument denominator `tDen = 2^128`: the runtime carries `t` in Q128. -/
def Qexp : Nat := 2 ^ 128

/-- The cert variable upper bound `H128 = ⌊ln2/2 · 2^128⌋`; the reduced argument satisfies
`0 ≤ t ≤ H128` on the nonnegative half of the core domain. -/
def H128 : Nat := 117932881612756647068972071382077242199

/-! ## Exact integer `ê(t) = NUM(t)/DEN(t)` from the implementation coefficients

The even/odd Horner accumulators evaluated as exact polynomials in the Q128 integer `t`, with each
runtime `>>sh` cleared to an integer scale. `evNum` accumulates `Ev` to scale `2^1193`; `odNum`
accumulates `Od` to scale `2^1042`; `t·Od` (scale `2^1170`) is lifted by `2^23` to the common
`2^1193`. The shared `2^1193` cancels in `ê = NUM/DEN`, so the scale is immaterial to the cut. -/

/-- `t²·P` at the polynomial level. -/
def mulT2 (P : List Int) : List Int := 0 :: 0 :: P

/-- The even Horner accumulator `Ev`, cleared to scale `2^1193` (a polynomial in `t`, even
degrees only). The per-stage constants are the even coefficients `A0..A4` lifted by the cleared
shift product. -/
def evNum : List Int :=
  polyAdd [0x4e14a45e8ec305e233e11b4174e214ac * 2 ^ 1193]
    (mulT2 (polyAdd [0x93f11e65781741b92fa7fc4f4fffcca2 * 2 ^ 933]
      (mulT2 (polyAdd [0x9064d965e1c4863b73604e0ddbec53f9 * 2 ^ 671]
        (mulT2 (polyAdd [0x9a036222e11aee18465042f8ea64c8 * 2 ^ 415]
          (mulT2 (polyAdd [0xb9aacfad41060587203a79af0ebc * 2 ^ 157] [0, 0, 1]))))))))

/-- The odd Horner accumulator `Od`, cleared to scale `2^1042` (a polynomial in `t`, even degrees
only — the leading `t` factor is applied in `tod`). The per-stage constants are the odd
coefficients `B0..B4`. -/
def odNum : List Int :=
  polyAdd [0x270a522f476182f119f08da0ba710a56 * 2 ^ 1042]
    (mulT2 (polyAdd [0xaf5662483c4ce783a9ef5fe025f42e9e * 2 ^ 779]
      (mulT2 (polyAdd [0xad4506b00b1246c7e5b4fd33e1201b * 2 ^ 524]
        (mulT2 (polyAdd [0xc926ddbf3830ca5561cc01585402d0 * 2 ^ 259]
          (mulT2 [0xdc07aff85e5bb5629d0fb64a84bb])))))))

/-- `t·Od` lifted to the common scale `2^1193` (`= 2^23 · t · odNum`). -/
def todNum : List Int := polyScale (2 ^ 23) (0 :: odNum)

/-- `ê`-numerator `NUM(t) = Ev(t) + t·Od(t)` (scale `2^1193`). -/
def numExp : List Int := polyAdd evNum todNum

/-- `ê`-denominator `DEN(t) = Ev(t) − t·Od(t)` (scale `2^1193`). -/
def denExp : List Int := polySub evNum todNum

/-! ## Taylor partial-sum numerator at the cut argument

`expN27 = expPolyNum [0,1] [Qexp] 27` evaluates to `expNumI 27 t Qexp` (the integer numerator of the
depth-27 partial sum `S_27(t/Qexp)`). -/

/-- Polynomial-level depth-27 partial-sum numerator at argument `t/Qexp`. -/
def expN27 : List Int := expPolyNum [0, 1] [(Qexp : Int)] 27

/-! ## Margin-nudged rational targets

`yUB/wUB = ê·(1 + 2⁻¹²⁰)` and `yLB/wLB = ê·(1 − 2⁻¹²⁶)`. The numerator margins ride on `NUM`; the
denominator margins are the bare `2^120`/`2^126`. -/

def yUB : List Int := polyScale (2 ^ 120 + 1) numExp
def wUB : List Int := polyScale (2 ^ 120) denExp
def yLB : List Int := polyScale (2 ^ 126 - 1) numExp
def wLB : List Int := polyScale (2 ^ 126) denExp

/-! ## The cut certificate polynomials

`certExpUp = yUB·(28!·Qexp²⁸) − (expN27·(28·Qexp) + 2·t²⁸)·wUB`, the `capUB_of_partial` residue at
`K = 27`; nonnegativity on a cell gives `capUB t Qexp (yUB t) (wUB t)`.

`certExpLo = expN27·wLB − yLB·(27!·Qexp²⁷)`, the `capLB` residue at the single partial sum `n = 27`;
nonnegativity gives `capLB t Qexp (yLB t) (wLB t)`. -/

/-- `28! · Qexp^28`. -/
def fact28Q28 : Int := 304888344611713860501504000000 * (Qexp : Int) ^ 28

/-- `27! · Qexp^27`. -/
def fact27Q27 : Int := 10888869450418352160768000000 * (Qexp : Int) ^ 27

/-- The `capUB_of_partial` tail polynomial `expN27·(28·Qexp) + 2·t²⁸`. -/
def tailUp : List Int :=
  polyAdd (polyScale (28 * (Qexp : Int)) expN27) (polyScale 2 (polyPow [0, 1] 28))

def certExpUp : List Int := polySub (polyScale fact28Q28 yUB) (polyMul tailUp wUB)

def certExpLo : List Int := polySub (polyMul expN27 wLB) (polyScale fact27Q27 yLB)

/-- `DEN(t) − 1`: nonnegativity over the domain certifies `1 ≤ DEN(t)`, so the rational denominator
is a positive `Nat`. -/
def certDenM1 : List Int := polyAdd denExp [-1]

end ExpCert
