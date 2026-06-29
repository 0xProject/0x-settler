import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.Order.Floor.Defs
import Common.Seam.RealExpBridge
import ExpProof.Spec.RealExp
import ExpProof.Spec.Cut

open scoped BigOperators

/-!
# `expRayToWad` real bridge

The bridge from the real-free `Nat` cuts (`ExpProof.Spec.Cut`) to the public
`Real.exp` brackets (`ExpProof.Spec.RealExp`).

The bridge has two reductions:

1. *Cut → real exp bound.* `Common.RealExpBridge.exp_le_of_capUB` /
   `le_exp_of_capLB` turn a folded `capUB`/`capLB` directly into a `Real.exp`
   bound on the cut argument. The octave-folded argument `(k·tDen + tNum)/tDen`
   already equals `k·1 + tNum/tDen`, and `exp(k + s) = (e^1)^k · e^s`; but the
   tie to `E = WAD·exp(x/RAY)` runs through the runtime's specific octave/argument
   constants (the reduced-argument identity `x/RAY = k·ln2 + t`), which the
   certificate and floor layers supply. So this reduction is exposed as the standalone
   `expBound_of_*Cut` lemmas, and the connection to `E` is taken as a hypothesis.

2. *Pre-floor accumulator → bracket.* The cut conclusions are the real
   inequalities `A ≤ E` (never over) and `E < A + 1` (not two below) on the
   pre-floor accumulator `A`; the runtime returns `r = ⌊A⌋` (the `Floor` layer,
   after its floor proof). Given those three facts the public brackets follow by
   `Int.floor` reasoning. These are the standalone, axiom-clean reduction lemmas
   used by the certificate and floor layers.
-/

namespace ExpRealBridge

open Common.Exp Common.RealExpBridge ExpFloor ExpFloorCert ExpRealSpec

noncomputable section

/-! ## Cut To A `Real.exp` Bound On The Folded Argument

The folded cut argument `(k·tDen + tNum)/tDen` splits as `k + tNum/tDen`, so
`exp((k·tDen + tNum)/tDen) = (exp 1)^k · exp(tNum/tDen)` — the multiplicative
octave factor `(e^a)^k` the floor layer folds against the runtime's `2^k`
(with `a = ln2` in the unfolded `ln2`-denominator form). -/

/-- The octave fold on the cut argument: an integer step `k` factors out
multiplicatively. -/
theorem exp_folded_arg {tNum tDen k : Nat} (hq : 0 < tDen) :
    Real.exp (((k * tDen + tNum : Nat) : Real) / (tDen : Real)) =
      (Real.exp 1) ^ k * Real.exp ((tNum : Real) / (tDen : Real)) := by
  have hqne : (tDen : Real) ≠ 0 := by
    have : (0 : Real) < (tDen : Real) := by exact_mod_cast hq
    exact ne_of_gt this
  have harg : (((k * tDen + tNum : Nat) : Real) / (tDen : Real)) =
      (k : Real) + (tNum : Real) / (tDen : Real) := by
    push_cast
    field_simp
  rw [harg, Real.exp_add, ← Real.exp_nat_mul, mul_one]


/-- The never-over cut yields a real upper bound on the octave-folded
exponential: `exp((k·tDen + tNum)/tDen) ≤ yUB/wUB`. -/
theorem expBound_of_neverOverCut {tNum tDen k yUB wUB : Nat}
    (hq : 0 < tDen) (hw : 0 < wUB)
    (hcut : ExpNeverOverCut tNum tDen k yUB wUB) :
    Real.exp (((k * tDen + tNum : Nat) : Real) / (tDen : Real)) ≤ (yUB : Real) / wUB :=
  exp_le_of_capUB hq hw hcut

/-- The not-two-below cut yields a real lower bound on the octave-folded
exponential: `yLB/wLB ≤ exp((k·tDen + tNum)/tDen)`. -/
theorem expBound_of_notTwoBelowCut {tNum tDen k yLB wLB : Nat}
    (hq : 0 < tDen) (hw : 0 < wLB)
    (hcut : ExpNotTwoBelowCut tNum tDen k yLB wLB) :
    (yLB : Real) / wLB ≤ Real.exp (((k * tDen + tNum : Nat) : Real) / (tDen : Real)) :=
  le_exp_of_capLB hq hw hcut

/-- Core-octave (`k = 0`) upper bound on the bare reduced argument. -/
theorem expBound_of_coreOctaveExactCut_le {tNum tDen yUB wUB yLB wLB : Nat}
    (hq : 0 < tDen) (hw : 0 < wUB)
    (hcut : CoreOctaveExactCut tNum tDen yUB wUB yLB wLB) :
    Real.exp ((tNum : Real) / (tDen : Real)) ≤ (yUB : Real) / wUB :=
  exp_le_of_capUB hq hw hcut.1

/-- Core-octave (`k = 0`) lower bound on the bare reduced argument. -/
theorem expBound_of_coreOctaveExactCut_ge {tNum tDen yUB wUB yLB wLB : Nat}
    (hq : 0 < tDen) (hw : 0 < wLB)
    (hcut : CoreOctaveExactCut tNum tDen yUB wUB yLB wLB) :
    (yLB : Real) / wLB ≤ Real.exp ((tNum : Real) / (tDen : Real)) :=
  le_exp_of_capLB hq hw hcut.2

/-! ## Negative-argument reciprocal

For `x < 0` the runtime reduces `−x` and forms `exp(x/RAY) = 1 / exp(−x/RAY)`.
The lower cap on `exp(−t)` becomes the upper bound the never-over half needs, and
vice versa; `Real.exp_neg` is the bridge. These standalone lemmas expose that
reciprocal so the floor layer can route the negative branch. -/

/-- `exp(−s) = 1 / exp(s)`; the reciprocal relating the two sign branches. -/
theorem exp_neg_eq_inv (s : Real) : Real.exp (-s) = (Real.exp s)⁻¹ :=
  Real.exp_neg s

/-- A lower cap on `exp(s)` is an upper bound on `exp(−s)`: if `g/v ≤ exp(s)` and
`g/v > 0` then `exp(−s) ≤ v/g`. -/
theorem expNeg_le_of_le_exp {s : Real} {g v : Real} (hg : 0 < g) (hv : 0 < v)
    (h : g / v ≤ Real.exp s) : Real.exp (-s) ≤ v / g := by
  rw [exp_neg_eq_inv]
  have hexp_pos : 0 < Real.exp s := Real.exp_pos s
  have hgv : (0 : Real) < g / v := div_pos hg hv
  rw [inv_le_comm₀ hexp_pos (by positivity)]
  calc (v / g) ⁻¹ = g / v := by rw [inv_div]
    _ ≤ Real.exp s := h

/-- An upper cap on `exp(s)` is a lower bound on `exp(−s)`: if `exp(s) ≤ y/w` and
`y/w > 0` then `w/y ≤ exp(−s)`. -/
theorem le_expNeg_of_exp_le {s : Real} {y w : Real} (hy : 0 < y) (hw : 0 < w)
    (h : Real.exp s ≤ y / w) : w / y ≤ Real.exp (-s) := by
  rw [exp_neg_eq_inv]
  have hexp_pos : 0 < Real.exp s := Real.exp_pos s
  rw [le_inv_comm₀ (by positivity) hexp_pos]
  calc Real.exp s ≤ y / w := h
    _ = (w / y)⁻¹ := by rw [inv_div]

/-! ## Pre-floor Accumulator To Public Brackets

`A` is the real pre-floor accumulator and `r = ⌊A⌋` the runtime result (the
`Floor` layer discharges `r = ⌊A⌋`). The cut conclusions are
`A ≤ E` (never over) and `E < A + 1` (not two below). -/

/-- **Floor-or-one-less reduction.** From the never-over conclusion `A ≤ E`, the
not-two-below conclusion `E < A + 1`, and the floor step `(r : Real) = ⌊A⌋` (so
`r ≤ A < r + 1`), the global 2-wide bracket holds. -/
theorem floorOrOneLessBracket_of_accum {x : Int} {r : Int} {A : Real}
    (hfloor : (r : Real) ≤ A) (hfloor1 : A < (r : Real) + 1)
    (hover : A ≤ expRayToWadTarget x)
    (hunder : expRayToWadTarget x < A + 1) :
    FloorOrOneLessBracket x r := by
  refine ⟨le_trans hfloor hover, ?_⟩
  calc expRayToWadTarget x < A + 1 := hunder
    _ < ((r : Real) + 1) + 1 := by linarith
    _ = (r : Real) + 2 := by ring

/-- **Exact-floor reduction.** On the core octave the margin slack is negligible,
so the floor catches `E` exactly: from `r ≤ A`, the never-over `A ≤ E`, and the
sharpened upper bound `E < r + 1`, the 1-wide bracket holds. -/
theorem exactFloorBracket_of_accum {x : Int} {r : Int} {A : Real}
    (hfloor : (r : Real) ≤ A)
    (hover : A ≤ expRayToWadTarget x)
    (hexact : expRayToWadTarget x < (r : Real) + 1) :
    ExactFloorBracket x r :=
  ⟨le_trans hfloor hover, hexact⟩

/-- **One-unit underestimation reduction.** The lower bound `r ≥ ⌊E⌋ − 1` is the
lower half of the floor-or-one-less bracket; given that bracket it follows. -/
theorem underByAtMostOne_of_floorOrOneLess {x : Int} {r : Int}
    (h : FloorOrOneLessBracket x r) : UnderByAtMostOne x r :=
  floorOrOneLess_to_underByAtMostOne h

/-- **One-unit underestimation reduction, direct.** From the pre-floor accumulator facts the
1-unit lower bound follows directly. -/
theorem underByAtMostOne_of_accum {x : Int} {r : Int} {A : Real}
    (hfloor : (r : Real) ≤ A) (hfloor1 : A < (r : Real) + 1)
    (hover : A ≤ expRayToWadTarget x)
    (hunder : expRayToWadTarget x < A + 1) :
    UnderByAtMostOne x r :=
  floorOrOneLess_to_underByAtMostOne
    (floorOrOneLessBracket_of_accum hfloor hfloor1 hover hunder)

end

end ExpRealBridge
