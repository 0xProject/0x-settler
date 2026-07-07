import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Floor.Defs
import Common.Foundation.ExpSum
import ExpProof.Cert.ExpVUp
import ExpProof.Cert.ExpVLo
import ExpProof.Cert.ExpVNum
import ExpProof.Cert.ExpVDenM1

/-!
# From cell certificates to the **v-form** reduced-argument Taylor caps

The v-form cell covers (`Cert/ExpVUp`, `Cert/ExpVLo`, `Cert/ExpVNum`, `Cert/ExpVDenM1`) certify the
four v-form certificate polynomials nonnegative over `t ∈ [0, H129]`. This module converts that
nonnegativity into the two bare-argument Taylor caps the floor layer folds with `2^k`, targeting the
implementation's exact **v-form** rational `ê_v(t) = NUM(t)/DEN(t)` (built from the even/odd Horner
polynomials in `v = t²`) nudged by the dyadic margin, with `Qexp = 2^128`:

* `capExpUp` — never-over `exp(t/Qexp) ≤ yUB(t)/wUB(t)` with `yUB/wUB = ê_v·(1 + 2⁻¹³²)`;
* `capExpLo` — not-two-below `yLB(t)/wLB(t) ≤ exp(t/Qexp)` with `yLB/wLB = ê_v·(1 − 2⁻¹³²)`.

The bridge is the depth-`K = 27` `Common.Exp.capUB_of_partial`/`capLB` shape.
-/

namespace ExpCertV

open Common.Poly Common.Exp

set_option maxRecDepth 100000

/-! ## The two Int→Nat cap bridges at Taylor depth `K = 27` -/

/-- One evaluated partial sum (depth 27) plus the geometric tail gives a full upper cap. -/
theorem capUB27_of_int {tn td y w : Nat} (htd : 0 < td) (hH : 2 * tn ≤ 29 * td)
    (h : (expNumI 27 (tn : Int) (td : Int) * (28 * (td : Int)) + 2 * (tn : Int) ^ 28) *
        (w : Int) ≤ (y : Int) * (304888344611713860501504000000 * (td : Int) ^ 28)) :
    capUB tn td y w := by
  refine capUB_of_partial htd (by omega : 2 * tn ≤ (27 + 2) * td) ?_
  show (expNum 27 tn td * ((27 + 1) * td) + 2 * tn ^ (27 + 1)) * w ≤ y * (fact 28 * td ^ 28)
  rw [show fact 28 = 304888344611713860501504000000 from by decide,
      show (27 + 1) = 28 from rfl]
  refine Int.ofNat_le.mp ?_
  rw [expNumI_eq_expNum] at h
  simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_pow]
  exact h

/-- The single depth-27 partial sum reaches the lower target. -/
theorem capLB27_of_int {tn td y w : Nat}
    (h : (y : Int) * (10888869450418352160768000000 * (td : Int) ^ 27) ≤
        expNumI 27 (tn : Int) (td : Int) * (w : Int)) :
    capLB tn td y w := by
  refine ⟨27, ?_⟩
  show y * (fact 27 * td ^ 27) ≤ expNum 27 tn td * w
  rw [show fact 27 = 10888869450418352160768000000 from by decide]
  refine Int.ofNat_le.mp ?_
  rw [expNumI_eq_expNum] at h
  simp only [Int.natCast_mul, Int.natCast_pow]
  exact h

/-! ## Evaluation shapes of the certificate polynomials -/

theorem evalExpN27 (t : Int) : evalPoly expN27 t = expNumI 27 t (Qexp : Int) := by
  unfold expN27
  rw [evalPoly_expPolyNum]
  congr 1 <;> simp [evalPoly]

theorem evalYUB (t : Int) : evalPoly yUB t = (2 ^ 132 + 1) * evalPoly numExpV t := by
  unfold yUB; rw [evalPoly_polyScale]

theorem evalWUB (t : Int) : evalPoly wUB t = 2 ^ 132 * evalPoly denExpV t := by
  unfold wUB; rw [evalPoly_polyScale]

theorem evalYLB (t : Int) : evalPoly yLB t = (2 ^ 132 - 1) * evalPoly numExpV t := by
  unfold yLB; rw [evalPoly_polyScale]

theorem evalWLB (t : Int) : evalPoly wLB t = 2 ^ 132 * evalPoly denExpV t := by
  unfold wLB; rw [evalPoly_polyScale]

theorem evalTailUp (t : Int) :
    evalPoly tailUp t = 28 * (Qexp : Int) * expNumI 27 t (Qexp : Int) + 2 * t ^ 28 := by
  unfold tailUp
  rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyScale, evalPoly_polyPow, evalExpN27]
  congr 1
  show _ = 2 * t ^ 28
  rw [show evalPoly ([0, 1] : List Int) t = t from by simp [evalPoly]]

/-- The never-over cert evaluates to the `capUB27_of_int` residue. -/
theorem evalCertExpUp (t : Int) :
    evalPoly certExpUp t =
      fact28Q28 * evalPoly yUB t -
        (28 * (Qexp : Int) * expNumI 27 t (Qexp : Int) + 2 * t ^ 28) * evalPoly wUB t := by
  unfold certExpUp
  rw [evalPoly_polySub, evalPoly_polyScale, evalPoly_polyMul, evalTailUp]

/-- The not-two-below cert evaluates to the `capLB27_of_int` residue. -/
theorem evalCertExpLo (t : Int) :
    evalPoly certExpLo t =
      expNumI 27 t (Qexp : Int) * evalPoly wLB t - fact27Q27 * evalPoly yLB t := by
  unfold certExpLo
  rw [evalPoly_polySub, evalPoly_polyMul, evalPoly_polyScale, evalExpN27]

/-! ## Positivity of the rational over the domain -/

/-- `1 ≤ DEN(t)` over the domain. -/
theorem denExpV_ge_one {t : Int} (h1 : 0 ≤ t) (h2 : t ≤ (H129 : Int)) :
    1 ≤ evalPoly denExpV t := by
  have h := denM1V_nonneg h1 h2
  unfold certDenM1 at h
  rw [evalPoly_polyAdd] at h
  rw [show evalPoly ([-1] : List Int) t = -1 from by simp [evalPoly]] at h
  omega

/-- `0 ≤ NUM(t)` over the domain. -/
theorem numExpV_nonneg' {t : Int} (h1 : 0 ≤ t) (h2 : t ≤ (H129 : Int)) :
    0 ≤ evalPoly numExpV t := numExpV_nonneg h1 h2

/-! ## The bare-argument Taylor caps -/

theorem Qexp_eq : (Qexp : Int) = 2 ^ 129 := by unfold Qexp; norm_num

theorem Qexp_pos : 0 < Qexp := by unfold Qexp; norm_num

/-- **Never-over cap** at the v-form rational `yUB/wUB = ê_v·(1 + 2⁻¹³²)`: for every reduced argument
`t ∈ [0, H129]`, `exp(t/Qexp) ≤ yUB(t)/wUB(t)`. -/
theorem capExpUp {t : Int} (h1 : 0 ≤ t) (h2 : t ≤ (H129 : Int)) :
    capUB t.toNat Qexp (evalPoly yUB t).toNat (evalPoly wUB t).toNat := by
  have hnum : 0 ≤ evalPoly numExpV t := numExpV_nonneg h1 h2
  have hden : 1 ≤ evalPoly denExpV t := denExpV_ge_one h1 h2
  have hden0 : 0 ≤ evalPoly denExpV t := by omega
  have hc120 : (0 : Int) ≤ 2 ^ 132 + 1 := by norm_num
  have hp120 : (0 : Int) ≤ 2 ^ 132 := by norm_num
  have hyub : 0 ≤ evalPoly yUB t := by
    rw [evalYUB]; exact Int.mul_nonneg hc120 hnum
  have hwub : 0 ≤ evalPoly wUB t := by
    rw [evalWUB]; exact Int.mul_nonneg hp120 hden0
  have htn : (t.toNat : Int) = t := Int.toNat_of_nonneg h1
  have hyn : ((evalPoly yUB t).toNat : Int) = evalPoly yUB t := Int.toNat_of_nonneg hyub
  have hwn : ((evalPoly wUB t).toNat : Int) = evalPoly wUB t := Int.toNat_of_nonneg hwub
  refine capUB27_of_int Qexp_pos ?_ ?_
  · have htle : t.toNat ≤ H129 := by
      have : (t.toNat : Int) ≤ (H129 : Int) := by rw [htn]; exact h2
      exact_mod_cast this
    have hHQ : 2 * H129 < 29 * Qexp := by unfold H129 Qexp; norm_num
    omega
  · rw [htn, hyn, hwn, Qexp_eq]
    have h := expVUp_nonneg h1 h2
    rw [evalCertExpUp] at h
    unfold fact28Q28 at h
    rw [Qexp_eq] at h
    have key : (28 * (2 : Int) ^ 129 * expNumI 27 t (2 ^ 129) + 2 * t ^ 28) * evalPoly wUB t ≤
        304888344611713860501504000000 * ((2 : Int) ^ 129) ^ 28 * evalPoly yUB t := by omega
    calc (expNumI 27 t (2 ^ 129) * (28 * (2 : Int) ^ 129) + 2 * t ^ 28) * evalPoly wUB t
        = (28 * (2 : Int) ^ 129 * expNumI 27 t (2 ^ 129) + 2 * t ^ 28) * evalPoly wUB t := by ring
      _ ≤ 304888344611713860501504000000 * ((2 : Int) ^ 129) ^ 28 * evalPoly yUB t := key
      _ = evalPoly yUB t * (304888344611713860501504000000 * ((2 : Int) ^ 129) ^ 28) := by ring

/-- **Not-two-below cap** at the v-form rational `yLB/wLB = ê_v·(1 − 2⁻¹³²)`: for every reduced
argument `t ∈ [0, H129]`, `yLB(t)/wLB(t) ≤ exp(t/Qexp)`. -/
theorem capExpLo {t : Int} (h1 : 0 ≤ t) (h2 : t ≤ (H129 : Int)) :
    capLB t.toNat Qexp (evalPoly yLB t).toNat (evalPoly wLB t).toNat := by
  have hnum : 0 ≤ evalPoly numExpV t := numExpV_nonneg h1 h2
  have hden : 1 ≤ evalPoly denExpV t := denExpV_ge_one h1 h2
  have hden0 : 0 ≤ evalPoly denExpV t := by omega
  have hc126 : (0 : Int) ≤ 2 ^ 132 - 1 := by norm_num
  have hp126 : (0 : Int) ≤ 2 ^ 132 := by norm_num
  have hylb : 0 ≤ evalPoly yLB t := by
    rw [evalYLB]; exact Int.mul_nonneg hc126 hnum
  have hwlb : 0 ≤ evalPoly wLB t := by
    rw [evalWLB]; exact Int.mul_nonneg hp126 hden0
  have htn : (t.toNat : Int) = t := Int.toNat_of_nonneg h1
  have hyn : ((evalPoly yLB t).toNat : Int) = evalPoly yLB t := Int.toNat_of_nonneg hylb
  have hwn : ((evalPoly wLB t).toNat : Int) = evalPoly wLB t := Int.toNat_of_nonneg hwlb
  refine capLB27_of_int ?_
  rw [htn, hyn, hwn, Qexp_eq]
  have h := expVLo_nonneg h1 h2
  rw [evalCertExpLo] at h
  unfold fact27Q27 at h
  rw [Qexp_eq] at h
  calc evalPoly yLB t * (10888869450418352160768000000 * ((2 : Int) ^ 129) ^ 27)
      = 10888869450418352160768000000 * ((2 : Int) ^ 129) ^ 27 * evalPoly yLB t := by ring
    _ ≤ expNumI 27 t (2 ^ 129) * evalPoly wLB t := by omega

/-- info: 'ExpCertV.capExpUp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms capExpUp

/-- info: 'ExpCertV.capExpLo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms capExpLo

end ExpCertV
