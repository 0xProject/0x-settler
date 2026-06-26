import LnProof.Floor.CutEquiv
import LnProof.Error.Cert
import LnProof.Error.Core.CutDefs

/-!
# Error bound — ExpMargin

The `sumGE`→certificate toolkit: exp-margin polynomials (poly / L1 / value forms), nonnegative-interval evaluation, and the `sumGE_of_expMargin*` bridges.
-/

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

namespace LnFloorCert

open LnYul LnFloor LnExp LnPoly

attribute [local irreducible] lnWadToRayBody


def expMarginPoly (n : Nat) (pn qd y : List Int) (w : Nat) : List Int :=
  polySub (polyScale (w : Int) (expPolyNum pn qd n))
    (polyScale (fact n : Int) (polyMul y (polyPow qd n)))

def expMarginFastState (pn qd y : List Int) (w : Nat) : Nat → List Int × List Int
  | 0 => (polySub [((w : Nat) : Int)] y, [1])
  | n + 1 =>
      let st := expMarginFastState pn qd y w n
      let pp := polyMul pn st.2
      (polyAdd (polyScale (((n + 1 : Nat) : Int)) (polyMul qd st.1))
        (polyScale (((w : Nat) : Int)) pp), pp)

def expMarginPolyFast (n : Nat) (pn qd y : List Int) (w : Nat) : List Int :=
  (expMarginFastState pn qd y w n).1

theorem evalPoly_expMarginFastState_pow (pn qd y : List Int) (w n : Nat) (x : Int) :
    evalPoly (expMarginFastState pn qd y w n).2 x = evalPoly pn x ^ n := by
  induction n with
  | zero =>
      simp [expMarginFastState, evalPoly]
  | succ n ih =>
      simp [expMarginFastState, evalPoly_polyMul, ih, Int.pow_succ]
      rw [Int.mul_comm]

theorem evalPoly_expMarginPolyFast (pn qd y : List Int) (w n : Nat) (x : Int) :
    evalPoly (expMarginPolyFast n pn qd y w) x =
      (w : Int) * expNumI n (evalPoly pn x) (evalPoly qd x) -
        (fact n : Int) * evalPoly y x * evalPoly qd x ^ n := by
  induction n with
  | zero =>
      simp [expMarginPolyFast, expMarginFastState, evalPoly_polySub,
        expNumI, fact, evalPoly]
  | succ n ih =>
      unfold expMarginPolyFast
      simp only [expMarginFastState, evalPoly_polyAdd, evalPoly_polyScale,
        evalPoly_polyMul, evalPoly_expMarginFastState_pow, expNumI, fact]
      rw [show evalPoly (expMarginFastState pn qd y w n).fst x =
          evalPoly (expMarginPolyFast n pn qd y w) x by rfl]
      rw [ih]
      simp only [Int.pow_succ]
      simp only [Int.natCast_add, Int.natCast_one, Int.natCast_mul]
      generalize ((n : Int) + 1) = N
      generalize (w : Int) = W
      generalize expNumI n (evalPoly pn x) (evalPoly qd x) = E
      generalize evalPoly pn x = P
      generalize evalPoly pn x ^ n = Pn
      generalize (fact n : Int) = F
      generalize evalPoly y x = Y
      generalize evalPoly qd x = Q
      simp only [Int.mul_add, Int.mul_sub]
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      omega

theorem sumGE_of_expMarginPoly {n m p q y w : Nat} {pn qd yp : List Int}
    (hcert : 0 ≤ evalPoly (expMarginPoly n pn qd yp w) (m : Int))
    (hpn : evalPoly pn (m : Int) = (p : Int))
    (hqd : evalPoly qd (m : Int) = (q : Int))
    (hy : evalPoly yp (m : Int) = (y : Int)) :
    sumGE n p q y w := by
  unfold expMarginPoly at hcert
  rw [evalPoly_polySub, evalPoly_polyScale, evalPoly_expPolyNum,
    evalPoly_polyScale, evalPoly_polyMul, evalPoly_polyPow, hpn, hqd, hy] at hcert
  rw [expNumI_eq_expNum] at hcert
  unfold sumGE
  refine Int.ofNat_le.mp ?_
  simp only [Int.natCast_mul, Int.natCast_pow]
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at hcert ⊢
  omega

theorem sumGE_of_expMarginPolyFast {n m p q y w : Nat} {pn qd yp : List Int}
    (hcert : 0 ≤ evalPoly (expMarginPolyFast n pn qd yp w) (m : Int))
    (hpn : evalPoly pn (m : Int) = (p : Int))
    (hqd : evalPoly qd (m : Int) = (q : Int))
    (hy : evalPoly yp (m : Int) = (y : Int)) :
    sumGE n p q y w := by
  rw [evalPoly_expMarginPolyFast, hpn, hqd, hy] at hcert
  rw [expNumI_eq_expNum] at hcert
  unfold sumGE
  refine Int.ofNat_le.mp ?_
  simp only [Int.natCast_mul, Int.natCast_pow]
  simp only [Int.mul_comm, Int.mul_left_comm] at hcert ⊢
  omega

def expMarginL1BoundState (pb qb yb w : Nat) : Nat → Nat × Nat
  | 0 => (w + yb, 1)
  | n + 1 =>
      let st := expMarginL1BoundState pb qb yb w n
      let pp := pb * st.2
      ((n + 1) * qb * st.1 + w * pp, pp)

def expMarginL1Bound (n pb qb yb w : Nat) : Nat :=
  (expMarginL1BoundState pb qb yb w n).1

theorem polyL1_singleton_nat (w : Nat) :
    polyL1 [((w : Nat) : Int)] = w := by
  simp [polyL1]

theorem polyL1_expMarginFastState (pn qd y : List Int) (w n : Nat) :
    polyL1 (expMarginFastState pn qd y w n).1 ≤
        (expMarginL1BoundState (polyL1 pn) (polyL1 qd) (polyL1 y) w n).1 ∧
      polyL1 (expMarginFastState pn qd y w n).2 ≤
        (expMarginL1BoundState (polyL1 pn) (polyL1 qd) (polyL1 y) w n).2 := by
  induction n with
  | zero =>
      unfold expMarginFastState expMarginL1BoundState
      constructor
      · unfold polySub
        have hadd := polyL1_polyAdd [((w : Nat) : Int)] (polyNeg y)
        rw [polyL1_singleton_nat, polyL1_polyNeg] at hadd
        exact hadd
      · simp [polyL1]
  | succ n ih =>
      unfold expMarginFastState expMarginL1BoundState
      let st := expMarginFastState pn qd y w n
      let bt := expMarginL1BoundState (polyL1 pn) (polyL1 qd) (polyL1 y) w n
      have hpw : polyL1 (polyMul pn st.2) ≤ polyL1 pn * bt.2 := by
        have hmul := polyL1_polyMul pn st.2
        exact Nat.le_trans hmul (Nat.mul_le_mul_left _ ih.2)
      constructor
      · have hsum := polyL1_polyAdd
          (polyScale (((n + 1 : Nat) : Int)) (polyMul qd st.1))
          (polyScale (((w : Nat) : Int)) (polyMul pn st.2))
        have hscale1 := polyL1_polyScale (((n + 1 : Nat) : Int)) (polyMul qd st.1)
        have hmul1 := polyL1_polyMul qd st.1
        have hscale2 := polyL1_polyScale (((w : Nat) : Int)) (polyMul pn st.2)
        have h1 : polyL1 (polyScale (((n + 1 : Nat) : Int)) (polyMul qd st.1)) ≤
            (n + 1) * polyL1 qd * bt.1 := by
          have hm : polyL1 (polyMul qd st.1) ≤ polyL1 qd * bt.1 :=
            Nat.le_trans hmul1 (Nat.mul_le_mul_left _ ih.1)
          have hs := Nat.mul_le_mul_left (n + 1) hm
          simpa [Int.natAbs_natCast, Nat.mul_assoc] using Nat.le_trans hscale1 hs
        have h2 : polyL1 (polyScale (((w : Nat) : Int)) (polyMul pn st.2)) ≤
            w * (polyL1 pn * bt.2) := by
          have hs := Nat.mul_le_mul_left w hpw
          simpa [Int.natAbs_natCast] using Nat.le_trans hscale2 hs
        exact Nat.le_trans hsum (Nat.add_le_add h1 h2)
      · exact hpw

theorem polyL1_expMarginPolyFast (pn qd y : List Int) (w n : Nat) :
    polyL1 (expMarginPolyFast n pn qd y w) ≤
      expMarginL1Bound n (polyL1 pn) (polyL1 qd) (polyL1 y) w := by
  exact (polyL1_expMarginFastState pn qd y w n).1

def expMarginValState (p q y w : Int) : Nat → Int × Int
  | 0 => (w - y, 1)
  | n + 1 =>
      let st := expMarginValState p q y w n
      let pp := p * st.2
      (((n + 1 : Nat) : Int) * q * st.1 + w * pp, pp)

def expMarginVal (n : Nat) (p q y w : Int) : Int :=
  (expMarginValState p q y w n).1

theorem expMarginValState_pow (p q y w : Int) (n : Nat) :
    (expMarginValState p q y w n).2 = p ^ n := by
  induction n with
  | zero =>
      simp [expMarginValState]
  | succ n ih =>
      simp [expMarginValState, ih, Int.pow_succ]
      rw [Int.mul_comm]

theorem expMarginVal_eq (p q y w : Int) (n : Nat) :
    expMarginVal n p q y w =
      w * expNumI n p q - (fact n : Int) * y * q ^ n := by
  induction n with
  | zero =>
      simp [expMarginVal, expMarginValState, expNumI, fact]
  | succ n ih =>
      unfold expMarginVal
      simp only [expMarginValState, expMarginValState_pow, expNumI, fact]
      rw [show (expMarginValState p q y w n).fst = expMarginVal n p q y w by rfl]
      rw [ih]
      simp only [Int.pow_succ, Int.natCast_add, Int.natCast_one, Int.natCast_mul]
      generalize ((n : Int) + 1) = N
      generalize expNumI n p q = E
      generalize p = P
      generalize p ^ n = Pn
      generalize (fact n : Int) = F
      generalize q = Q
      generalize y = Y
      generalize w = W
      simp only [Int.mul_add, Int.mul_sub]
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      omega

theorem sumGE_of_expMarginVal {n p q y w : Nat}
    (hcert : 0 ≤ expMarginVal n (p : Int) (q : Int) (y : Int) (w : Int)) :
    sumGE n p q y w := by
  rw [expMarginVal_eq, expNumI_eq_expNum] at hcert
  unfold sumGE
  refine Int.ofNat_le.mp ?_
  simp only [Int.natCast_mul, Int.natCast_pow]
  simp only [Int.mul_comm, Int.mul_left_comm] at hcert ⊢
  omega

def shiftedExpMarginCellOkB (B n : Nat) (pn qd y : List Int)
    (lo hi outW : Nat) (S : List Int) : Bool :=
  decide (lo ≤ hi) &&
    let pS := polyShift pn (lo : Int)
    let qS := polyShift qd (lo : Int)
    let yS := polyShift y (lo : Int)
    let K := ((2 ^ B : Nat) : Int)
    decide (polyL1 S * 2 < 2 ^ B) &&
      decide (expMarginL1Bound n (polyL1 pS) (polyL1 qS) (polyL1 yS) outW * 2 < 2 ^ B) &&
        decide (evalPoly S K =
          expMarginVal n (evalPoly pS K) (evalPoly qS K) (evalPoly yS K) (outW : Int)) &&
          decide (0 ≤ (hornerIv S 0 (((hi - lo : Nat) : Int))).1)

theorem shiftedExpMarginCellOkB_sound {B n lo hi outW m : Nat}
    {pn qd y S : List Int}
    (h : shiftedExpMarginCellOkB B n pn qd y lo hi outW S = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    0 ≤ expMarginVal n (evalPoly pn (m : Int)) (evalPoly qd (m : Int))
      (evalPoly y (m : Int)) (outW : Int) := by
  unfold shiftedExpMarginCellOkB at h
  let pS := polyShift pn (lo : Int)
  let qS := polyShift qd (lo : Int)
  let yS := polyShift y (lo : Int)
  let K := ((2 ^ B : Nat) : Int)
  rw [Bool.and_eq_true] at h
  rcases h with ⟨hlohiB, h⟩
  rw [Bool.and_eq_true] at h
  rcases h with ⟨h, hIvB⟩
  rw [Bool.and_eq_true] at h
  rcases h with ⟨h, hEvalB⟩
  rw [Bool.and_eq_true] at h
  rcases h with ⟨hSB, hBoundB⟩
  have hlohi : lo ≤ hi := of_decide_eq_true hlohiB
  have hS : polyL1 S * 2 < 2 ^ B := of_decide_eq_true hSB
  have hBound :
      expMarginL1Bound n (polyL1 pS) (polyL1 qS) (polyL1 yS) outW * 2 < 2 ^ B :=
    of_decide_eq_true hBoundB
  have hEval : evalPoly S K =
      expMarginVal n (evalPoly pS K) (evalPoly qS K) (evalPoly yS K) (outW : Int) :=
    of_decide_eq_true hEvalB
  have hIv : 0 ≤ (hornerIv S 0 (((hi - lo : Nat) : Int))).1 :=
    of_decide_eq_true hIvB
  let d : Int := (m : Int) - (lo : Int)
  have hd0 : 0 ≤ d := by
    simp [d]
    omega
  have hdhi : d ≤ ((hi - lo : Nat) : Int) := by
    simp [d]
    omega
  have hshiftBound :
      polyL1 (expMarginPolyFast n pS qS yS outW) * 2 < 2 ^ B := by
    have hle := polyL1_expMarginPolyFast pS qS yS outW n
    omega
  have hEvalPoly :
      evalPoly S ((2 : Int) ^ B) =
        evalPoly (expMarginPolyFast n pS qS yS outW) ((2 : Int) ^ B) := by
    rw [int_two_pow, ← show K = ((2 ^ B : Nat) : Int) by rfl]
    rw [evalPoly_expMarginPolyFast, ← expMarginVal_eq]
    exact hEval
  have hext := evalPoly_ext (B := B) S (expMarginPolyFast n pS qS yS outW)
    hS hshiftBound hEvalPoly
  have hhorner := (hornerIv_sound S (lo := 0) (hi := ((hi - lo : Nat) : Int))
    (x := d) (Int.le_refl 0) hd0 hdhi).1
  have hSnon : 0 ≤ evalPoly S d := by
    omega
  have hEq := hext d
  rw [hEq] at hSnon
  rw [evalPoly_expMarginPolyFast, ← expMarginVal_eq] at hSnon
  have hm_decomp : (lo : Int) + d = (m : Int) := by
    simp [d]
  have hp := polyShift_eval pn (lo : Int) d
  have hq := polyShift_eval qd (lo : Int) d
  have hy := polyShift_eval y (lo : Int) d
  rw [hm_decomp] at hp hq hy
  simpa [pS, qS, yS, hp, hq, hy] using hSnon

def ivAdd (a b : Int × Int) : Int × Int :=
  (a.1 + b.1, a.2 + b.2)

def ivScaleNat (k : Nat) (a : Int × Int) : Int × Int :=
  (((k : Nat) : Int) * a.1, ((k : Nat) : Int) * a.2)

def ivMulNonneg (a b : Int × Int) : Int × Int :=
  (a.1 * b.1, a.2 * b.2)

def ivMulNonnegLeft (q a : Int × Int) : Int × Int :=
  ((if 0 ≤ a.1 then q.1 * a.1 else q.2 * a.1),
    (if a.2 ≤ 0 then q.1 * a.2 else q.2 * a.2))

theorem ivAdd_sound {a b : Int × Int} {x y : Int}
    (ha : a.1 ≤ x ∧ x ≤ a.2) (hb : b.1 ≤ y ∧ y ≤ b.2) :
    (ivAdd a b).1 ≤ x + y ∧ x + y ≤ (ivAdd a b).2 := by
  unfold ivAdd
  omega

theorem ivScaleNat_sound {k : Nat} {a : Int × Int} {x : Int}
    (ha : a.1 ≤ x ∧ x ≤ a.2) :
    (ivScaleNat k a).1 ≤ (k : Int) * x ∧ (k : Int) * x ≤ (ivScaleNat k a).2 := by
  unfold ivScaleNat
  have hk : 0 ≤ (k : Int) := Int.natCast_nonneg _
  constructor
  · exact mul_le_mul_left_nonneg ha.1 hk
  · exact mul_le_mul_left_nonneg ha.2 hk

theorem ivMulNonneg_sound {a b : Int × Int} {x y : Int}
    (ha0 : 0 ≤ a.1) (hb0 : 0 ≤ b.1)
    (ha : a.1 ≤ x ∧ x ≤ a.2) (hb : b.1 ≤ y ∧ y ≤ b.2) :
    (ivMulNonneg a b).1 ≤ x * y ∧ x * y ≤ (ivMulNonneg a b).2 := by
  unfold ivMulNonneg
  have hx0 : 0 ≤ x := by omega
  have hy0 : 0 ≤ y := by omega
  constructor
  · calc
      a.1 * b.1 ≤ x * b.1 := mul_le_mul_right_nonneg ha.1 hb0
      _ ≤ x * y := mul_le_mul_left_nonneg hb.1 hx0
  · calc
      x * y ≤ a.2 * y := mul_le_mul_right_nonneg ha.2 hy0
      _ ≤ a.2 * b.2 := mul_le_mul_left_nonneg hb.2 (by omega : 0 ≤ a.2)

theorem ivMulNonnegLeft_sound {q a : Int × Int} {x y : Int}
    (hq0 : 0 ≤ q.1) (hq : q.1 ≤ x ∧ x ≤ q.2) (ha : a.1 ≤ y ∧ y ≤ a.2) :
    (ivMulNonnegLeft q a).1 ≤ x * y ∧ x * y ≤ (ivMulNonnegLeft q a).2 := by
  unfold ivMulNonnegLeft
  have hx0 : 0 ≤ x := by omega
  have hq20 : 0 ≤ q.2 := by omega
  constructor
  · by_cases ha10 : 0 ≤ a.1
    · rw [if_pos ha10]
      have hy0 : 0 ≤ y := by omega
      calc
        q.1 * a.1 ≤ x * a.1 := mul_le_mul_right_nonneg hq.1 ha10
        _ ≤ x * y := mul_le_mul_left_nonneg ha.1 hx0
    · rw [if_neg ha10]
      by_cases hypos : 0 ≤ y
      · have hle0 : q.2 * a.1 ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos hq20 (by omega)
        have hxy0 : 0 ≤ x * y := Int.mul_nonneg hx0 hypos
        omega
      · have hy_nonpos : y ≤ 0 := by omega
        calc
          q.2 * a.1 ≤ q.2 * y := mul_le_mul_left_nonneg ha.1 hq20
          _ ≤ x * y := by
            have h := mul_le_mul_left_nonpos hq.2 hy_nonpos
            simpa only [Int.mul_comm] using h
  · by_cases ha20 : a.2 ≤ 0
    · rw [if_pos ha20]
      have hy_nonpos : y ≤ 0 := by omega
      calc
        x * y ≤ q.1 * y := by
          have h := mul_le_mul_left_nonpos hq.1 hy_nonpos
          simpa only [Int.mul_comm] using h
        _ ≤ q.1 * a.2 := mul_le_mul_left_nonneg ha.2 hq0
    · rw [if_neg ha20]
      by_cases hy_nonpos : y ≤ 0
      · have hxy0 : x * y ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos hx0 hy_nonpos
        have h0hi : 0 ≤ q.2 * a.2 := Int.mul_nonneg hq20 (by omega)
        omega
      · have hy0 : 0 ≤ y := by omega
        calc
          x * y ≤ q.2 * y := mul_le_mul_right_nonneg hq.2 hy0
          _ ≤ q.2 * a.2 := mul_le_mul_left_nonneg ha.2 hq20

def expMarginIvState (p q y : Int × Int) (w : Nat) : Nat → (Int × Int) × (Int × Int)
  | 0 => (((w : Int) - y.2, (w : Int) - y.1), (1, 1))
  | n + 1 =>
      let st := expMarginIvState p q y w n
      let pp := ivMulNonneg p st.2
      (ivAdd (ivScaleNat (n + 1) (ivMulNonnegLeft q st.1))
        (ivScaleNat w pp), pp)

def expMarginIvLower (n : Nat) (p q y : Int × Int) (w : Nat) : Int :=
  (expMarginIvState p q y w n).1.1

theorem expMarginIvState_sound {p q y : Int × Int} {P Q Y : Int} {w n : Nat}
    (hp0 : 0 ≤ p.1) (hq0 : 0 ≤ q.1)
    (hp : p.1 ≤ P ∧ P ≤ p.2)
    (hq : q.1 ≤ Q ∧ Q ≤ q.2)
    (hy : y.1 ≤ Y ∧ Y ≤ y.2) :
    0 ≤ (expMarginIvState p q y w n).2.1 ∧
      ((expMarginIvState p q y w n).1.1 ≤
          expMarginVal n P Q Y (w : Int) ∧
        expMarginVal n P Q Y (w : Int) ≤
          (expMarginIvState p q y w n).1.2) ∧
      ((expMarginIvState p q y w n).2.1 ≤ P ^ n ∧
        P ^ n ≤ (expMarginIvState p q y w n).2.2) := by
  induction n with
  | zero =>
      simp [expMarginIvState, expMarginVal, expMarginValState]
      omega
  | succ n ih =>
      simp only [expMarginIvState]
      let st := expMarginIvState p q y w n
      have hst := ih
      have hpp := ivMulNonneg_sound hp0 hst.1 hp hst.2.2
      have hpp0 : 0 ≤ (ivMulNonneg p st.2).1 := by
        unfold ivMulNonneg
        exact Int.mul_nonneg hp0 hst.1
      have hqm := ivMulNonnegLeft_sound hq0 hq hst.2.1
      have hterm1 := ivScaleNat_sound (k := n + 1) hqm
      have hterm2 := ivScaleNat_sound (k := w) hpp
      have hsum := ivAdd_sound hterm1 hterm2
      constructor
      · exact hpp0
      constructor
      · simpa [expMarginVal, expMarginValState, expMarginValState_pow, Int.mul_assoc] using hsum
      · rw [Int.pow_succ]
        simpa only [Int.mul_comm, Int.mul_left_comm] using hpp

theorem expMarginIvLower_sound {n p q y w : Nat} {pIv qIv yIv : Int × Int}
    (hp0 : 0 ≤ pIv.1) (hq0 : 0 ≤ qIv.1)
    (hp : pIv.1 ≤ (p : Int) ∧ (p : Int) ≤ pIv.2)
    (hq : qIv.1 ≤ (q : Int) ∧ (q : Int) ≤ qIv.2)
    (hy : yIv.1 ≤ (y : Int) ∧ (y : Int) ≤ yIv.2)
    (hlo : 0 ≤ expMarginIvLower n pIv qIv yIv w) :
    sumGE n p q y w := by
  have h := expMarginIvState_sound (p := pIv) (q := qIv) (y := yIv)
    (P := (p : Int)) (Q := (q : Int)) (Y := (y : Int)) (w := w) (n := n)
    hp0 hq0 hp hq hy
  exact sumGE_of_expMarginVal (n := n) (p := p) (q := q) (y := y) (w := w)
    (Int.le_trans hlo h.2.1.1)


theorem ge_phase_lower_algebra {tn td x k c e : Int}
    (hk : 0 ≤ k) (hbr : tn * 2 ^ 99 ≤ x * td) :
    (2 ^ 99 * k) * tn + (c + e) * td ≤
      (x * k + c + e) * td := by
  have hs := mul_le_mul_right_nonneg hbr hk
  have hs' : (2 ^ 99 * k) * tn ≤ (x * k) * td := by
    calc
      (2 ^ 99 * k) * tn = (tn * 2 ^ 99) * k := by
        simp only [Int.mul_comm, Int.mul_left_comm]
      _ ≤ (x * td) * k := hs
      _ = (x * k) * td := by
        simp only [Int.mul_comm, Int.mul_left_comm]
  have hadd := Int.add_le_add_right hs' ((c + e) * td)
  rw [← Int.add_mul] at hadd
  simpa only [Int.add_assoc] using hadd

theorem sumGE_mono_N {n m p q y w : Nat} (hq : 0 < q) (hnm : n ≤ m)
    (h : sumGE n p q y w) : sumGE m p q y w := by
  unfold sumGE at h ⊢
  let Dn := fact n * q ^ n
  let Dm := fact m * q ^ m
  have hDn : 0 < Dn := Nat.mul_pos (fact_pos n) (Nat.pow_pos hq)
  have hmono := expNum_mono_N (p := p) (q := q) hnm
  change expNum n p q * Dm ≤ expNum m p q * Dn at hmono
  refine Nat.le_of_mul_le_mul_right ?_ hDn
  calc
    y * Dm * Dn = (y * Dn) * Dm := by
      rw [Nat.mul_assoc, Nat.mul_comm Dm Dn, ← Nat.mul_assoc]
    _ ≤ (expNum n p q * w) * Dm := Nat.mul_le_mul_right _ h
    _ = (expNum n p q * Dm) * w := by
      rw [Nat.mul_assoc, Nat.mul_comm w Dm, ← Nat.mul_assoc]
    _ ≤ (expNum m p q * Dn) * w := Nat.mul_le_mul_right _ hmono
    _ = expNum m p q * w * Dn := by
      rw [Nat.mul_assoc, Nat.mul_comm Dn w, ← Nat.mul_assoc]

theorem pos_shift_direct_exact_of_sumGE {x n : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hclt : evmClz x < 160)
    (hleaf : sumGE n
      (lnErrArg (int256 (lnTail (evmSub 160 (evmClz x)) (mant x)))) lnErrQ
      (posTopX (evmClz x) (mant x)) (10 ^ 18)) :
    capLB (lnErrArg (int256 (lnWadToRayBody x))) lnErrQ x (10 ^ 18) := by
  have hx256 : x < 2 ^ 256 := by omega
  have hbody :
      lnWadToRayBody x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
    rw [lnWadToRayBody_eq_tail hx256]
    rfl
  have htop : x ≤ posTopX (evmClz x) (mant x) := by
    have hw := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
    have hpos : 0 < (mant x + 1) * 2 ^ (160 - evmClz x) :=
      Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by decide))
    unfold posTopX
    omega
  refine capLB_exact_of_sumGE_mono (n := n) (p0 :=
      lnErrArg (int256 (lnTail (evmSub 160 (evmClz x)) (mant x))))
      (p := lnErrArg (int256 (lnWadToRayBody x)))
      (y0 := posTopX (evmClz x) (mant x)) (y := x) ?_ htop hleaf
  rw [hbody]

theorem lnErrArg_mono {r0 r : Int} (hle : r0 ≤ r) : lnErrArg r0 ≤ lnErrArg r := by
  unfold lnErrArg lnErrorBoundDen lnErrorBoundNum
  exact Nat.mul_le_mul_right (2 ^ 99)
    (Int.toNat_le_toNat (by omega :
      r0 * (1000000000 : Int) + (1698600000 : Int) ≤
        r * (1000000000 : Int) + (1698600000 : Int)))

theorem capLB_exact_of_body_interval_sumGE {n x lo hi : Nat}
    (hlo : 1 ≤ lo) (hxlo : lo ≤ x) (hxhi : x ≤ hi) (hhi : hi < 2 ^ 255)
    (h : sumGE n (lnErrArg (int256 (lnWadToRayBody lo))) lnErrQ hi (10 ^ 18)) :
    capLB (lnErrArg (int256 (lnWadToRayBody x))) lnErrQ x (10 ^ 18) := by
  have hmono := lnWadToRayBody_mono (x := lo) (y := x) (by omega) hxlo (by omega)
  have hrle : int256 (lnWadToRayBody lo) ≤ int256 (lnWadToRayBody x) :=
    toInt_of_sle (lnWadToRayBody_lt (by omega : lo < 2 ^ 256))
      (lnWadToRayBody_lt (by omega : x < 2 ^ 256)) hmono
  exact capLB_exact_of_sumGE_mono (p0 := lnErrArg (int256 (lnWadToRayBody lo)))
    (y0 := hi) (lnErrArg_mono hrle) hxhi h

end LnFloorCert
