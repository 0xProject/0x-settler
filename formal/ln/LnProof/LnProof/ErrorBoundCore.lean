import LnProof.ExpLogCutSpec
import LnProof.ErrorBoundCert

set_option maxRecDepth 100000

/-!
# Public cut statement for the `lnWadToRay` error bound

This module exposes the requested named rational bound and packages it with
the existing real-free cut-log interface.  The lower side is the established
floor cut.  The upper side is a rational strict upper cut over denominator
`QS * den`.
-/

namespace LnFloorCert

open LnGeneratedModel LnFloor LnExp LnPoly

attribute [local irreducible] model_ln_wad_evm

theorem capLB_lift_right {p q y w den : Nat} (hq : 0 < q)
    (h : capLB p q y w) : capLB (p * den) (q * den) y w := by
  refine capLB_arg (q' := q) hq ?_ h
  rw [← Nat.mul_assoc, Nat.mul_right_comm p den q]
  exact Nat.le_refl _

theorem capUB_lift_right {p q y w den : Nat} (hq : 0 < q)
    (h : capUB p q y w) : capUB (p * den) (q * den) y w := by
  refine capUB_arg (q' := q) hq ?_ h
  rw [Nat.mul_right_comm p den q]
  rw [Nat.mul_assoc]
  exact Nat.le_refl _

/-- Internal strict-margin version inherited from the floor proof.  Its
`10^31 - 10` denominator is much stronger than the exact rational cut below
and is reused only where the existing branch proofs already establish it. -/
def CutLogWadRayLtRationalStrict (x : Nat) (r : Int) (num den : Nat) : Prop :=
  if 1 ≤ r * (den : Int) + (num : Int) then
    CutRatioLeExp (x * 10 ^ 31) (10 ^ 18 * (10 ^ 31 - 10))
      ((r * (den : Int) + (num : Int)).toNat * 2 ^ 99) (QS * den)
  else
    CutExpLe ((-(r * (den : Int) + (num : Int))).toNat * 2 ^ 99) (QS * den)
      (10 ^ 18 * (10 ^ 31 - 10)) (x * 10 ^ 31)

/-- Rational upper-cut predicate for wad-input, ray-output logarithms.

`CutLogWadRayLtRational x r num den` is the real-free counterpart of
`10^27 * log(x / 10^18) < r + num / den`.  The positive-exponent branch proves
a lower exponential cut for `(r * den + num) / den`; the reciprocal branch
proves the corresponding upper exponential cut for the negated exponent. -/
def CutLogWadRayLtRational (x : Nat) (r : Int) (num den : Nat) : Prop :=
  if 1 ≤ r * (den : Int) + (num : Int) then
    CutRatioLeExp x (10 ^ 18)
      ((r * (den : Int) + (num : Int)).toNat * 2 ^ 99) (QS * den)
  else
    CutExpLe ((-(r * (den : Int) + (num : Int))).toNat * 2 ^ 99) (QS * den)
      (10 ^ 18) x

def lnErrQ : Nat := QS * lnErrorBoundDen
def lnErrArg (r : Int) : Nat :=
  (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat * 2 ^ 99
def lnErrNegArg (r : Int) : Nat :=
  (-(r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int))).toNat * 2 ^ 99
def wadRayNum (x : Nat) : Nat := x * 10 ^ 31
def wadRayStrictDen : Nat := 10 ^ 18 * (10 ^ 31 - 10)
def posTopX (c m : Nat) : Nat := (m + 1) * 2 ^ (160 - c) - 1
def twoPow27N : Nat := 2 ^ 27
def twoPow72N : Nat := 2 ^ 72
def twoPow99N : Nat := 2 ^ 99
def twoPow27I : Int := 2 ^ 27
def twoPow72I : Int := 2 ^ 72
def twoPow99I : Int := 2 ^ 99
def lnPhaseScaleN : Nat := 1000000000000000000000000000
def lnPhaseScaleI : Int := 1000000000000000000000000000
def lnBiasI : Int := 116873961749927929127912020551516284764321243411868

/-- First-order exact-wad budget with the common `10^18` and `2^99` factors
cancelled out. -/
theorem wad_exact_upper_budget :
    10 ^ 31 * (10 ^ 27 * lnErrorBoundDen) ≤
      (10 ^ 27 * lnErrorBoundDen + lnErrorBoundNum) * (10 ^ 31 - 10) := by
  unfold lnErrorBoundDen lnErrorBoundNum
  decide +kernel

theorem capLB_strict_to_exact {p q x : Nat}
    (h : capLB p q (wadRayNum x) wadRayStrictDen) : capLB p q x (10 ^ 18) := by
  refine capLB_weaken (p := p) (q := q) (y := wadRayNum x) (w := wadRayStrictDen)
    (y' := x) (w' := 10 ^ 18) (by unfold wadRayStrictDen; decide) h ?_
  unfold wadRayNum wadRayStrictDen
  have hden : 10 ^ 18 * (10 ^ 31 - 10) ≤ 10 ^ 18 * 10 ^ 31 := by
    exact Nat.mul_le_mul_left _ (by decide : (10 ^ 31 - 10 : Nat) ≤ 10 ^ 31)
  calc
    x * (10 ^ 18 * (10 ^ 31 - 10)) ≤ x * (10 ^ 18 * 10 ^ 31) :=
      Nat.mul_le_mul_left _ hden
    _ = x * 10 ^ 31 * 10 ^ 18 := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]

theorem capUB_strict_to_exact {p q x : Nat} (hx : 0 < x)
    (h : capUB p q wadRayStrictDen (wadRayNum x)) : capUB p q (10 ^ 18) x := by
  refine capUB_weaken (p := p) (q := q) (y := wadRayStrictDen) (w := wadRayNum x)
    (y' := 10 ^ 18) (w' := x) ?_ h ?_
  · unfold wadRayNum
    exact Nat.mul_pos hx (by decide)
  · unfold wadRayNum wadRayStrictDen
    have hden : 10 ^ 31 - 10 ≤ (10 ^ 31 : Nat) := by decide
    calc
      (10 ^ 18 * (10 ^ 31 - 10)) * x ≤ (10 ^ 18 * 10 ^ 31) * x :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hden)
      _ = 10 ^ 18 * (x * 10 ^ 31) := by
        simp only [Nat.mul_comm, Nat.mul_left_comm]

theorem CutLogWadRayLtRational_of_strict {x : Nat} {r : Int} {num den : Nat}
    (hx : 0 < x) :
    CutLogWadRayLtRationalStrict x r num den →
      CutLogWadRayLtRational x r num den := by
  intro h
  unfold CutLogWadRayLtRationalStrict at h
  unfold CutLogWadRayLtRational
  by_cases hpos : 1 ≤ r * (den : Int) + (num : Int)
  · rw [if_pos hpos] at h ⊢
    exact capLB_strict_to_exact h
  · rw [if_neg hpos] at h ⊢
    exact capUB_strict_to_exact hx h

theorem capLB_exact_of_sumGE_mono {n p0 p y0 y : Nat}
    (hp : p0 ≤ p) (hy : y ≤ y0)
    (h : sumGE n p0 lnErrQ y0 (10 ^ 18)) :
    capLB p lnErrQ y (10 ^ 18) := by
  have hq : 0 < lnErrQ := by
    unfold lnErrQ QS lnErrorBoundDen
    decide
  have cap0 : capLB p0 lnErrQ y0 (10 ^ 18) := ⟨n, h⟩
  have capP : capLB p lnErrQ y0 (10 ^ 18) := by
    refine capLB_arg (p := p) (q := lnErrQ) (p' := p0) (q' := lnErrQ)
      hq ?_ cap0
    exact Nat.mul_le_mul_right _ hp
  refine capLB_weaken (p := p) (q := lnErrQ) (y := y0) (w := 10 ^ 18)
    (y' := y) (w' := 10 ^ 18) (by decide) capP ?_
  exact Nat.mul_le_mul_right _ hy

theorem sumGE_exact_mono {n p0 p y0 y : Nat}
    (hp : p0 ≤ p) (hy : y ≤ y0)
    (h : sumGE n p0 lnErrQ y0 (10 ^ 18)) :
    sumGE n p lnErrQ y (10 ^ 18) := by
  unfold sumGE at h ⊢
  have hleft : y * (fact n * lnErrQ ^ n) ≤ y0 * (fact n * lnErrQ ^ n) :=
    Nat.mul_le_mul_right _ hy
  have harg : expNum n p0 lnErrQ * lnErrQ ^ n ≤ expNum n p lnErrQ * lnErrQ ^ n := by
    simpa using expNum_arg_mono
      (p := p0) (q := lnErrQ) (p' := p) (q' := lnErrQ)
      (Nat.mul_le_mul_right lnErrQ hp) n
  have hqpow : 0 < lnErrQ ^ n := Nat.pow_pos (by unfold lnErrQ QS lnErrorBoundDen; decide)
  have hexp : expNum n p0 lnErrQ ≤ expNum n p lnErrQ :=
    Nat.le_of_mul_le_mul_right harg hqpow
  exact Nat.le_trans hleft (Nat.le_trans h (Nat.mul_le_mul_right _ hexp))

theorem sumGE_arg_mono {n p q p' q' y w : Nat}
    (hq' : 0 < q') (harg : p' * q ≤ p * q')
    (h : sumGE n p' q' y w) :
    sumGE n p q y w := by
  unfold sumGE at h ⊢
  have hmono := expNum_arg_mono harg n
  have hqpow : 0 < q' ^ n := Nat.pow_pos hq'
  refine Nat.le_of_mul_le_mul_right ?_ hqpow
  calc
    (y * (fact n * q ^ n)) * q' ^ n =
        (y * (fact n * q' ^ n)) * q ^ n := by
          simp only [Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (expNum n p' q' * w) * q ^ n :=
        Nat.mul_le_mul_right _ h
    _ = (expNum n p' q' * q ^ n) * w := by
        simp only [Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (expNum n p q * q' ^ n) * w :=
        Nat.mul_le_mul_right _ hmono
    _ = (expNum n p q * w) * q' ^ n := by
        simp only [Nat.mul_comm, Nat.mul_left_comm]

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
    omega
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
      (lnErrArg (toInt (lnTail (evmSub 160 (evmClz x)) (mant x)))) lnErrQ
      (posTopX (evmClz x) (mant x)) (10 ^ 18)) :
    capLB (lnErrArg (toInt (model_ln_wad_evm x))) lnErrQ x (10 ^ 18) := by
  have hx256 : x < 2 ^ 256 := by omega
  have hmodel :
      model_ln_wad_evm x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
    rw [model_eq_tail hx256]
    rfl
  have htop : x ≤ posTopX (evmClz x) (mant x) := by
    have hw := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
    have hpos : 0 < (mant x + 1) * 2 ^ (160 - evmClz x) :=
      Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by decide))
    unfold posTopX
    omega
  refine capLB_exact_of_sumGE_mono (n := n) (p0 :=
      lnErrArg (toInt (lnTail (evmSub 160 (evmClz x)) (mant x))))
      (p := lnErrArg (toInt (model_ln_wad_evm x)))
      (y0 := posTopX (evmClz x) (mant x)) (y := x) ?_ htop hleaf
  rw [hmodel]
  exact Nat.le_refl _

theorem lnErrArg_mono {r0 r : Int} (hle : r0 ≤ r) : lnErrArg r0 ≤ lnErrArg r := by
  unfold lnErrArg lnErrorBoundDen lnErrorBoundNum
  exact Nat.mul_le_mul_right (2 ^ 99)
    (Int.toNat_le_toNat (by omega :
      r0 * (1000000000 : Int) + (1698600000 : Int) ≤
        r * (1000000000 : Int) + (1698600000 : Int)))

theorem capLB_exact_of_model_interval_sumGE {n x lo hi : Nat}
    (hlo : 1 ≤ lo) (hxlo : lo ≤ x) (hxhi : x ≤ hi) (hhi : hi < 2 ^ 255)
    (h : sumGE n (lnErrArg (toInt (model_ln_wad_evm lo))) lnErrQ hi (10 ^ 18)) :
    capLB (lnErrArg (toInt (model_ln_wad_evm x))) lnErrQ x (10 ^ 18) := by
  have hmono := model_ln_wad_mono (x := lo) (y := x) (by omega) hxlo (by omega)
  have hrle : toInt (model_ln_wad_evm lo) ≤ toInt (model_ln_wad_evm x) :=
    toInt_of_sle (model_lt (by omega : lo < 2 ^ 256))
      (model_lt (by omega : x < 2 ^ 256)) hmono
  exact capLB_exact_of_sumGE_mono (p0 := lnErrArg (toInt (model_ln_wad_evm lo)))
    (y0 := hi) (lnErrArg_mono hrle) hxhi h

/-- The exact wad input has `r = 0`, and the published fractional bound is
large enough to clear the strictness denominator directly. -/
theorem cutLogWadRayLtRational_at_wad :
    CutLogWadRayLtRational (10 ^ 18) 0 lnErrorBoundNum lnErrorBoundDen := by
  apply CutLogWadRayLtRational_of_strict (by decide)
  unfold CutLogWadRayLtRationalStrict
  rw [if_pos]
  · change capLB (lnErrorBoundNum * 2 ^ 99) (QS * lnErrorBoundDen)
      (10 ^ 18 * 10 ^ 31) (10 ^ 18 * (10 ^ 31 - 10))
    refine ⟨1, ?_⟩
    simp only [fact, expNum, Nat.pow_one, Nat.mul_one]
    have h := Nat.mul_le_mul_right (2 ^ 99)
      (Nat.mul_le_mul_left (10 ^ 18) wad_exact_upper_budget)
    simpa [QS, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.left_distrib,
      Nat.right_distrib] using h
  · unfold lnErrorBoundNum lnErrorBoundDen
    decide

theorem cutLogWadRayLtRational_at_neg_one {x : Nat}
    (hx : x < 10 ^ 18) :
    CutLogWadRayLtRational x (-1) lnErrorBoundNum lnErrorBoundDen := by
  unfold CutLogWadRayLtRational
  rw [if_pos]
  · change capLB (((-1 : Int) * (lnErrorBoundDen : Int) +
        (lnErrorBoundNum : Int)).toNat * 2 ^ 99) (QS * lnErrorBoundDen)
      x (10 ^ 18)
    have hq : 0 < QS * lnErrorBoundDen := by
      unfold QS lnErrorBoundDen
      decide
    have cap0 : capLB 0 (QS * lnErrorBoundDen) 1 1 := capLB_one (QS * lnErrorBoundDen)
    have capA : capLB (((-1 : Int) * (lnErrorBoundDen : Int) +
        (lnErrorBoundNum : Int)).toNat * 2 ^ 99) (QS * lnErrorBoundDen) 1 1 := by
      refine capLB_arg hq ?_ cap0
      simp only [Nat.zero_mul, Nat.zero_le]
    refine capLB_weaken (p := (((-1 : Int) * (lnErrorBoundDen : Int) +
        (lnErrorBoundNum : Int)).toNat * 2 ^ 99)) (q := QS * lnErrorBoundDen)
        (y := 1) (w := 1) ?_ capA ?_
    · decide
    · simpa [Nat.mul_one, Nat.one_mul] using (by omega : x ≤ 10 ^ 18)
  · unfold lnErrorBoundNum lnErrorBoundDen
    decide

theorem c160_arg_le_int {A r : Int}
    (h : A ≤ (r + 1) * twoPow99I - twoPow27I) :
    A * 1000000000 + 698600000 * twoPow99I ≤
      (r * 1000000000 + 1698600000) * twoPow99I := by
  have hm : A * (1000000000 : Int) ≤
      ((r + 1) * twoPow99I - twoPow27I) * (1000000000 : Int) :=
    Int.mul_le_mul_of_nonneg_right h (by decide)
  have hle := Int.add_le_add_right hm (698600000 * twoPow99I)
  have e : ((r + 1) * twoPow99I - twoPow27I) *
        (1000000000 : Int) + 698600000 * twoPow99I =
      (r * 1000000000 + 1698600000) * twoPow99I -
        twoPow27I * (1000000000 : Int) := by
    simp only [Int.sub_mul, Int.add_mul, Int.one_mul]
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hslack : 0 ≤ twoPow27I * (1000000000 : Int) :=
    Int.mul_nonneg (by unfold twoPow27I; decide) (by decide)
  calc
    A * 1000000000 + 698600000 * twoPow99I
        ≤ ((r + 1) * twoPow99I - twoPow27I) *
            1000000000 + 698600000 * twoPow99I := hle
    _ = (r * 1000000000 + 1698600000) * twoPow99I -
        twoPow27I * (1000000000 : Int) := e
    _ ≤ (r * 1000000000 + 1698600000) * twoPow99I :=
        Int.sub_le_self _ hslack

theorem c160_arg_le {a b : Nat} {r : Int}
    (h : (a : Int) + (b : Int) ≤ (r + 1) * twoPow99I - twoPow27I)
    (harg : 0 ≤ r * (1000000000 : Int) + 1698600000) :
    (a + b) * 1000000000 + 698600000 * twoPow99N ≤
      (r * (1000000000 : Int) + 1698600000).toNat * twoPow99N := by
  have hcast : (((r * (1000000000 : Int) + 1698600000).toNat : Nat) : Int) =
      r * (1000000000 : Int) + 1698600000 :=
    Int.toNat_of_nonneg harg
  have hsum : ((a + b : Nat) : Int) ≤
      (r + 1) * twoPow99I - twoPow27I := by
    simpa only [Int.natCast_add] using h
  apply Int.ofNat_le.mp
  simp only [Int.natCast_add, Int.natCast_mul, hcast]
  simpa [twoPow99I, twoPow99N] using c160_arg_le_int hsum

theorem c160_phase_arg_le {X r : Int} (hX : 0 ≤ X)
    (hsc : (X * 7450580596923828125 + ln2kInt 160 + lnBiasI) * twoPow27I ≤
        ((r + 1) * twoPow72I - 1) * twoPow27I)
    (harg_nonneg : 0 ≤ r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) :
    (X.toNat * lnPhaseScaleN + BIASc * twoPow27N) *
        lnErrorBoundDen + lnErrorExtraNum * twoPow99N ≤
      (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat * twoPow99N := by
  have hVs0 : (X * 7450580596923828125 + ln2kInt 160 + lnBiasI) * twoPow27I =
      X * lnPhaseScaleI + lnBiasI * twoPow27I := by
    have hVs := v_scale_pos X 160 (by decide)
    simpa only [Nat.sub_self, Nat.zero_mul, Int.natCast_zero, Int.zero_mul,
      Int.add_zero, twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
  rw [hVs0] at hsc
  have hXn : ((X.toNat : Nat) : Int) = X := Int.toNat_of_nonneg hX
  have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
    unfold twoPow27N twoPow27I lnBiasI
    decide +kernel
  rw [← hBc] at hsc
  have er : ((r + 1) * twoPow72I - 1) * twoPow27I =
      (r + 1) * 2 ^ 99 - 2 ^ 27 := by
    unfold twoPow72I twoPow27I
    rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
      by decide]
    omega
  rw [er] at hsc
  have hscNat :
      (((X.toNat * lnPhaseScaleN : Nat) : Int) +
        ((BIASc * twoPow27N : Nat) : Int)) ≤ (r + 1) * twoPow99I - twoPow27I := by
    have hScale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := by
      unfold lnPhaseScaleN lnPhaseScaleI
      rfl
    rw [Int.natCast_mul, hXn]
    rw [hScale]
    unfold twoPow99I twoPow27I
    exact hsc
  have hcore := c160_arg_le
    (a := X.toNat * lnPhaseScaleN)
    (b := BIASc * twoPow27N) (r := r) hscNat
    (by simpa [lnErrorBoundDen, lnErrorBoundNum] using harg_nonneg)
  simpa [lnErrorBoundDen, lnErrorBoundNum, lnErrorExtraNum, lnPhaseScaleN,
    twoPow27N, twoPow99N] using hcore

theorem phase_lt_scaled_le {V T : Int} (h : V < T) :
    V * 2 ^ 27 ≤ (T - 1) * 2 ^ 27 := by
  omega

def posPhaseI (m c : Nat) : Int :=
  toInt (x1W (zWord m)) * lnPhaseScaleI +
    ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
      lnBiasI * twoPow27I

def posAccI (m c : Nat) : Int :=
  toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c + lnBiasI

def posResidueGap (m c : Nat) (r : Int) : Int :=
  (r + 1) * twoPow72I - posAccI m c

def posResidueGapThreshold : Int := 86144214621787901969

def firstCongruentGE (q r lo : Nat) : Nat :=
  if lo ≤ r then
    r
  else
    r + ((lo - r + q - 1) / q) * q

theorem firstCongruentGE_le_of_mod {q r lo h : Nat}
    (hq : 0 < q) (hmod : h % q = r) (hlo : lo ≤ h) :
    firstCongruentGE q r lo ≤ h := by
  unfold firstCongruentGE
  let k := h / q
  have hdecomp : h = k * q + r := by
    have hdm := Nat.div_add_mod h q
    rw [hmod] at hdm
    simpa [k, Nat.add_comm, Nat.mul_comm] using hdm.symm
  by_cases hlr : lo ≤ r
  · simp [hlr]
    rw [hdecomp]
    omega
  · simp [hlr]
    have hlo' : lo ≤ k * q + r := by
      rw [← hdecomp]
      exact hlo
    have hsub : lo - r ≤ k * q := by omega
    have hceil : (lo - r + q - 1) / q ≤ k := by
      rw [Nat.div_le_iff_le_mul_add_pred hq]
      calc
        lo - r + q - 1 = (lo - r) + (q - 1) := by omega
        _ ≤ k * q + (q - 1) := Nat.add_le_add_right hsub _
        _ = q * k + (q - 1) := by rw [Nat.mul_comm]
    have hmul : ((lo - r + q - 1) / q) * q ≤ k * q :=
      Nat.mul_le_mul_right q hceil
    rw [hdecomp]
    omega

theorem no_congruent_of_first_gt {q r lo hi h : Nat}
    (hq : 0 < q) (hfirst : hi < firstCongruentGE q r lo)
    (hlo : lo ≤ h) (hhi : h ≤ hi) :
    h % q ≠ r := by
  intro hmod
  have hle := firstCongruentGE_le_of_mod hq hmod hlo
  omega

theorem bucket_index_eq_of_mod_bracket {r : Int} {d rem q : Nat}
    (hq : 0 < q) (hrem : rem < q)
    (hlo : r * (q : Int) ≤ (d : Int) * (q : Int) + (rem : Int))
    (hhi : (d : Int) * (q : Int) + (rem : Int) < (r + 1) * (q : Int)) :
    r = (d : Int) := by
  have hq_nonneg : (0 : Int) ≤ (q : Int) := by omega
  have hd_le_r : (d : Int) ≤ r := by
    by_cases hle : (d : Int) ≤ r
    · exact hle
    · have hsucc : r + 1 ≤ (d : Int) := by omega
      have hmul : (r + 1) * (q : Int) ≤ (d : Int) * (q : Int) :=
        Int.mul_le_mul_of_nonneg_right hsucc hq_nonneg
      omega
  have hr_le_d : r ≤ (d : Int) := by
    by_cases hle : r ≤ (d : Int)
    · exact hle
    · have hsucc : (d : Int) + 1 ≤ r := by omega
      have hmul : ((d : Int) + 1) * (q : Int) ≤ r * (q : Int) :=
        Int.mul_le_mul_of_nonneg_right hsucc hq_nonneg
      rw [Int.add_mul, Int.one_mul] at hmul
      omega
  omega

theorem posAccI_nonneg {m c : Nat}
    (hmlo : MLO ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    0 ≤ posAccI m c := by
  have hb := (LnGeneratedModel.r1_bound hmlo hmhi).1
  have hx1 :
      -(240000000000000000000000000000 : Int) * 7450580596923828125 ≤
        toInt (x1W (zWord m)) * 7450580596923828125 :=
    Int.mul_le_mul_of_nonneg_right hb (by decide)
  have hln2 : (LN2c : Int) ≤ ln2kInt c := by
    unfold ln2kInt
    rw [if_pos (by omega : c ≤ 160)]
    have hk : (1 : Int) ≤ ((160 - c : Nat) : Int) := by
      omega
    have hmul := Int.mul_le_mul_of_nonneg_left hk
      (by change (0 : Int) ≤ 3273295013171879848905889459134067659407864468560; decide)
    simpa [Int.mul_one] using hmul
  have hfloor :
      0 ≤
        (-(240000000000000000000000000000 : Int)) *
          7450580596923828125 + (LN2c : Int) + lnBiasI := by
    unfold LN2c lnBiasI
    decide
  unfold posAccI
  omega

theorem lnTail_floor_bracket_pos {m c : Nat}
    (hmlo : MLO ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    let r := toInt (lnTail (evmSub 160 c) m)
    r * twoPow72I ≤ posAccI m c ∧ posAccI m c < (r + 1) * twoPow72I := by
  have hc256 : c < 256 := by omega
  have hacc := r4_value hmlo hmhi hc256
  let s := evmSar 72
    (evmAdd (evmAdd (evmMul (x1W (zWord m)) Kc) (evmMul LN2c (evmSub 160 c))) BIASc)
  have hs := evmSar_sandwich_72 (evmAdd_lt
    (evmAdd (evmMul (x1W (zWord m)) Kc) (evmMul LN2c (evmSub 160 c))) BIASc)
  have hslt : s < 2 ^ 256 := by
    unfold s
    exact hs.1
  have hnon := posAccI_nonneg hmlo hmhi hc
  have hcorr : toInt (lnTail (evmSub 160 c) m) = toInt s := by
    unfold lnTail
    change toInt (evmAdd (evmIszero (evmNot s)) s) = toInt s
    rw [corr_toInt hslt]
    rw [if_neg]
    intro hsneg
    have hhi := hs.2.2
    rw [hacc] at hhi
    change posAccI m c < toInt s * 4722366482869645213696 +
      4722366482869645213696 at hhi
    rw [hsneg] at hhi
    omega
  rw [hcorr]
  have hlo := hs.2.1
  have hhi := hs.2.2
  rw [hacc] at hlo hhi
  change toInt s * 4722366482869645213696 ≤ posAccI m c at hlo
  change posAccI m c < toInt s * 4722366482869645213696 +
    4722366482869645213696 at hhi
  have hpow : twoPow72I = (4722366482869645213696 : Int) := by
    unfold twoPow72I
    decide
  rw [hpow]
  have heq : (toInt s + 1) * (4722366482869645213696 : Int) =
      toInt s * 4722366482869645213696 + 4722366482869645213696 := by
    rw [Int.add_mul, Int.one_mul]
  change toInt s * (4722366482869645213696 : Int) ≤ posAccI m c ∧
    posAccI m c < (toInt s + 1) * (4722366482869645213696 : Int)
  rw [heq]
  exact ⟨hlo, hhi⟩

theorem lnTail_nonneg_pos {m c : Nat}
    (hmlo : MLO ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    0 ≤ toInt (lnTail (evmSub 160 c) m) := by
  have hbr := lnTail_floor_bracket_pos hmlo hmhi hc
  have hnon := posAccI_nonneg hmlo hmhi hc
  unfold twoPow72I at hbr
  omega

theorem posResidueGap_bounds {m c : Nat}
    (hmlo : MLO ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    let r := toInt (lnTail (evmSub 160 c) m)
    1 ≤ posResidueGap m c r ∧ posResidueGap m c r ≤ twoPow72I := by
  have hbr := lnTail_floor_bracket_pos hmlo hmhi hc
  unfold posResidueGap
  have hpow : twoPow72I = (4722366482869645213696 : Int) := by
    unfold twoPow72I
    decide
  rw [hpow] at hbr ⊢
  omega

theorem posResidueGap_eq_twoPow72_sub_mod {m c : Nat}
    (hmlo : MLO ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    let r := toInt (lnTail (evmSub 160 c) m)
    posResidueGap m c r =
      ((twoPow72N - (posAccI m c).toNat % twoPow72N : Nat) : Int) := by
  intro r
  let q : Nat := twoPow72N
  let A : Nat := (posAccI m c).toNat
  let d : Nat := A / q
  let rem : Nat := A % q
  change posResidueGap m c r = ((q - rem : Nat) : Int)
  have hq : 0 < q := by
    unfold q twoPow72N
    decide
  have hqI : ((q : Nat) : Int) = twoPow72I := by
    unfold q twoPow72N twoPow72I
    decide
  have hnon : 0 ≤ posAccI m c := posAccI_nonneg hmlo hmhi hc
  have hAcast : ((A : Nat) : Int) = posAccI m c := by
    unfold A
    exact Int.toNat_of_nonneg hnon
  have hdm := Nat.div_add_mod A q
  have hdm' : A / q * q + A % q = A := by
    simpa [Nat.mul_comm] using hdm
  have hAeq : (d : Int) * (q : Int) + (rem : Int) = posAccI m c := by
    unfold d rem
    rw [← Int.natCast_mul, ← Int.natCast_add, hdm', hAcast]
  have hrem_lt : rem < q := by
    unfold rem
    exact Nat.mod_lt A hq
  have hbr := lnTail_floor_bracket_pos (m := m) (c := c) hmlo hmhi hc
  change r * twoPow72I ≤ posAccI m c ∧
    posAccI m c < (r + 1) * twoPow72I at hbr
  have hlo : r * (q : Int) ≤ (d : Int) * (q : Int) + (rem : Int) := by
    rw [hAeq, hqI]
    exact hbr.1
  have hhi : (d : Int) * (q : Int) + (rem : Int) < (r + 1) * (q : Int) := by
    rw [hAeq, hqI]
    exact hbr.2
  have hr : r = (d : Int) :=
    bucket_index_eq_of_mod_bracket (r := r) (d := d) (rem := rem) (q := q)
      hq hrem_lt hlo hhi
  unfold posResidueGap
  rw [hr, ← hqI, ← hAeq]
  have hremle : rem ≤ q := Nat.le_of_lt hrem_lt
  have hsubcast : ((q - rem : Nat) : Int) = (q : Int) - (rem : Int) := by
    omega
  rw [hsubcast]
  rw [Int.add_mul, Int.one_mul]
  omega

theorem lnTail_eq_of_posAcc_window {lo m c : Nat}
    (hlo1 : MLO ≤ lo) (hlom : lo ≤ m) (hmhi : m < MHI) (hc : c < 160)
    (hdiff :
      posAccI m c - posAccI lo c +
          posResidueGap m c (toInt (lnTail (evmSub 160 c) m)) ≤ twoPow72I) :
    toInt (lnTail (evmSub 160 c) lo) =
      toInt (lnTail (evmSub 160 c) m) := by
  have hlohi : lo < MHI := by omega
  have hbrLo := lnTail_floor_bracket_pos hlo1 hlohi hc
  have hbrM := lnTail_floor_bracket_pos (by omega : MLO ≤ m) hmhi hc
  let rlo := toInt (lnTail (evmSub 160 c) lo)
  let rm := toInt (lnTail (evmSub 160 c) m)
  have hrloLo := hbrLo.1
  have hrloHi := hbrLo.2
  have hrmLo := hbrM.1
  have hrmHi := hbrM.2
  have hx := LnGeneratedModel.r1_mono hlo1 hlom hmhi
  have hacc_mono : posAccI lo c ≤ posAccI m c := by
    have hmul := Int.mul_le_mul_of_nonneg_right hx
      (by change (0 : Int) ≤ 7450580596923828125; decide)
    have h1 := Int.add_le_add_right hmul (ln2kInt c)
    have h2 := Int.add_le_add_right h1 lnBiasI
    simpa [posAccI, Int.add_assoc] using h2
  have hpow : twoPow72I = (4722366482869645213696 : Int) := by
    unfold twoPow72I
    decide
  rw [hpow] at hdiff hrloLo hrloHi hrmLo hrmHi
  unfold posResidueGap at hdiff
  change posAccI m c - posAccI lo c +
      ((rm + 1) * 4722366482869645213696 - posAccI m c) ≤
        4722366482869645213696 at hdiff
  change rlo * 4722366482869645213696 ≤ posAccI lo c at hrloLo
  change posAccI lo c < (rlo + 1) * 4722366482869645213696 at hrloHi
  change rm * 4722366482869645213696 ≤ posAccI m c at hrmLo
  change posAccI m c < (rm + 1) * 4722366482869645213696 at hrmHi
  generalize hQ : (4722366482869645213696 : Int) = Q at hdiff hrloLo hrloHi hrmLo hrmHi
  change posAccI m c - posAccI lo c + ((rm + 1) * Q - posAccI m c) ≤ Q at hdiff
  change rlo * Q ≤ posAccI lo c at hrloLo
  change posAccI lo c < (rlo + 1) * Q at hrloHi
  change rm * Q ≤ posAccI m c at hrmLo
  change posAccI m c < (rm + 1) * Q at hrmHi
  have hdiffQ :
      posAccI m c - posAccI lo c + ((rm + 1) * Q - posAccI m c) ≤ Q := by
    simpa [hQ] using hdiff
  have hQpos : (0 : Int) < Q := by
    rw [← hQ]
    decide
  have hQnonneg : (0 : Int) ≤ Q := by omega
  have sub_swap (A B C : Int) : C - B = A - B + (C - A) := by omega
  have cancel_bucket {A B Q' : Int} (h : A + Q' - B ≤ Q') : A ≤ B := by omega
  have lt_of_le_lt {A B C : Int} (hAB : A ≤ B) (hBC : B < C) : A < C := by omega
  have le_lt_false {A B : Int} (hBA : B ≤ A) (hAB : A < B) : False := by omega
  have succ_le_of_not_le {A B : Int} (h : ¬ A ≤ B) : B + 1 ≤ A := by omega
  have hmlo_for_rm : rm * Q ≤ posAccI lo c := by
    have hcollapse :
        (rm + 1) * Q - posAccI lo c ≤ Q := by
      calc
        (rm + 1) * Q - posAccI lo c =
            posAccI m c - posAccI lo c + ((rm + 1) * Q - posAccI m c) := by
              exact sub_swap (posAccI m c) (posAccI lo c) ((rm + 1) * Q)
        _ ≤ Q := hdiffQ
    have hsplit : (rm + 1) * Q = rm * Q + Q := by
      rw [Int.add_mul, Int.one_mul]
    rw [hsplit] at hcollapse
    exact cancel_bucket hcollapse
  have hmhi_for_rm : posAccI lo c < (rm + 1) * Q :=
    lt_of_le_lt hacc_mono hrmHi
  have hle1 : rlo ≤ rm := by
    by_cases hle : rlo ≤ rm
    · exact hle
    · have hge : rm + 1 ≤ rlo := succ_le_of_not_le hle
      have hmul := Int.mul_le_mul_of_nonneg_right hge hQnonneg
      have hcontr : (rm + 1) * Q ≤ posAccI lo c :=
        Int.le_trans hmul hrloLo
      exact False.elim (le_lt_false hcontr hmhi_for_rm)
  have hle2 : rm ≤ rlo := by
    by_cases hle : rm ≤ rlo
    · exact hle
    · have hge : rlo + 1 ≤ rm := succ_le_of_not_le hle
      have hmul := Int.mul_le_mul_of_nonneg_right hge hQnonneg
      have hcontr : (rlo + 1) * Q ≤ posAccI lo c :=
        Int.le_trans hmul hmlo_for_rm
      exact False.elim (le_lt_false hcontr hrloHi)
  change rlo = rm
  exact Int.le_antisymm hle1 hle2

theorem posAccI_mono_m {lo m c : Nat}
    (hlo : MLO ≤ lo) (hlom : lo ≤ m) (hmhi : m < MHI) :
    posAccI lo c ≤ posAccI m c := by
  have hx := LnGeneratedModel.r1_mono hlo hlom hmhi
  have hmul := Int.mul_le_mul_of_nonneg_right hx
    (by change (0 : Int) ≤ 7450580596923828125; decide)
  unfold posAccI
  omega

theorem lnTail_eq_of_same_posAcc_endpoints {lo hi m c : Nat}
    (hlo : MLO ≤ lo) (hlom : lo ≤ m) (hmhi : m ≤ hi) (hhi : hi < MHI)
    (hc : c < 160)
    (heq : toInt (lnTail (evmSub 160 c) lo) =
      toInt (lnTail (evmSub 160 c) hi)) :
    toInt (lnTail (evmSub 160 c) m) =
      toInt (lnTail (evmSub 160 c) hi) := by
  have hmlo : MLO ≤ m := by omega
  have hmhi' : m < MHI := by omega
  have hlohi : lo < MHI := by omega
  have hbrLo := lnTail_floor_bracket_pos hlo hlohi hc
  have hbrM := lnTail_floor_bracket_pos hmlo hmhi' hc
  have hbrHi := lnTail_floor_bracket_pos (by omega : MLO ≤ hi) hhi hc
  have haccLoM : posAccI lo c ≤ posAccI m c :=
    posAccI_mono_m hlo hlom hmhi'
  have haccMHi : posAccI m c ≤ posAccI hi c :=
    posAccI_mono_m hmlo hmhi hhi
  have hpow : twoPow72I = (4722366482869645213696 : Int) := by
    unfold twoPow72I
    decide
  rw [hpow] at hbrLo hbrM hbrHi
  generalize hQ : (4722366482869645213696 : Int) = Q at hbrLo hbrM hbrHi
  change toInt (lnTail (evmSub 160 c) lo) * Q ≤ posAccI lo c ∧
    posAccI lo c < (toInt (lnTail (evmSub 160 c) lo) + 1) * Q at hbrLo
  change toInt (lnTail (evmSub 160 c) m) * Q ≤ posAccI m c ∧
    posAccI m c < (toInt (lnTail (evmSub 160 c) m) + 1) * Q at hbrM
  change toInt (lnTail (evmSub 160 c) hi) * Q ≤ posAccI hi c ∧
    posAccI hi c < (toInt (lnTail (evmSub 160 c) hi) + 1) * Q at hbrHi
  rw [← heq] at hbrHi
  have hQnonneg : (0 : Int) ≤ Q := by rw [← hQ]; decide
  have succ_le_of_not_le {A B : Int} (h : ¬ A ≤ B) : B + 1 ≤ A := by omega
  have le_lt_false {A B : Int} (hBA : B ≤ A) (hAB : A < B) : False := by omega
  have hm_eq_lo :
      toInt (lnTail (evmSub 160 c) m) =
        toInt (lnTail (evmSub 160 c) lo) := by
    have hm_le_lo : toInt (lnTail (evmSub 160 c) m) ≤
        toInt (lnTail (evmSub 160 c) lo) := by
      by_cases hle : toInt (lnTail (evmSub 160 c) m) ≤
          toInt (lnTail (evmSub 160 c) lo)
      · exact hle
      · have hsucc : toInt (lnTail (evmSub 160 c) lo) + 1 ≤
            toInt (lnTail (evmSub 160 c) m) := succ_le_of_not_le hle
        have hmul := Int.mul_le_mul_of_nonneg_right hsucc hQnonneg
        have hcontr : (toInt (lnTail (evmSub 160 c) lo) + 1) * Q ≤
            posAccI hi c :=
          Int.le_trans (Int.le_trans hmul hbrM.1) haccMHi
        exact False.elim (le_lt_false hcontr hbrHi.2)
    have hlo_le_m : toInt (lnTail (evmSub 160 c) lo) ≤
        toInt (lnTail (evmSub 160 c) m) := by
      by_cases hle : toInt (lnTail (evmSub 160 c) lo) ≤
          toInt (lnTail (evmSub 160 c) m)
      · exact hle
      · have hsucc : toInt (lnTail (evmSub 160 c) m) + 1 ≤
            toInt (lnTail (evmSub 160 c) lo) := succ_le_of_not_le hle
        have hmul := Int.mul_le_mul_of_nonneg_right hsucc hQnonneg
        have hcontr : (toInt (lnTail (evmSub 160 c) m) + 1) * Q ≤
            posAccI m c :=
          Int.le_trans (Int.le_trans hmul hbrLo.1) haccLoM
        exact False.elim (le_lt_false hcontr hbrM.2)
    exact Int.le_antisymm hm_le_lo hlo_le_m
  exact Eq.trans hm_eq_lo heq

theorem posResidueGap_ge_of_same_posAcc_endpoints {lo hi m c : Nat}
    (hlo : MLO ≤ lo) (hlom : lo ≤ m) (hmhi : m ≤ hi) (hhi : hi < MHI)
    (hc : c < 160)
    (heq : toInt (lnTail (evmSub 160 c) lo) =
      toInt (lnTail (evmSub 160 c) hi)) :
    posResidueGap hi c (toInt (lnTail (evmSub 160 c) hi)) ≤
      posResidueGap m c (toInt (lnTail (evmSub 160 c) m)) := by
  have hmlo : MLO ≤ m := by omega
  have htail :=
    lnTail_eq_of_same_posAcc_endpoints hlo hlom hmhi hhi hc heq
  have hacc : posAccI m c ≤ posAccI hi c :=
    posAccI_mono_m hmlo hmhi hhi
  unfold posResidueGap
  rw [htail]
  have sub_left_antitone {A B C : Int} (h : A ≤ B) : C - B ≤ C - A := by omega
  exact sub_left_antitone hacc

theorem lnErrArg_eq_posPhase_gap {m c : Nat}
    (hmlo : MLO ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    let r := toInt (lnTail (evmSub 160 c) m)
    ((lnErrArg r : Nat) : Int) =
      posPhaseI m c * (lnErrorBoundDen : Int) +
        (lnErrorExtraNum : Int) * twoPow99I +
          posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) := by
  intro r
  have hr0 : 0 ≤ r := lnTail_nonneg_pos hmlo hmhi hc
  have harg : 0 ≤ r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
    unfold lnErrorBoundDen lnErrorBoundNum
    omega
  have hVs := v_scale_pos (toInt (x1W (zWord m))) c (by omega : c ≤ 160)
  have hVs' : posAccI m c * twoPow27I = posPhaseI m c := by
    unfold posAccI posPhaseI
    simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  have hnum : ((lnErrorBoundNum : Nat) : Int) = (1698600000 : Int) := by
    unfold lnErrorBoundNum
    rfl
  have hextra : ((lnErrorExtraNum : Nat) : Int) = (698600000 : Int) := by
    unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen
    decide +kernel
  unfold lnErrArg posResidueGap
  rw [Int.natCast_mul, Int.toNat_of_nonneg harg]
  rw [hden, hnum, hextra]
  unfold twoPow99I twoPow27I at hVs' ⊢
  unfold twoPow72I
  rw [← hVs']
  change (r * 1000000000 + 1698600000) * 633825300114114700748351602688 =
    posAccI m c * 134217728 * 1000000000 +
      698600000 * 633825300114114700748351602688 +
        ((r + 1) * 4722366482869645213696 - posAccI m c) * 134217728 *
          1000000000
  have hP : (4722366482869645213696 : Int) * 134217728 =
      633825300114114700748351602688 := by
    decide
  have hN : (1698600000 : Int) = 1000000000 + 698600000 := by
    decide
  rw [hN, ← hP]
  simp only [Int.add_mul, Int.mul_add, Int.add_assoc, Int.sub_eq_add_neg,
    Int.neg_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  generalize r * (134217728 * (1000000000 * 4722366482869645213696)) = X
  generalize 134217728 * (1000000000 * 4722366482869645213696) = Y
  generalize 134217728 * (698600000 * 4722366482869645213696) = Z
  generalize posAccI m c * (134217728 * 1000000000) = W
  omega

def PosShiftResidueOk (m c : Nat) (r : Int) : Prop :=
  posPhaseI m c * (lnErrorBoundDen : Int) + (lnErrorCoarsePosResidue : Int) ≤
    (r + 1) * twoPow99I * (lnErrorBoundDen : Int)

def PosShiftGeResidueOk (m c : Nat) (r : Int) : Prop :=
  posPhaseI m c * (lnErrorBoundDen : Int) + (lnErrorCoarseGePosResidue : Int) ≤
    (r + 1) * twoPow99I * (lnErrorBoundDen : Int)

def PosShiftResidueGapOk (m c : Nat) (r : Int) : Prop :=
  (lnErrorCoarsePosResidue : Int) ≤
    posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int)

def PosShiftGeResidueGapOk (m c : Nat) (r : Int) : Prop :=
  (lnErrorCoarseGePosResidue : Int) ≤
    posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int)

def PosShiftDirectResidueGapOk (m c : Nat) (r : Int) : Prop :=
  (lnErrorDirectResidueGap : Int) ≤ posResidueGap m c r

def residueGapOkB (m c : Nat) (r : Int) : Bool :=
  decide ((lnErrorCoarsePosResidue : Int) ≤
    posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int))

def geResidueGapOkB (m c : Nat) (r : Int) : Bool :=
  decide ((lnErrorCoarseGePosResidue : Int) ≤
    posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int))

def directResidueGapOkB (m c : Nat) (r : Int) : Bool :=
  decide ((lnErrorDirectResidueGap : Int) ≤ posResidueGap m c r)

def directResidueGapModOkB (m c : Nat) : Bool :=
  decide ((posAccI m c).toNat % twoPow72N ≤ twoPow72N - lnErrorDirectResidueGap)

theorem PosShiftResidueGapOk.of_bool {m c : Nat} {r : Int}
    (h : residueGapOkB m c r = true) : PosShiftResidueGapOk m c r := by
  unfold residueGapOkB PosShiftResidueGapOk at *
  exact of_decide_eq_true h

theorem PosShiftGeResidueGapOk.of_bool {m c : Nat} {r : Int}
    (h : geResidueGapOkB m c r = true) : PosShiftGeResidueGapOk m c r := by
  unfold geResidueGapOkB PosShiftGeResidueGapOk at *
  exact of_decide_eq_true h

theorem PosShiftDirectResidueGapOk.of_bool {m c : Nat} {r : Int}
    (h : directResidueGapOkB m c r = true) : PosShiftDirectResidueGapOk m c r := by
  unfold directResidueGapOkB PosShiftDirectResidueGapOk at *
  exact of_decide_eq_true h

theorem PosShiftDirectResidueGapOk.of_modB {m c : Nat}
    (hmlo : MLO ≤ m) (hmhi : m < MHI) (hc : c < 160)
    (h : directResidueGapModOkB m c = true) :
    PosShiftDirectResidueGapOk m c (toInt (lnTail (evmSub 160 c) m)) := by
  unfold directResidueGapModOkB at h
  have hmod :
      (posAccI m c).toNat % twoPow72N ≤ twoPow72N - lnErrorDirectResidueGap :=
    of_decide_eq_true h
  have heq := posResidueGap_eq_twoPow72_sub_mod (m := m) (c := c) hmlo hmhi hc
  change posResidueGap m c (toInt (lnTail (evmSub 160 c) m)) =
      ((twoPow72N - (posAccI m c).toNat % twoPow72N : Nat) : Int) at heq
  unfold PosShiftDirectResidueGapOk
  rw [heq]
  apply Int.ofNat_le.mpr
  have hgap_le_q : lnErrorDirectResidueGap ≤ twoPow72N := by
    unfold lnErrorDirectResidueGap twoPow72N
    decide
  omega

theorem PosShiftResidueGapOk_of_gap_threshold {m c : Nat} {r : Int}
    (hgap : posResidueGapThreshold ≤ posResidueGap m c r) :
    PosShiftResidueGapOk m c r := by
  have hconst :
      (lnErrorCoarsePosResidue : Int) ≤
        posResidueGapThreshold * twoPow27I * (lnErrorBoundDen : Int) := by
    unfold lnErrorCoarsePosResidue posResidueGapThreshold twoPow27I lnErrorBoundDen
    decide +kernel
  have h27 : 0 ≤ twoPow27I := by
    change (0 : Int) ≤ 134217728
    decide
  have hden : 0 ≤ (lnErrorBoundDen : Int) := by
    change (0 : Int) ≤ 1000000000
    decide
  have hmul := Int.mul_le_mul_of_nonneg_right hgap h27
  have hmul2 := Int.mul_le_mul_of_nonneg_right hmul hden
  unfold PosShiftResidueGapOk
  exact Int.le_trans hconst hmul2

theorem posResidueGap_lt_threshold_of_not_ok {m c : Nat} {r : Int}
    (_hgap_pos : 1 ≤ posResidueGap m c r)
    (h : residueGapOkB m c r = false) :
    posResidueGap m c r < posResidueGapThreshold := by
  unfold residueGapOkB at h
  rw [decide_eq_false_iff_not] at h
  by_cases hle : posResidueGapThreshold ≤ posResidueGap m c r
  · exact False.elim (h (PosShiftResidueGapOk_of_gap_threshold hle))
  · omega

theorem PosShiftResidueOk_of_gap {m c : Nat} {r : Int}
    (hc : c ≤ 160) (hgap : PosShiftResidueGapOk m c r) :
    PosShiftResidueOk m c r := by
  have hVs := v_scale_pos (toInt (x1W (zWord m))) c hc
  have hVs' : posAccI m c * twoPow27I = posPhaseI m c := by
    unfold posAccI posPhaseI
    simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
  unfold PosShiftResidueGapOk posResidueGap at hgap
  unfold PosShiftResidueOk
  rw [← hVs']
  unfold twoPow72I twoPow27I at hgap
  unfold twoPow27I twoPow99I
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  rw [hden] at hgap ⊢
  omega

theorem PosShiftResidueOk_of_gapB {m c : Nat} {r : Int}
    (hc : c ≤ 160) (h : residueGapOkB m c r = true) :
    PosShiftResidueOk m c r :=
  PosShiftResidueOk_of_gap hc (PosShiftResidueGapOk.of_bool h)

theorem PosShiftGeResidueOk_of_gap {m c : Nat} {r : Int}
    (hc : c ≤ 160) (hgap : PosShiftGeResidueGapOk m c r) :
    PosShiftGeResidueOk m c r := by
  have hVs := v_scale_pos (toInt (x1W (zWord m))) c hc
  have hVs' : posAccI m c * twoPow27I = posPhaseI m c := by
    unfold posAccI posPhaseI
    simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
  unfold PosShiftGeResidueGapOk posResidueGap at hgap
  unfold PosShiftGeResidueOk
  rw [← hVs']
  unfold twoPow72I twoPow27I at hgap
  unfold twoPow27I twoPow99I
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  rw [hden] at hgap ⊢
  omega

theorem PosShiftGeResidueOk_of_gapB {m c : Nat} {r : Int}
    (hc : c ≤ 160) (h : geResidueGapOkB m c r = true) :
    PosShiftGeResidueOk m c r :=
  PosShiftGeResidueOk_of_gap hc (PosShiftGeResidueGapOk.of_bool h)

structure ResidueCell where
  lo : Nat
  hi : Nat

def geResidueCellOkB (lo hi c : Nat) : Bool :=
  decide (Sc ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          decide (toInt (lnTail (evmSub 160 c) lo) =
            toInt (lnTail (evmSub 160 c) hi)) &&
            geResidueGapOkB hi c (toInt (lnTail (evmSub 160 c) hi))

def directResidueCellOkB (lo hi c : Nat) : Bool :=
  decide (MLO ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          decide (toInt (lnTail (evmSub 160 c) lo) =
            toInt (lnTail (evmSub 160 c) hi)) &&
            directResidueGapOkB hi c (toInt (lnTail (evmSub 160 c) hi))

def geResidueRunCellOkB (lo hi c : Nat) : Bool :=
  decide (Sc ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          let rlo := toInt (lnTail (evmSub 160 c) lo)
          decide (posAccI hi c < (rlo + 1) * twoPow72I) &&
            decide ((lnErrorCoarseGePosResidue : Int) ≤
              ((rlo + 1) * twoPow72I - posAccI hi c) * twoPow27I *
                (lnErrorBoundDen : Int))

def residueRunCellOkB (lo hi c : Nat) : Bool :=
  decide (MLO ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          let rlo := toInt (lnTail (evmSub 160 c) lo)
          decide (posAccI hi c < (rlo + 1) * twoPow72I) &&
            decide ((lnErrorCoarsePosResidue : Int) ≤
              ((rlo + 1) * twoPow72I - posAccI hi c) * twoPow27I *
                (lnErrorBoundDen : Int))

def directResidueRunCellOkB (lo hi c : Nat) : Bool :=
  decide (MLO ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          let rlo := toInt (lnTail (evmSub 160 c) lo)
          decide (posAccI hi c < (rlo + 1) * twoPow72I) &&
            decide ((lnErrorDirectResidueGap : Int) ≤
              (rlo + 1) * twoPow72I - posAccI hi c)

theorem geResidueCellOkB_sound {lo hi m c : Nat}
    (h : geResidueCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGeResidueOk m c (toInt (lnTail (evmSub 160 c) m)) := by
  unfold geResidueCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hloSc, _hlohi⟩, hhi⟩, hc⟩, htailEq⟩, hgapHiB⟩ := h
  have hloMLO : MLO ≤ lo := by
    simp only [Sc, MLO] at hloSc ⊢
    omega
  have hgapLe :=
    posResidueGap_ge_of_same_posAcc_endpoints hloMLO hlom hmhi hhi hc htailEq
  have hgapHi := PosShiftGeResidueGapOk.of_bool hgapHiB
  have hgapM :
      PosShiftGeResidueGapOk m c (toInt (lnTail (evmSub 160 c) m)) := by
    unfold PosShiftGeResidueGapOk at hgapHi ⊢
    have h27 : 0 ≤ twoPow27I := by
      change (0 : Int) ≤ 134217728
      decide
    have hden : 0 ≤ (lnErrorBoundDen : Int) := by
      change (0 : Int) ≤ 1000000000
      decide
    have hmul := Int.mul_le_mul_of_nonneg_right hgapLe h27
    have hmul2 := Int.mul_le_mul_of_nonneg_right hmul hden
    exact Int.le_trans hgapHi hmul2
  exact PosShiftGeResidueOk_of_gap (by omega : c ≤ 160) hgapM

theorem directResidueCellOkB_sound {lo hi m c : Nat}
    (h : directResidueCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftDirectResidueGapOk m c (toInt (lnTail (evmSub 160 c) m)) := by
  unfold directResidueCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, hc⟩, htailEq⟩, hgapHiB⟩ := h
  have hgapLe :=
    posResidueGap_ge_of_same_posAcc_endpoints hlo hlom hmhi hhi hc htailEq
  have hgapHi := PosShiftDirectResidueGapOk.of_bool hgapHiB
  unfold PosShiftDirectResidueGapOk at hgapHi ⊢
  exact Int.le_trans hgapHi hgapLe

theorem lnTail_eq_of_residue_run {lo hi m c : Nat}
    (hlo : MLO ≤ lo) (hlom : lo ≤ m) (hmhi : m ≤ hi) (hhi : hi < MHI)
    (hc : c < 160)
    (hboundary : posAccI hi c <
      (toInt (lnTail (evmSub 160 c) lo) + 1) * twoPow72I) :
    toInt (lnTail (evmSub 160 c) m) =
      toInt (lnTail (evmSub 160 c) lo) := by
  have hlohi : lo < MHI := by omega
  have hmhi' : m < MHI := by omega
  have hbrLo := lnTail_floor_bracket_pos hlo hlohi hc
  have hbrM := lnTail_floor_bracket_pos (by omega : MLO ≤ m) hmhi' hc
  have haccLoM := posAccI_mono_m (c := c) hlo hlom hmhi'
  have haccMHi := posAccI_mono_m (c := c) (by omega : MLO ≤ m) hmhi hhi
  let rlo := toInt (lnTail (evmSub 160 c) lo)
  let rm := toInt (lnTail (evmSub 160 c) m)
  have hboundaryM : posAccI m c < (rlo + 1) * twoPow72I := by
    exact Int.lt_of_le_of_lt haccMHi (by simpa [rlo] using hboundary)
  have hrm_le : rm ≤ rlo := by
    have hmul : rm * twoPow72I < (rlo + 1) * twoPow72I :=
      Int.lt_of_le_of_lt hbrM.1 hboundaryM
    have hlt : rm < rlo + 1 :=
      (Int.mul_lt_mul_right (a := twoPow72I) (b := rm) (c := rlo + 1)
        (by unfold twoPow72I; decide)).mp hmul
    exact Int.le_of_lt_add_one hlt
  have hrlo_le : rlo ≤ rm := by
    have hmul : rlo * twoPow72I < (rm + 1) * twoPow72I := by
      exact Int.lt_of_le_of_lt (Int.le_trans hbrLo.1 haccLoM) hbrM.2
    have hlt : rlo < rm + 1 :=
      (Int.mul_lt_mul_right (a := twoPow72I) (b := rlo) (c := rm + 1)
        (by unfold twoPow72I; decide)).mp hmul
    exact Int.le_of_lt_add_one hlt
  exact Int.le_antisymm hrm_le hrlo_le

theorem geResidueRunCellOkB_sound {lo hi m c : Nat}
    (h : geResidueRunCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGeResidueOk m c (toInt (lnTail (evmSub 160 c) m)) := by
  unfold geResidueRunCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hloSc, _hlohi⟩, hhi⟩, hc⟩, hrun⟩ := h
  obtain ⟨hboundary, hgapHi⟩ := hrun
  have hlo : MLO ≤ lo := by
    simp only [Sc, MLO] at hloSc ⊢
    omega
  have htail := lnTail_eq_of_residue_run hlo hlom hmhi hhi hc hboundary
  have hmhi' : m < MHI := by omega
  have haccMHi := posAccI_mono_m (c := c) (by omega : MLO ≤ m) hmhi hhi
  let rlo := toInt (lnTail (evmSub 160 c) lo)
  let rm := toInt (lnTail (evmSub 160 c) m)
  have hgapLe :
      (rlo + 1) * twoPow72I - posAccI hi c ≤
        (rm + 1) * twoPow72I - posAccI m c := by
    rw [show rm = rlo by simpa [rm, rlo] using htail]
    exact Int.sub_le_sub_left haccMHi ((rlo + 1) * twoPow72I)
  have h27 : 0 ≤ twoPow27I := by
    unfold twoPow27I
    decide
  have hden : 0 ≤ (lnErrorBoundDen : Int) := by
    change (0 : Int) ≤ 1000000000
    decide
  have hscaled1 :
      ((rlo + 1) * twoPow72I - posAccI hi c) * twoPow27I ≤
        ((rm + 1) * twoPow72I - posAccI m c) * twoPow27I :=
    Int.mul_le_mul_of_nonneg_right hgapLe h27
  have hscaled2 :
      ((rlo + 1) * twoPow72I - posAccI hi c) * twoPow27I *
          (lnErrorBoundDen : Int) ≤
        ((rm + 1) * twoPow72I - posAccI m c) * twoPow27I *
          (lnErrorBoundDen : Int) :=
    Int.mul_le_mul_of_nonneg_right hscaled1 hden
  have hgapM : PosShiftGeResidueGapOk m c rm := by
    unfold PosShiftGeResidueGapOk posResidueGap
    exact Int.le_trans hgapHi hscaled2
  simpa [rm] using PosShiftGeResidueOk_of_gap (by omega : c ≤ 160) hgapM

theorem residueRunCellOkB_sound {lo hi m c : Nat}
    (h : residueRunCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftResidueOk m c (toInt (lnTail (evmSub 160 c) m)) := by
  unfold residueRunCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, hc⟩, hrun⟩ := h
  obtain ⟨hboundary, hgapHi⟩ := hrun
  have htail := lnTail_eq_of_residue_run hlo hlom hmhi hhi hc hboundary
  have haccMHi := posAccI_mono_m (c := c) (by omega : MLO ≤ m) hmhi hhi
  let rlo := toInt (lnTail (evmSub 160 c) lo)
  let rm := toInt (lnTail (evmSub 160 c) m)
  have hgapLe :
      (rlo + 1) * twoPow72I - posAccI hi c ≤
        (rm + 1) * twoPow72I - posAccI m c := by
    rw [show rm = rlo by simpa [rm, rlo] using htail]
    exact Int.sub_le_sub_left haccMHi ((rlo + 1) * twoPow72I)
  have h27 : 0 ≤ twoPow27I := by
    unfold twoPow27I
    decide
  have hden : 0 ≤ (lnErrorBoundDen : Int) := by
    change (0 : Int) ≤ 1000000000
    decide
  have hscaled1 :
      ((rlo + 1) * twoPow72I - posAccI hi c) * twoPow27I ≤
        ((rm + 1) * twoPow72I - posAccI m c) * twoPow27I :=
    Int.mul_le_mul_of_nonneg_right hgapLe h27
  have hscaled2 :
      ((rlo + 1) * twoPow72I - posAccI hi c) * twoPow27I *
          (lnErrorBoundDen : Int) ≤
        ((rm + 1) * twoPow72I - posAccI m c) * twoPow27I *
          (lnErrorBoundDen : Int) :=
    Int.mul_le_mul_of_nonneg_right hscaled1 hden
  have hgapM : PosShiftResidueGapOk m c rm := by
    unfold PosShiftResidueGapOk posResidueGap
    exact Int.le_trans hgapHi hscaled2
  simpa [rm] using PosShiftResidueOk_of_gap (by omega : c ≤ 160) hgapM

theorem directResidueRunCellOkB_sound {lo hi m c : Nat}
    (h : directResidueRunCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftDirectResidueGapOk m c (toInt (lnTail (evmSub 160 c) m)) := by
  unfold directResidueRunCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, hc⟩, hrun⟩ := h
  obtain ⟨hboundary, hgapHi⟩ := hrun
  have htail := lnTail_eq_of_residue_run hlo hlom hmhi hhi hc hboundary
  have haccMHi := posAccI_mono_m (c := c) (by omega : MLO ≤ m) hmhi hhi
  let rlo := toInt (lnTail (evmSub 160 c) lo)
  let rm := toInt (lnTail (evmSub 160 c) m)
  have hgapLe :
      (rlo + 1) * twoPow72I - posAccI hi c ≤
        (rm + 1) * twoPow72I - posAccI m c := by
    rw [show rm = rlo by simpa [rm, rlo] using htail]
    exact Int.sub_le_sub_left haccMHi ((rlo + 1) * twoPow72I)
  have hgapM : PosShiftDirectResidueGapOk m c rm := by
    unfold PosShiftDirectResidueGapOk posResidueGap
    exact Int.le_trans hgapHi hgapLe
  simpa [rm] using hgapM

def geResidueCellListCoverB (c : Nat) : Nat → Nat → List ResidueCell → Bool
  | lo, hi, [] => decide (hi < lo)
  | lo, hi, cell :: cells =>
      decide (cell.lo = lo) &&
        decide (lo ≤ cell.hi) &&
          decide (cell.hi ≤ hi) &&
            geResidueCellOkB cell.lo cell.hi c &&
              geResidueCellListCoverB c (cell.hi + 1) hi cells

theorem geResidueCellListCoverB_sound {cells : List ResidueCell} {c lo hi m : Nat}
    (h : geResidueCellListCoverB c lo hi cells = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGeResidueOk m c (toInt (lnTail (evmSub 160 c) m)) := by
  induction cells generalizing lo with
  | nil =>
      unfold geResidueCellListCoverB at h
      have hlt : hi < lo := of_decide_eq_true h
      omega
  | cons cell cells ih =>
      unfold geResidueCellListCoverB at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hlo, _hlohi⟩, _hhihi⟩, hok⟩, hrest⟩ := h
      by_cases hmcell : m ≤ cell.hi
      · exact geResidueCellOkB_sound hok (by omega) hmcell
      · exact ih hrest (by omega)

def directResidueCellListCoverB (c : Nat) : Nat → Nat → List ResidueCell → Bool
  | lo, hi, [] => decide (hi < lo)
  | lo, hi, cell :: cells =>
      decide (cell.lo = lo) &&
        decide (lo ≤ cell.hi) &&
          decide (cell.hi ≤ hi) &&
            directResidueCellOkB cell.lo cell.hi c &&
              directResidueCellListCoverB c (cell.hi + 1) hi cells

theorem directResidueCellListCoverB_sound {cells : List ResidueCell} {c lo hi m : Nat}
    (h : directResidueCellListCoverB c lo hi cells = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftDirectResidueGapOk m c (toInt (lnTail (evmSub 160 c) m)) := by
  induction cells generalizing lo with
  | nil =>
      unfold directResidueCellListCoverB at h
      have hlt : hi < lo := of_decide_eq_true h
      omega
  | cons cell cells ih =>
      unfold directResidueCellListCoverB at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hlo, _hlohi⟩, _hhihi⟩, hok⟩, hrest⟩ := h
      by_cases hmcell : m ≤ cell.hi
      · exact directResidueCellOkB_sound hok (by omega) hmcell
      · exact ih hrest (by omega)

theorem pos_direct_residue_arg_le_int {A r : Int}
    (hres : A * (lnErrorBoundDen : Int) +
        (lnErrorDirectResidueGap : Int) * twoPow27I * (lnErrorBoundDen : Int) ≤
      (r + 1) * twoPow99I * (lnErrorBoundDen : Int)) :
    A * (lnErrorBoundDen : Int) + (lnErrorExtraNum : Int) * twoPow99I +
        (lnErrorDirectResidueGap : Int) * twoPow27I * (lnErrorBoundDen : Int) ≤
      (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  have hnum : ((lnErrorBoundNum : Nat) : Int) = (1698600000 : Int) := by
    unfold lnErrorBoundNum
    rfl
  have hextra : ((lnErrorExtraNum : Nat) : Int) = (698600000 : Int) := by
    unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen
    decide +kernel
  rw [hden] at hres
  rw [hden, hnum, hextra]
  unfold twoPow99I twoPow27I at hres ⊢
  omega

theorem direct_residue_phase_bound {m c : Nat} {r : Int}
    (hc : c ≤ 160) (hgap : PosShiftDirectResidueGapOk m c r) :
    posPhaseI m c * (lnErrorBoundDen : Int) +
        (lnErrorDirectResidueGap : Int) * twoPow27I * (lnErrorBoundDen : Int) ≤
      (r + 1) * twoPow99I * (lnErrorBoundDen : Int) := by
  have hVs := v_scale_pos (toInt (x1W (zWord m))) c hc
  have hVs' : posAccI m c * twoPow27I = posPhaseI m c := by
    unfold posAccI posPhaseI
    simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
  unfold PosShiftDirectResidueGapOk posResidueGap at hgap
  rw [← hVs']
  unfold twoPow27I twoPow99I
  unfold twoPow72I at hgap
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  rw [hden]
  omega

def posPhaseNatGe (m c : Nat) : Nat :=
  (toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
    (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
      BIASc * twoPow27N * lnErrorBoundDen

def posAvailGe (m c : Nat) (r : Int) : Nat :=
  lnErrArg r - posPhaseNatGe m c

def posBaseYGe (m c : Nat) : Nat :=
  ((m * 9999999999999999999999999996615) *
    ((2 * (10 ^ 40 - 1)) ^ (160 - c))) *
    (Sc * (10 ^ 31 - 3384))

def posBaseWGe (c : Nat) : Nat :=
  (560227709747861399187319382270000000000000000000000000000000 *
    ((10 ^ 40 : Nat) ^ (160 - c))) *
    (10 ^ 18 * 10 ^ 31)

def PosShiftGeBudgetOk (m c x : Nat) (r : Int) : Prop :=
  posPhaseNatGe m c ≤ lnErrArg r ∧
    wadRayNum x * (posBaseWGe c * lnErrQ) ≤
      (posBaseYGe m c * (lnErrQ + posAvailGe m c r)) * wadRayStrictDen

def PosShiftGeBudgetIneqOk (m c x : Nat) (r : Int) : Prop :=
  wadRayNum x * (posBaseWGe c * lnErrQ) ≤
    (posBaseYGe m c * (lnErrQ + posAvailGe m c r)) * wadRayStrictDen

def posConstNat (c : Nat) : Nat :=
  (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
    BIASc * twoPow27N * lnErrorBoundDen

def posNegXNat (m : Nat) : Nat :=
  (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen

def posPhaseNatLt (m c : Nat) : Nat :=
  posConstNat c - posNegXNat m

def posAvailLt (m c : Nat) (r : Int) : Nat :=
  lnErrArg r - posPhaseNatLt m c

def posBaseYLt (m c : Nat) : Nat :=
  ((2 * (10 ^ 40 - 1)) ^ (160 - c) * (Sc * (10 ^ 31 - 3384))) *
    (m * 9999999999999999999999999996615)

def posBaseWLt (c : Nat) : Nat :=
  (((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31)) *
    560227709747861399187319382270000000000000000000000000000000)

def PosShiftLtBudgetOk (m c x : Nat) (r : Int) : Prop :=
  posNegXNat m ≤ posConstNat c ∧
    posPhaseNatLt m c ≤ lnErrArg r ∧
      wadRayNum x * (posBaseWLt c * lnErrQ) ≤
        (posBaseYLt m c * (lnErrQ + posAvailLt m c r)) * wadRayStrictDen

def PosShiftLtBudgetIneqOk (m c x : Nat) (r : Int) : Prop :=
  wadRayNum x * (posBaseWLt c * lnErrQ) ≤
    (posBaseYLt m c * (lnErrQ + posAvailLt m c r)) * wadRayStrictDen

def PosShiftGeTopBudgetIneqOk (m c : Nat) : Prop :=
  PosShiftGeBudgetIneqOk m c (posTopX c m) (toInt (lnTail (evmSub 160 c) m))

def PosShiftLtTopBudgetIneqOk (m c : Nat) : Prop :=
  PosShiftLtBudgetIneqOk m c (posTopX c m) (toInt (lnTail (evmSub 160 c) m))

def lnPhaseExtraArg : Nat := lnErrorExtraNum * twoPow99N

def PosShiftGePhaseDirectOk (n m c : Nat) : Prop :=
  sumGE n (posPhaseNatGe m c + lnPhaseExtraArg) lnErrQ (posTopX c m) (10 ^ 18)

def PosShiftLtPhaseDirectOk (n m c : Nat) : Prop :=
  sumGE n (posPhaseNatLt m c + lnPhaseExtraArg) lnErrQ (posTopX c m) (10 ^ 18)

def minPosAvail : Nat := lnPhaseExtraArg + twoPow27N * lnErrorBoundDen

def PosShiftGeMinPhaseDirectOk (n m c : Nat) : Prop :=
  sumGE n (posPhaseNatGe m c + minPosAvail) lnErrQ (posTopX c m) (10 ^ 18)

def PosShiftLtMinPhaseDirectOk (n m c : Nat) : Prop :=
  sumGE n (posPhaseNatLt m c + minPosAvail) lnErrQ (posTopX c m) (10 ^ 18)

def lnDirectGapArg : Nat := lnErrorDirectResidueGap * twoPow27N * lnErrorBoundDen

def PosShiftGePhaseGapDirectOk (n m c : Nat) : Prop :=
  sumGE n (posPhaseNatGe m c + lnPhaseExtraArg + lnDirectGapArg) lnErrQ
    (posTopX c m) (10 ^ 18)

def PosShiftLtPhaseGapDirectOk (n m c : Nat) : Prop :=
  sumGE n (posPhaseNatLt m c + lnPhaseExtraArg + lnDirectGapArg) lnErrQ
    (posTopX c m) (10 ^ 18)

def posTopXPoly (c : Nat) : List Int :=
  [((2 ^ (160 - c) : Nat) : Int) - 1, ((2 ^ (160 - c) : Nat) : Int)]

theorem eval_posTopXPoly (m c : Nat) :
    evalPoly (posTopXPoly c) (m : Int) = (posTopX c m : Int) := by
  unfold posTopXPoly posTopX
  simp only [evalPoly]
  have hpow : 0 < 2 ^ (160 - c) := Nat.pow_pos (by decide)
  have hprod : 1 ≤ (m + 1) * 2 ^ (160 - c) := Nat.succ_le_of_lt
    (Nat.mul_pos (Nat.succ_pos m) hpow)
  rw [Int.natCast_sub (n := 1) (m := (m + 1) * 2 ^ (160 - c)) hprod]
  simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one, Int.mul_zero, Int.add_zero]
  rw [Int.add_mul, Int.one_mul]
  omega

def gePhaseLowerPN (c : Nat) : List Int :=
  polyAdd
    (polyScale (((2 ^ 99 * lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)) geTN2b)
    (polyScale (((posConstNat c + lnPhaseExtraArg : Nat) : Int)) geTD2b)

def gePhaseLowerQD : List Int :=
  polyScale ((lnErrQ : Nat) : Int) geTD2b

def gePhaseLowerMarginPoly (c : Nat) : List Int :=
  expMarginPolyFast 320 (gePhaseLowerPN c) gePhaseLowerQD (posTopXPoly c) (10 ^ 18)

theorem geTD2b_pos_of_outer {m : Nat} (h1 : Sc + 46 ≤ m) (h2 : m < MHI) :
    0 < evalPoly geTD2b (m : Int) := by
  have hw1 : (56022770974786139918731938273 : Int) ≤ (m : Int) := by
    simp only [Sc] at h1
    omega
  have hw2 : (m : Int) ≤ 79228162514264337593543950335 := by
    simp only [MHI] at h2
    omega
  have h := geTD2_nonneg hw1 hw2
  rw [evalCertGeTD2] at h
  omega

theorem geTN2b_nonneg_of_outer {m : Nat} (h1 : Sc + 46 ≤ m) (h2 : m < MHI) :
    0 ≤ evalPoly geTN2b (m : Int) := by
  have hw1 : (56022770974786139918731938273 : Int) ≤ (m : Int) := by
    simp only [Sc] at h1
    omega
  have hw2 : (m : Int) ≤ 79228162514264337593543950335 := by
    simp only [MHI] at h2
    omega
  exact geTN2_nonneg hw1 hw2

theorem gePhaseLowerPN_nonneg {m c : Nat} (h1 : Sc + 46 ≤ m) (h2 : m < MHI) :
    0 ≤ evalPoly (gePhaseLowerPN c) (m : Int) := by
  have htn := geTN2b_nonneg_of_outer h1 h2
  have htd : 0 ≤ evalPoly geTD2b (m : Int) := by
    exact Int.le_of_lt (geTD2b_pos_of_outer h1 h2)
  unfold gePhaseLowerPN
  rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyScale]
  exact Int.add_nonneg
    (Int.mul_nonneg (Int.natCast_nonneg _) htn)
    (Int.mul_nonneg (Int.natCast_nonneg _) htd)

theorem gePhaseLowerQD_pos {m : Nat} (h1 : Sc + 46 ≤ m) (h2 : m < MHI) :
    0 < evalPoly gePhaseLowerQD (m : Int) := by
  unfold gePhaseLowerQD
  rw [evalPoly_polyScale]
  exact Int.mul_pos (by unfold lnErrQ QS lnErrorBoundDen; decide)
    (geTD2b_pos_of_outer h1 h2)

theorem posPhaseNatGe_cast_decomp {m c : Nat}
    (hX : 0 ≤ toInt (x1W (zWord m))) :
    ((posPhaseNatGe m c : Nat) : Int) =
      toInt (x1W (zWord m)) *
        ((lnPhaseScaleN * lnErrorBoundDen : Nat) : Int) +
          (posConstNat c : Int) := by
  have hXn : (((toInt (x1W (zWord m))).toNat : Nat) : Int) =
      toInt (x1W (zWord m)) :=
    Int.toNat_of_nonneg hX
  unfold posPhaseNatGe posConstNat
  simp only [Int.natCast_add, Int.natCast_mul, hXn]
  simp only [Int.mul_assoc]
  rw [Int.add_assoc]

theorem gePhaseLowerPN_le_phase_mul_TD {m c : Nat}
    (h1 : Sc + 46 ≤ m) (h2 : m < MHI) :
    evalPoly (gePhaseLowerPN c) (m : Int) ≤
      ((posPhaseNatGe m c + lnPhaseExtraArg : Nat) : Int) *
        evalPoly geTD2b (m : Int) := by
  have hbr := bracket_ge_lo h1 h2
  generalize hTN : evalPoly geTN2b (m : Int) = TN at hbr ⊢
  generalize hTD : evalPoly geTD2b (m : Int) = TD at hbr ⊢
  have hX := x1_nonneg_ge h1 h2
  have hphase0 := posPhaseNatGe_cast_decomp (m := m) (c := c) hX
  generalize hXV : toInt (x1W (zWord m)) = X at hbr hphase0 ⊢
  let K : Int := ((lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)
  let C : Int := (posConstNat c : Int)
  let E : Int := (lnPhaseExtraArg : Int)
  have hphase :
      ((posPhaseNatGe m c + lnPhaseExtraArg : Nat) : Int) = X * K + C + E := by
    rw [Int.natCast_add, hphase0]
  have hpn :
      evalPoly (gePhaseLowerPN c) (m : Int) = (2 ^ 99 * K) * TN + (C + E) * TD := by
    unfold gePhaseLowerPN
    rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyScale, hTN, hTD]
    simp only [K, C, E, Int.natCast_add, Int.natCast_mul, Int.natCast_pow,
      Int.mul_assoc]
    rfl
  have hAlg := ge_phase_lower_algebra
    (tn := TN) (td := TD) (x := X) (k := K) (c := C) (e := E)
    (by unfold K; exact Int.natCast_nonneg _) hbr
  rw [hpn, hphase]
  exact hAlg

theorem gePhaseLowerMargin_sound {m c : Nat}
    (h1 : Sc + 46 ≤ m) (h2 : m < MHI)
    (hcert : 0 ≤ evalPoly (gePhaseLowerMarginPoly c) (m : Int)) :
    PosShiftGePhaseDirectOk 320 m c := by
  let PN := evalPoly (gePhaseLowerPN c) (m : Int)
  let QD := evalPoly gePhaseLowerQD (m : Int)
  let P := posPhaseNatGe m c + lnPhaseExtraArg
  have hPNnon : 0 ≤ PN := by
    simpa [PN] using gePhaseLowerPN_nonneg (m := m) (c := c) h1 h2
  have hQDpos : 0 < QD := by
    simpa [QD] using gePhaseLowerQD_pos (m := m) h1 h2
  have hPNcast : (((PN.toNat : Nat) : Int)) = PN :=
    Int.toNat_of_nonneg hPNnon
  have hQDcast : (((QD.toNat : Nat) : Int)) = QD :=
    Int.toNat_of_nonneg (Int.le_of_lt hQDpos)
  have hY := eval_posTopXPoly m c
  have hsum : sumGE 320 PN.toNat QD.toNat (posTopX c m) (10 ^ 18) := by
    refine sumGE_of_expMarginPolyFast
      (n := 320) (m := m) (p := PN.toNat) (q := QD.toNat)
      (y := posTopX c m) (w := 10 ^ 18)
      (pn := gePhaseLowerPN c) (qd := gePhaseLowerQD) (yp := posTopXPoly c)
      ?_ ?_ ?_ ?_
    · simpa [gePhaseLowerMarginPoly, PN, QD] using hcert
    · exact hPNcast.symm
    · exact hQDcast.symm
    · exact hY
  have hqpos : 0 < QD.toNat := by
    apply Int.ofNat_lt.mp
    rw [hQDcast]
    exact hQDpos
  have harg : PN.toNat * lnErrQ ≤ P * QD.toNat := by
    apply Int.ofNat_le.mp
    simp only [Int.natCast_mul, hPNcast, hQDcast]
    have hPNle : PN ≤ (P : Int) * evalPoly geTD2b (m : Int) := by
      simpa [PN, P] using gePhaseLowerPN_le_phase_mul_TD (m := m) (c := c) h1 h2
    have hlnNon : 0 ≤ (lnErrQ : Int) := by
      unfold lnErrQ QS lnErrorBoundDen
      decide
    have hmul := Int.mul_le_mul_of_nonneg_right hPNle hlnNon
    have hQD :
        QD = (lnErrQ : Int) * evalPoly geTD2b (m : Int) := by
      unfold QD gePhaseLowerQD
      rw [evalPoly_polyScale]
    rw [hQD]
    simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hmul
  unfold PosShiftGePhaseDirectOk
  exact sumGE_arg_mono (q' := QD.toNat) hqpos harg hsum

theorem gePhaseLowerMarginVal_sound {m c : Nat}
    (h1 : Sc + 46 ≤ m) (h2 : m < MHI)
    (hcert : 0 ≤ expMarginVal 320 (evalPoly (gePhaseLowerPN c) (m : Int))
      (evalPoly gePhaseLowerQD (m : Int)) (evalPoly (posTopXPoly c) (m : Int))
      (((10 ^ 18 : Nat) : Int))) :
    PosShiftGePhaseDirectOk 320 m c := by
  let PN := evalPoly (gePhaseLowerPN c) (m : Int)
  let QD := evalPoly gePhaseLowerQD (m : Int)
  let P := posPhaseNatGe m c + lnPhaseExtraArg
  have hPNnon : 0 ≤ PN := by
    simpa [PN] using gePhaseLowerPN_nonneg (m := m) (c := c) h1 h2
  have hQDpos : 0 < QD := by
    simpa [QD] using gePhaseLowerQD_pos (m := m) h1 h2
  have hPNcast : (((PN.toNat : Nat) : Int)) = PN :=
    Int.toNat_of_nonneg hPNnon
  have hQDcast : (((QD.toNat : Nat) : Int)) = QD :=
    Int.toNat_of_nonneg (Int.le_of_lt hQDpos)
  have hY := eval_posTopXPoly m c
  have hsum : sumGE 320 PN.toNat QD.toNat (posTopX c m) (10 ^ 18) := by
    refine sumGE_of_expMarginVal
      (n := 320) (p := PN.toNat) (q := QD.toNat)
      (y := posTopX c m) (w := 10 ^ 18) ?_
    rw [hPNcast, hQDcast, ← hY]
    exact hcert
  have hqpos : 0 < QD.toNat := by
    apply Int.ofNat_lt.mp
    rw [hQDcast]
    exact hQDpos
  have harg : PN.toNat * lnErrQ ≤ P * QD.toNat := by
    apply Int.ofNat_le.mp
    simp only [Int.natCast_mul, hPNcast, hQDcast]
    have hPNle : PN ≤ (P : Int) * evalPoly geTD2b (m : Int) := by
      simpa [PN, P] using gePhaseLowerPN_le_phase_mul_TD (m := m) (c := c) h1 h2
    have hlnNon : 0 ≤ (lnErrQ : Int) := by
      unfold lnErrQ QS lnErrorBoundDen
      decide
    have hmul := Int.mul_le_mul_of_nonneg_right hPNle hlnNon
    have hQD :
        QD = (lnErrQ : Int) * evalPoly geTD2b (m : Int) := by
      unfold QD gePhaseLowerQD
      rw [evalPoly_polyScale]
    rw [hQD]
    simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hmul
  unfold PosShiftGePhaseDirectOk
  exact sumGE_arg_mono (q' := QD.toNat) hqpos harg hsum

def gePhaseLowerPNMin (c : Nat) : List Int :=
  polyAdd
    (polyScale (((2 ^ 99 * lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)) geTN2b)
    (polyScale (((posConstNat c + minPosAvail : Nat) : Int)) geTD2b)

def gePhaseLowerMarginPolyMin (c : Nat) : List Int :=
  expMarginPolyFast 320 (gePhaseLowerPNMin c) gePhaseLowerQD (posTopXPoly c) (10 ^ 18)

theorem gePhaseLowerPNMin_nonneg {m c : Nat} (h1 : Sc + 46 ≤ m) (h2 : m < MHI) :
    0 ≤ evalPoly (gePhaseLowerPNMin c) (m : Int) := by
  have htn := geTN2b_nonneg_of_outer h1 h2
  have htd : 0 ≤ evalPoly geTD2b (m : Int) := by
    exact Int.le_of_lt (geTD2b_pos_of_outer h1 h2)
  unfold gePhaseLowerPNMin
  rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyScale]
  exact Int.add_nonneg
    (Int.mul_nonneg (Int.natCast_nonneg _) htn)
    (Int.mul_nonneg (Int.natCast_nonneg _) htd)

theorem gePhaseLowerPNMin_le_phase_mul_TD {m c : Nat}
    (h1 : Sc + 46 ≤ m) (h2 : m < MHI) :
    evalPoly (gePhaseLowerPNMin c) (m : Int) ≤
      ((posPhaseNatGe m c + minPosAvail : Nat) : Int) *
        evalPoly geTD2b (m : Int) := by
  have hbr := bracket_ge_lo h1 h2
  generalize hTN : evalPoly geTN2b (m : Int) = TN at hbr ⊢
  generalize hTD : evalPoly geTD2b (m : Int) = TD at hbr ⊢
  have hX := x1_nonneg_ge h1 h2
  have hphase0 := posPhaseNatGe_cast_decomp (m := m) (c := c) hX
  generalize hXV : toInt (x1W (zWord m)) = X at hbr hphase0 ⊢
  let K : Int := ((lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)
  let C : Int := (posConstNat c : Int)
  let E : Int := (minPosAvail : Int)
  have hphase :
      ((posPhaseNatGe m c + minPosAvail : Nat) : Int) = X * K + C + E := by
    rw [Int.natCast_add, hphase0]
  have hpn :
      evalPoly (gePhaseLowerPNMin c) (m : Int) = (2 ^ 99 * K) * TN + (C + E) * TD := by
    unfold gePhaseLowerPNMin
    rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyScale, hTN, hTD]
    simp only [K, C, E, Int.natCast_add, Int.natCast_mul, Int.natCast_pow,
      Int.mul_assoc]
    rfl
  have hAlg := ge_phase_lower_algebra
    (tn := TN) (td := TD) (x := X) (k := K) (c := C) (e := E)
    (by unfold K; exact Int.natCast_nonneg _) hbr
  rw [hpn, hphase]
  exact hAlg

theorem gePhaseLowerMarginValMin_sound {m c : Nat}
    (h1 : Sc + 46 ≤ m) (h2 : m < MHI)
    (hcert : 0 ≤ expMarginVal 320 (evalPoly (gePhaseLowerPNMin c) (m : Int))
      (evalPoly gePhaseLowerQD (m : Int)) (evalPoly (posTopXPoly c) (m : Int))
      (((10 ^ 18 : Nat) : Int))) :
    PosShiftGeMinPhaseDirectOk 320 m c := by
  let PN := evalPoly (gePhaseLowerPNMin c) (m : Int)
  let QD := evalPoly gePhaseLowerQD (m : Int)
  let P := posPhaseNatGe m c + minPosAvail
  have hPNnon : 0 ≤ PN := by
    simpa [PN] using gePhaseLowerPNMin_nonneg (m := m) (c := c) h1 h2
  have hQDpos : 0 < QD := by
    simpa [QD] using gePhaseLowerQD_pos (m := m) h1 h2
  have hPNcast : (((PN.toNat : Nat) : Int)) = PN :=
    Int.toNat_of_nonneg hPNnon
  have hQDcast : (((QD.toNat : Nat) : Int)) = QD :=
    Int.toNat_of_nonneg (Int.le_of_lt hQDpos)
  have hY := eval_posTopXPoly m c
  have hsum : sumGE 320 PN.toNat QD.toNat (posTopX c m) (10 ^ 18) := by
    refine sumGE_of_expMarginVal
      (n := 320) (p := PN.toNat) (q := QD.toNat)
      (y := posTopX c m) (w := 10 ^ 18) ?_
    rw [hPNcast, hQDcast, ← hY]
    exact hcert
  have hqpos : 0 < QD.toNat := by
    apply Int.ofNat_lt.mp
    rw [hQDcast]
    exact hQDpos
  have harg : PN.toNat * lnErrQ ≤ P * QD.toNat := by
    apply Int.ofNat_le.mp
    simp only [Int.natCast_mul, hPNcast, hQDcast]
    have hPNle : PN ≤ (P : Int) * evalPoly geTD2b (m : Int) := by
      simpa [PN, P] using gePhaseLowerPNMin_le_phase_mul_TD (m := m) (c := c) h1 h2
    have hlnNon : 0 ≤ (lnErrQ : Int) := by
      unfold lnErrQ QS lnErrorBoundDen
      decide
    have hmul := Int.mul_le_mul_of_nonneg_right hPNle hlnNon
    have hQD :
        QD = (lnErrQ : Int) * evalPoly geTD2b (m : Int) := by
      unfold QD gePhaseLowerQD
      rw [evalPoly_polyScale]
    rw [hQD]
    simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hmul
  unfold PosShiftGeMinPhaseDirectOk
  exact sumGE_arg_mono (q' := QD.toNat) hqpos harg hsum

def PosShiftTopDirectOk (n m c : Nat) : Prop :=
  sumGE n (lnErrArg (toInt (lnTail (evmSub 160 c) m))) lnErrQ
    (posTopX c m) (10 ^ 18)

def expSumState (p q : Nat) : Nat → Nat × Nat × Nat
  | 0 => (1, 1, 1)
  | n + 1 =>
      let s := expSumState p q n
      let pp := s.2.2 * p
      ((n + 1) * q * s.1 + pp, (n + 1) * q * s.2.1, pp)

theorem expSumState_spec (p q : Nat) :
    ∀ n, expSumState p q n = (expNum n p q, fact n * q ^ n, p ^ n)
  | 0 => by
      simp [expSumState, expNum, fact]
  | n + 1 => by
      simp [expSumState, expSumState_spec p q n, expNum, fact, Nat.pow_succ,
        Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

def expSumStateGo (p q : Nat) : Nat → Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | 0, _i, e, d, pp => (e, d, pp)
  | k + 1, i, e, d, pp =>
      let pp' := pp * p
      expSumStateGo p q k (i + 1) ((i + 1) * q * e + pp') ((i + 1) * q * d) pp'

theorem expSumStateGo_spec (p q : Nat) :
    ∀ k i e d pp,
      expSumState p q i = (e, d, pp) →
        expSumStateGo p q k i e d pp = expSumState p q (i + k)
  | 0, i, e, d, pp, h => by
      simp [expSumStateGo, h]
  | k + 1, i, e, d, pp, h => by
      simp only [expSumStateGo]
      let pp' := pp * p
      have hnext : expSumState p q (i + 1) =
          ((i + 1) * q * e + pp', (i + 1) * q * d, pp') := by
        rw [show i + 1 = Nat.succ i by omega]
        simp [expSumState, h, pp']
      have ih := expSumStateGo_spec p q k (i + 1)
        ((i + 1) * q * e + pp') ((i + 1) * q * d) pp' hnext
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

def expSumStateFast (p q n : Nat) : Nat × Nat × Nat :=
  expSumStateGo p q n 0 1 1 1

theorem expSumStateFast_eq (p q n : Nat) :
    expSumStateFast p q n = expSumState p q n := by
  unfold expSumStateFast
  have h := expSumStateGo_spec p q n 0 1 1 1 (by simp [expSumState])
  simpa using h

def sumGEB (n p q y w : Nat) : Bool :=
  let s := expSumState p q n
  decide (y * s.2.1 ≤ s.1 * w)

theorem sumGE_of_sumGEB {n p q y w : Nat} (h : sumGEB n p q y w = true) :
    sumGE n p q y w := by
  unfold sumGEB at h
  simpa [sumGE, expSumState_spec p q n] using (of_decide_eq_true h)

structure PosShiftDirectCell where
  c : Nat
  lo : Nat
  hi : Nat
  n : Nat

def PosShiftDirectCell.Ok (cell : PosShiftDirectCell) : Prop :=
  MLO ≤ cell.lo ∧ cell.lo ≤ cell.hi ∧ cell.hi < MHI ∧ cell.c < 160 ∧
    sumGE cell.n (lnErrArg (toInt (lnTail (evmSub 160 cell.c) cell.lo))) lnErrQ
      (posTopX cell.c cell.hi) (10 ^ 18)

def PosShiftDirectCell.okB (cell : PosShiftDirectCell) : Bool :=
  decide (MLO ≤ cell.lo) &&
    decide (cell.lo ≤ cell.hi) &&
      decide (cell.hi < MHI) &&
        decide (cell.c < 160) &&
          decide (sumGE cell.n
            (lnErrArg (toInt (lnTail (evmSub 160 cell.c) cell.lo))) lnErrQ
            (posTopX cell.c cell.hi) (10 ^ 18))

def PosShiftDirectCell.Covers (cell : PosShiftDirectCell) (m c : Nat) : Prop :=
  c = cell.c ∧ cell.lo ≤ m ∧ m ≤ cell.hi

def PosShiftDirectCell.coversB (cell : PosShiftDirectCell) (m c : Nat) : Bool :=
  decide (c = cell.c) && decide (cell.lo ≤ m) && decide (m ≤ cell.hi)

theorem PosShiftDirectCell.ok_of_okB {cell : PosShiftDirectCell}
    (h : cell.okB = true) : cell.Ok := by
  unfold PosShiftDirectCell.okB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, hlohi⟩, hhi⟩, hc⟩, hsum⟩ := h
  exact ⟨hlo, hlohi, hhi, hc, hsum⟩

theorem PosShiftDirectCell.covers_of_coversB {cell : PosShiftDirectCell} {m c : Nat}
    (h : cell.coversB m c = true) : cell.Covers m c := by
  unfold PosShiftDirectCell.coversB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hc, hlo⟩, hhi⟩ := h
  exact ⟨hc, hlo, hhi⟩

def directCellsCoverB (cells : List PosShiftDirectCell) (m c : Nat) : Bool :=
  cells.any (fun cell => cell.okB && cell.coversB m c)

def directCellsCover320B (cells : List PosShiftDirectCell) (m c : Nat) : Bool :=
  cells.any (fun cell => decide (cell.n = 320) && cell.okB && cell.coversB m c)

def localDirectCell (m c : Nat) : PosShiftDirectCell :=
  { c := c, lo := max MLO (m - 16), hi := m, n := 320 }

def localDirectCertB (m c : Nat) : Bool :=
  (localDirectCell m c).okB

def residueOrDirectCertB (cells : List PosShiftDirectCell) (m c : Nat) (r : Int) : Bool :=
  residueGapOkB m c r || directCellsCover320B cells m c

def residueOrLocalDirectCertB (m c : Nat) (r : Int) : Bool :=
  residueGapOkB m c r || localDirectCertB m c

def posShiftDirectCells : List PosShiftDirectCell := []

theorem posTopX_mono_m {c m hi : Nat} (hm : m ≤ hi) :
    posTopX c m ≤ posTopX c hi := by
  unfold posTopX
  have hmul : (m + 1) * 2 ^ (160 - c) ≤ (hi + 1) * 2 ^ (160 - c) :=
    Nat.mul_le_mul_right _ (by omega)
  have hpos : 0 < (m + 1) * 2 ^ (160 - c) :=
    Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by decide))
  omega

theorem lnTail_mono_m {c lo m hi : Nat}
    (hlo : MLO ≤ lo) (hlom : lo ≤ m) (hmhi : m ≤ hi) (hhi : hi < MHI)
    (hc : c < 256) :
    toInt (lnTail (evmSub 160 c) lo) ≤ toInt (lnTail (evmSub 160 c) m) := by
  have hmhi' : m < MHI := by omega
  have hw := ln2k_bound (c := c) hc
  exact tail_mono hlo hlom hmhi' hw.1 hw.2

theorem PosShiftDirectCell.sound {cell : PosShiftDirectCell} {m c : Nat}
    (hok : cell.Ok) (hcov : cell.Covers m c) :
    PosShiftTopDirectOk cell.n m c := by
  obtain ⟨hlo, hlohi, hhi, _hc, hsum⟩ := hok
  obtain ⟨hc_eq, hmlo, hmhi⟩ := hcov
  subst c
  unfold PosShiftTopDirectOk
  refine sumGE_exact_mono (n := cell.n)
    (p0 := lnErrArg (toInt (lnTail (evmSub 160 cell.c) cell.lo)))
    (p := lnErrArg (toInt (lnTail (evmSub 160 cell.c) m)))
    (y0 := posTopX cell.c cell.hi) (y := posTopX cell.c m) ?_ ?_ hsum
  · exact lnErrArg_mono (lnTail_mono_m hlo hmlo hmhi hhi (by omega))
  · exact posTopX_mono_m hmhi

theorem direct_of_cells_cover {cells : List PosShiftDirectCell} {m c : Nat}
    (h : directCellsCoverB cells m c = true) :
    ∃ n, PosShiftTopDirectOk n m c := by
  unfold directCellsCoverB at h
  rw [List.any_eq_true] at h
  obtain ⟨cell, _hmem, hokcov⟩ := h
  simp only [Bool.and_eq_true] at hokcov
  obtain ⟨hok, hcov⟩ := hokcov
  exact ⟨cell.n, PosShiftDirectCell.sound
    (PosShiftDirectCell.ok_of_okB hok)
    (PosShiftDirectCell.covers_of_coversB hcov)⟩

theorem direct320_of_cells_cover {cells : List PosShiftDirectCell} {m c : Nat}
    (h : directCellsCover320B cells m c = true) :
    PosShiftTopDirectOk 320 m c := by
  unfold directCellsCover320B at h
  rw [List.any_eq_true] at h
  obtain ⟨cell, _hmem, hcert⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcert
  obtain ⟨⟨hn, hok⟩, hcov⟩ := hcert
  have hs := PosShiftDirectCell.sound
    (PosShiftDirectCell.ok_of_okB hok)
    (PosShiftDirectCell.covers_of_coversB hcov)
  simpa [hn] using hs

theorem residue_or_direct_of_certB {cells : List PosShiftDirectCell} {m c : Nat} {r : Int}
    (hc : c ≤ 160) (h : residueOrDirectCertB cells m c r = true) :
    PosShiftResidueOk m c r ∨ PosShiftTopDirectOk 320 m c := by
  unfold residueOrDirectCertB at h
  simp only [Bool.or_eq_true] at h
  rcases h with hres | hdir
  · exact Or.inl (PosShiftResidueOk_of_gapB hc hres)
  · exact Or.inr (direct320_of_cells_cover hdir)

theorem residue_or_direct_of_local_certB {m c : Nat} {r : Int}
    (hc : c ≤ 160) (h : residueOrLocalDirectCertB m c r = true) :
    PosShiftResidueOk m c r ∨ PosShiftTopDirectOk 320 m c := by
  unfold residueOrLocalDirectCertB localDirectCertB at h
  simp only [Bool.or_eq_true] at h
  rcases h with hres | hdir
  · exact Or.inl (PosShiftResidueOk_of_gapB hc hres)
  · have hokCell := PosShiftDirectCell.ok_of_okB hdir
    have hlohi := hokCell.2.1
    have hcell : (localDirectCell m c).Covers m c := by
      simpa [localDirectCell, PosShiftDirectCell.Covers] using
        (⟨rfl, hlohi, Nat.le_refl m⟩ :
          c = c ∧ (localDirectCell m c).lo ≤ m ∧ m ≤ (localDirectCell m c).hi)
    have hs := PosShiftDirectCell.sound hokCell hcell
    have hs320 : PosShiftTopDirectOk 320 m c := by
      simpa [localDirectCell] using hs
    exact Or.inr hs320

theorem posPhaseNatGe_mono_m {lo m c : Nat}
    (hlo : Sc ≤ lo) (hlom : lo ≤ m) (hmhi : m < MHI) :
    posPhaseNatGe lo c ≤ posPhaseNatGe m c := by
  unfold posPhaseNatGe
  have hmlo : MLO ≤ lo := by
    simp only [Sc, MLO] at hlo ⊢
    omega
  have hx := LnGeneratedModel.r1_mono hmlo hlom hmhi
  have hxNat : (toInt (x1W (zWord lo))).toNat ≤
      (toInt (x1W (zWord m))).toNat :=
    Int.toNat_le_toNat hx
  have hmul : (toInt (x1W (zWord lo))).toNat * lnPhaseScaleN * lnErrorBoundDen ≤
      (toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen := by
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hxNat)
  omega

theorem posNegXNat_antitone_m {lo m : Nat}
    (hlo : MLO ≤ lo) (hlom : lo ≤ m) (hmhi : m < MHI) :
    posNegXNat m ≤ posNegXNat lo := by
  unfold posNegXNat
  have hx := LnGeneratedModel.r1_mono hlo hlom hmhi
  have hneg : -toInt (x1W (zWord m)) ≤ -toInt (x1W (zWord lo)) := by
    omega
  have hn : (-toInt (x1W (zWord m))).toNat ≤
      (-toInt (x1W (zWord lo))).toNat :=
    Int.toNat_le_toNat hneg
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hn)

theorem posPhaseNatLt_mono_m {lo m c : Nat}
    (hlo : MLO ≤ lo) (hlom : lo ≤ m) (hmhi : m < MHI) :
    posPhaseNatLt lo c ≤ posPhaseNatLt m c := by
  unfold posPhaseNatLt
  have hn := posNegXNat_antitone_m (lo := lo) (m := m) hlo hlom hmhi
  exact Nat.sub_le_sub_left hn (posConstNat c)

def gePhaseCellOkB (lo hi c : Nat) : Bool :=
  decide (Sc ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          sumGEB 320 (posPhaseNatGe lo c + lnPhaseExtraArg) lnErrQ
            (posTopX c hi) (10 ^ 18)

def ltPhaseCellOkB (lo hi c : Nat) : Bool :=
  decide (MLO ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < Sc) &&
        decide (c < 160) &&
          sumGEB 320 (posPhaseNatLt lo c + lnPhaseExtraArg) lnErrQ
            (posTopX c hi) (10 ^ 18)

def gePhaseGapCellOkB (lo hi c : Nat) : Bool :=
  decide (Sc ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          sumGEB 320 (posPhaseNatGe lo c + lnPhaseExtraArg + lnDirectGapArg)
            lnErrQ (posTopX c hi) (10 ^ 18)

def ltPhaseGapCellOkB (lo hi c : Nat) : Bool :=
  decide (MLO ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < Sc) &&
        decide (c < 160) &&
          sumGEB 320 (posPhaseNatLt lo c + lnPhaseExtraArg + lnDirectGapArg)
            lnErrQ (posTopX c hi) (10 ^ 18)

def geTopBudgetCoarseCellOkB (lo hi c : Nat) : Bool :=
  decide (Sc ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          decide (wadRayNum (posTopX c hi) * (posBaseWGe c * lnErrQ) ≤
            (posBaseYGe lo c * (lnErrQ + minPosAvail)) * wadRayStrictDen)

def ltTopBudgetCoarseCellOkB (lo hi c : Nat) : Bool :=
  decide (MLO ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < Sc) &&
        decide (c < 160) &&
          decide (wadRayNum (posTopX c hi) * (posBaseWLt c * lnErrQ) ≤
            (posBaseYLt lo c * (lnErrQ + minPosAvail)) * wadRayStrictDen)

def geTopBudgetRunCellOkB (lo hi c : Nat) : Bool :=
  decide (Sc ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          let rlo := toInt (lnTail (evmSub 160 c) lo)
          decide (posAccI hi c < (rlo + 1) * twoPow72I) &&
            decide (wadRayNum (posTopX c hi) * (posBaseWGe c * lnErrQ) ≤
              (posBaseYGe lo c * (lnErrQ + posAvailGe hi c rlo)) * wadRayStrictDen)

def ltTopBudgetRunCellOkB (lo hi c : Nat) : Bool :=
  decide (MLO ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < Sc) &&
        decide (c < 160) &&
          let rlo := toInt (lnTail (evmSub 160 c) lo)
          decide (posAccI hi c < (rlo + 1) * twoPow72I) &&
            decide (wadRayNum (posTopX c hi) * (posBaseWLt c * lnErrQ) ≤
              (posBaseYLt lo c * (lnErrQ + posAvailLt hi c rlo)) * wadRayStrictDen)

theorem gePhaseCell_sound {lo hi m c : Nat} (h : gePhaseCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGePhaseDirectOk 320 m c := by
  unfold gePhaseCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, _hc⟩, hsum⟩ := h
  unfold PosShiftGePhaseDirectOk
  refine sumGE_exact_mono (n := 320)
    (p0 := posPhaseNatGe lo c + lnPhaseExtraArg)
    (p := posPhaseNatGe m c + lnPhaseExtraArg)
    (y0 := posTopX c hi) (y := posTopX c m) ?_ ?_ (sumGE_of_sumGEB hsum)
  · exact Nat.add_le_add_right
      (posPhaseNatGe_mono_m hlo hlom (by omega)) lnPhaseExtraArg
  · exact posTopX_mono_m hmhi

theorem ltPhaseCell_sound {lo hi m c : Nat} (h : ltPhaseCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftLtPhaseDirectOk 320 m c := by
  unfold ltPhaseCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, _hc⟩, hsum⟩ := h
  unfold PosShiftLtPhaseDirectOk
  refine sumGE_exact_mono (n := 320)
    (p0 := posPhaseNatLt lo c + lnPhaseExtraArg)
    (p := posPhaseNatLt m c + lnPhaseExtraArg)
    (y0 := posTopX c hi) (y := posTopX c m) ?_ ?_ (sumGE_of_sumGEB hsum)
  · exact Nat.add_le_add_right
      (posPhaseNatLt_mono_m hlo hlom (by simp only [Sc, MHI] at hhi ⊢; omega))
      lnPhaseExtraArg
  · exact posTopX_mono_m hmhi

theorem gePhaseGapCell_sound {lo hi m c : Nat}
    (h : gePhaseGapCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGePhaseGapDirectOk 320 m c := by
  unfold gePhaseGapCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, _hc⟩, hsum⟩ := h
  unfold PosShiftGePhaseGapDirectOk
  refine sumGE_exact_mono (n := 320)
    (p0 := posPhaseNatGe lo c + lnPhaseExtraArg + lnDirectGapArg)
    (p := posPhaseNatGe m c + lnPhaseExtraArg + lnDirectGapArg)
    (y0 := posTopX c hi) (y := posTopX c m) ?_ ?_ (sumGE_of_sumGEB hsum)
  · exact Nat.add_le_add_right
      (Nat.add_le_add_right (posPhaseNatGe_mono_m hlo hlom (by omega))
        lnPhaseExtraArg) lnDirectGapArg
  · exact posTopX_mono_m hmhi

theorem ltPhaseGapCell_sound {lo hi m c : Nat}
    (h : ltPhaseGapCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftLtPhaseGapDirectOk 320 m c := by
  unfold ltPhaseGapCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, _hc⟩, hsum⟩ := h
  unfold PosShiftLtPhaseGapDirectOk
  refine sumGE_exact_mono (n := 320)
    (p0 := posPhaseNatLt lo c + lnPhaseExtraArg + lnDirectGapArg)
    (p := posPhaseNatLt m c + lnPhaseExtraArg + lnDirectGapArg)
    (y0 := posTopX c hi) (y := posTopX c m) ?_ ?_ (sumGE_of_sumGEB hsum)
  · exact Nat.add_le_add_right
      (Nat.add_le_add_right
        (posPhaseNatLt_mono_m hlo hlom (by simp only [Sc, MHI] at hhi ⊢; omega))
        lnPhaseExtraArg) lnDirectGapArg
  · exact posTopX_mono_m hmhi

def phaseSearchFuel : Nat := 128
def phaseCoverFuel : Nat := 20000

def lnErrorHardMantissa : Nat := 39770979022059719714796403827

def phaseSearchMax (fuel : Nat) (ok : Nat → Bool) (lo hi best : Nat) : Nat :=
  match fuel with
  | 0 => best
  | fuel + 1 =>
      if lo ≤ hi then
        let mid := (lo + hi) / 2
        if ok mid then
          phaseSearchMax fuel ok (mid + 1) hi mid
        else
          phaseSearchMax fuel ok lo (mid - 1) best
      else
        best

def gePhaseCoverB : Nat → Nat → Nat → Nat → Bool
  | 0, _c, lo, hi => decide (hi < lo)
  | fuel + 1, c, lo, hi =>
      if hi < lo then
        true
      else
        let mx := phaseSearchMax phaseSearchFuel (fun h => gePhaseCellOkB lo h c)
          lo hi (lo - 1)
        decide (lo ≤ mx) &&
          decide (mx ≤ hi) &&
            gePhaseCellOkB lo mx c &&
              gePhaseCoverB fuel c (mx + 1) hi

def ltPhaseCoverB : Nat → Nat → Nat → Nat → Bool
  | 0, _c, lo, hi => decide (hi < lo)
  | fuel + 1, c, lo, hi =>
      if hi < lo then
        true
      else if lo = lnErrorHardMantissa then
        ltPhaseCoverB fuel c (lo + 1) hi
      else
        let mx := phaseSearchMax phaseSearchFuel (fun h => ltPhaseCellOkB lo h c)
          lo hi (lo - 1)
        decide (lo ≤ mx) &&
          decide (mx ≤ hi) &&
            ltPhaseCellOkB lo mx c &&
              ltPhaseCoverB fuel c (mx + 1) hi

theorem gePhaseCoverB_sound {fuel c lo hi m : Nat}
    (h : gePhaseCoverB fuel c lo hi = true) (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGePhaseDirectOk 320 m c := by
  revert lo
  induction fuel with
  | zero =>
      intro lo h hlom
      unfold gePhaseCoverB at h
      simp only [decide_eq_true_eq] at h
      omega
  | succ fuel ih =>
      intro lo h hlom
      unfold gePhaseCoverB at h
      by_cases hdone : hi < lo
      · rw [if_pos hdone] at h
        omega
      · rw [if_neg hdone] at h
        let mx := phaseSearchMax phaseSearchFuel (fun h => gePhaseCellOkB lo h c)
          lo hi (lo - 1)
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨hlmx, hmxhi⟩, hcell⟩, hrest⟩ := h
        by_cases hleft : m ≤ mx
        · exact gePhaseCell_sound hcell hlom hleft
        · exact ih (lo := mx + 1) hrest (by omega)

theorem ltPhaseCoverB_sound {fuel c lo hi m : Nat}
    (h : ltPhaseCoverB fuel c lo hi = true) (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    m = lnErrorHardMantissa ∨ PosShiftLtPhaseDirectOk 320 m c := by
  revert lo
  induction fuel with
  | zero =>
      intro lo h hlom
      unfold ltPhaseCoverB at h
      simp only [decide_eq_true_eq] at h
      omega
  | succ fuel ih =>
      intro lo h hlom
      unfold ltPhaseCoverB at h
      by_cases hdone : hi < lo
      · rw [if_pos hdone] at h
        omega
      · rw [if_neg hdone] at h
        by_cases hhard : lo = lnErrorHardMantissa
        · rw [if_pos hhard] at h
          by_cases hm : m = lo
          · exact Or.inl (by omega)
          · exact ih (lo := lo + 1) h (by omega)
        · rw [if_neg hhard] at h
          let mx := phaseSearchMax phaseSearchFuel (fun h => ltPhaseCellOkB lo h c)
            lo hi (lo - 1)
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨⟨hlmx, hmxhi⟩, hcell⟩, hrest⟩ := h
          by_cases hleft : m ≤ mx
          · exact Or.inr (ltPhaseCell_sound hcell hlom hleft)
          · exact ih (lo := mx + 1) hrest (by omega)

structure PhaseCell where
  lo : Nat
  hi : Nat

def gePhaseCellListCoverB (c : Nat) : Nat → Nat → List PhaseCell → Bool
  | lo, hi, [] => decide (hi < lo)
  | lo, hi, cell :: cells =>
      decide (cell.lo = lo) &&
        decide (lo ≤ cell.hi) &&
          decide (cell.hi ≤ hi) &&
            gePhaseCellOkB cell.lo cell.hi c &&
              gePhaseCellListCoverB c (cell.hi + 1) hi cells

def ltPhaseCellListCoverB (c : Nat) : Nat → Nat → List PhaseCell → Bool
  | lo, hi, [] => decide (hi < lo)
  | lo, hi, cell :: cells =>
      decide (cell.lo = lo) &&
        decide (lo ≤ cell.hi) &&
          decide (cell.hi ≤ hi) &&
            ltPhaseCellOkB cell.lo cell.hi c &&
              ltPhaseCellListCoverB c (cell.hi + 1) hi cells

theorem gePhaseCellListCoverB_sound {cells : List PhaseCell} {c lo hi m : Nat}
    (h : gePhaseCellListCoverB c lo hi cells = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGePhaseDirectOk 320 m c := by
  induction cells generalizing lo with
  | nil =>
      unfold gePhaseCellListCoverB at h
      have hlt : hi < lo := of_decide_eq_true h
      omega
  | cons cell cells ih =>
      unfold gePhaseCellListCoverB at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hlo, _hlohi⟩, _hhihi⟩, hok⟩, hrest⟩ := h
      by_cases hmcell : m ≤ cell.hi
      · exact gePhaseCell_sound hok (by omega) hmcell
      · exact ih hrest (by omega)

theorem ltPhaseCellListCoverB_sound {cells : List PhaseCell} {c lo hi m : Nat}
    (h : ltPhaseCellListCoverB c lo hi cells = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftLtPhaseDirectOk 320 m c := by
  induction cells generalizing lo with
  | nil =>
      unfold ltPhaseCellListCoverB at h
      have hlt : hi < lo := of_decide_eq_true h
      omega
  | cons cell cells ih =>
      unfold ltPhaseCellListCoverB at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hlo, _hlohi⟩, _hhihi⟩, hok⟩, hrest⟩ := h
      by_cases hmcell : m ≤ cell.hi
      · exact ltPhaseCell_sound hok (by omega) hmcell
      · exact ih hrest (by omega)

theorem posPhaseI_le_of_floor {m c : Nat} {r : Int} (hc : c ≤ 160)
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI < (r + 1) * 2 ^ 72) :
    posPhaseI m c ≤ (r + 1) * twoPow99I - twoPow27I := by
  have h := phase_lt_scaled_le hr
  change (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI) * twoPow27I ≤ ((r + 1) * twoPow72I - 1) * twoPow27I at h
  have hVs := v_scale_pos (toInt (x1W (zWord m))) c hc
  have hVs' :
      (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
          lnBiasI) * twoPow27I =
        toInt (x1W (zWord m)) * lnPhaseScaleI +
          ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
            lnBiasI * twoPow27I := by
    simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
  rw [hVs'] at h
  have er : ((r + 1) * twoPow72I - 1) * twoPow27I =
      (r + 1) * twoPow99I - twoPow27I := by
    unfold twoPow72I twoPow27I twoPow99I
    rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
      by decide]
    omega
  rw [er] at h
  simpa [posPhaseI, lnPhaseScaleI, twoPow27I, lnBiasI] using h

theorem posPhaseNatGe_cast {m c : Nat}
    (hX : 0 ≤ toInt (x1W (zWord m))) :
    ((posPhaseNatGe m c : Nat) : Int) =
      posPhaseI m c * (lnErrorBoundDen : Int) := by
  have hXn : (((toInt (x1W (zWord m))).toNat : Nat) : Int) =
      toInt (x1W (zWord m)) :=
    Int.toNat_of_nonneg hX
  have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
    unfold twoPow27N twoPow27I lnBiasI
    decide +kernel
  have hLc : (((160 - c) * (LN2c * twoPow27N) : Nat) : Int) =
      ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) := by
    simp only [Int.natCast_mul]
    unfold twoPow27N twoPow27I
    rfl
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
  have hN : (((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
      (((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I)) *
        (1000000000 : Int) := by
    rw [show (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
        ((160 - c) * (LN2c * twoPow27N)) * lnErrorBoundDen by
          simp only [Nat.mul_assoc]]
    simp only [Int.natCast_mul, hLc, hden]
  unfold posPhaseNatGe posPhaseI
  simp only [Int.natCast_add, Int.natCast_mul, hXn, hBc, hN, hden, hscale]
  rw [Int.add_mul, Int.add_mul]

theorem posConstNat_cast (c : Nat) :
    ((posConstNat c : Nat) : Int) =
      (((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
        lnBiasI * twoPow27I) * (lnErrorBoundDen : Int) := by
  have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
    unfold twoPow27N twoPow27I lnBiasI
    decide +kernel
  have hLc : (((160 - c) * (LN2c * twoPow27N) : Nat) : Int) =
      ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) := by
    simp only [Int.natCast_mul]
    unfold twoPow27N twoPow27I
    rfl
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  have hN : (((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
      (((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I)) *
        (1000000000 : Int) := by
    rw [show (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
        ((160 - c) * (LN2c * twoPow27N)) * lnErrorBoundDen by
          simp only [Nat.mul_assoc]]
    simp only [Int.natCast_mul, hLc, hden]
  unfold posConstNat
  simp only [Int.natCast_add, Int.natCast_mul, hBc, hN, hden]
  rw [Int.add_mul]

theorem posNegXNat_cast {m : Nat}
    (hX : toInt (x1W (zWord m)) ≤ 0) :
    ((posNegXNat m : Nat) : Int) =
      (-toInt (x1W (zWord m)) * lnPhaseScaleI) * (lnErrorBoundDen : Int) := by
  have hXn : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) =
      -toInt (x1W (zWord m)) :=
    Int.toNat_of_nonneg (by omega)
  have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
  unfold posNegXNat
  simp only [Int.natCast_mul, hXn, hscale]

theorem posPhaseNatLt_cast {m c : Nat}
    (hX : toInt (x1W (zWord m)) ≤ 0)
    (hneg : posNegXNat m ≤ posConstNat c) :
    ((posPhaseNatLt m c : Nat) : Int) =
      posPhaseI m c * (lnErrorBoundDen : Int) := by
  have hconst := posConstNat_cast c
  have hnegc := posNegXNat_cast (m := m) hX
  have hsub : ((posConstNat c - posNegXNat m : Nat) : Int) =
      ((posConstNat c : Nat) : Int) - ((posNegXNat m : Nat) : Int) := by
    omega
  unfold posPhaseNatLt
  rw [hsub, hconst, hnegc]
  unfold posPhaseI
  rw [Int.add_mul, Int.add_mul, Int.add_mul]
  rw [show (-toInt (x1W (zWord m)) * lnPhaseScaleI) *
      (lnErrorBoundDen : Int) =
        -(toInt (x1W (zWord m)) * lnPhaseScaleI * (lnErrorBoundDen : Int)) by
        rw [Int.neg_mul, Int.neg_mul]]
  omega

theorem posPhaseNatGe_le_lnErrArg {m c : Nat} {r : Int}
    (hge : Sc ≤ m) (hmhi : m < MHI) (hc : c ≤ 160)
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI < (r + 1) * 2 ^ 72)
    (hr0 : -1 ≤ r) :
    posPhaseNatGe m c ≤ lnErrArg r := by
  have hX := x1_nonneg_geF hge hmhi
  have hphase := posPhaseI_le_of_floor hc hr
  have hcore := c160_arg_le_int (A := posPhaseI m c) (r := r) hphase
  have harg : 0 ≤ r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
    have h0 : 0 ≤ r + 1 := by omega
    have hp : 0 ≤ (r + 1) * (1000000000 : Int) :=
      Int.mul_nonneg h0 (by decide)
    have e : (r + 1) * (1000000000 : Int) + 698600000 =
        r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
      unfold lnErrorBoundDen lnErrorBoundNum
      rw [Int.add_mul, Int.one_mul]
      omega
    rw [← e]
    exact Int.add_nonneg hp (by decide)
  apply Int.ofNat_le.mp
  rw [posPhaseNatGe_cast hX]
  unfold lnErrArg
  rw [Int.natCast_mul, Int.toNat_of_nonneg harg]
  have hnon : 0 ≤ 698600000 * twoPow99I := by
    unfold twoPow99I
    decide
  have hle := Int.le_trans (Int.le_add_of_nonneg_right hnon) hcore
  simpa [lnErrorBoundDen, lnErrorBoundNum, twoPow99I] using hle

theorem posNegXNat_le_posConstNat {m c : Nat}
    (hX : toInt (x1W (zWord m)) ≤ 0) (hc : c ≤ 160)
    (hV0 : 0 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI) :
    posNegXNat m ≤ posConstNat c := by
  have hVs := v_scale_pos (toInt (x1W (zWord m))) c hc
  have hV0s : 0 ≤ posPhaseI m c := by
    have hmul := Int.mul_nonneg hV0
      (by unfold twoPow27I; decide : 0 ≤ twoPow27I)
    change 0 ≤ (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI) * twoPow27I at hmul
    have hVs' :
        (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
            lnBiasI) * twoPow27I =
          toInt (x1W (zWord m)) * lnPhaseScaleI +
            ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
              lnBiasI * twoPow27I := by
      simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
    rw [hVs'] at hmul
    simpa [posPhaseI, lnPhaseScaleI, twoPow27I, lnBiasI] using hmul
  apply Int.ofNat_le.mp
  rw [posNegXNat_cast hX, posConstNat_cast c]
  unfold posPhaseI at hV0s
  have hmain :
      -toInt (x1W (zWord m)) * lnPhaseScaleI ≤
        ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
          lnBiasI * twoPow27I := by
    rw [show -toInt (x1W (zWord m)) * lnPhaseScaleI =
        -(toInt (x1W (zWord m)) * lnPhaseScaleI) by rw [Int.neg_mul]]
    generalize toInt (x1W (zWord m)) * lnPhaseScaleI = A at hV0s ⊢
    omega
  exact Int.mul_le_mul_of_nonneg_right hmain (Int.natCast_nonneg _)

def ltPhaseLowerPN (c : Nat) : List Int :=
  polySub
    (polyScale (((posConstNat c + lnPhaseExtraArg : Nat) : Int)) ltTD)
    (polyScale (((2 ^ 99 * lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)) ltTN)

def ltPhaseLowerQD : List Int :=
  polyScale ((lnErrQ : Nat) : Int) ltTD

def ltPhaseLowerMarginPoly (c : Nat) : List Int :=
  expMarginPolyFast 320 (ltPhaseLowerPN c) ltPhaseLowerQD (posTopXPoly c) (10 ^ 18)

def polyIvOnCell (p : List Int) (lo hi : Nat) : Int × Int :=
  hornerIv (polyShift p (lo : Int)) 0 (((hi - lo : Nat) : Int))

def gePhaseLowerIvCellOkB (lo hi c : Nat) : Bool :=
  decide (Sc + 46 ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          let pIv := polyIvOnCell (gePhaseLowerPN c) lo hi
          let qIv := polyIvOnCell gePhaseLowerQD lo hi
          let yIv := polyIvOnCell (posTopXPoly c) lo hi
          decide (0 ≤ pIv.1) &&
            decide (0 ≤ qIv.1) &&
              decide (0 ≤ expMarginIvLower 320 pIv qIv yIv (10 ^ 18))

def ltPhaseLowerIvCellOkB (lo hi c : Nat) : Bool :=
  decide (MLO ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi + 46 ≤ Sc) &&
        decide (c < 160) &&
          let pIv := polyIvOnCell (ltPhaseLowerPN c) lo hi
          let qIv := polyIvOnCell ltPhaseLowerQD lo hi
          let yIv := polyIvOnCell (posTopXPoly c) lo hi
          decide (0 ≤ pIv.1) &&
            decide (0 ≤ qIv.1) &&
              decide (0 ≤ expMarginIvLower 320 pIv qIv yIv (10 ^ 18))

theorem ltTD_pos_of_outer {m : Nat} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) :
    0 < evalPoly ltTD (m : Int) := by
  have hw1 : (39614081257132168796771975168 : Int) ≤ (m : Int) := by
    simp only [MLO] at h1
    omega
  have hw2 : (m : Int) ≤ 56022770974786139918731938181 := by
    simp only [Sc] at h2
    omega
  have h := ltTD_nonneg hw1 hw2
  rw [evalCertLtTD] at h
  omega

theorem ltPhaseLowerQD_pos {m : Nat} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) :
    0 < evalPoly ltPhaseLowerQD (m : Int) := by
  unfold ltPhaseLowerQD
  rw [evalPoly_polyScale]
  exact Int.mul_pos (by unfold lnErrQ QS lnErrorBoundDen; decide)
    (ltTD_pos_of_outer h1 h2)

theorem posPhaseNatLt_cast_decomp {m c : Nat}
    (hX : toInt (x1W (zWord m)) ≤ 0)
    (hneg : posNegXNat m ≤ posConstNat c) :
    ((posPhaseNatLt m c : Nat) : Int) =
      (posConstNat c : Int) -
        (-toInt (x1W (zWord m))) *
          ((lnPhaseScaleN * lnErrorBoundDen : Nat) : Int) := by
  have hnegc : ((posNegXNat m : Nat) : Int) =
      (-toInt (x1W (zWord m))) *
        ((lnPhaseScaleN * lnErrorBoundDen : Nat) : Int) := by
    rw [posNegXNat_cast (m := m) hX]
    change ((-toInt (x1W (zWord m))) * ((lnPhaseScaleN : Nat) : Int)) *
        ((lnErrorBoundDen : Nat) : Int) =
      (-toInt (x1W (zWord m))) * ((lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)
    rw [Int.natCast_mul]
    rw [Int.mul_assoc]
  have hsub : ((posConstNat c - posNegXNat m : Nat) : Int) =
      ((posConstNat c : Nat) : Int) - ((posNegXNat m : Nat) : Int) := by
    omega
  unfold posPhaseNatLt
  rw [hsub, hnegc]

theorem lt_phase_lower_algebra {tn td neg k c e : Int}
    (hk : 0 ≤ k) (hbr : neg * td ≤ tn * 2 ^ 99) :
    (c + e) * td - (2 ^ 99 * k) * tn ≤
      (c - neg * k + e) * td := by
  have hmul := Int.mul_le_mul_of_nonneg_right hbr hk
  have hmul' : neg * td * k ≤ (2 ^ 99 * k) * tn := by
    simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hmul
  have hrewrite : (c + e) * td - neg * td * k = (c - neg * k + e) * td := by
    rw [Int.add_mul, Int.add_mul, Int.sub_mul]
    have hterm : neg * td * k = neg * k * td := by
      rw [Int.mul_assoc, Int.mul_comm td k, ← Int.mul_assoc]
    rw [hterm]
    omega
  calc
    (c + e) * td - (2 ^ 99 * k) * tn ≤
        (c + e) * td - neg * td * k := by
      exact Int.sub_le_sub_left hmul' ((c + e) * td)
    _ = (c - neg * k + e) * td := hrewrite

theorem ltPhaseLowerPN_le_phase_mul_TD {m c : Nat}
    (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) (hc : c < 160) :
    evalPoly (ltPhaseLowerPN c) (m : Int) ≤
      ((posPhaseNatLt m c + lnPhaseExtraArg : Nat) : Int) *
        evalPoly ltTD (m : Int) := by
  have hbr := bracket_lt_up h1 h2
  generalize hTN : evalPoly ltTN (m : Int) = TN at hbr ⊢
  generalize hTD : evalPoly ltTD (m : Int) = TD at hbr ⊢
  have hX := x1_nonpos_lt h1 h2
  have hmhi : m < MHI := by
    simp only [Sc, MHI] at h2 ⊢
    omega
  have hV0 : 0 ≤ toInt (x1W (zWord m)) * 7450580596923828125 +
      ln2kInt c + lnBiasI := by
    simpa [posAccI] using posAccI_nonneg h1 hmhi hc
  have hneg := posNegXNat_le_posConstNat hX (Nat.le_of_lt hc) hV0
  have hphase0 := posPhaseNatLt_cast_decomp (m := m) (c := c) hX hneg
  generalize hNegV : -toInt (x1W (zWord m)) = X at hbr hphase0 ⊢
  let K : Int := ((lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)
  let C : Int := (posConstNat c : Int)
  let E : Int := (lnPhaseExtraArg : Int)
  have hphase :
      ((posPhaseNatLt m c + lnPhaseExtraArg : Nat) : Int) = C - X * K + E := by
    rw [Int.natCast_add, hphase0]
  have hpn :
      evalPoly (ltPhaseLowerPN c) (m : Int) = (C + E) * TD - (2 ^ 99 * K) * TN := by
    unfold ltPhaseLowerPN polySub
    rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyNeg, evalPoly_polyScale,
      hTN, hTD]
    simp only [K, C, E, Int.natCast_add, Int.natCast_mul, Int.natCast_pow,
      Int.mul_assoc]
    rfl
  have hAlg := lt_phase_lower_algebra
    (tn := TN) (td := TD) (neg := X) (k := K) (c := C) (e := E)
    (by unfold K; exact Int.natCast_nonneg _) hbr
  rw [hpn, hphase]
  exact hAlg

theorem ltPhaseLowerMargin_sound {m c : Nat}
    (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) (hc : c < 160)
    (hpn_nonneg : 0 ≤ evalPoly (ltPhaseLowerPN c) (m : Int))
    (hcert : 0 ≤ evalPoly (ltPhaseLowerMarginPoly c) (m : Int)) :
    PosShiftLtPhaseDirectOk 320 m c := by
  let PN := evalPoly (ltPhaseLowerPN c) (m : Int)
  let QD := evalPoly ltPhaseLowerQD (m : Int)
  let P := posPhaseNatLt m c + lnPhaseExtraArg
  have hPNnon : 0 ≤ PN := by
    simpa [PN] using hpn_nonneg
  have hQDpos : 0 < QD := by
    simpa [QD] using ltPhaseLowerQD_pos (m := m) h1 h2
  have hPNcast : (((PN.toNat : Nat) : Int)) = PN :=
    Int.toNat_of_nonneg hPNnon
  have hQDcast : (((QD.toNat : Nat) : Int)) = QD :=
    Int.toNat_of_nonneg (Int.le_of_lt hQDpos)
  have hY := eval_posTopXPoly m c
  have hsum : sumGE 320 PN.toNat QD.toNat (posTopX c m) (10 ^ 18) := by
    refine sumGE_of_expMarginPolyFast
      (n := 320) (m := m) (p := PN.toNat) (q := QD.toNat)
      (y := posTopX c m) (w := 10 ^ 18)
      (pn := ltPhaseLowerPN c) (qd := ltPhaseLowerQD) (yp := posTopXPoly c)
      ?_ ?_ ?_ ?_
    · simpa [ltPhaseLowerMarginPoly, PN, QD] using hcert
    · exact hPNcast.symm
    · exact hQDcast.symm
    · exact hY
  have hqpos : 0 < QD.toNat := by
    apply Int.ofNat_lt.mp
    rw [hQDcast]
    exact hQDpos
  have harg : PN.toNat * lnErrQ ≤ P * QD.toNat := by
    apply Int.ofNat_le.mp
    simp only [Int.natCast_mul, hPNcast, hQDcast]
    have hPNle : PN ≤ (P : Int) * evalPoly ltTD (m : Int) := by
      simpa [PN, P] using ltPhaseLowerPN_le_phase_mul_TD (m := m) (c := c) h1 h2 hc
    have hlnNon : 0 ≤ (lnErrQ : Int) := by
      unfold lnErrQ QS lnErrorBoundDen
      decide
    have hmul := Int.mul_le_mul_of_nonneg_right hPNle hlnNon
    have hQD :
        QD = (lnErrQ : Int) * evalPoly ltTD (m : Int) := by
      unfold QD ltPhaseLowerQD
      rw [evalPoly_polyScale]
    rw [hQD]
    simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hmul
  unfold PosShiftLtPhaseDirectOk
  exact sumGE_arg_mono (q' := QD.toNat) hqpos harg hsum

theorem ltPhaseLowerMarginVal_sound {m c : Nat}
    (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) (hc : c < 160)
    (hpn_nonneg : 0 ≤ evalPoly (ltPhaseLowerPN c) (m : Int))
    (hcert : 0 ≤ expMarginVal 320 (evalPoly (ltPhaseLowerPN c) (m : Int))
      (evalPoly ltPhaseLowerQD (m : Int)) (evalPoly (posTopXPoly c) (m : Int))
      (((10 ^ 18 : Nat) : Int))) :
    PosShiftLtPhaseDirectOk 320 m c := by
  let PN := evalPoly (ltPhaseLowerPN c) (m : Int)
  let QD := evalPoly ltPhaseLowerQD (m : Int)
  let P := posPhaseNatLt m c + lnPhaseExtraArg
  have hPNnon : 0 ≤ PN := by
    simpa [PN] using hpn_nonneg
  have hQDpos : 0 < QD := by
    simpa [QD] using ltPhaseLowerQD_pos (m := m) h1 h2
  have hPNcast : (((PN.toNat : Nat) : Int)) = PN :=
    Int.toNat_of_nonneg hPNnon
  have hQDcast : (((QD.toNat : Nat) : Int)) = QD :=
    Int.toNat_of_nonneg (Int.le_of_lt hQDpos)
  have hY := eval_posTopXPoly m c
  have hsum : sumGE 320 PN.toNat QD.toNat (posTopX c m) (10 ^ 18) := by
    refine sumGE_of_expMarginVal
      (n := 320) (p := PN.toNat) (q := QD.toNat)
      (y := posTopX c m) (w := 10 ^ 18) ?_
    rw [hPNcast, hQDcast, ← hY]
    exact hcert
  have hqpos : 0 < QD.toNat := by
    apply Int.ofNat_lt.mp
    rw [hQDcast]
    exact hQDpos
  have harg : PN.toNat * lnErrQ ≤ P * QD.toNat := by
    apply Int.ofNat_le.mp
    simp only [Int.natCast_mul, hPNcast, hQDcast]
    have hPNle : PN ≤ (P : Int) * evalPoly ltTD (m : Int) := by
      simpa [PN, P] using ltPhaseLowerPN_le_phase_mul_TD (m := m) (c := c) h1 h2 hc
    have hlnNon : 0 ≤ (lnErrQ : Int) := by
      unfold lnErrQ QS lnErrorBoundDen
      decide
    have hmul := Int.mul_le_mul_of_nonneg_right hPNle hlnNon
    have hQD :
        QD = (lnErrQ : Int) * evalPoly ltTD (m : Int) := by
      unfold QD ltPhaseLowerQD
      rw [evalPoly_polyScale]
    rw [hQD]
    simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hmul
  unfold PosShiftLtPhaseDirectOk
  exact sumGE_arg_mono (q' := QD.toNat) hqpos harg hsum

def ltPhaseLowerPNMin (c : Nat) : List Int :=
  polySub
    (polyScale (((posConstNat c + minPosAvail : Nat) : Int)) ltTD)
    (polyScale (((2 ^ 99 * lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)) ltTN)

def ltPhaseLowerMarginPolyMin (c : Nat) : List Int :=
  expMarginPolyFast 320 (ltPhaseLowerPNMin c) ltPhaseLowerQD (posTopXPoly c) (10 ^ 18)

theorem ltPhaseLowerPNMin_le_phase_mul_TD {m c : Nat}
    (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) (hc : c < 160) :
    evalPoly (ltPhaseLowerPNMin c) (m : Int) ≤
      ((posPhaseNatLt m c + minPosAvail : Nat) : Int) *
        evalPoly ltTD (m : Int) := by
  have hbr := bracket_lt_up h1 h2
  generalize hTN : evalPoly ltTN (m : Int) = TN at hbr ⊢
  generalize hTD : evalPoly ltTD (m : Int) = TD at hbr ⊢
  have hX := x1_nonpos_lt h1 h2
  have hmhi : m < MHI := by
    simp only [Sc, MHI] at h2 ⊢
    omega
  have hV0 : 0 ≤ toInt (x1W (zWord m)) * 7450580596923828125 +
      ln2kInt c + lnBiasI := by
    simpa [posAccI] using posAccI_nonneg h1 hmhi hc
  have hneg := posNegXNat_le_posConstNat hX (Nat.le_of_lt hc) hV0
  have hphase0 := posPhaseNatLt_cast_decomp (m := m) (c := c) hX hneg
  generalize hNegV : -toInt (x1W (zWord m)) = X at hbr hphase0 ⊢
  let K : Int := ((lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)
  let C : Int := (posConstNat c : Int)
  let E : Int := (minPosAvail : Int)
  have hphase :
      ((posPhaseNatLt m c + minPosAvail : Nat) : Int) = C - X * K + E := by
    rw [Int.natCast_add, hphase0]
  have hpn :
      evalPoly (ltPhaseLowerPNMin c) (m : Int) = (C + E) * TD - (2 ^ 99 * K) * TN := by
    unfold ltPhaseLowerPNMin polySub
    rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyNeg, evalPoly_polyScale,
      hTN, hTD]
    simp only [K, C, E, Int.natCast_add, Int.natCast_mul, Int.natCast_pow,
      Int.mul_assoc]
    rfl
  have hAlg := lt_phase_lower_algebra
    (tn := TN) (td := TD) (neg := X) (k := K) (c := C) (e := E)
    (by unfold K; exact Int.natCast_nonneg _) hbr
  rw [hpn, hphase]
  exact hAlg

theorem ltPhaseLowerMarginValMin_sound {m c : Nat}
    (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) (hc : c < 160)
    (hpn_nonneg : 0 ≤ evalPoly (ltPhaseLowerPNMin c) (m : Int))
    (hcert : 0 ≤ expMarginVal 320 (evalPoly (ltPhaseLowerPNMin c) (m : Int))
      (evalPoly ltPhaseLowerQD (m : Int)) (evalPoly (posTopXPoly c) (m : Int))
      (((10 ^ 18 : Nat) : Int))) :
    PosShiftLtMinPhaseDirectOk 320 m c := by
  let PN := evalPoly (ltPhaseLowerPNMin c) (m : Int)
  let QD := evalPoly ltPhaseLowerQD (m : Int)
  let P := posPhaseNatLt m c + minPosAvail
  have hPNnon : 0 ≤ PN := by
    simpa [PN] using hpn_nonneg
  have hQDpos : 0 < QD := by
    simpa [QD] using ltPhaseLowerQD_pos (m := m) h1 h2
  have hPNcast : (((PN.toNat : Nat) : Int)) = PN :=
    Int.toNat_of_nonneg hPNnon
  have hQDcast : (((QD.toNat : Nat) : Int)) = QD :=
    Int.toNat_of_nonneg (Int.le_of_lt hQDpos)
  have hY := eval_posTopXPoly m c
  have hsum : sumGE 320 PN.toNat QD.toNat (posTopX c m) (10 ^ 18) := by
    refine sumGE_of_expMarginVal
      (n := 320) (p := PN.toNat) (q := QD.toNat)
      (y := posTopX c m) (w := 10 ^ 18) ?_
    rw [hPNcast, hQDcast, ← hY]
    exact hcert
  have hqpos : 0 < QD.toNat := by
    apply Int.ofNat_lt.mp
    rw [hQDcast]
    exact hQDpos
  have harg : PN.toNat * lnErrQ ≤ P * QD.toNat := by
    apply Int.ofNat_le.mp
    simp only [Int.natCast_mul, hPNcast, hQDcast]
    have hPNle : PN ≤ (P : Int) * evalPoly ltTD (m : Int) := by
      simpa [PN, P] using ltPhaseLowerPNMin_le_phase_mul_TD (m := m) (c := c) h1 h2 hc
    have hlnNon : 0 ≤ (lnErrQ : Int) := by
      unfold lnErrQ QS lnErrorBoundDen
      decide
    have hmul := Int.mul_le_mul_of_nonneg_right hPNle hlnNon
    have hQD :
        QD = (lnErrQ : Int) * evalPoly ltTD (m : Int) := by
      unfold QD ltPhaseLowerQD
      rw [evalPoly_polyScale]
    rw [hQD]
    simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hmul
  unfold PosShiftLtMinPhaseDirectOk
  exact sumGE_arg_mono (q' := QD.toNat) hqpos harg hsum

structure GePhaseLowerCell where
  lo : Nat
  hi : Nat
  marginWs : List Int

structure LtPhaseLowerCell where
  lo : Nat
  hi : Nat
  pnWs : List Int
  marginWs : List Int

def gePhaseLowerCellOkB (cell : GePhaseLowerCell) (c : Nat) : Bool :=
  decide (Sc + 46 ≤ cell.lo) &&
    decide (cell.lo ≤ cell.hi) &&
      decide (cell.hi < MHI) &&
        decide (c < 160) &&
          shiftedExpMarginCellOkB kB 320 (gePhaseLowerPN c) gePhaseLowerQD
            (posTopXPoly c) cell.lo cell.hi (10 ^ 18) cell.marginWs

def ltPhaseLowerCellOkB (cell : LtPhaseLowerCell) (c : Nat) : Bool :=
  decide (MLO ≤ cell.lo) &&
    decide (cell.lo ≤ cell.hi) &&
      decide (cell.hi + 46 ≤ Sc) &&
        decide (c < 160) &&
          checkCoverK kB (ltPhaseLowerPN c) (cell.lo : Int) (cell.hi : Int) cell.pnWs &&
            shiftedExpMarginCellOkB kB 320 (ltPhaseLowerPN c) ltPhaseLowerQD
              (posTopXPoly c) cell.lo cell.hi (10 ^ 18) cell.marginWs

theorem gePhaseLowerCell_sound {cell : GePhaseLowerCell} {m c : Nat}
    (h : gePhaseLowerCellOkB cell c = true)
    (hlom : cell.lo ≤ m) (hmhi : m ≤ cell.hi) :
    PosShiftGePhaseDirectOk 320 m c := by
  unfold gePhaseLowerCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, _hc⟩, hmargin⟩ := h
  exact gePhaseLowerMarginVal_sound (by omega : Sc + 46 ≤ m) (by omega : m < MHI)
    (shiftedExpMarginCellOkB_sound hmargin hlom hmhi)

theorem ltPhaseLowerCell_sound {cell : LtPhaseLowerCell} {m c : Nat}
    (h : ltPhaseLowerCellOkB cell c = true)
    (hlom : cell.lo ≤ m) (hmhi : m ≤ cell.hi) :
    PosShiftLtPhaseDirectOk 320 m c := by
  unfold ltPhaseLowerCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, hc⟩, hpn⟩, hmargin⟩ := h
  exact ltPhaseLowerMarginVal_sound (by omega : MLO ≤ m) (by omega : m + 46 ≤ Sc) hc
    (checkCoverK_sound _ _ _ _ _ hpn (m : Int) (by omega) (by omega))
    (shiftedExpMarginCellOkB_sound hmargin hlom hmhi)

def gePhaseLowerCellListCoverB (c : Nat) : Nat → Nat → List GePhaseLowerCell → Bool
  | lo, hi, [] => decide (hi < lo)
  | lo, hi, cell :: cells =>
      decide (cell.lo = lo) &&
        decide (lo ≤ cell.hi) &&
          decide (cell.hi ≤ hi) &&
            gePhaseLowerCellOkB cell c &&
              gePhaseLowerCellListCoverB c (cell.hi + 1) hi cells

def ltPhaseLowerCellListCoverB (c : Nat) : Nat → Nat → List LtPhaseLowerCell → Bool
  | lo, hi, [] => decide (hi < lo)
  | lo, hi, cell :: cells =>
      decide (cell.lo = lo) &&
        decide (lo ≤ cell.hi) &&
          decide (cell.hi ≤ hi) &&
            ltPhaseLowerCellOkB cell c &&
              ltPhaseLowerCellListCoverB c (cell.hi + 1) hi cells

theorem gePhaseLowerCellListCoverB_sound {cells : List GePhaseLowerCell} {c lo hi m : Nat}
    (h : gePhaseLowerCellListCoverB c lo hi cells = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGePhaseDirectOk 320 m c := by
  induction cells generalizing lo with
  | nil =>
      unfold gePhaseLowerCellListCoverB at h
      have hlt : hi < lo := of_decide_eq_true h
      omega
  | cons cell cells ih =>
      unfold gePhaseLowerCellListCoverB at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hlo, _hlohi⟩, _hhihi⟩, hok⟩, hrest⟩ := h
      by_cases hmcell : m ≤ cell.hi
      · exact gePhaseLowerCell_sound hok (by omega) hmcell
      · exact ih hrest (by omega)

theorem ltPhaseLowerCellListCoverB_sound {cells : List LtPhaseLowerCell} {c lo hi m : Nat}
    (h : ltPhaseLowerCellListCoverB c lo hi cells = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftLtPhaseDirectOk 320 m c := by
  induction cells generalizing lo with
  | nil =>
      unfold ltPhaseLowerCellListCoverB at h
      have hlt : hi < lo := of_decide_eq_true h
      omega
  | cons cell cells ih =>
      unfold ltPhaseLowerCellListCoverB at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hlo, _hlohi⟩, _hhihi⟩, hok⟩, hrest⟩ := h
      by_cases hmcell : m ≤ cell.hi
      · exact ltPhaseLowerCell_sound hok (by omega) hmcell
      · exact ih hrest (by omega)

theorem minPosAvail_cast :
    ((minPosAvail : Nat) : Int) =
      (lnErrorExtraNum : Int) * twoPow99I +
        twoPow27I * (lnErrorBoundDen : Int) := by
  unfold minPosAvail lnPhaseExtraArg twoPow99N twoPow27N twoPow99I twoPow27I
  unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen
  decide +kernel

theorem posPhaseNatGe_minAvail_le_lnErrArg {m c : Nat}
    (hge : Sc ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    posPhaseNatGe m c + minPosAvail ≤
      lnErrArg (toInt (lnTail (evmSub 160 c) m)) := by
  let r := toInt (lnTail (evmSub 160 c) m)
  have hmlo : MLO ≤ m := by
    simp only [Sc, MLO] at hge ⊢
    omega
  have hX := x1_nonneg_geF hge hmhi
  have hgap : 1 ≤ posResidueGap m c r := by
    simpa [r] using (posResidueGap_bounds hmlo hmhi hc).1
  have hdecomp := lnErrArg_eq_posPhase_gap (m := m) (c := c) hmlo hmhi hc
  change ((lnErrArg r : Nat) : Int) =
      posPhaseI m c * (lnErrorBoundDen : Int) +
        (lnErrorExtraNum : Int) * twoPow99I +
          posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) at hdecomp
  apply Int.ofNat_le.mp
  rw [Int.natCast_add, posPhaseNatGe_cast hX, minPosAvail_cast, hdecomp]
  have h27 : 0 ≤ twoPow27I := by
    unfold twoPow27I
    decide
  have hden : 0 ≤ (lnErrorBoundDen : Int) := by
    change (0 : Int) ≤ 1000000000
    decide
  have hgap27 :
      1 * twoPow27I ≤ posResidueGap m c r * twoPow27I :=
    Int.mul_le_mul_of_nonneg_right hgap h27
  have hgapDen :
      1 * twoPow27I * (lnErrorBoundDen : Int) ≤
        posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) :=
    Int.mul_le_mul_of_nonneg_right hgap27 hden
  have hgapDen' :
      twoPow27I * (lnErrorBoundDen : Int) ≤
        posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) := by
    simpa [Int.one_mul] using hgapDen
  have hinner :
      (lnErrorExtraNum : Int) * twoPow99I +
          twoPow27I * (lnErrorBoundDen : Int) ≤
        (lnErrorExtraNum : Int) * twoPow99I +
          posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) :=
    Int.add_le_add_left hgapDen' _
  have hmain :
      posPhaseI m c * (lnErrorBoundDen : Int) +
          ((lnErrorExtraNum : Int) * twoPow99I +
            twoPow27I * (lnErrorBoundDen : Int)) ≤
        posPhaseI m c * (lnErrorBoundDen : Int) +
          ((lnErrorExtraNum : Int) * twoPow99I +
            posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int)) :=
    Int.add_le_add_left hinner _
  simpa [Int.add_assoc] using hmain

theorem posPhaseNatLt_minAvail_le_lnErrArg {m c : Nat}
    (hmlo : MLO ≤ m) (hmlt : m < Sc) (hc : c < 160) :
    posPhaseNatLt m c + minPosAvail ≤
      lnErrArg (toInt (lnTail (evmSub 160 c) m)) := by
  let r := toInt (lnTail (evmSub 160 c) m)
  have hmhi : m < MHI := by
    simp only [Sc, MHI] at hmlt ⊢
    omega
  have hX := x1_nonpos_ltF hmlo hmlt
  have hV0 : 0 ≤
      toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c + lnBiasI := by
    simpa [posAccI] using posAccI_nonneg hmlo hmhi hc
  have hneg := posNegXNat_le_posConstNat hX (by omega : c ≤ 160) hV0
  have hgap : 1 ≤ posResidueGap m c r := by
    simpa [r] using (posResidueGap_bounds hmlo hmhi hc).1
  have hdecomp := lnErrArg_eq_posPhase_gap (m := m) (c := c) hmlo hmhi hc
  change ((lnErrArg r : Nat) : Int) =
      posPhaseI m c * (lnErrorBoundDen : Int) +
        (lnErrorExtraNum : Int) * twoPow99I +
          posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) at hdecomp
  apply Int.ofNat_le.mp
  rw [Int.natCast_add, posPhaseNatLt_cast hX hneg, minPosAvail_cast, hdecomp]
  have h27 : 0 ≤ twoPow27I := by
    unfold twoPow27I
    decide
  have hden : 0 ≤ (lnErrorBoundDen : Int) := by
    change (0 : Int) ≤ 1000000000
    decide
  have hgap27 :
      1 * twoPow27I ≤ posResidueGap m c r * twoPow27I :=
    Int.mul_le_mul_of_nonneg_right hgap h27
  have hgapDen :
      1 * twoPow27I * (lnErrorBoundDen : Int) ≤
        posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) :=
    Int.mul_le_mul_of_nonneg_right hgap27 hden
  have hgapDen' :
      twoPow27I * (lnErrorBoundDen : Int) ≤
        posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) := by
    simpa [Int.one_mul] using hgapDen
  have hinner :
      (lnErrorExtraNum : Int) * twoPow99I +
          twoPow27I * (lnErrorBoundDen : Int) ≤
        (lnErrorExtraNum : Int) * twoPow99I +
          posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) :=
    Int.add_le_add_left hgapDen' _
  have hmain :
      posPhaseI m c * (lnErrorBoundDen : Int) +
          ((lnErrorExtraNum : Int) * twoPow99I +
            twoPow27I * (lnErrorBoundDen : Int)) ≤
        posPhaseI m c * (lnErrorBoundDen : Int) +
          ((lnErrorExtraNum : Int) * twoPow99I +
            posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int)) :=
    Int.add_le_add_left hinner _
  simpa [Int.add_assoc] using hmain

theorem posAvailGe_min {m c : Nat}
    (hge : Sc ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    minPosAvail ≤
      posAvailGe m c (toInt (lnTail (evmSub 160 c) m)) := by
  unfold posAvailGe
  have h := posPhaseNatGe_minAvail_le_lnErrArg hge hmhi hc
  omega

theorem posAvailLt_min {m c : Nat}
    (hmlo : MLO ≤ m) (hmlt : m < Sc) (hc : c < 160) :
    minPosAvail ≤
      posAvailLt m c (toInt (lnTail (evmSub 160 c) m)) := by
  unfold posAvailLt
  have h := posPhaseNatLt_minAvail_le_lnErrArg hmlo hmlt hc
  omega

theorem wadRayNum_mono {x y : Nat} (hxy : x ≤ y) : wadRayNum x ≤ wadRayNum y := by
  unfold wadRayNum
  exact Nat.mul_le_mul_right _ hxy

theorem posBaseYGe_mono_m {lo m c : Nat} (hlom : lo ≤ m) :
    posBaseYGe lo c ≤ posBaseYGe m c := by
  unfold posBaseYGe
  have h1 :
      lo * 9999999999999999999999999996615 ≤
        m * 9999999999999999999999999996615 :=
    Nat.mul_le_mul_right _ hlom
  have h2 :
      (lo * 9999999999999999999999999996615) *
          (2 * (10 ^ 40 - 1)) ^ (160 - c) ≤
        (m * 9999999999999999999999999996615) *
          (2 * (10 ^ 40 - 1)) ^ (160 - c) :=
    Nat.mul_le_mul_right _ h1
  exact Nat.mul_le_mul_right _ h2

theorem posBaseYLt_mono_m {lo m c : Nat} (hlom : lo ≤ m) :
    posBaseYLt lo c ≤ posBaseYLt m c := by
  unfold posBaseYLt
  have h1 :
      lo * 9999999999999999999999999996615 ≤
        m * 9999999999999999999999999996615 :=
    Nat.mul_le_mul_right _ hlom
  exact Nat.mul_le_mul_left _ h1

theorem geTopBudgetCoarseCellOkB_sound {lo hi m c : Nat}
    (h : geTopBudgetCoarseCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGeTopBudgetIneqOk m c := by
  unfold geTopBudgetCoarseCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, hc⟩, hineq⟩ := h
  unfold PosShiftGeTopBudgetIneqOk PosShiftGeBudgetIneqOk
  let r := toInt (lnTail (evmSub 160 c) m)
  have hleft :
      wadRayNum (posTopX c m) * (posBaseWGe c * lnErrQ) ≤
        wadRayNum (posTopX c hi) * (posBaseWGe c * lnErrQ) := by
    exact Nat.mul_le_mul_right _ (wadRayNum_mono (posTopX_mono_m hmhi))
  have hbase : posBaseYGe lo c ≤ posBaseYGe m c :=
    posBaseYGe_mono_m hlom
  have havail : minPosAvail ≤ posAvailGe m c r :=
    posAvailGe_min (m := m) (c := c) (by omega) (by omega) hc
  have hmargin : lnErrQ + minPosAvail ≤ lnErrQ + posAvailGe m c r :=
    Nat.add_le_add_left havail lnErrQ
  have hright :
      (posBaseYGe lo c * (lnErrQ + minPosAvail)) * wadRayStrictDen ≤
        (posBaseYGe m c * (lnErrQ + posAvailGe m c r)) * wadRayStrictDen := by
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hbase hmargin)
  exact Nat.le_trans hleft (Nat.le_trans hineq hright)

theorem ltTopBudgetCoarseCellOkB_sound {lo hi m c : Nat}
    (h : ltTopBudgetCoarseCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftLtTopBudgetIneqOk m c := by
  unfold ltTopBudgetCoarseCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, hc⟩, hineq⟩ := h
  unfold PosShiftLtTopBudgetIneqOk PosShiftLtBudgetIneqOk
  let r := toInt (lnTail (evmSub 160 c) m)
  have hleft :
      wadRayNum (posTopX c m) * (posBaseWLt c * lnErrQ) ≤
        wadRayNum (posTopX c hi) * (posBaseWLt c * lnErrQ) := by
    exact Nat.mul_le_mul_right _ (wadRayNum_mono (posTopX_mono_m hmhi))
  have hbase : posBaseYLt lo c ≤ posBaseYLt m c :=
    posBaseYLt_mono_m hlom
  have havail : minPosAvail ≤ posAvailLt m c r :=
    posAvailLt_min (m := m) (c := c) (by omega) (by omega) hc
  have hmargin : lnErrQ + minPosAvail ≤ lnErrQ + posAvailLt m c r :=
    Nat.add_le_add_left havail lnErrQ
  have hright :
      (posBaseYLt lo c * (lnErrQ + minPosAvail)) * wadRayStrictDen ≤
        (posBaseYLt m c * (lnErrQ + posAvailLt m c r)) * wadRayStrictDen := by
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hbase hmargin)
  exact Nat.le_trans hleft (Nat.le_trans hineq hright)

theorem geTopBudgetRunCellOkB_sound {lo hi m c : Nat}
    (h : geTopBudgetRunCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGeTopBudgetIneqOk m c := by
  unfold geTopBudgetRunCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hloSc, hlohi⟩, hhi⟩, hc⟩, hrun⟩ := h
  obtain ⟨hboundary, hineq⟩ := hrun
  have hlo : MLO ≤ lo := by
    simp only [Sc, MLO] at hloSc ⊢
    omega
  let rlo := toInt (lnTail (evmSub 160 c) lo)
  let rm := toInt (lnTail (evmSub 160 c) m)
  let rhi := toInt (lnTail (evmSub 160 c) hi)
  have hmhi' : m < MHI := by omega
  have htailM : rm = rlo := by
    simpa [rm, rlo] using
      lnTail_eq_of_residue_run hlo hlom hmhi hhi hc hboundary
  have htailHi : rhi = rlo := by
    simpa [rhi, rlo] using
      lnTail_eq_of_residue_run hlo hlohi (Nat.le_refl hi) hhi hc hboundary
  unfold PosShiftGeTopBudgetIneqOk PosShiftGeBudgetIneqOk
  have hleft :
      wadRayNum (posTopX c m) * (posBaseWGe c * lnErrQ) ≤
        wadRayNum (posTopX c hi) * (posBaseWGe c * lnErrQ) := by
    exact Nat.mul_le_mul_right _ (wadRayNum_mono (posTopX_mono_m hmhi))
  have hbase : posBaseYGe lo c ≤ posBaseYGe m c :=
    posBaseYGe_mono_m hlom
  have hphase_m_hi : posPhaseNatGe m c ≤ posPhaseNatGe hi c :=
    posPhaseNatGe_mono_m (lo := m) (m := hi) (c := c) (by omega) hmhi hhi
  have havail : posAvailGe hi c rlo ≤ posAvailGe m c rm := by
    unfold posAvailGe
    rw [htailM]
    exact Nat.sub_le_sub_left hphase_m_hi (lnErrArg rlo)
  have hmargin : lnErrQ + posAvailGe hi c rlo ≤ lnErrQ + posAvailGe m c rm :=
    Nat.add_le_add_left havail lnErrQ
  have hright :
      (posBaseYGe lo c * (lnErrQ + posAvailGe hi c rlo)) * wadRayStrictDen ≤
        (posBaseYGe m c * (lnErrQ + posAvailGe m c rm)) * wadRayStrictDen := by
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hbase hmargin)
  have hineq' :
      wadRayNum (posTopX c hi) * (posBaseWGe c * lnErrQ) ≤
        (posBaseYGe lo c * (lnErrQ + posAvailGe hi c rlo)) * wadRayStrictDen := by
    simpa [rlo] using hineq
  have hle := Nat.le_trans hleft (Nat.le_trans hineq' hright)
  simpa [rm] using hle

theorem ltTopBudgetRunCellOkB_sound {lo hi m c : Nat}
    (h : ltTopBudgetRunCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftLtTopBudgetIneqOk m c := by
  unfold ltTopBudgetRunCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, hlohi⟩, hhiSc⟩, hc⟩, hrun⟩ := h
  obtain ⟨hboundary, hineq⟩ := hrun
  have hhi : hi < MHI := by
    simp only [Sc, MHI] at hhiSc ⊢
    omega
  let rlo := toInt (lnTail (evmSub 160 c) lo)
  let rm := toInt (lnTail (evmSub 160 c) m)
  let rhi := toInt (lnTail (evmSub 160 c) hi)
  have hmhi' : m < MHI := by omega
  have htailM : rm = rlo := by
    simpa [rm, rlo] using
      lnTail_eq_of_residue_run hlo hlom hmhi hhi hc hboundary
  have htailHi : rhi = rlo := by
    simpa [rhi, rlo] using
      lnTail_eq_of_residue_run hlo hlohi (Nat.le_refl hi) hhi hc hboundary
  unfold PosShiftLtTopBudgetIneqOk PosShiftLtBudgetIneqOk
  have hleft :
      wadRayNum (posTopX c m) * (posBaseWLt c * lnErrQ) ≤
        wadRayNum (posTopX c hi) * (posBaseWLt c * lnErrQ) := by
    exact Nat.mul_le_mul_right _ (wadRayNum_mono (posTopX_mono_m hmhi))
  have hbase : posBaseYLt lo c ≤ posBaseYLt m c :=
    posBaseYLt_mono_m hlom
  have hphase_m_hi : posPhaseNatLt m c ≤ posPhaseNatLt hi c :=
    posPhaseNatLt_mono_m (lo := m) (m := hi) (c := c) (by omega) hmhi (by
      simp only [Sc, MHI] at hhiSc ⊢
      omega)
  have havail : posAvailLt hi c rlo ≤ posAvailLt m c rm := by
    unfold posAvailLt
    rw [htailM]
    exact Nat.sub_le_sub_left hphase_m_hi (lnErrArg rlo)
  have hmargin : lnErrQ + posAvailLt hi c rlo ≤ lnErrQ + posAvailLt m c rm :=
    Nat.add_le_add_left havail lnErrQ
  have hright :
      (posBaseYLt lo c * (lnErrQ + posAvailLt hi c rlo)) * wadRayStrictDen ≤
        (posBaseYLt m c * (lnErrQ + posAvailLt m c rm)) * wadRayStrictDen := by
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hbase hmargin)
  have hineq' :
      wadRayNum (posTopX c hi) * (posBaseWLt c * lnErrQ) ≤
        (posBaseYLt lo c * (lnErrQ + posAvailLt hi c rlo)) * wadRayStrictDen := by
    simpa [rlo] using hineq
  have hle := Nat.le_trans hleft (Nat.le_trans hineq' hright)
  simpa [rm] using hle

theorem posPhaseNatLt_le_lnErrArg {m c : Nat} {r : Int}
    (hX : toInt (x1W (zWord m)) ≤ 0) (hc : c ≤ 160)
    (hneg : posNegXNat m ≤ posConstNat c)
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI < (r + 1) * 2 ^ 72)
    (hr0 : -1 ≤ r) :
    posPhaseNatLt m c ≤ lnErrArg r := by
  have hphase := posPhaseI_le_of_floor hc hr
  have hcore := c160_arg_le_int (A := posPhaseI m c) (r := r) hphase
  have harg : 0 ≤ r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
    have h0 : 0 ≤ r + 1 := by omega
    have hp : 0 ≤ (r + 1) * (1000000000 : Int) :=
      Int.mul_nonneg h0 (by decide)
    have e : (r + 1) * (1000000000 : Int) + 698600000 =
        r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
      unfold lnErrorBoundDen lnErrorBoundNum
      rw [Int.add_mul, Int.one_mul]
      omega
    rw [← e]
    exact Int.add_nonneg hp (by decide)
  apply Int.ofNat_le.mp
  rw [posPhaseNatLt_cast hX hneg]
  unfold lnErrArg
  rw [Int.natCast_mul, Int.toNat_of_nonneg harg]
  have hnon : 0 ≤ 698600000 * twoPow99I := by
    unfold twoPow99I
    decide
  have hle := Int.le_trans (Int.le_add_of_nonneg_right hnon) hcore
  simpa [lnErrorBoundDen, lnErrorBoundNum, twoPow99I] using hle

theorem posPhaseNatGe_extra_le_lnErrArg {m c : Nat} {r : Int}
    (hge : Sc ≤ m) (hmhi : m < MHI) (hc : c ≤ 160)
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI < (r + 1) * 2 ^ 72)
    (hr0 : -1 ≤ r) :
    posPhaseNatGe m c + lnPhaseExtraArg ≤ lnErrArg r := by
  have hX := x1_nonneg_geF hge hmhi
  have hphase := posPhaseI_le_of_floor hc hr
  have hcore := c160_arg_le_int (A := posPhaseI m c) (r := r) hphase
  have harg : 0 ≤ r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
    have h0 : 0 ≤ r + 1 := by omega
    have hp : 0 ≤ (r + 1) * (1000000000 : Int) :=
      Int.mul_nonneg h0 (by decide)
    have e : (r + 1) * (1000000000 : Int) + 698600000 =
        r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
      unfold lnErrorBoundDen lnErrorBoundNum
      rw [Int.add_mul, Int.one_mul]
      omega
    rw [← e]
    exact Int.add_nonneg hp (by decide)
  apply Int.ofNat_le.mp
  rw [Int.natCast_add, posPhaseNatGe_cast hX]
  unfold lnPhaseExtraArg lnErrArg
  have htarget : ((((r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat *
      2 ^ 99 : Nat) : Int)) =
      (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
    rw [Int.natCast_mul, Int.toNat_of_nonneg harg]
    unfold twoPow99I
    rfl
  have hextra : (((lnErrorExtraNum * twoPow99N : Nat) : Int)) =
      (lnErrorExtraNum : Int) * twoPow99I := by
    unfold twoPow99N twoPow99I
    rfl
  rw [htarget, hextra]
  simpa [lnErrorBoundDen, lnErrorBoundNum, lnErrorExtraNum, twoPow99N, twoPow99I]
    using hcore

theorem posPhaseNatLt_extra_le_lnErrArg {m c : Nat} {r : Int}
    (hX : toInt (x1W (zWord m)) ≤ 0) (hc : c ≤ 160)
    (hneg : posNegXNat m ≤ posConstNat c)
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI < (r + 1) * 2 ^ 72)
    (hr0 : -1 ≤ r) :
    posPhaseNatLt m c + lnPhaseExtraArg ≤ lnErrArg r := by
  have hphase := posPhaseI_le_of_floor hc hr
  have hcore := c160_arg_le_int (A := posPhaseI m c) (r := r) hphase
  have harg : 0 ≤ r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
    have h0 : 0 ≤ r + 1 := by omega
    have hp : 0 ≤ (r + 1) * (1000000000 : Int) :=
      Int.mul_nonneg h0 (by decide)
    have e : (r + 1) * (1000000000 : Int) + 698600000 =
        r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
      unfold lnErrorBoundDen lnErrorBoundNum
      rw [Int.add_mul, Int.one_mul]
      omega
    rw [← e]
    exact Int.add_nonneg hp (by decide)
  apply Int.ofNat_le.mp
  rw [Int.natCast_add, posPhaseNatLt_cast hX hneg]
  unfold lnPhaseExtraArg lnErrArg
  have htarget : ((((r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat *
      2 ^ 99 : Nat) : Int)) =
      (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
    rw [Int.natCast_mul, Int.toNat_of_nonneg harg]
    unfold twoPow99I
    rfl
  have hextra : (((lnErrorExtraNum * twoPow99N : Nat) : Int)) =
      (lnErrorExtraNum : Int) * twoPow99I := by
    unfold twoPow99N twoPow99I
    rfl
  rw [htarget, hextra]
  simpa [lnErrorBoundDen, lnErrorBoundNum, lnErrorExtraNum, twoPow99N, twoPow99I]
    using hcore

theorem posPhaseNatGe_gap_extra_le_lnErrArg {m c : Nat} {r : Int}
    (hX : 0 ≤ toInt (x1W (zWord m))) (hc : c ≤ 160) (hr0 : -1 ≤ r)
    (hgap : PosShiftDirectResidueGapOk m c r) :
    posPhaseNatGe m c + lnPhaseExtraArg + lnDirectGapArg ≤ lnErrArg r := by
  have hres := direct_residue_phase_bound (m := m) (c := c) (r := r) hc hgap
  have hcore := pos_direct_residue_arg_le_int hres
  have harg : 0 ≤ r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
    have h0 : 0 ≤ r + 1 := by omega
    have hp : 0 ≤ (r + 1) * (1000000000 : Int) :=
      Int.mul_nonneg h0 (by decide)
    have e : (r + 1) * (1000000000 : Int) + 698600000 =
        r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
      unfold lnErrorBoundDen lnErrorBoundNum
      rw [Int.add_mul, Int.one_mul]
      omega
    rw [← e]
    exact Int.add_nonneg hp (by decide)
  apply Int.ofNat_le.mp
  rw [Int.natCast_add, Int.natCast_add, posPhaseNatGe_cast hX]
  unfold lnPhaseExtraArg lnDirectGapArg lnErrArg
  have htarget : ((((r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat *
      2 ^ 99 : Nat) : Int)) =
      (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
    rw [Int.natCast_mul, Int.toNat_of_nonneg harg]
    unfold twoPow99I
    rfl
  have hextra : (((lnErrorExtraNum * twoPow99N : Nat) : Int)) =
      (lnErrorExtraNum : Int) * twoPow99I := by
    unfold twoPow99N twoPow99I
    rfl
  have hgapcast :
      (((lnErrorDirectResidueGap * twoPow27N * lnErrorBoundDen : Nat) : Int)) =
        (lnErrorDirectResidueGap : Int) * twoPow27I * (lnErrorBoundDen : Int) := by
    unfold lnErrorDirectResidueGap twoPow27N twoPow27I lnErrorBoundDen
    decide
  rw [htarget, hextra, hgapcast]
  simpa [lnErrorBoundDen, lnErrorBoundNum, lnErrorExtraNum, twoPow99I]
    using hcore

theorem posPhaseNatLt_gap_extra_le_lnErrArg {m c : Nat} {r : Int}
    (hX : toInt (x1W (zWord m)) ≤ 0) (hc : c ≤ 160)
    (hneg : posNegXNat m ≤ posConstNat c) (hr0 : -1 ≤ r)
    (hgap : PosShiftDirectResidueGapOk m c r) :
    posPhaseNatLt m c + lnPhaseExtraArg + lnDirectGapArg ≤ lnErrArg r := by
  have hres := direct_residue_phase_bound (m := m) (c := c) (r := r) hc hgap
  have hcore := pos_direct_residue_arg_le_int hres
  have harg : 0 ≤ r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
    have h0 : 0 ≤ r + 1 := by omega
    have hp : 0 ≤ (r + 1) * (1000000000 : Int) :=
      Int.mul_nonneg h0 (by decide)
    have e : (r + 1) * (1000000000 : Int) + 698600000 =
        r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
      unfold lnErrorBoundDen lnErrorBoundNum
      rw [Int.add_mul, Int.one_mul]
      omega
    rw [← e]
    exact Int.add_nonneg hp (by decide)
  apply Int.ofNat_le.mp
  rw [Int.natCast_add, Int.natCast_add, posPhaseNatLt_cast hX hneg]
  unfold lnPhaseExtraArg lnDirectGapArg lnErrArg
  have htarget : ((((r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat *
      2 ^ 99 : Nat) : Int)) =
      (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
    rw [Int.natCast_mul, Int.toNat_of_nonneg harg]
    unfold twoPow99I
    rfl
  have hextra : (((lnErrorExtraNum * twoPow99N : Nat) : Int)) =
      (lnErrorExtraNum : Int) * twoPow99I := by
    unfold twoPow99N twoPow99I
    rfl
  have hgapcast :
      (((lnErrorDirectResidueGap * twoPow27N * lnErrorBoundDen : Nat) : Int)) =
        (lnErrorDirectResidueGap : Int) * twoPow27I * (lnErrorBoundDen : Int) := by
    unfold lnErrorDirectResidueGap twoPow27N twoPow27I lnErrorBoundDen
    decide
  rw [htarget, hextra, hgapcast]
  simpa [lnErrorBoundDen, lnErrorBoundNum, lnErrorExtraNum, twoPow99I]
    using hcore

theorem ge_phase_gap_direct_to_top {n m c : Nat} {r : Int}
    (hX : 0 ≤ toInt (x1W (zWord m))) (hc : c ≤ 160) (hr0 : -1 ≤ r)
    (hgap : PosShiftDirectResidueGapOk m c r)
    (hdirect : PosShiftGePhaseGapDirectOk n m c) :
    sumGE n (lnErrArg r) lnErrQ (posTopX c m) (10 ^ 18) := by
  unfold PosShiftGePhaseGapDirectOk at hdirect
  exact sumGE_exact_mono
    (posPhaseNatGe_gap_extra_le_lnErrArg hX hc hr0 hgap)
    (Nat.le_refl _) hdirect

theorem lt_phase_gap_direct_to_top {n m c : Nat} {r : Int}
    (hX : toInt (x1W (zWord m)) ≤ 0) (hc : c ≤ 160)
    (hneg : posNegXNat m ≤ posConstNat c) (hr0 : -1 ≤ r)
    (hgap : PosShiftDirectResidueGapOk m c r)
    (hdirect : PosShiftLtPhaseGapDirectOk n m c) :
    sumGE n (lnErrArg r) lnErrQ (posTopX c m) (10 ^ 18) := by
  unfold PosShiftLtPhaseGapDirectOk at hdirect
  exact sumGE_exact_mono
    (posPhaseNatLt_gap_extra_le_lnErrArg hX hc hneg hr0 hgap)
    (Nat.le_refl _) hdirect

theorem capLB_first_order_self (p q : Nat) :
    capLB p q (q + p) q := by
  refine ⟨1, ?_⟩
  simp only [fact, expNum, Nat.pow_one, Nat.mul_one, Nat.one_mul, Nat.zero_add]
  exact Nat.le_refl _

theorem capLB_cancel_first_order_budget {arg const neg q C W G V yT wT : Nat}
    (hq : 0 < q)
    (hconst : capLB const q C W)
    (hneg : capUB neg q G V)
    (hneg_le : neg ≤ const)
    (hphase : const - neg ≤ arg)
    (hW : 0 < W)
    (hG : 0 < G)
    (hbudget : yT * ((W * q) * G) ≤
      ((C * (q + (arg - (const - neg)))) * V) * wT) :
    capLB arg q yT wT := by
  have capE := capLB_first_order_self (arg - (const - neg)) q
  have hsum0 := capLB_mul hconst capE
  have hsplit : const + (arg - (const - neg)) =
      ((const - neg) + (arg - (const - neg))) + neg := by
    calc
      const + (arg - (const - neg)) =
          (const - neg + neg) + (arg - (const - neg)) := by
            rw [Nat.sub_add_cancel hneg_le]
      _ = ((const - neg) + (arg - (const - neg))) + neg := by
            omega
  rw [hsplit] at hsum0
  have capV := capLB_cancel (q := q) hq hsum0 hneg
  have harg : (const - neg) + (arg - (const - neg)) = arg := by
    exact Nat.add_sub_of_le hphase
  rw [harg] at capV
  refine capLB_weaken ?_ capV hbudget
  exact Nat.mul_pos (Nat.mul_pos hW hq) hG

theorem pos_residue_arg_le_int {A r : Int}
    (hres : A * (lnErrorBoundDen : Int) + (lnErrorCoarsePosResidue : Int) ≤
      (r + 1) * twoPow99I * (lnErrorBoundDen : Int)) :
    A * (lnErrorBoundDen : Int) + (lnErrorExtraNum : Int) * twoPow99I +
        (lnErrorCoarsePosResidue : Int) ≤
      (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  have hnum : ((lnErrorBoundNum : Nat) : Int) = (1698600000 : Int) := by
    unfold lnErrorBoundNum
    rfl
  have hextra : ((lnErrorExtraNum : Nat) : Int) = (698600000 : Int) := by
    unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen
    decide +kernel
  rw [hden] at hres
  rw [hden, hnum, hextra]
  unfold twoPow99I at hres ⊢
  omega

theorem pos_ge_residue_arg_le_int {A r : Int}
    (hres : A * (lnErrorBoundDen : Int) + (lnErrorCoarseGePosResidue : Int) ≤
      (r + 1) * twoPow99I * (lnErrorBoundDen : Int)) :
    A * (lnErrorBoundDen : Int) + (lnErrorExtraNum : Int) * twoPow99I +
        (lnErrorCoarseGePosResidue : Int) ≤
      (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  have hnum : ((lnErrorBoundNum : Nat) : Int) = (1698600000 : Int) := by
    unfold lnErrorBoundNum
    rfl
  have hextra : ((lnErrorExtraNum : Nat) : Int) = (698600000 : Int) := by
    unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen
    decide +kernel
  rw [hden] at hres
  rw [hden, hnum, hextra]
  unfold twoPow99I at hres ⊢
  omega

theorem errBudgetL_fold {m k : Nat} (hm : Sc - 45 ≤ m) (hk : k ≤ 159) :
    (m + 1) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) ≤
      m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 31 - 3384) *
        (10 ^ 31 + lnErrorCoarsePosBudgetCap) * (10 ^ 31 - 10) * 10 ^ 18) := by
  have hb := errBudgetL_le (k := k) hk
  have hcross : (m + 1) * (Sc - 45) ≤ m * ((Sc - 45) + 1) := by
    have e1 : (m + 1) * (Sc - 45) = m * (Sc - 45) + (Sc - 45) := by
      rw [Nat.add_mul, Nat.one_mul]
    have e2 : m * ((Sc - 45) + 1) = m * (Sc - 45) + m := by
      rw [Nat.mul_add, Nat.mul_one]
    omega
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < Sc - 45 by decide)
  calc (Sc - 45) * ((m + 1) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142))
      = ((m + 1) * (Sc - 45)) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm]
    _ ≤ (m * ((Sc - 45) + 1)) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) :=
        Nat.mul_le_mul_right _ hcross
    _ = m * (((Sc - 45) + 1) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142)) := by
        simp only [Nat.mul_assoc]
    _ = m * (((Sc - 45) + 1) * 2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) := by
        simp only [Nat.mul_assoc]
    _ ≤ m * ((Sc - 45) * (10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarsePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18) :=
        Nat.mul_le_mul_left _ hb
    _ = (Sc - 45) * (m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarsePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem errBudgetL_ge_fold {m k : Nat} (hm : Sc ≤ m) (hk : k ≤ 159) :
    (m + 1) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) ≤
      m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 31 - 3384) *
        (10 ^ 31 + lnErrorCoarseGePosBudgetCap) * (10 ^ 31 - 10) * 10 ^ 18) := by
  have hb := errBudgetLGe_le (k := k) hk
  have hcross : (m + 1) * Sc ≤ m * (Sc + 1) := by
    have e1 : (m + 1) * Sc = m * Sc + Sc := by
      rw [Nat.add_mul, Nat.one_mul]
    have e2 : m * (Sc + 1) = m * Sc + m := by
      rw [Nat.mul_add, Nat.mul_one]
    omega
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < Sc by decide)
  calc Sc * ((m + 1) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142))
      = ((m + 1) * Sc) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm]
    _ ≤ (m * (Sc + 1)) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) :=
        Nat.mul_le_mul_right _ hcross
    _ = m * ((Sc + 1) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142)) := by
        simp only [Nat.mul_assoc]
    _ = m * ((Sc + 1) * 2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) := by
        simp only [Nat.mul_assoc]
    _ ≤ m * (Sc * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseGePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18)) :=
        Nat.mul_le_mul_left _ (by
          simpa only [Nat.mul_assoc] using hb)
    _ = Sc * (m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseGePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem lo_ge_pos_budget_exact {m c x : Nat} {r : Int} (h1 : Sc ≤ m) (h2 : m < MHI)
    (_hc : c < 160)
    (hbudget : PosShiftGeBudgetOk m c x r) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have cap1 := capLB_lift_right (den := lnErrorBoundDen) QS_pos (x1capGeLoF h1 h2)
  have cap2LQ := capLB_lift_right (den := lnErrorBoundDen) QS_pos cap2L
  have cap2 := capLB_pow cap2LQ (160 - c)
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have cap12 := capLB_mul cap1 cap2
  have cap123 := capLB_mul cap12 capB
  change capLB (posPhaseNatGe m c) lnErrQ (posBaseYGe m c) (posBaseWGe c) at cap123
  have capE := capLB_first_order_self (posAvailGe m c r) lnErrQ
  have capR0 := capLB_mul cap123 capE
  have hphase : posPhaseNatGe m c ≤ lnErrArg r := hbudget.1
  have hsum : posPhaseNatGe m c + posAvailGe m c r = lnErrArg r := by
    unfold posAvailGe
    exact Nat.add_sub_of_le hphase
  rw [hsum] at capR0
  refine capLB_weaken ?_ capR0 ?_
  · unfold posBaseWGe lnErrQ QS lnErrorBoundDen
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))
      (by decide)) (by decide)
  · exact hbudget.2

theorem lo_lt_pos_budget_exact {m c x : Nat} {r : Int} (h1 : MLO ≤ m) (h2 : m < Sc)
    (_hc : c < 160)
    (hbudget : PosShiftLtBudgetOk m c x r) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have cap1 := capUB_lift_right (den := lnErrorBoundDen) QS_pos (x1capLtLoF h1 h2)
  have cap2LQ := capLB_lift_right (den := lnErrorBoundDen) QS_pos cap2L
  have cap2 := capLB_pow cap2LQ (160 - c)
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have hsum0 := capLB_mul cap2 capB
  change capUB (posNegXNat m) lnErrQ
    560227709747861399187319382270000000000000000000000000000000
    (m * 9999999999999999999999999996615) at cap1
  change capLB (posConstNat c) lnErrQ
    ((2 * (10 ^ 40 - 1)) ^ (160 - c) * (Sc * (10 ^ 31 - 3384)))
    (((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31))) at hsum0
  refine capLB_cancel_first_order_budget
    (arg := lnErrArg r)
    (const := posConstNat c)
    (neg := posNegXNat m)
    (q := lnErrQ)
    (C := ((2 * (10 ^ 40 - 1)) ^ (160 - c) * (Sc * (10 ^ 31 - 3384))))
    (W := (((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31))))
    (G := 560227709747861399187319382270000000000000000000000000000000)
    (V := m * 9999999999999999999999999996615)
    (yT := wadRayNum x)
    (wT := wadRayStrictDen)
    (by unfold lnErrQ; decide)
    hsum0 cap1 hbudget.1 hbudget.2.1 ?_ ?_ ?_
  · exact Nat.mul_pos (Nat.pow_pos (by decide)) (by decide)
  · decide
  · simpa [PosShiftLtBudgetOk, posBaseYLt, posBaseWLt, posAvailLt,
      posPhaseNatLt, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hbudget.2.2

theorem ln_err_arg_nonneg {r : Int} (hr0 : -1 ≤ r) :
    0 ≤ r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
  have h0 : 0 ≤ r + 1 := by omega
  have hp : 0 ≤ (r + 1) * (1000000000 : Int) :=
    Int.mul_nonneg h0 (by decide)
  have e : (r + 1) * (1000000000 : Int) + 698600000 =
      r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
    unfold lnErrorBoundDen lnErrorBoundNum
    rw [Int.add_mul, Int.one_mul]
    omega
  rw [← e]
  exact Int.add_nonneg hp (by decide)

theorem ln_err_neg_arg_nonneg {r : Int} (hr : r ≤ -2) :
    0 ≤ -(r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) := by
  unfold lnErrorBoundDen lnErrorBoundNum
  omega

theorem ln_err_neg_arg_le_int {A r : Int}
    (hA : A ≤ (r + 1) * twoPow99I - twoPow27I) (_hr : r ≤ -2) :
    (-(r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int))) * twoPow99I ≤
      -(A * (lnErrorBoundDen : Int) + 698600000 * twoPow99I) := by
  unfold twoPow99I twoPow27I at hA
  have hmul := Int.mul_le_mul_of_nonneg_right hA (by decide : 0 ≤ (1000000000 : Int))
  have eDen : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  have eNum : ((lnErrorBoundNum : Nat) : Int) = (1698600000 : Int) := by
    unfold lnErrorBoundNum
    rfl
  rw [eDen, eNum]
  unfold twoPow99I
  omega

theorem v_c160_nonneg {m : Nat} (h1 : MLO ≤ m) (h2 : m < MHI) :
    0 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt 160 +
      lnBiasI := by
  have hb := (LnGeneratedModel.r1_bound h1 h2).1
  have hm := Int.mul_le_mul_of_nonneg_right hb
    (by decide : 0 ≤ (7450580596923828125 : Int))
  have hfloor :
      0 ≤
        (-(240000000000000000000000000000 : Int)) *
          7450580596923828125 + lnBiasI := by
    unfold lnBiasI
    decide
  have hln2 : ln2kInt 160 = 0 := by
    unfold ln2kInt
    rw [if_pos (by decide)]
    decide
  rw [hln2]
  omega

def ten31 : Nat := 10 ^ 31

def c160W0 : Nat := Sc * ten31
def c160W : Nat := Sc * (10 : Nat) ^ 111

def c160R0 : Nat := ten31 - 3385
def c160R1 : Nat := ten31 - 3384
def c160R2 : Nat := ten31 + lnErrorExtraCap
def c160R3 : Nat := ten31 - 10
def c160R4 : Nat := 10 ^ 18
def c160R : Nat := Sc * (c160R0 * c160R1 * c160R2 * c160R3 * c160R4)

theorem lo_ge_c160_exact {m x : Nat} {r : Int} (h1 : Sc ≤ m) (h2 : m < MHI)
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt 160 +
      116873961749927929127912020551516284764321243411868 < (r + 1) * 2 ^ 72)
    (hr0 : -1 ≤ r) (hmx : m ≤ x) (hxm : x < m + 1) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have hx : x = m := by omega
  subst x
  have hX1 := x1_nonneg_geF h1 h2
  have harg_nonneg := ln_err_arg_nonneg hr0
  have cap1 := capLB_lift_right (den := lnErrorBoundDen) QS_pos (x1capGeLoF h1 h2)
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have cap12 := capLB_mul cap1 capB
  have cap123 := capLB_mul cap12 capEFracL
  have hmul :
      ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 *
        lnErrorBoundDen + BIASc * 2 ^ 27 * lnErrorBoundDen +
          lnErrorExtraNum * 2 ^ 99) * lnErrQ ≤ lnErrArg r * lnErrQ := by
    have hmul0 :
        ((((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
          BIASc * 2 ^ 27) * lnErrorBoundDen +
            lnErrorExtraNum * 2 ^ 99) * lnErrQ ≤ lnErrArg r * lnErrQ) := by
      simpa [lnErrArg, lnErrQ] using
      Nat.mul_le_mul_right (QS * lnErrorBoundDen)
        (c160_phase_arg_le (X := toInt (x1W (zWord m))) hX1
          (phase_lt_scaled_le hr) harg_nonneg)
    have hdist :
        (toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 *
          lnErrorBoundDen + BIASc * 2 ^ 27 * lnErrorBoundDen +
            lnErrorExtraNum * 2 ^ 99 =
        (((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
          BIASc * 2 ^ 27) * lnErrorBoundDen +
            lnErrorExtraNum * 2 ^ 99) := by
      rw [Nat.add_mul]
    rw [hdist]
    exact hmul0
  have capR : capLB (lnErrArg r) lnErrQ
      (((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384))) *
        (10 ^ 31 + lnErrorExtraCap))
      ((560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) :=
    @capLB_arg
      (lnErrArg r) lnErrQ
      (((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 *
        lnErrorBoundDen + BIASc * 2 ^ 27 * lnErrorBoundDen +
          lnErrorExtraNum * 2 ^ 99))
      lnErrQ
      ((((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384))) *
        (10 ^ 31 + lnErrorExtraCap)))
      (((560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31)) * 10 ^ 31))
      (by unfold lnErrQ; decide) hmul cap123
  refine capLB_weaken (p := lnErrArg r) (q := lnErrQ)
    (y := ((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384))) *
      (10 ^ 31 + lnErrorExtraCap))
    (w := ((560227709747861399187319382270000000000000000000000000000000 *
      (10 ^ 18 * 10 ^ 31)) * 10 ^ 31))
    ?_ capR ?_
  · have h1' : 0 < (560227709747861399187319382270000000000000000000000000000000 : Nat) *
        (10 ^ 18 * 10 ^ 31) := by decide
    exact Nat.mul_pos h1' (by decide)
  · have hb := Nat.mul_le_mul_left (m * Sc) errBudgetL0_exact
    have eL : (m * 10 ^ 31) *
        ((560227709747861399187319382270000000000000000000000000000000 *
          (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) =
        m * Sc * (10 : Nat) ^ 142 := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * (10 : Nat) ^ 31 from by unfold Sc; decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have eR : (((m * 9999999999999999999999999996615) *
          (Sc * (10 ^ 31 - 3384))) * (10 ^ 31 + lnErrorExtraCap)) *
          (10 ^ 18 * (10 ^ 31 - 10)) =
        m * Sc * (((10 : Nat) ^ 31 - 3385) * ((10 : Nat) ^ 31 - 3384) *
          ((10 : Nat) ^ 31 + lnErrorExtraCap) * ((10 : Nat) ^ 31 - 10) *
            (10 : Nat) ^ 18) := by
      rw [show (9999999999999999999999999996615 : Nat) = (10 : Nat) ^ 31 - 3385
        from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    unfold wadRayNum wadRayStrictDen
    rw [eL, eR]
    exact hb

theorem lo_lt_c160_exact {m x : Nat} {r : Int} (h1 : MLO ≤ m) (h2 : m < Sc)
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt 160 +
      116873961749927929127912020551516284764321243411868 < (r + 1) * 2 ^ 72)
    (hmx : m ≤ x) (hxm : x < m + 1) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have hx : x = m := by omega
  subst x
  have hmhi : m < MHI := by
    simp only [Sc, MHI] at h2 ⊢
    omega
  have hV0I := v_c160_nonneg h1 hmhi
  have hV0 : 0 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt 160 +
      116873961749927929127912020551516284764321243411868 := by
    simpa [lnBiasI] using hV0I
  have hr0 : -1 ≤ r := by
    rcases Int.lt_or_le r (-1) with hlt | hle
    · exfalso
      have hrle : (r + 1) * 2 ^ 72 ≤ 0 := by
        have hle' : r + 1 ≤ 0 := by omega
        exact Int.mul_le_mul_of_nonneg_right hle' (by decide : (0 : Int) ≤ 2 ^ 72)
      omega
    · exact hle
  have hX1 := x1_nonpos_ltF h1 h2
  have harg_nonneg := ln_err_arg_nonneg hr0
  have cap1 := capUB_lift_right (den := lnErrorBoundDen) QS_pos (x1capLtLoF h1 h2)
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have capBE := capLB_mul capB capEFracL
  change capUB ((-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen)
    lnErrQ 560227709747861399187319382270000000000000000000000000000000
      (m * 9999999999999999999999999996615) at cap1
  change capLB (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N)
    lnErrQ (Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorExtraCap))
      (10 ^ 18 * 10 ^ 31 * 10 ^ 31) at capBE
  have hVs0 : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt 160 +
        lnBiasI) * twoPow27I =
      toInt (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
    have hVs := v_scale_pos (toInt (x1W (zWord m))) 160 (by decide)
    simpa only [Nat.sub_self, Nat.zero_mul, Int.natCast_zero, Int.zero_mul,
      Int.add_zero, twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
  have hV0s : 0 ≤
      toInt (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
    have hpow27 : (0 : Int) ≤ twoPow27I := by
      unfold twoPow27I
      decide
    have h := Int.mul_le_mul_of_nonneg_right hV0I hpow27
    rw [hVs0] at h
    exact h
  have hnegXn :
      (((-toInt (x1W (zWord m))).toNat : Nat) : Int) =
        -toInt (x1W (zWord m)) :=
    Int.toNat_of_nonneg (by omega)
  have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
    unfold twoPow27N twoPow27I lnBiasI
    decide +kernel
  have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  have hextra : ((lnErrorExtraNum * twoPow99N : Nat) : Int) =
      698600000 * twoPow99I := by
    unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen twoPow99N twoPow99I
    decide +kernel
  have hsub_le : (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN *
        lnErrorBoundDen ≤
      BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N := by
    apply Int.ofNat_le.mp
    simp only [Int.natCast_add, Int.natCast_mul, hnegXn, hBc, hscale, hden, hextra]
    have hmain : (-toInt (x1W (zWord m))) * lnPhaseScaleI ≤ lnBiasI * twoPow27I := by
      rw [Int.neg_mul]
      generalize toInt (x1W (zWord m)) * lnPhaseScaleI = A at hV0s ⊢
      generalize lnBiasI * twoPow27I = B at hV0s ⊢
      omega
    have hmul := Int.mul_le_mul_of_nonneg_right hmain (by decide : 0 ≤ (1000000000 : Int))
    have hnon : 0 ≤ 698600000 * twoPow99I := by
      unfold twoPow99I
      decide
    exact Int.le_trans hmul (Int.le_add_of_nonneg_right hnon)
  have hsplit :
      BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N =
        (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
          (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen) +
          (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen := by
    exact (Nat.sub_add_cancel hsub_le).symm
  rw [hsplit] at capBE
  have capV := capLB_cancel (q := lnErrQ) (by unfold lnErrQ; decide) capBE cap1
  have hple :
      BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
          (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen ≤
        lnErrArg r := by
    apply Int.ofNat_le.mp
    have htarget : (((r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat *
        2 ^ 99 : Nat) : Int) =
        (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
      rw [Int.natCast_mul, Int.toNat_of_nonneg harg_nonneg]
      unfold twoPow99I
      rfl
    have hsub_cast :
        (((BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
          (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)) =
        (toInt (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I) *
            (1000000000 : Int) + 698600000 * twoPow99I := by
      have hsI := congrArg (fun n : Nat => ((n : Nat) : Int)) hsplit
      simp only [Int.natCast_add, Int.natCast_mul, hnegXn, hBc, hscale, hden, hextra] at hsI
      rw [Int.neg_mul] at hsI
      generalize (((BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
        (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)) = S
        at hsI ⊢
      generalize toInt (x1W (zWord m)) * lnPhaseScaleI = A at hsI ⊢
      generalize lnBiasI * twoPow27I = B at hsI ⊢
      generalize 698600000 * twoPow99I = E at hsI ⊢
      omega
    rw [lnErrArg, htarget, hsub_cast]
    have hsc : (toInt (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I) ≤
        (r + 1) * twoPow99I - twoPow27I := by
      have hrI : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt 160 +
          lnBiasI < (r + 1) * 2 ^ 72 := by
        simpa [lnBiasI] using hr
      have h := phase_lt_scaled_le hrI
      change (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt 160 +
          lnBiasI) * twoPow27I ≤ ((r + 1) * twoPow72I - 1) * twoPow27I at h
      rw [hVs0] at h
      have er : ((r + 1) * twoPow72I - 1) * twoPow27I =
          (r + 1) * twoPow99I - twoPow27I := by
        unfold twoPow72I twoPow27I twoPow99I
        rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
          by decide]
        omega
      rw [er] at h
      exact h
    have hcore := c160_arg_le_int (A :=
        toInt (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I) (r := r) hsc
    simpa [lnErrorBoundDen, lnErrorBoundNum, twoPow99I] using hcore
  have hmul :
      (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
          (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen) * lnErrQ ≤
        lnErrArg r * lnErrQ :=
    Nat.mul_le_mul_right _ hple
  have capR : capLB (lnErrArg r) lnErrQ
      ((Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorExtraCap)) *
        (m * 9999999999999999999999999996615))
      (((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
        560227709747861399187319382270000000000000000000000000000000) :=
    @capLB_arg
      (lnErrArg r) lnErrQ
      (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
        (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen)
      lnErrQ
      ((Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorExtraCap)) *
        (m * 9999999999999999999999999996615))
      (((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
        560227709747861399187319382270000000000000000000000000000000)
      (by unfold lnErrQ; decide) hmul capV
  refine capLB_weaken (p := lnErrArg r) (q := lnErrQ)
    (y := (Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorExtraCap)) *
      (m * 9999999999999999999999999996615))
    (w := ((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
      560227709747861399187319382270000000000000000000000000000000)
    ?_ capR ?_
  · have h1' : 0 < ((10 ^ 18 * 10 ^ 31) * 10 ^ 31 : Nat) := by decide
    exact Nat.mul_pos h1' (by decide)
  · have hb := Nat.mul_le_mul_left (m * Sc) errBudgetL0_exact
    have eL : (m * 10 ^ 31) *
        (((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
          560227709747861399187319382270000000000000000000000000000000) =
        m * Sc * (10 : Nat) ^ 142 := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * (10 : Nat) ^ 31 from by unfold Sc; decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have eR : ((Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorExtraCap)) *
          (m * 9999999999999999999999999996615)) *
          (10 ^ 18 * (10 ^ 31 - 10)) =
        m * Sc * (((10 : Nat) ^ 31 - 3385) * ((10 : Nat) ^ 31 - 3384) *
          ((10 : Nat) ^ 31 + lnErrorExtraCap) * ((10 : Nat) ^ 31 - 10) *
            (10 : Nat) ^ 18) := by
      rw [show (9999999999999999999999999996615 : Nat) = (10 : Nat) ^ 31 - 3385
        from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    unfold wadRayNum wadRayStrictDen
    rw [eL, eR]
    exact hb

theorem lo_ge_pos_exact {m c x : Nat} {r : Int} (h1 : Sc ≤ m) (h2 : m < MHI)
    (hc1 : 1 ≤ c) (hc : c < 160)
    (hr0 : 0 ≤ r)
    (hres : PosShiftResidueOk m c r)
    (hxm : x < (m + 1) * 2 ^ (160 - c)) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have harg_nonneg := ln_err_arg_nonneg (by omega : -1 ≤ r)
  have hX1 := x1_nonneg_geF h1 h2
  have cap1 := capLB_lift_right (den := lnErrorBoundDen) QS_pos (x1capGeLoF h1 h2)
  have cap2LQ := capLB_lift_right (den := lnErrorBoundDen) QS_pos cap2L
  have cap2 := capLB_pow cap2LQ (160 - c)
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have cap12 := capLB_mul cap1 cap2
  have cap123 := capLB_mul cap12 capB
  have cap1234 := capLB_mul cap123 capECoarsePosL
  change capLB
    (((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
      (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
        BIASc * twoPow27N * lnErrorBoundDen) +
      (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue))
    lnErrQ
      (((m * 9999999999999999999999999996615) *
        ((2 * (10 ^ 40 - 1)) ^ (160 - c))) *
        (Sc * (10 ^ 31 - 3384)) *
        (10 ^ 31 + lnErrorCoarsePosBudgetCap))
      (((560227709747861399187319382270000000000000000000000000000000 *
        ((10 ^ 40 : Nat) ^ (160 - c))) *
        (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) at cap1234
  have hple :
      ((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
          BIASc * twoPow27N * lnErrorBoundDen) +
        (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue) ≤
      lnErrArg r := by
    apply Int.ofNat_le.mp
    have htarget : (((r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat *
        2 ^ 99 : Nat) : Int) =
        (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
      rw [Int.natCast_mul, Int.toNat_of_nonneg harg_nonneg]
      unfold twoPow99I
      rfl
    have hX1n : ((toInt (x1W (zWord m))).toNat : Int) =
        toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
      unfold twoPow27N twoPow27I lnBiasI
      decide +kernel
    have hLc : (((160 - c) * (LN2c * twoPow27N) : Nat) : Int) =
        ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) := by
      simp only [Int.natCast_mul]
      unfold twoPow27N twoPow27I
      rfl
    have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
      unfold lnErrorBoundDen
      rfl
    have hextra : ((lnErrorExtraNum * twoPow99N : Nat) : Int) =
        (lnErrorExtraNum : Int) * twoPow99I := by
      unfold twoPow99N twoPow99I
      rfl
    have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
    have hN : (((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
        (((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I)) *
          (1000000000 : Int) := by
      rw [show (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
          ((160 - c) * (LN2c * twoPow27N)) * lnErrorBoundDen by
            simp only [Nat.mul_assoc]]
      simp only [Int.natCast_mul, hLc, hden]
    have hsum_cast :
        ((((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
            BIASc * twoPow27N * lnErrorBoundDen) +
          (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue) : Nat) : Int) =
        posPhaseI m c * (lnErrorBoundDen : Int) +
          (lnErrorExtraNum : Int) * twoPow99I +
            (lnErrorCoarsePosResidue : Int) := by
      simp only [Int.natCast_add, Int.natCast_mul, hX1n, hBc, hN, hden,
        hextra, hscale]
      unfold posPhaseI
      generalize toInt (x1W (zWord m)) * lnPhaseScaleI = A
      generalize ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B
      generalize lnBiasI * twoPow27I = C
      generalize (lnErrorExtraNum : Int) * twoPow99I = E
      generalize (lnErrorCoarsePosResidue : Int) = G
      omega
    rw [lnErrArg, htarget, hsum_cast]
    exact pos_residue_arg_le_int hres
  have hmul :
      (((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
          BIASc * twoPow27N * lnErrorBoundDen) +
        (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue)) * lnErrQ ≤
      lnErrArg r * lnErrQ :=
    Nat.mul_le_mul_right _ hple
  have capR := capLB_arg (q := lnErrQ) (by unfold lnErrQ; decide) hmul cap1234
  refine capLB_weaken (p := lnErrArg r) (q := lnErrQ)
    (y := (((m * 9999999999999999999999999996615) *
      ((2 * (10 ^ 40 - 1)) ^ (160 - c))) *
      (Sc * (10 ^ 31 - 3384)) *
      (10 ^ 31 + lnErrorCoarsePosBudgetCap)))
    (w := (((560227709747861399187319382270000000000000000000000000000000 *
      ((10 ^ 40 : Nat) ^ (160 - c))) *
      (10 ^ 18 * 10 ^ 31)) * 10 ^ 31)) ?_ capR ?_
  · have h1' : 0 < (560227709747861399187319382270000000000000000000000000000000 : Nat) *
        ((10 ^ 40 : Nat) ^ (160 - c)) := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
    have h2' : 0 < (560227709747861399187319382270000000000000000000000000000000 : Nat) *
        ((10 ^ 40 : Nat) ^ (160 - c)) * (10 ^ 18 * 10 ^ 31) :=
      Nat.mul_pos h1' (by decide)
    exact Nat.mul_pos h2' (by decide)
  · have hMLO : Sc - 45 ≤ m := by omega
    have hb := errBudgetL_fold (k := 160 - c) hMLO (by omega)
    have hx1 : x + 1 ≤ (m + 1) * 2 ^ (160 - c) := by omega
    have hxw : (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) ≤
        (m + 1) * 2 ^ (160 - c) *
          (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) :=
      Nat.mul_le_mul_right _ hx1
    have hfold : (m + 1) * 2 ^ (160 - c) *
        (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) ≤
        m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarsePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
      have h := Nat.mul_le_mul_left Sc hb
      have e1 : Sc * ((m + 1) * (2 ^ (160 - c) *
          (10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) =
          (m + 1) * 2 ^ (160 - c) *
            (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have e2 : Sc * (m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarsePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18)) =
          m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
            (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarsePosBudgetCap) *
            (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e1] at h
      rw [e2] at h
      exact h
    have eL : x * 10 ^ 31 *
        (((560227709747861399187319382270000000000000000000000000000000 *
          (10 ^ 40 : Nat) ^ (160 - c)) * (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) ≤
        (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * 10 ^ 31 from by decide]
      have eAC : x * 10 ^ 31 *
          (((Sc * 10 ^ 31 * (10 ^ 40 : Nat) ^ (160 - c)) *
            (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) =
          x * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) *
            ((10 : Nat) ^ 31 * (10 ^ 31 * (10 ^ 18 * 10 ^ 31 * 10 ^ 31))))) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [eAC, show ((10 : Nat) ^ 31 * (10 ^ 31 * (10 ^ 18 * 10 ^ 31 * 10 ^ 31))) =
        10 ^ 142 from by decide]
      exact Nat.mul_le_mul_right _ (by omega : x ≤ x + 1)
    have eR : (((m * 9999999999999999999999999996615) *
        ((2 * (10 ^ 40 - 1)) ^ (160 - c))) *
        (Sc * (10 ^ 31 - 3384)) * (10 ^ 31 + lnErrorCoarsePosBudgetCap)) *
        (10 ^ 18 * (10 ^ 31 - 10)) =
        m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarsePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
      rw [show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    unfold wadRayNum wadRayStrictDen
    generalize hT1 : x * 10 ^ 31 *
      (((560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 40 : Nat) ^ (160 - c)) * (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) = T1
      at eL ⊢
    generalize hT2 : (x + 1) *
      (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) = T2 at eL hxw
    generalize hT3 : (m + 1) * 2 ^ (160 - c) *
      (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) = T3 at hxw hfold
    generalize hT4 : m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
      (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarsePosBudgetCap) *
      (10 ^ 31 - 10) * 10 ^ 18) * Sc = T4 at hfold eR
    generalize hT5 : (((m * 9999999999999999999999999996615) *
      ((2 * (10 ^ 40 - 1)) ^ (160 - c))) *
      (Sc * (10 ^ 31 - 3384)) * (10 ^ 31 + lnErrorCoarsePosBudgetCap)) *
      (10 ^ 18 * (10 ^ 31 - 10)) = T5 at eR ⊢
    omega

theorem lo_ge_pos_exact_ge_residue {m c x : Nat} {r : Int} (h1 : Sc ≤ m) (h2 : m < MHI)
    (hc1 : 1 ≤ c) (hc : c < 160)
    (hr0 : 0 ≤ r)
    (hres : PosShiftGeResidueOk m c r)
    (hxm : x < (m + 1) * 2 ^ (160 - c)) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have harg_nonneg := ln_err_arg_nonneg (by omega : -1 ≤ r)
  have hX1 := x1_nonneg_geF h1 h2
  have cap1 := capLB_lift_right (den := lnErrorBoundDen) QS_pos (x1capGeLoF h1 h2)
  have cap2LQ := capLB_lift_right (den := lnErrorBoundDen) QS_pos cap2L
  have cap2 := capLB_pow cap2LQ (160 - c)
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have cap12 := capLB_mul cap1 cap2
  have cap123 := capLB_mul cap12 capB
  have cap1234 := capLB_mul cap123 capECoarseGePosL
  change capLB
    (((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
      (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
        BIASc * twoPow27N * lnErrorBoundDen) +
      (lnErrorExtraNum * twoPow99N + lnErrorCoarseGePosResidue))
    lnErrQ
      (((m * 9999999999999999999999999996615) *
        ((2 * (10 ^ 40 - 1)) ^ (160 - c))) *
        (Sc * (10 ^ 31 - 3384)) *
        (10 ^ 31 + lnErrorCoarseGePosBudgetCap))
      (((560227709747861399187319382270000000000000000000000000000000 *
        ((10 ^ 40 : Nat) ^ (160 - c))) *
        (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) at cap1234
  have hple :
      ((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
          BIASc * twoPow27N * lnErrorBoundDen) +
        (lnErrorExtraNum * twoPow99N + lnErrorCoarseGePosResidue) ≤
      lnErrArg r := by
    apply Int.ofNat_le.mp
    have htarget : (((r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat *
        2 ^ 99 : Nat) : Int) =
        (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
      rw [Int.natCast_mul, Int.toNat_of_nonneg harg_nonneg]
      unfold twoPow99I
      rfl
    have hX1n : ((toInt (x1W (zWord m))).toNat : Int) =
        toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
      unfold twoPow27N twoPow27I lnBiasI
      decide +kernel
    have hLc : (((160 - c) * (LN2c * twoPow27N) : Nat) : Int) =
        ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) := by
      simp only [Int.natCast_mul]
      unfold twoPow27N twoPow27I
      rfl
    have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
      unfold lnErrorBoundDen
      rfl
    have hextra : ((lnErrorExtraNum * twoPow99N : Nat) : Int) =
        (lnErrorExtraNum : Int) * twoPow99I := by
      unfold twoPow99N twoPow99I
      rfl
    have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
    have hN : (((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
        (((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I)) *
          (1000000000 : Int) := by
      rw [show (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
          ((160 - c) * (LN2c * twoPow27N)) * lnErrorBoundDen by
            simp only [Nat.mul_assoc]]
      simp only [Int.natCast_mul, hLc, hden]
    have hsum_cast :
        ((((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
            BIASc * twoPow27N * lnErrorBoundDen) +
          (lnErrorExtraNum * twoPow99N + lnErrorCoarseGePosResidue) : Nat) : Int) =
        posPhaseI m c * (lnErrorBoundDen : Int) +
          (lnErrorExtraNum : Int) * twoPow99I +
            (lnErrorCoarseGePosResidue : Int) := by
      simp only [Int.natCast_add, Int.natCast_mul, hX1n, hBc, hN, hden,
        hextra, hscale]
      unfold posPhaseI
      generalize toInt (x1W (zWord m)) * lnPhaseScaleI = A
      generalize ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B
      generalize lnBiasI * twoPow27I = C
      generalize (lnErrorExtraNum : Int) * twoPow99I = E
      generalize (lnErrorCoarseGePosResidue : Int) = G
      omega
    rw [lnErrArg, htarget, hsum_cast]
    exact pos_ge_residue_arg_le_int hres
  have hmul :
      (((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
          BIASc * twoPow27N * lnErrorBoundDen) +
        (lnErrorExtraNum * twoPow99N + lnErrorCoarseGePosResidue)) * lnErrQ ≤
      lnErrArg r * lnErrQ :=
    Nat.mul_le_mul_right _ hple
  have capR := capLB_arg (q := lnErrQ) (by unfold lnErrQ; decide) hmul cap1234
  refine capLB_weaken (p := lnErrArg r) (q := lnErrQ)
    (y := (((m * 9999999999999999999999999996615) *
      ((2 * (10 ^ 40 - 1)) ^ (160 - c))) *
      (Sc * (10 ^ 31 - 3384)) *
      (10 ^ 31 + lnErrorCoarseGePosBudgetCap)))
    (w := (((560227709747861399187319382270000000000000000000000000000000 *
      ((10 ^ 40 : Nat) ^ (160 - c))) *
      (10 ^ 18 * 10 ^ 31)) * 10 ^ 31)) ?_ capR ?_
  · have h1' : 0 < (560227709747861399187319382270000000000000000000000000000000 : Nat) *
        ((10 ^ 40 : Nat) ^ (160 - c)) := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
    have h2' : 0 < (560227709747861399187319382270000000000000000000000000000000 : Nat) *
        ((10 ^ 40 : Nat) ^ (160 - c)) * (10 ^ 18 * 10 ^ 31) :=
      Nat.mul_pos h1' (by decide)
    exact Nat.mul_pos h2' (by decide)
  · have hb := errBudgetL_ge_fold (k := 160 - c) h1 (by omega)
    have hx1 : x + 1 ≤ (m + 1) * 2 ^ (160 - c) := by omega
    have hxw : (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) ≤
        (m + 1) * 2 ^ (160 - c) *
          (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) :=
      Nat.mul_le_mul_right _ hx1
    have hfold : (m + 1) * 2 ^ (160 - c) *
        (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) ≤
        m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseGePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
      have h := Nat.mul_le_mul_left Sc hb
      have e1 : Sc * ((m + 1) * (2 ^ (160 - c) *
          (10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) =
          (m + 1) * 2 ^ (160 - c) *
            (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have e2 : Sc * (m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseGePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18)) =
          m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
            (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseGePosBudgetCap) *
            (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e1] at h
      rw [e2] at h
      exact h
    have eL : x * 10 ^ 31 *
        (((560227709747861399187319382270000000000000000000000000000000 *
          (10 ^ 40 : Nat) ^ (160 - c)) * (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) ≤
        (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * 10 ^ 31 from by decide]
      have eAC : x * 10 ^ 31 *
          (((Sc * 10 ^ 31 * (10 ^ 40 : Nat) ^ (160 - c)) *
            (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) =
          x * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) *
            ((10 : Nat) ^ 31 * (10 ^ 31 * (10 ^ 18 * 10 ^ 31 * 10 ^ 31))))) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [eAC, show ((10 : Nat) ^ 31 * (10 ^ 31 * (10 ^ 18 * 10 ^ 31 * 10 ^ 31))) =
        10 ^ 142 from by decide]
      exact Nat.mul_le_mul_right _ (by omega : x ≤ x + 1)
    have eR : (((m * 9999999999999999999999999996615) *
        ((2 * (10 ^ 40 - 1)) ^ (160 - c))) *
        (Sc * (10 ^ 31 - 3384)) * (10 ^ 31 + lnErrorCoarseGePosBudgetCap)) *
        (10 ^ 18 * (10 ^ 31 - 10)) =
        m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseGePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
      rw [show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    unfold wadRayNum wadRayStrictDen
    generalize hT1 : x * 10 ^ 31 *
      (((560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 40 : Nat) ^ (160 - c)) * (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) = T1
      at eL ⊢
    generalize hT2 : (x + 1) *
      (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) = T2 at eL hxw
    generalize hT3 : (m + 1) * 2 ^ (160 - c) *
      (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) = T3 at hxw hfold
    generalize hT4 : m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
      (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseGePosBudgetCap) *
      (10 ^ 31 - 10) * 10 ^ 18) * Sc = T4 at hfold eR
    generalize hT5 : (((m * 9999999999999999999999999996615) *
      ((2 * (10 ^ 40 - 1)) ^ (160 - c))) *
      (Sc * (10 ^ 31 - 3384)) * (10 ^ 31 + lnErrorCoarseGePosBudgetCap)) *
      (10 ^ 18 * (10 ^ 31 - 10)) = T5 at eR ⊢
    omega

theorem lo_lt_pos_exact {m c x : Nat} {r : Int} (h1 : Sc - 45 ≤ m) (h2 : m < Sc)
    (hc1 : 1 ≤ c) (hc : c < 160)
    (hrlo : r * 2 ^ 72 ≤ toInt (x1W (zWord m)) * 7450580596923828125 +
      ln2kInt c + 116873961749927929127912020551516284764321243411868)
    (hr0 : 0 ≤ r)
    (hres : PosShiftResidueOk m c r)
    (hxm : x < (m + 1) * 2 ^ (160 - c)) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have hmlo : MLO ≤ m := Nat.le_trans (by decide : MLO ≤ Sc - 45) h1
  have harg_nonneg := ln_err_arg_nonneg (by omega : -1 ≤ r)
  have cap1 := capUB_lift_right (den := lnErrorBoundDen) QS_pos (x1capLtLoF hmlo h2)
  have cap2LQ := capLB_lift_right (den := lnErrorBoundDen) QS_pos cap2L
  have cap2 := capLB_pow cap2LQ (160 - c)
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have cap2B := capLB_mul cap2 capB
  have hsum := capLB_mul cap2B capECoarsePosL
  have hX1 := x1_nonpos_ltF hmlo h2
  have hVs := v_scale_pos (toInt (x1W (zWord m))) c (by omega : c ≤ 160)
  have hV0 : 0 ≤ (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516284764321243411868) * 2 ^ 27 := by
    have h0 : 0 ≤ r * 2 ^ 72 := Int.mul_nonneg hr0 (by decide)
    have hg : 0 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551516284764321243411868 := by
      generalize hgV : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551516284764321243411868 = V at hrlo ⊢
      generalize hgR : r * 2 ^ 72 = R at hrlo h0
      omega
    exact Int.mul_nonneg hg (by decide)
  change capUB ((-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen)
    lnErrQ 560227709747861399187319382270000000000000000000000000000000
      (m * 9999999999999999999999999996615) at cap1
  change capLB
    (((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
      BIASc * twoPow27N * lnErrorBoundDen) +
      (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue))
    lnErrQ
      (((2 * (10 ^ 40 - 1)) ^ (160 - c) * (Sc * (10 ^ 31 - 3384))) *
        (10 ^ 31 + lnErrorCoarsePosBudgetCap))
      ((((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31)) * 10 ^ 31)) at hsum
  have hnegXn : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) =
      -toInt (x1W (zWord m)) :=
    Int.toNat_of_nonneg (by omega)
  have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
    unfold twoPow27N twoPow27I lnBiasI
    decide +kernel
  have hLc : (((160 - c) * (LN2c * twoPow27N) : Nat) : Int) =
      ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) := by
    simp only [Int.natCast_mul]
    unfold twoPow27N twoPow27I
    rfl
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  have hextra : ((lnErrorExtraNum * twoPow99N : Nat) : Int) =
      (lnErrorExtraNum : Int) * twoPow99I := by
    unfold twoPow99N twoPow99I
    rfl
  have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
  have hN : (((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
      (((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I)) *
        (1000000000 : Int) := by
    rw [show (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
        ((160 - c) * (LN2c * twoPow27N)) * lnErrorBoundDen by
          simp only [Nat.mul_assoc]]
    simp only [Int.natCast_mul, hLc, hden]
  have hVsI :
      (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
          lnBiasI) * twoPow27I = posPhaseI m c := by
    unfold posPhaseI
    simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
  have hV0I : 0 ≤ posPhaseI m c := by
    have hV0' : 0 ≤ (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        lnBiasI) * twoPow27I := by
      simpa [lnBiasI, twoPow27I] using hV0
    rw [hVsI] at hV0'
    exact hV0'
  have hcancel_le :
      (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen ≤
        ((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
          BIASc * twoPow27N * lnErrorBoundDen) +
          (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue) := by
    apply Int.ofNat_le.mp
    simp only [Int.natCast_add, Int.natCast_mul, hnegXn, hBc, hN, hden, hextra, hscale]
    have hmain : (-toInt (x1W (zWord m))) * lnPhaseScaleI ≤
        ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
          lnBiasI * twoPow27I := by
      unfold posPhaseI at hV0I
      rw [Int.neg_mul]
      generalize toInt (x1W (zWord m)) * lnPhaseScaleI = A at hV0I ⊢
      generalize ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B at hV0I ⊢
      generalize lnBiasI * twoPow27I = C at hV0I ⊢
      omega
    have hmul := Int.mul_le_mul_of_nonneg_right hmain (by decide : 0 ≤ (1000000000 : Int))
    have hmul' : (-toInt (x1W (zWord m))) * lnPhaseScaleI * (1000000000 : Int) ≤
        ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) * (1000000000 : Int) +
          lnBiasI * twoPow27I * (1000000000 : Int) := by
      have e : (((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
          lnBiasI * twoPow27I) * (1000000000 : Int) =
          ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) * (1000000000 : Int) +
            lnBiasI * twoPow27I * (1000000000 : Int) := by
        rw [Int.add_mul]
      rw [e] at hmul
      exact hmul
    have hnon : 0 ≤ (lnErrorExtraNum : Int) * twoPow99I +
        (lnErrorCoarsePosResidue : Int) := by
      have hE : 0 ≤ (lnErrorExtraNum : Int) * twoPow99I := by
        unfold twoPow99I
        exact Int.mul_nonneg (Int.natCast_nonneg _) (by decide)
      exact Int.add_nonneg hE (Int.natCast_nonneg _)
    exact Int.le_trans hmul' (Int.le_add_of_nonneg_right hnon)
  have hsplit :
      ((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
        BIASc * twoPow27N * lnErrorBoundDen) +
        (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue) =
      (((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
        BIASc * twoPow27N * lnErrorBoundDen) +
        (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue) -
          (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen) +
        (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen := by
    exact (Nat.sub_add_cancel hcancel_le).symm
  rw [hsplit] at hsum
  have capV := capLB_cancel (q := lnErrQ) (by unfold lnErrQ; decide) hsum cap1
  have hple :
      ((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
        BIASc * twoPow27N * lnErrorBoundDen) +
        (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue) -
          (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen ≤
      lnErrArg r := by
    apply Int.ofNat_le.mp
    have htarget : (((r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat *
        2 ^ 99 : Nat) : Int) =
        (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
      rw [Int.natCast_mul, Int.toNat_of_nonneg harg_nonneg]
      unfold twoPow99I
      rfl
    have hsub_cast :
        (((((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
          BIASc * twoPow27N * lnErrorBoundDen) +
          (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue) -
            (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN *
              lnErrorBoundDen : Nat) : Int)) =
        posPhaseI m c * (lnErrorBoundDen : Int) +
          (lnErrorExtraNum : Int) * twoPow99I +
            (lnErrorCoarsePosResidue : Int) := by
      have hsI := congrArg (fun n : Nat => ((n : Nat) : Int)) hsplit
      simp only [Int.natCast_add, Int.natCast_mul, hnegXn, hBc, hN, hden,
        hextra, hscale] at hsI
      rw [show -toInt (x1W (zWord m)) * lnPhaseScaleI =
          -(toInt (x1W (zWord m)) * lnPhaseScaleI) by rw [Int.neg_mul]] at hsI
      generalize (((((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
        BIASc * twoPow27N * lnErrorBoundDen) +
        (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue) -
          (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN *
            lnErrorBoundDen : Nat) : Int)) = S at hsI ⊢
      unfold posPhaseI
      rw [hden]
      generalize toInt (x1W (zWord m)) * lnPhaseScaleI = A at hsI ⊢
      generalize ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) = L at hsI ⊢
      generalize lnBiasI * twoPow27I = B at hsI ⊢
      generalize (lnErrorExtraNum : Int) * twoPow99I = E at hsI ⊢
      generalize (lnErrorCoarsePosResidue : Int) = G at hsI ⊢
      omega
    rw [lnErrArg, htarget, hsub_cast]
    exact pos_residue_arg_le_int hres
  have hmul :
      (((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
        BIASc * twoPow27N * lnErrorBoundDen) +
        (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue) -
          (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen) * lnErrQ ≤
      lnErrArg r * lnErrQ :=
    Nat.mul_le_mul_right _ hple
  have capR := capLB_arg (q := lnErrQ) (by unfold lnErrQ; decide) hmul capV
  refine capLB_weaken (p := lnErrArg r) (q := lnErrQ)
    (y := ((((2 * (10 ^ 40 - 1)) ^ (160 - c) * (Sc * (10 ^ 31 - 3384))) *
      (10 ^ 31 + lnErrorCoarsePosBudgetCap)) *
      (m * 9999999999999999999999999996615)))
    (w := ((((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31)) *
      10 ^ 31) *
      560227709747861399187319382270000000000000000000000000000000)) ?_ capR ?_
  · have h1' : 0 < (((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31)) *
        10 ^ 31 : Nat) :=
      Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by decide)) (by decide)) (by decide)
    exact Nat.mul_pos h1' (by decide)
  · have hMLO : Sc - 45 ≤ m := h1
    have hb := errBudgetL_fold (k := 160 - c) hMLO (by omega)
    have hx1 : x + 1 ≤ (m + 1) * 2 ^ (160 - c) := by omega
    have hxw : (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) ≤
        (m + 1) * 2 ^ (160 - c) *
          (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) :=
      Nat.mul_le_mul_right _ hx1
    have hfold : (m + 1) * 2 ^ (160 - c) *
        (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) ≤
        m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarsePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
      have h := Nat.mul_le_mul_left Sc hb
      have e1 : Sc * ((m + 1) * (2 ^ (160 - c) *
          (10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) =
          (m + 1) * 2 ^ (160 - c) *
            (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have e2 : Sc * (m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarsePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18)) =
          m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
            (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarsePosBudgetCap) *
            (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e1] at h
      rw [e2] at h
      exact h
    have eL : x * 10 ^ 31 * ((((10 ^ 40 : Nat) ^ (160 - c) *
        (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) *
        560227709747861399187319382270000000000000000000000000000000) ≤
        (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * 10 ^ 31 from by decide]
      have eAC : x * 10 ^ 31 * ((((10 ^ 40 : Nat) ^ (160 - c) *
          (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) * (Sc * 10 ^ 31)) =
          x * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) *
            ((10 : Nat) ^ 18 * ((10 : Nat) ^ 31 *
              ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 * (10 : Nat) ^ 31)))))) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [eAC, show ((10 : Nat) ^ 18 * ((10 : Nat) ^ 31 *
        ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 * (10 : Nat) ^ 31)))) = 10 ^ 142
        from by decide]
      exact Nat.mul_le_mul_right _ (by omega : x ≤ x + 1)
    have eR : ((((2 * (10 ^ 40 - 1)) ^ (160 - c) * (Sc * (10 ^ 31 - 3384))) *
        (10 ^ 31 + lnErrorCoarsePosBudgetCap)) *
        (m * 9999999999999999999999999996615)) *
        (10 ^ 18 * (10 ^ 31 - 10)) =
        m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarsePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
      rw [show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    unfold wadRayNum wadRayStrictDen
    generalize hT1 : x * 10 ^ 31 * ((((10 ^ 40 : Nat) ^ (160 - c) *
      (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) *
      560227709747861399187319382270000000000000000000000000000000) = T1 at eL ⊢
    generalize hT2 : (x + 1) *
      (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) = T2 at eL hxw
    generalize hT3 : (m + 1) * 2 ^ (160 - c) *
      (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) = T3 at hxw hfold
    generalize hT4 : m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
      (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarsePosBudgetCap) *
      (10 ^ 31 - 10) * 10 ^ 18) * Sc = T4 at hfold eR
    generalize hT5 : ((((2 * (10 ^ 40 - 1)) ^ (160 - c) *
      (Sc * (10 ^ 31 - 3384))) * (10 ^ 31 + lnErrorCoarsePosBudgetCap)) *
      (m * 9999999999999999999999999996615)) *
      (10 ^ 18 * (10 ^ 31 - 10)) = T5 at eR ⊢
    omega

theorem lo_ge_neg_exact {m c x : Nat} {r : Int} (h1 : Sc ≤ m) (h2 : m < MHI)
    (hc : 160 < c) (hc2 : c ≤ 255)
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516284764321243411868 < (r + 1) * 2 ^ 72)
    (hrlo : r * 2 ^ 72 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516284764321243411868)
    (hr0 : 0 ≤ r)
    (hmx : m = x * 2 ^ (c - 160)) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have harg_nonneg := ln_err_arg_nonneg (by omega : -1 ≤ r)
  have cap1 := capLB_lift_right (den := lnErrorBoundDen) QS_pos (x1capGeLoF h1 h2)
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have cap1B := capLB_mul cap1 capB
  have cap1BE := capLB_mul cap1B capECoarseNegL
  have cap2UQ := capUB_lift_right (den := lnErrorBoundDen) QS_pos cap2U
  have cap2 := capUB_pow (by unfold QS lnErrorBoundDen; decide) cap2UQ (c - 160)
  have hX1 := x1_nonneg_geF h1 h2
  have hVs := v_scale_neg (toInt (x1W (zWord m))) c hc
  have hV0 : 0 ≤ (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516284764321243411868) * 2 ^ 27 := by
    have h0 : 0 ≤ r * 2 ^ 72 := Int.mul_nonneg hr0 (by decide)
    have hg : 0 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551516284764321243411868 := by
      generalize hgV : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551516284764321243411868 = V at hrlo ⊢
      generalize hgR : r * 2 ^ 72 = R at hrlo h0
      omega
    exact Int.mul_nonneg hg (by decide)
  change capLB ((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
      BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N)
    lnErrQ
      ((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384)) *
        (10 ^ 31 + lnErrorCoarseNegBudgetCap))
      ((560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) at cap1BE
  have hcancel_le : (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) ≤
      (toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N := by
    apply Int.ofNat_le.mp
    have hX1n : ((toInt (x1W (zWord m))).toNat : Int) = toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
      unfold twoPow27N twoPow27I lnBiasI
      decide +kernel
    have hLc : (((c - 160) * (LN2c * twoPow27N) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) := by
      simp only [Int.natCast_mul]
      unfold twoPow27N twoPow27I
      rfl
    have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
      unfold lnErrorBoundDen
      rfl
    have hextra : ((lnErrorExtraNum * twoPow99N : Nat) : Int) =
        698600000 * twoPow99I := by
      unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen twoPow99N twoPow99I
      decide +kernel
    have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
    have hV0I : 0 ≤ (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        lnBiasI) * twoPow27I := by
      simpa [lnBiasI, twoPow27I] using hV0
    have hVsI :
        (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
            lnBiasI) * twoPow27I +
          ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) =
        toInt (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
      simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI) * twoPow27I = V27 at hV0I hVsI
    generalize hgA : toInt (x1W (zWord m)) * lnPhaseScaleI = A at hVsI
    generalize hgB : ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B at hVsI hLc
    generalize hgC : (c - 160) * (LN2c * twoPow27N) = Cn at hLc ⊢
    generalize hgD : (toInt (x1W (zWord m))).toNat * lnPhaseScaleN = D at ⊢
    have hAD : (D : Int) = A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n, hscale]
    generalize hgE : BIASc * twoPow27N = E at hBc ⊢
    generalize hgX : lnErrorExtraNum * twoPow99N = Ex at hextra ⊢
    have hN : (((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
        B * (1000000000 : Int) := by
      rw [show (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
          Cn * lnErrorBoundDen by
            rw [← hgC]
            simp only [Nat.mul_assoc]]
      simp only [Int.natCast_mul, hLc, hden]
    clear hX1n hX1 cap1 capB cap1B cap1BE cap2UQ cap2 hr h1 h2 hc hc2 hmx hrlo hVs
    simp only [Int.natCast_add, Int.natCast_mul, hden, hAD, hBc, hextra, hN]
    omega
  have hsplit : (toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
      BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N =
      ((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
          (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen)) +
        (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) := by
    exact (Nat.sub_add_cancel hcancel_le).symm
  rw [hsplit] at cap1BE
  have capV := capLB_cancel (q := lnErrQ) (by unfold lnErrQ; decide) cap1BE cap2
  have hple : (toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
      BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
        (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) ≤
      lnErrArg r := by
    apply Int.ofNat_le.mp
    have htarget : (((r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat *
        2 ^ 99 : Nat) : Int) =
        (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
      rw [Int.natCast_mul, Int.toNat_of_nonneg harg_nonneg]
      unfold twoPow99I
      rfl
    have hX1n : ((toInt (x1W (zWord m))).toNat : Int) = toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
      unfold twoPow27N twoPow27I lnBiasI
      decide +kernel
    have hLc : (((c - 160) * (LN2c * twoPow27N) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) := by
      simp only [Int.natCast_mul]
      unfold twoPow27N twoPow27I
      rfl
    have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
      unfold lnErrorBoundDen
      rfl
    have hextra : ((lnErrorExtraNum * twoPow99N : Nat) : Int) =
        698600000 * twoPow99I := by
      unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen twoPow99N twoPow99I
      decide +kernel
    have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
    have hsub_cast :
        (((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
            (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
        (toInt (x1W (zWord m)) * lnPhaseScaleI -
            ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
            lnBiasI * twoPow27I) * (1000000000 : Int) +
          698600000 * twoPow99I := by
      have hsI := congrArg (fun n : Nat => ((n : Nat) : Int)) hsplit
      have hN : (((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
          (((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I)) *
            (1000000000 : Int) := by
        rw [show (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
            ((c - 160) * (LN2c * twoPow27N)) * lnErrorBoundDen by
              simp only [Nat.mul_assoc]]
        simp only [Int.natCast_mul, hLc, hden]
      simp only [Int.natCast_add, Int.natCast_mul, hX1n, hBc, hN, hden,
        hextra, hscale] at hsI
      generalize (((toInt (x1W (zWord m))).toNat * lnPhaseScaleN *
        lnErrorBoundDen + BIASc * twoPow27N * lnErrorBoundDen +
        lnErrorExtraNum * twoPow99N -
        (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) = S at hsI ⊢
      generalize toInt (x1W (zWord m)) * lnPhaseScaleI = A at hsI ⊢
      generalize ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B at hsI ⊢
      generalize lnBiasI * twoPow27I = C at hsI ⊢
      generalize 698600000 * twoPow99I = E at hsI ⊢
      omega
    rw [lnErrArg, htarget, hsub_cast]
    have hsc : toInt (x1W (zWord m)) * lnPhaseScaleI -
          ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
          lnBiasI * twoPow27I ≤
        (r + 1) * twoPow99I - twoPow27I := by
      have h := phase_lt_scaled_le (V := toInt (x1W (zWord m)) *
          7450580596923828125 + ln2kInt c + lnBiasI)
        (T := (r + 1) * twoPow72I) (by simpa [lnBiasI, twoPow72I] using hr)
      change (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
          lnBiasI) * twoPow27I ≤ ((r + 1) * twoPow72I - 1) * twoPow27I at h
      have er : ((r + 1) * twoPow72I - 1) * twoPow27I =
          (r + 1) * twoPow99I - twoPow27I := by
        unfold twoPow72I twoPow27I twoPow99I
        rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
          by decide]
        omega
      rw [er] at h
      have hVsI :
          (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
              lnBiasI) * twoPow27I +
            ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) =
          toInt (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
        simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
      generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 +
        ln2kInt c + lnBiasI) * twoPow27I = V27 at h hVsI
      generalize hgL : ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = L at hVsI ⊢
      generalize hgA : toInt (x1W (zWord m)) * lnPhaseScaleI = A at hVsI ⊢
      generalize hgB : lnBiasI * twoPow27I = B at hVsI ⊢
      omega
    have hcore := c160_arg_le_int (A :=
      toInt (x1W (zWord m)) * lnPhaseScaleI -
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
        lnBiasI * twoPow27I) (r := r) hsc
    simpa [lnErrorBoundDen, lnErrorBoundNum, twoPow99I] using hcore
  have hmul :
      ((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
          (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen)) * lnErrQ ≤
        lnErrArg r * lnErrQ :=
    Nat.mul_le_mul_right _ hple
  have capR : capLB (lnErrArg r) lnErrQ
      (((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384)) *
        (10 ^ 31 + lnErrorCoarseNegBudgetCap)) * (10 ^ 40) ^ (c - 160))
      ((((560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) * (2 * (10 ^ 40 + 1)) ^ (c - 160))) :=
    @capLB_arg
      (lnErrArg r) lnErrQ
      ((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
          (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen))
      lnErrQ
      (((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384)) *
        (10 ^ 31 + lnErrorCoarseNegBudgetCap)) * (10 ^ 40) ^ (c - 160))
      ((((560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) * (2 * (10 ^ 40 + 1)) ^ (c - 160)))
      (by unfold lnErrQ; decide) hmul capV
  refine capLB_weaken (p := lnErrArg r) (q := lnErrQ)
    (y := (((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384)) *
      (10 ^ 31 + lnErrorCoarseNegBudgetCap)) * (10 ^ 40) ^ (c - 160)))
    (w := ((((560227709747861399187319382270000000000000000000000000000000 *
      (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) * (2 * (10 ^ 40 + 1)) ^ (c - 160))))
    ?_ capR ?_
  · have h1' : 0 < (560227709747861399187319382270000000000000000000000000000000 : Nat) *
        (10 ^ 18 * 10 ^ 31) * 10 ^ 31 := by decide
    exact Nat.mul_pos h1' (Nat.pow_pos (by decide))
  · have hb := errBudgetLn_le (j := c - 160) (by omega)
    have hbf := Nat.mul_le_mul_left (x * Sc) hb
    have eL : x * 10 ^ 31 *
        (((560227709747861399187319382270000000000000000000000000000000 *
          (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) * (2 * (10 ^ 40 + 1)) ^ (c - 160)) =
        x * Sc * ((10 : Nat) ^ 142 * (2 * (10 ^ 40 + 1)) ^ (c - 160)) := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * 10 ^ 31 from by decide]
      have e' : ∀ P : Nat, (10 : Nat) ^ 18 * ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 *
          ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 * P)))) = (10 : Nat) ^ 142 * P := by
        intro P
        rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc,
          show ((10 : Nat) ^ 18 * 10 ^ 31 * 10 ^ 31 * 10 ^ 31 * 10 ^ 31) = 10 ^ 142
            from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e' ((2 * (10 ^ 40 + 1)) ^ (c - 160))]
    have eR : (((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384)) *
        (10 ^ 31 + lnErrorCoarseNegBudgetCap)) * (10 ^ 40 : Nat) ^ (c - 160)) *
        (10 ^ 18 * (10 ^ 31 - 10)) =
        x * Sc * (2 ^ (c - 160) * (10 ^ 40 : Nat) ^ (c - 160) * (10 ^ 31 - 3385) *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18) := by
      rw [hmx, show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    unfold wadRayNum wadRayStrictDen
    generalize hT1 : x * 10 ^ 31 *
      (((560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) * (2 * (10 ^ 40 + 1)) ^ (c - 160)) = T1
      at eL ⊢
    generalize hT2 : x * Sc * ((10 : Nat) ^ 142 * (2 * (10 ^ 40 + 1)) ^ (c - 160)) = T2
      at eL hbf
    generalize hT3 : x * Sc * (2 ^ (c - 160) * (10 ^ 40 : Nat) ^ (c - 160) *
      (10 ^ 31 - 3385) * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap) *
      (10 ^ 31 - 10) * 10 ^ 18) = T3 at eR hbf
    generalize hT4 : (((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384)) *
      (10 ^ 31 + lnErrorCoarseNegBudgetCap)) * (10 ^ 40 : Nat) ^ (c - 160)) *
      (10 ^ 18 * (10 ^ 31 - 10)) = T4 at eR ⊢
    omega

theorem lo_lt_neg_exact {m c x : Nat} {r : Int} (h1 : MLO ≤ m) (h2 : m < Sc)
    (hc : 160 < c) (hc2 : c ≤ 255)
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516284764321243411868 < (r + 1) * 2 ^ 72)
    (hrlo : r * 2 ^ 72 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516284764321243411868)
    (hr0 : 0 ≤ r)
    (hmx : m = x * 2 ^ (c - 160)) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have harg_nonneg := ln_err_arg_nonneg (by omega : -1 ≤ r)
  have cap1 := capUB_lift_right (den := lnErrorBoundDen) QS_pos (x1capLtLoF h1 h2)
  have cap2UQ := capUB_lift_right (den := lnErrorBoundDen) QS_pos cap2U
  have hb := capUB_mul (by unfold QS lnErrorBoundDen; decide) cap1
    (capUB_pow (by unfold QS lnErrorBoundDen; decide) cap2UQ (c - 160))
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have hsum := capLB_mul capB capECoarseNegL
  have hX1 := x1_nonpos_ltF h1 h2
  have hVs := v_scale_neg (toInt (x1W (zWord m))) c hc
  have hV0 : 0 ≤ (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516284764321243411868) * 2 ^ 27 := by
    have h0 : 0 ≤ r * 2 ^ 72 := Int.mul_nonneg hr0 (by decide)
    have hg : 0 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551516284764321243411868 := by
      generalize hgV : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551516284764321243411868 = V at hrlo ⊢
      generalize hgR : r * 2 ^ 72 = R at hrlo h0
      omega
    exact Int.mul_nonneg hg (by decide)
  change capUB (((-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen) +
      (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen))
    lnErrQ
      (560227709747861399187319382270000000000000000000000000000000 *
        ((2 * (10 ^ 40 + 1)) ^ (c - 160)))
      ((m * 9999999999999999999999999996615) * ((10 ^ 40) ^ (c - 160))) at hb
  change capLB (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N)
    lnErrQ (Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap))
      ((10 ^ 18 * 10 ^ 31) * 10 ^ 31) at hsum
  have hcancel_le :
      (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) ≤
      BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N := by
    apply Int.ofNat_le.mp
    have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) =
        -toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
      unfold twoPow27N twoPow27I lnBiasI
      decide +kernel
    have hLc : (((c - 160) * (LN2c * twoPow27N) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) := by
      simp only [Int.natCast_mul]
      unfold twoPow27N twoPow27I
      rfl
    have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
      unfold lnErrorBoundDen
      rfl
    have hextra : ((lnErrorExtraNum * twoPow99N : Nat) : Int) =
        698600000 * twoPow99I := by
      unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen twoPow99N twoPow99I
      decide +kernel
    have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
    have hV0I : 0 ≤ (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        lnBiasI) * twoPow27I := by
      simpa [lnBiasI, twoPow27I] using hV0
    have hVsI :
        (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
            lnBiasI) * twoPow27I +
          ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) =
        toInt (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
      simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI) * twoPow27I = V27 at hV0I hVsI
    generalize hgA : toInt (x1W (zWord m)) * lnPhaseScaleI = A at hVsI
    generalize hgB : ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B at hVsI hLc
    generalize hgC : (c - 160) * (LN2c * twoPow27N) = Cn at hLc ⊢
    generalize hgD : (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n, hscale]
      rw [Int.neg_mul]
    generalize hgE : BIASc * twoPow27N = E at hBc ⊢
    generalize hgX : lnErrorExtraNum * twoPow99N = Ex at hextra ⊢
    have hN : (((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
        B * (1000000000 : Int) := by
      rw [show (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
          Cn * lnErrorBoundDen by
            rw [← hgC]
            simp only [Nat.mul_assoc]]
      simp only [Int.natCast_mul, hLc, hden]
    clear hX1n hX1 cap1 cap2UQ hb capB hsum hr h1 h2 hc hc2 hmx hrlo hVs
    simp only [Int.natCast_add, Int.natCast_mul, hden, hAD, hBc, hextra, hN]
    omega
  have hsplit : BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N =
      (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
        ((-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen))) +
        ((-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen)) := by
    exact (Nat.sub_add_cancel hcancel_le).symm
  rw [hsplit] at hsum
  have capV := capLB_cancel (q := lnErrQ) (by unfold lnErrQ; decide) hsum hb
  have hple : BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
      ((-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen)) ≤
      lnErrArg r := by
    apply Int.ofNat_le.mp
    have htarget : (((r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat *
        2 ^ 99 : Nat) : Int) =
        (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
      rw [Int.natCast_mul, Int.toNat_of_nonneg harg_nonneg]
      unfold twoPow99I
      rfl
    have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) =
        -toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
      unfold twoPow27N twoPow27I lnBiasI
      decide +kernel
    have hLc : (((c - 160) * (LN2c * twoPow27N) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) := by
      simp only [Int.natCast_mul]
      unfold twoPow27N twoPow27I
      rfl
    have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
      unfold lnErrorBoundDen
      rfl
    have hextra : ((lnErrorExtraNum * twoPow99N : Nat) : Int) =
        698600000 * twoPow99I := by
      unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen twoPow99N twoPow99I
      decide +kernel
    have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
    have hN : (((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
        (((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I)) *
          (1000000000 : Int) := by
      rw [show (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
          ((c - 160) * (LN2c * twoPow27N)) * lnErrorBoundDen by
            simp only [Nat.mul_assoc]]
      simp only [Int.natCast_mul, hLc, hden]
    have hsub_cast :
        (((BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
          ((-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
            (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen)) : Nat) : Int)) =
        (toInt (x1W (zWord m)) * lnPhaseScaleI -
            ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
            lnBiasI * twoPow27I) * (1000000000 : Int) +
          698600000 * twoPow99I := by
      have hsI := congrArg (fun n : Nat => ((n : Nat) : Int)) hsplit
      simp only [Int.natCast_add, Int.natCast_mul, hX1n, hBc, hN, hden,
        hextra, hscale] at hsI
      rw [show -toInt (x1W (zWord m)) * lnPhaseScaleI =
          -(toInt (x1W (zWord m)) * lnPhaseScaleI) by rw [Int.neg_mul]] at hsI
      generalize (((BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum *
        twoPow99N - ((-toInt (x1W (zWord m))).toNat * lnPhaseScaleN *
        lnErrorBoundDen + (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen)) : Nat) : Int)) = S
        at hsI ⊢
      generalize toInt (x1W (zWord m)) * lnPhaseScaleI = A at hsI ⊢
      generalize ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B at hsI ⊢
      generalize lnBiasI * twoPow27I = C at hsI ⊢
      generalize 698600000 * twoPow99I = E at hsI ⊢
      omega
    rw [lnErrArg, htarget, hsub_cast]
    have hsc : toInt (x1W (zWord m)) * lnPhaseScaleI -
          ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
          lnBiasI * twoPow27I ≤
        (r + 1) * twoPow99I - twoPow27I := by
      have h := phase_lt_scaled_le (V := toInt (x1W (zWord m)) *
          7450580596923828125 + ln2kInt c + lnBiasI)
        (T := (r + 1) * twoPow72I) (by simpa [lnBiasI, twoPow72I] using hr)
      change (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
          lnBiasI) * twoPow27I ≤ ((r + 1) * twoPow72I - 1) * twoPow27I at h
      have er : ((r + 1) * twoPow72I - 1) * twoPow27I =
          (r + 1) * twoPow99I - twoPow27I := by
        unfold twoPow72I twoPow27I twoPow99I
        rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
          by decide]
        omega
      rw [er] at h
      have hVsI :
          (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
              lnBiasI) * twoPow27I +
            ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) =
          toInt (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
        simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
      generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 +
        ln2kInt c + lnBiasI) * twoPow27I = V27 at h hVsI
      generalize hgL : ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = L at hVsI ⊢
      generalize hgA : toInt (x1W (zWord m)) * lnPhaseScaleI = A at hVsI ⊢
      generalize hgB : lnBiasI * twoPow27I = B at hVsI ⊢
      omega
    have hcore := c160_arg_le_int (A :=
      toInt (x1W (zWord m)) * lnPhaseScaleI -
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
        lnBiasI * twoPow27I) (r := r) hsc
    simpa [lnErrorBoundDen, lnErrorBoundNum, twoPow99I] using hcore
  have hmul : (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
      ((-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen))) * lnErrQ ≤
      lnErrArg r * lnErrQ :=
    Nat.mul_le_mul_right _ hple
  have capR : capLB (lnErrArg r) lnErrQ
      ((Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap)) *
        (m * 9999999999999999999999999996615 * (10 ^ 40 : Nat) ^ (c - 160)))
      (((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
        (560227709747861399187319382270000000000000000000000000000000 *
          (2 * (10 ^ 40 + 1)) ^ (c - 160))) :=
    @capLB_arg
      (lnErrArg r) lnErrQ
      (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
        ((-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen)))
      lnErrQ
      ((Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap)) *
        (m * 9999999999999999999999999996615 * (10 ^ 40 : Nat) ^ (c - 160)))
      (((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
        (560227709747861399187319382270000000000000000000000000000000 *
          (2 * (10 ^ 40 + 1)) ^ (c - 160)))
      (by unfold lnErrQ; decide) hmul capV
  refine capLB_weaken (p := lnErrArg r) (q := lnErrQ)
    (y := ((Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap)) *
      (m * 9999999999999999999999999996615 * (10 ^ 40 : Nat) ^ (c - 160))))
    (w := (((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
      (560227709747861399187319382270000000000000000000000000000000 *
        (2 * (10 ^ 40 + 1)) ^ (c - 160))))
    ?_ capR ?_
  · have h1' : 0 < ((10 ^ 18 * 10 ^ 31) * 10 ^ 31 : Nat) := by decide
    exact Nat.mul_pos h1' (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))
  · have hbg := errBudgetLn_le (j := c - 160) (by omega)
    have hbf := Nat.mul_le_mul_left (x * Sc) hbg
    have eL : x * 10 ^ 31 * (((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
        (560227709747861399187319382270000000000000000000000000000000 *
          (2 * (10 ^ 40 + 1)) ^ (c - 160))) =
        x * Sc * ((10 : Nat) ^ 142 * (2 * (10 ^ 40 + 1)) ^ (c - 160)) := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * 10 ^ 31 from by decide]
      have e' : ∀ P : Nat, (10 : Nat) ^ 18 * ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 *
          ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 * P)))) = (10 : Nat) ^ 142 * P := by
        intro P
        rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc,
          show ((10 : Nat) ^ 18 * 10 ^ 31 * 10 ^ 31 * 10 ^ 31 * 10 ^ 31) = 10 ^ 142
            from by decide]
      have eAC : x * 10 ^ 31 * (((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
          (Sc * 10 ^ 31 * (2 * (10 ^ 40 + 1)) ^ (c - 160))) =
          x * (Sc * ((10 : Nat) ^ 18 * ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 *
            ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 *
              (2 * (10 ^ 40 + 1)) ^ (c - 160))))))) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [eAC, e' ((2 * (10 ^ 40 + 1)) ^ (c - 160))]
      simp only [Nat.mul_assoc]
    have eR : ((Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap)) *
        (m * 9999999999999999999999999996615 * (10 ^ 40 : Nat) ^ (c - 160))) *
        (10 ^ 18 * (10 ^ 31 - 10)) =
        x * Sc * (2 ^ (c - 160) * (10 ^ 40 : Nat) ^ (c - 160) * (10 ^ 31 - 3385) *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18) := by
      rw [hmx, show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    unfold wadRayNum wadRayStrictDen
    generalize hT1 : x * 10 ^ 31 * (((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
      (560227709747861399187319382270000000000000000000000000000000 *
        (2 * (10 ^ 40 + 1)) ^ (c - 160))) = T1 at eL ⊢
    generalize hT2 : x * Sc * ((10 : Nat) ^ 142 * (2 * (10 ^ 40 + 1)) ^ (c - 160)) = T2
      at eL hbf
    generalize hT3 : x * Sc * (2 ^ (c - 160) * (10 ^ 40 : Nat) ^ (c - 160) *
      (10 ^ 31 - 3385) * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap) *
      (10 ^ 31 - 10) * 10 ^ 18) = T3 at eR hbf
    generalize hT4 : ((Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap)) *
      (m * 9999999999999999999999999996615 * (10 ^ 40 : Nat) ^ (c - 160))) *
      (10 ^ 18 * (10 ^ 31 - 10)) = T4 at eR ⊢
    omega

theorem bn_ge_neg_exact {m c x : Nat} {r : Int} (h1 : Sc ≤ m) (h2 : m < MHI)
    (hc : 160 < c) (hc2 : c ≤ 255)
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516284764321243411868 < (r + 1) * 2 ^ 72)
    (hrneg : r ≤ -2)
    (hmx : m = x * 2 ^ (c - 160)) :
    capUB (lnErrNegArg r) lnErrQ wadRayStrictDen (wadRayNum x) := by
  have hneg_nonneg := ln_err_neg_arg_nonneg hrneg
  have cap1 := capLB_lift_right (den := lnErrorBoundDen) QS_pos (x1capGeLoF h1 h2)
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have cap1B := capLB_mul cap1 capB
  have hb := capLB_mul cap1B capECoarseNegL
  have cap2UQ := capUB_lift_right (den := lnErrorBoundDen) QS_pos cap2U
  have hsum := capUB_pow (by unfold QS lnErrorBoundDen; decide) cap2UQ (c - 160)
  have hX1 := x1_nonneg_geF h1 h2
  have hVs := v_scale_neg (toInt (x1W (zWord m))) c hc
  have hgap : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516284764321243411868) * 2 ^ 27 ≤
      (r + 1) * 2 ^ 99 - 2 ^ 27 := by
    have hsc := Int.mul_le_mul_of_nonneg_right
      (show toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551516284764321243411868 ≤ (r + 1) * 2 ^ 72 - 1
        from by omega) (by decide : (0 : Int) ≤ 2 ^ 27)
    have er : ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 = (r + 1) * 2 ^ 99 - 2 ^ 27 := by
      rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
        by decide]
      omega
    rw [er] at hsc
    exact hsc
  change capLB ((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
      BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N)
    lnErrQ
      ((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384)) *
        (10 ^ 31 + lnErrorCoarseNegBudgetCap))
      ((560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) at hb
  have hcancel_le :
      (toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N ≤
        (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) := by
    apply Int.ofNat_le.mp
    have hX1n : ((toInt (x1W (zWord m))).toNat : Int) = toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
      unfold twoPow27N twoPow27I lnBiasI
      decide +kernel
    have hLc : (((c - 160) * (LN2c * twoPow27N) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) := by
      simp only [Int.natCast_mul]
      unfold twoPow27N twoPow27I
      rfl
    have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
      unfold lnErrorBoundDen
      rfl
    have hextra : ((lnErrorExtraNum * twoPow99N : Nat) : Int) =
        698600000 * twoPow99I := by
      unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen twoPow99N twoPow99I
      decide +kernel
    have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
    have hVsI :
        (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
            lnBiasI) * twoPow27I +
          ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) =
        toInt (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
      simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
    have hgapI : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        lnBiasI) * twoPow27I ≤ (r + 1) * twoPow99I - twoPow27I := by
      simpa [lnBiasI, twoPow27I, twoPow99I] using hgap
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI) * twoPow27I = V27 at hgapI hVsI
    generalize hgA : toInt (x1W (zWord m)) * lnPhaseScaleI = A at hVsI
    generalize hgB : ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B at hgapI hVsI hLc
    generalize hgC : (c - 160) * (LN2c * twoPow27N) = Cn at hLc ⊢
    generalize hgD : (toInt (x1W (zWord m))).toNat * lnPhaseScaleN = D at ⊢
    have hAD : (D : Int) = A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n, hscale]
    generalize hgE : BIASc * twoPow27N = E at hBc ⊢
    generalize hgBias : lnBiasI * twoPow27I = Bias at hVsI hBc
    generalize hgX : lnErrorExtraNum * twoPow99N = Ex at hextra ⊢
    have hN : (((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
        B * (1000000000 : Int) := by
      rw [show (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
          Cn * lnErrorBoundDen by
            rw [← hgC]
            simp only [Nat.mul_assoc]]
      simp only [Int.natCast_mul, hLc, hden]
    clear hX1n hX1 cap1 capB cap1B hb cap2UQ hsum hr h1 h2 hc hc2 hmx hVs
    simp only [Int.natCast_add, Int.natCast_mul, hden, hAD, hBc, hextra, hN]
    unfold twoPow99I twoPow27I at hgapI
    unfold twoPow99I at ⊢
    omega
  have hsplit : (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
      ((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) -
        ((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N)) +
        ((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N) := by
    exact (Nat.sub_add_cancel hcancel_le).symm
  change capUB ((c - 160) * (LN2c * twoPow27N * lnErrorBoundDen)) lnErrQ
    ((2 * (10 ^ 40 + 1)) ^ (c - 160)) ((10 ^ 40) ^ (c - 160)) at hsum
  rw [hsplit] at hsum
  have capV := capUB_cancel (q := lnErrQ) (by unfold lnErrQ; decide) hsum hb
  have hple : lnErrNegArg r ≤
      (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) -
        ((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N) := by
    apply Int.ofNat_le.mp
    have htarget : (((-(r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int))).toNat *
        2 ^ 99 : Nat) : Int) =
        (-(r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int))) * twoPow99I := by
      rw [Int.natCast_mul, Int.toNat_of_nonneg hneg_nonneg]
      unfold twoPow99I
      rfl
    have hX1n : ((toInt (x1W (zWord m))).toNat : Int) = toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
      unfold twoPow27N twoPow27I lnBiasI
      decide +kernel
    have hLc : (((c - 160) * (LN2c * twoPow27N) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) := by
      simp only [Int.natCast_mul]
      unfold twoPow27N twoPow27I
      rfl
    have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
      unfold lnErrorBoundDen
      rfl
    have hextra : ((lnErrorExtraNum * twoPow99N : Nat) : Int) =
        698600000 * twoPow99I := by
      unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen twoPow99N twoPow99I
      decide +kernel
    have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
    have hN : (((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
        (((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I)) *
          (1000000000 : Int) := by
      rw [show (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
          ((c - 160) * (LN2c * twoPow27N)) * lnErrorBoundDen by
            simp only [Nat.mul_assoc]]
      simp only [Int.natCast_mul, hLc, hden]
    have hsub_cast :
        ((((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) -
          ((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
            BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N) : Nat) : Int)) =
        -((toInt (x1W (zWord m)) * lnPhaseScaleI -
            ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
            lnBiasI * twoPow27I) * (1000000000 : Int) +
          698600000 * twoPow99I) := by
      have hsI := congrArg (fun n : Nat => ((n : Nat) : Int)) hsplit
      simp only [Int.natCast_add, Int.natCast_mul, hX1n, hBc, hN, hden,
        hextra, hscale] at hsI
      generalize ((((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) -
          ((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
            BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N) : Nat) : Int)) = S
        at hsI ⊢
      generalize toInt (x1W (zWord m)) * lnPhaseScaleI = A at hsI ⊢
      generalize ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B at hsI ⊢
      generalize lnBiasI * twoPow27I = C at hsI ⊢
      generalize 698600000 * twoPow99I = E at hsI ⊢
      omega
    rw [lnErrNegArg, htarget, hsub_cast]
    have hsc : toInt (x1W (zWord m)) * lnPhaseScaleI -
          ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
          lnBiasI * twoPow27I ≤
        (r + 1) * twoPow99I - twoPow27I := by
      have hVsI :
          (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
              lnBiasI) * twoPow27I +
            ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) =
          toInt (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
        simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
      have hgapI : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
          lnBiasI) * twoPow27I ≤ (r + 1) * twoPow99I - twoPow27I := by
        simpa [lnBiasI, twoPow27I, twoPow99I] using hgap
      generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 +
        ln2kInt c + lnBiasI) * twoPow27I = V27 at hgapI hVsI
      generalize hgL : ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = L at hVsI ⊢
      generalize hgA : toInt (x1W (zWord m)) * lnPhaseScaleI = A at hVsI ⊢
      generalize hgB : lnBiasI * twoPow27I = B at hVsI ⊢
      omega
    exact ln_err_neg_arg_le_int hsc hrneg
  have hmul : lnErrNegArg r * lnErrQ ≤
      ((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) -
        ((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N)) * lnErrQ :=
    Nat.mul_le_mul_right _ hple
  have capR0 : capUB (lnErrNegArg r) lnErrQ
      ((2 * (10 ^ 40 + 1)) ^ (c - 160) *
        (560227709747861399187319382270000000000000000000000000000000 *
          (10 ^ 18 * 10 ^ 31) * 10 ^ 31))
      ((10 ^ 40) ^ (c - 160) *
        (m * 9999999999999999999999999996615 * (Sc * (10 ^ 31 - 3384)) *
          (10 ^ 31 + lnErrorCoarseNegBudgetCap))) :=
    @capUB_arg
      (lnErrNegArg r) lnErrQ
      ((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) -
        ((toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N))
      lnErrQ
      ((2 * (10 ^ 40 + 1)) ^ (c - 160) *
        (560227709747861399187319382270000000000000000000000000000000 *
          (10 ^ 18 * 10 ^ 31) * 10 ^ 31))
      ((10 ^ 40) ^ (c - 160) *
        (m * 9999999999999999999999999996615 * (Sc * (10 ^ 31 - 3384)) *
          (10 ^ 31 + lnErrorCoarseNegBudgetCap)))
      (by unfold lnErrQ; decide) hmul capV
  refine capUB_weaken (p := lnErrNegArg r) (q := lnErrQ)
    (y := ((2 * (10 ^ 40 + 1)) ^ (c - 160) *
      (560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31) * 10 ^ 31)))
    (w := ((10 ^ 40) ^ (c - 160) *
      (m * 9999999999999999999999999996615 * (Sc * (10 ^ 31 - 3384)) *
        (10 ^ 31 + lnErrorCoarseNegBudgetCap)))) ?_ capR0 ?_
  · have h1' : 0 < (10 ^ 40 : Nat) ^ (c - 160) := Nat.pow_pos (by decide)
    have hm0 : 0 < m := by simp only [Sc] at h1; omega
    have hScp : 0 < Sc := by simp only [Sc]; omega
    exact Nat.mul_pos h1'
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hm0 (by decide))
        (Nat.mul_pos hScp (by decide))) (by decide))
  · have hbg := errBudgetBn_le (j := c - 160) (by omega)
    have hbf := Nat.mul_le_mul_left (x * Sc) hbg
    have eL : ((2 * (10 ^ 40 + 1)) ^ (c - 160) *
        (560227709747861399187319382270000000000000000000000000000000 *
          (10 ^ 18 * 10 ^ 31) * 10 ^ 31)) * (x * 10 ^ 31) =
        x * Sc * ((2 * (10 ^ 40 + 1)) ^ (c - 160) * (10 : Nat) ^ 31 *
          (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31) := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * 10 ^ 31 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have eR : (10 ^ 18 * (10 ^ 31 - 10)) *
        ((10 ^ 40 : Nat) ^ (c - 160) *
          (m * 9999999999999999999999999996615 * (Sc * (10 ^ 31 - 3384)) *
            (10 ^ 31 + lnErrorCoarseNegBudgetCap))) =
        x * Sc * (10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 40 : Nat) ^ (c - 160) *
          2 ^ (c - 160) * (10 ^ 31 - 3385) * (10 ^ 31 - 3384) *
          (10 ^ 31 + lnErrorCoarseNegBudgetCap)) := by
      rw [hmx, show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    unfold wadRayNum wadRayStrictDen
    generalize hT1 : ((2 * (10 ^ 40 + 1)) ^ (c - 160) *
      (560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31) * 10 ^ 31)) * (x * 10 ^ 31) = T1 at eL ⊢
    generalize hT2 : x * Sc * ((2 * (10 ^ 40 + 1)) ^ (c - 160) * (10 : Nat) ^ 31 *
      (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31) = T2 at eL hbf
    generalize hT3 : x * Sc * (10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 40 : Nat) ^ (c - 160) *
      2 ^ (c - 160) * (10 ^ 31 - 3385) * (10 ^ 31 - 3384) *
      (10 ^ 31 + lnErrorCoarseNegBudgetCap)) = T3 at eR hbf
    generalize hT4 : (10 ^ 18 * (10 ^ 31 - 10)) *
      ((10 ^ 40 : Nat) ^ (c - 160) *
        (m * 9999999999999999999999999996615 * (Sc * (10 ^ 31 - 3384)) *
          (10 ^ 31 + lnErrorCoarseNegBudgetCap))) = T4 at eR ⊢
    omega

theorem bn_lt_neg_exact {m c x : Nat} {r : Int} (h1 : MLO ≤ m) (h2 : m < Sc)
    (hc : 160 < c) (hc2 : c ≤ 255)
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516284764321243411868 < (r + 1) * 2 ^ 72)
    (hrneg : r ≤ -2)
    (hmx : m = x * 2 ^ (c - 160)) :
    capUB (lnErrNegArg r) lnErrQ wadRayStrictDen (wadRayNum x) := by
  have hneg_nonneg := ln_err_neg_arg_nonneg hrneg
  have cap1 := capUB_lift_right (den := lnErrorBoundDen) QS_pos (x1capLtLoF h1 h2)
  have cap2UQ := capUB_lift_right (den := lnErrorBoundDen) QS_pos cap2U
  have hsum := capUB_mul (by unfold QS lnErrorBoundDen; decide) cap1
    (capUB_pow (by unfold QS lnErrorBoundDen; decide) cap2UQ (c - 160))
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have hb := capLB_mul capB capECoarseNegL
  have hX1 := x1_nonpos_ltF h1 h2
  have hVs := v_scale_neg (toInt (x1W (zWord m))) c hc
  have hgap : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516284764321243411868) * 2 ^ 27 ≤
      (r + 1) * 2 ^ 99 - 2 ^ 27 := by
    have hsc := Int.mul_le_mul_of_nonneg_right
      (show toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551516284764321243411868 ≤ (r + 1) * 2 ^ 72 - 1
        from by omega) (by decide : (0 : Int) ≤ 2 ^ 27)
    have er : ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 = (r + 1) * 2 ^ 99 - 2 ^ 27 := by
      rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
        by decide]
      omega
    rw [er] at hsc
    exact hsc
  change capUB ((-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
      (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen))
    lnErrQ
      (560227709747861399187319382270000000000000000000000000000000 *
        ((2 * (10 ^ 40 + 1)) ^ (c - 160)))
      ((m * 9999999999999999999999999996615) * ((10 ^ 40) ^ (c - 160))) at hsum
  change capLB (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N)
    lnErrQ (Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap))
      ((10 ^ 18 * 10 ^ 31) * 10 ^ 31) at hb
  have hcancel_le : BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N ≤
      (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) := by
    apply Int.ofNat_le.mp
    have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) =
        -toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
      unfold twoPow27N twoPow27I lnBiasI
      decide +kernel
    have hLc : (((c - 160) * (LN2c * twoPow27N) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) := by
      simp only [Int.natCast_mul]
      unfold twoPow27N twoPow27I
      rfl
    have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
      unfold lnErrorBoundDen
      rfl
    have hextra : ((lnErrorExtraNum * twoPow99N : Nat) : Int) =
        698600000 * twoPow99I := by
      unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen twoPow99N twoPow99I
      decide +kernel
    have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
    have hVsI :
        (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
            lnBiasI) * twoPow27I +
          ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) =
        toInt (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
      simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
    have hgapI : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        lnBiasI) * twoPow27I ≤ (r + 1) * twoPow99I - twoPow27I := by
      simpa [lnBiasI, twoPow27I, twoPow99I] using hgap
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI) * twoPow27I = V27 at hgapI hVsI
    generalize hgA : toInt (x1W (zWord m)) * lnPhaseScaleI = A at hVsI
    generalize hgB : ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B at hgapI hVsI hLc
    generalize hgC : (c - 160) * (LN2c * twoPow27N) = Cn at hLc ⊢
    generalize hgD : (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n, hscale]
      rw [Int.neg_mul]
    generalize hgE : BIASc * twoPow27N = E at hBc ⊢
    generalize hgBias : lnBiasI * twoPow27I = Bias at hVsI hBc
    generalize hgX : lnErrorExtraNum * twoPow99N = Ex at hextra ⊢
    have hN : (((c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) : Nat) : Int) =
        B * (1000000000 : Int) := by
      rw [show (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) =
          Cn * lnErrorBoundDen by
            rw [← hgC]
            simp only [Nat.mul_assoc]]
      simp only [Int.natCast_mul, hLc, hden]
    clear hX1n hX1 cap1 cap2UQ hsum capB hb hr h1 h2 hc hc2 hmx hVs
    simp only [Int.natCast_add, Int.natCast_mul, hden, hAD, hBc, hextra, hN]
    unfold twoPow99I twoPow27I at hgapI
    unfold twoPow99I at ⊢
    omega
  have hsplit : (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
      (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) =
      ((-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) -
          (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N)) +
        (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N) := by
    exact (Nat.sub_add_cancel hcancel_le).symm
  rw [hsplit] at hsum
  have capV := capUB_cancel (q := lnErrQ) (by unfold lnErrQ; decide) hsum hb
  have hple : lnErrNegArg r ≤
      (-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) -
          (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N) := by
    apply Int.ofNat_le.mp
    have htarget : (((-(r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int))).toNat *
        2 ^ 99 : Nat) : Int) =
        (-(r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int))) * twoPow99I := by
      rw [Int.natCast_mul, Int.toNat_of_nonneg hneg_nonneg]
      unfold twoPow99I
      rfl
    have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) =
        -toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
      unfold twoPow27N twoPow27I lnBiasI
      decide +kernel
    have hLc : (((c - 160) * (LN2c * twoPow27N) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) := by
      simp only [Int.natCast_mul]
      unfold twoPow27N twoPow27I
      rfl
    have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
      unfold lnErrorBoundDen
      rfl
    have hextra : ((lnErrorExtraNum * twoPow99N : Nat) : Int) =
        698600000 * twoPow99I := by
      unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen twoPow99N twoPow99I
      decide +kernel
    have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
    have hN : (((c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) : Nat) : Int) =
        (((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I)) *
          (1000000000 : Int) := by
      rw [show (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) =
          ((c - 160) * (LN2c * twoPow27N)) * lnErrorBoundDen by
            simp only [Nat.mul_assoc]]
      simp only [Int.natCast_mul, hLc, hden]
    have hsub_cast :
        ((((-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) -
          (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N) : Nat) : Int)) =
        -((toInt (x1W (zWord m)) * lnPhaseScaleI -
            ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
            lnBiasI * twoPow27I) * (1000000000 : Int) +
          698600000 * twoPow99I) := by
      have hsI := congrArg (fun n : Nat => ((n : Nat) : Int)) hsplit
      simp only [Int.natCast_add, Int.natCast_mul, hX1n, hBc, hN, hden,
        hextra, hscale] at hsI
      rw [show -toInt (x1W (zWord m)) * lnPhaseScaleI =
          -(toInt (x1W (zWord m)) * lnPhaseScaleI) by rw [Int.neg_mul]] at hsI
      generalize ((((-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) -
        (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N) : Nat) : Int)) = S
        at hsI ⊢
      generalize toInt (x1W (zWord m)) * lnPhaseScaleI = A at hsI ⊢
      generalize ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B at hsI ⊢
      generalize lnBiasI * twoPow27I = C at hsI ⊢
      generalize 698600000 * twoPow99I = E at hsI ⊢
      omega
    rw [lnErrNegArg, htarget, hsub_cast]
    have hsc : toInt (x1W (zWord m)) * lnPhaseScaleI -
          ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
          lnBiasI * twoPow27I ≤
        (r + 1) * twoPow99I - twoPow27I := by
      have hVsI :
          (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
              lnBiasI) * twoPow27I +
            ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) =
          toInt (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
        simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
      have hgapI : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
          lnBiasI) * twoPow27I ≤ (r + 1) * twoPow99I - twoPow27I := by
        simpa [lnBiasI, twoPow27I, twoPow99I] using hgap
      generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 +
        ln2kInt c + lnBiasI) * twoPow27I = V27 at hgapI hVsI
      generalize hgL : ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = L at hVsI ⊢
      generalize hgA : toInt (x1W (zWord m)) * lnPhaseScaleI = A at hVsI ⊢
      generalize hgB : lnBiasI * twoPow27I = B at hVsI ⊢
      omega
    exact ln_err_neg_arg_le_int hsc hrneg
  have hmul : lnErrNegArg r * lnErrQ ≤
      ((-toInt (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) -
          (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N)) * lnErrQ :=
    Nat.mul_le_mul_right _ hple
  have capR0 := capUB_arg (q := lnErrQ) (by unfold lnErrQ; decide) hmul capV
  refine capUB_weaken ?_ capR0 ?_
  · have hm0 : 0 < m := by simp only [MLO] at h1; omega
    have hScp : 0 < Sc := by simp only [Sc]; omega
    exact Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos hm0 (by omega)) (Nat.pow_pos (by omega)))
      (Nat.mul_pos (Nat.mul_pos hScp (by omega)) (by omega))
  · have hbg := errBudgetBn_le (j := c - 160) (by omega)
    have hbf := Nat.mul_le_mul_left (x * Sc) hbg
    have eL : 560227709747861399187319382270000000000000000000000000000000 *
        (2 * (10 ^ 40 + 1)) ^ (c - 160) * ((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
        (x * 10 ^ 31) =
        x * Sc * ((2 * (10 ^ 40 + 1)) ^ (c - 160) * (10 : Nat) ^ 31 *
          (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31) := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * 10 ^ 31 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have eR : 10 ^ 18 * (10 ^ 31 - 10) * (m * 9999999999999999999999999996615 *
        (10 ^ 40 : Nat) ^ (c - 160) *
          (Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap))) =
        x * Sc * (10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 40 : Nat) ^ (c - 160) *
          2 ^ (c - 160) * (10 ^ 31 - 3385) * (10 ^ 31 - 3384) *
          (10 ^ 31 + lnErrorCoarseNegBudgetCap)) := by
      rw [hmx, show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    unfold wadRayNum wadRayStrictDen
    generalize hT1 : 560227709747861399187319382270000000000000000000000000000000 *
      (2 * (10 ^ 40 + 1)) ^ (c - 160) * ((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
      (x * 10 ^ 31) = T1 at eL ⊢
    generalize hT2 : x * Sc * ((2 * (10 ^ 40 + 1)) ^ (c - 160) * (10 : Nat) ^ 31 *
      (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31) = T2 at eL hbf
    generalize hT3 : x * Sc * (10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 40 : Nat) ^ (c - 160) *
      2 ^ (c - 160) * (10 ^ 31 - 3385) * (10 ^ 31 - 3384) *
      (10 ^ 31 + lnErrorCoarseNegBudgetCap)) = T3 at eR hbf
    generalize hT4 : 10 ^ 18 * (10 ^ 31 - 10) * (m * 9999999999999999999999999996615 *
      (10 ^ 40 : Nat) ^ (c - 160) *
        (Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap))) = T4 at eR ⊢
    omega

theorem r_nonneg_of_c160_v_nonneg {m : Nat} {R : Int}
    (hV0 : 0 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt 160 +
      116873961749927929127912020551516284764321243411868)
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt 160 +
      116873961749927929127912020551516284764321243411868 < (R + 1) * 2 ^ 72) :
    0 ≤ R := by
  rcases Int.lt_or_le R 0 with hneg | hnon
  · exfalso
    have hle : (R + 1) * 2 ^ 72 ≤ 0 := by
      have : R + 1 ≤ 0 := by omega
      exact Int.mul_le_mul_of_nonneg_right this (by decide : (0 : Int) ≤ 2 ^ 72)
    omega
  · exact hnon

theorem wad_le_of_clz_lt_160 {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hclt : evmClz x < 160) :
    10 ^ 18 ≤ x := by
  rcases Nat.lt_or_ge x (10 ^ 18) with hxlt | hxge
  · exfalso
    have hclz : evmClz x = 255 - Nat.log2 x := evmClz_eq h1 (by omega)
    have hx60 : x < 2 ^ 60 := by
      have hdec : (10 : Nat) ^ 18 < 2 ^ 60 := by decide
      omega
    have hlog : Nat.log2 x < 60 := (Nat.log2_lt (by omega)).mpr hx60
    have hlog_le : Nat.log2 x ≤ 59 := by omega
    have hclz_ge : 196 ≤ evmClz x := by
      rw [hclz]
      omega
    omega
  · exact hxge

theorem model_ln_wad_nonneg_of_clz_lt_160 {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hclt : evmClz x < 160) :
    0 ≤ toInt (model_ln_wad_evm x) := by
  have hxge := wad_le_of_clz_lt_160 h1 h2 hclt
  rcases Int.lt_or_le (toInt (model_ln_wad_evm x)) 0 with hneg | hnon
  · have hxlt := (model_ln_wad_negative_iff h1 h2).mp hneg
    omega
  · exact hnon

theorem model_ln_wad_error_bound_upper_c160 {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hne : x ≠ 10 ^ 18) (hc160 : evmClz x = 160) :
    CutLogWadRayLtRational x (toInt (model_ln_wad_evm x)) lnErrorBoundNum lnErrorBoundDen := by
  obtain ⟨hbr1, hbr2⟩ := model_floor_bracket h1 h2 hne
  rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr1 hbr2
  have hbr2' : toInt (x1W (zWord (mant x))) * 7450580596923828125 +
      ln2kInt (evmClz x) + 116873961749927929127912020551516284764321243411868 <
      (toInt (model_ln_wad_evm x) + 1) * 2 ^ 72 := by
    have e : (toInt (model_ln_wad_evm x) + 1) * 2 ^ 72 =
        toInt (model_ln_wad_evm x) * 2 ^ 72 + 2 ^ 72 := by
      rw [Int.add_mul, Int.one_mul]
    omega
  revert hbr1 hbr2'
  generalize toInt (model_ln_wad_evm x) = R
  intro hbr1 hbr2'
  obtain ⟨me, hmlo, hmhi⟩ := mant_facts h1 h2
  have hmant_eq : mant x = x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 := me
  have hmant_lo : MLO ≤ mant x := by rw [hmant_eq]; exact hmlo
  have hmant_hi : mant x < MHI := by rw [hmant_eq]; exact hmhi
  have hc : evmClz x ≤ 160 := by omega
  obtain ⟨hw1, hw2⟩ := mant_window_le h1 h2 hc
  have hw1' : mant x ≤ x := by
    rw [hc160] at hw1
    simpa only [Nat.sub_self, Nat.pow_zero, Nat.mul_one] using hw1
  have hw2' : x < mant x + 1 := by
    rw [hc160] at hw2
    simpa only [Nat.sub_self, Nat.pow_zero, Nat.mul_one] using hw2
  have hbr2c : toInt (x1W (zWord (mant x))) * 7450580596923828125 +
      ln2kInt 160 + 116873961749927929127912020551516284764321243411868 <
      (R + 1) * 2 ^ 72 := by
    simpa [hc160] using hbr2'
  apply CutLogWadRayLtRational_of_strict (by omega)
  unfold CutLogWadRayLtRationalStrict
  rw [if_pos]
  · rcases Nat.lt_or_ge (mant x) Sc with hbranch | hbranch
    · exact lo_lt_c160_exact hmant_lo hbranch hbr2c hw1' hw2'
    · have hV0 := v_pos_ge_pos hbranch hmant_hi (by decide : 160 ≤ 160)
      have hr0 := r_nonneg_of_c160_v_nonneg hV0 hbr2c
      exact lo_ge_c160_exact hbranch hmant_hi hbr2c (by omega) hw1' hw2'
  · rcases Nat.lt_or_ge (mant x) Sc with hbranch | hbranch
    · have hmhi : mant x < MHI := hmant_hi
      have hV0I := v_c160_nonneg hmant_lo hmhi
      have hV0 : 0 ≤ toInt (x1W (zWord (mant x))) * 7450580596923828125 +
          ln2kInt 160 + 116873961749927929127912020551516284764321243411868 := by
        simpa [lnBiasI] using hV0I
      have hr0 := r_nonneg_of_c160_v_nonneg hV0 hbr2c
      unfold lnErrorBoundDen lnErrorBoundNum
      omega
    · have hV0 := v_pos_ge_pos hbranch hmant_hi (by decide : 160 ≤ 160)
      have hr0 := r_nonneg_of_c160_v_nonneg hV0 hbr2c
      unfold lnErrorBoundDen lnErrorBoundNum
      omega

theorem model_ln_wad_error_bound_upper_neg_shift_nonneg {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hcgt : 160 < evmClz x) (hr0 : 0 ≤ toInt (model_ln_wad_evm x)) :
    CutLogWadRayLtRational x (toInt (model_ln_wad_evm x)) lnErrorBoundNum lnErrorBoundDen := by
  obtain ⟨hbr1, hbr2⟩ := model_floor_bracket h1 h2 hne
  rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr1 hbr2
  have hbr2' : toInt (x1W (zWord (mant x))) * 7450580596923828125 +
      ln2kInt (evmClz x) + 116873961749927929127912020551516284764321243411868 <
      (toInt (model_ln_wad_evm x) + 1) * 2 ^ 72 := by
    have e : (toInt (model_ln_wad_evm x) + 1) * 2 ^ 72 =
        toInt (model_ln_wad_evm x) * 2 ^ 72 + 2 ^ 72 := by
      rw [Int.add_mul, Int.one_mul]
    omega
  revert hbr1 hbr2' hr0
  generalize toInt (model_ln_wad_evm x) = R
  intro hr0 hbrLo hbrHi
  obtain ⟨me, hmlo, hmhi⟩ := mant_facts h1 h2
  have hmant_eq : mant x = x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 := me
  have hmant_lo : MLO ≤ mant x := by rw [hmant_eq]; exact hmlo
  have hmant_hi : mant x < MHI := by rw [hmant_eq]; exact hmhi
  obtain ⟨_hc1, hc255⟩ := clz_bounds h1 h2
  have hw := mant_window_gt h1 h2 hcgt
  have hpos : 1 ≤ R * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
    unfold lnErrorBoundDen lnErrorBoundNum
    omega
  apply CutLogWadRayLtRational_of_strict (by omega)
  unfold CutLogWadRayLtRationalStrict
  rw [if_pos hpos]
  change capLB (lnErrArg R) lnErrQ (wadRayNum x) wadRayStrictDen
  rcases Nat.lt_or_ge (mant x) Sc with hbranch | hbranch
  · exact lo_lt_neg_exact hmant_lo hbranch hcgt hc255 hbrHi hbrLo hr0 hw
  · exact lo_ge_neg_exact hbranch hmant_hi hcgt hc255 hbrHi hbrLo hr0 hw

theorem model_ln_wad_error_bound_upper_neg_shift_rec_ge {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hcgt : 160 < evmClz x) (hrneg : toInt (model_ln_wad_evm x) ≤ -2) :
    CutLogWadRayLtRational x (toInt (model_ln_wad_evm x)) lnErrorBoundNum lnErrorBoundDen := by
  obtain ⟨_hbr1, hbr2⟩ := model_floor_bracket h1 h2 hne
  rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr2
  have hbrHi : toInt (x1W (zWord (mant x))) * 7450580596923828125 +
      ln2kInt (evmClz x) + 116873961749927929127912020551516284764321243411868 <
      (toInt (model_ln_wad_evm x) + 1) * 2 ^ 72 := by
    have e : (toInt (model_ln_wad_evm x) + 1) * 2 ^ 72 =
        toInt (model_ln_wad_evm x) * 2 ^ 72 + 2 ^ 72 := by
      rw [Int.add_mul, Int.one_mul]
    omega
  revert hbrHi hrneg
  generalize toInt (model_ln_wad_evm x) = R
  intro hrneg hbrHi
  obtain ⟨me, hmlo, hmhi⟩ := mant_facts h1 h2
  have hmant_eq : mant x = x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 := me
  have hmant_lo : MLO ≤ mant x := by rw [hmant_eq]; exact hmlo
  have hmant_hi : mant x < MHI := by rw [hmant_eq]; exact hmhi
  obtain ⟨_hc1, hc255⟩ := clz_bounds h1 h2
  have hw := mant_window_gt h1 h2 hcgt
  have hneg : ¬1 ≤ R * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
    unfold lnErrorBoundDen lnErrorBoundNum
    omega
  apply CutLogWadRayLtRational_of_strict (by omega)
  unfold CutLogWadRayLtRationalStrict
  rw [if_neg hneg]
  change capUB (lnErrNegArg R) lnErrQ wadRayStrictDen (wadRayNum x)
  rcases Nat.lt_or_ge (mant x) Sc with hbranch | hbranch
  · exact bn_lt_neg_exact hmant_lo hbranch hcgt hc255 hbrHi hrneg hw
  · exact bn_ge_neg_exact hbranch hmant_hi hcgt hc255 hbrHi hrneg hw

theorem model_ln_wad_positive_shift_ge_top_or_direct {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hclt : evmClz x < 160) (hge : Sc ≤ mant x)
    (hcert : PosShiftGeTopBudgetIneqOk (mant x) (evmClz x) ∨
      PosShiftTopDirectOk 320 (mant x) (evmClz x)) :
    capLB (lnErrArg (toInt (model_ln_wad_evm x))) lnErrQ x (10 ^ 18) := by
  have hx256 : x < 2 ^ 256 := by omega
  have htail :
      model_ln_wad_evm x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
    rw [model_eq_tail hx256]
    rfl
  rcases hcert with htopBudget | hdirect
  · have htop : x ≤ posTopX (evmClz x) (mant x) := by
      have hw := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
      have hpos : 0 < (mant x + 1) * 2 ^ (160 - evmClz x) :=
        Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by decide))
      unfold posTopX
      omega
    obtain ⟨_hbr1, hbr2⟩ := model_floor_bracket h1 h2 hne
    rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr2
    have hbrHi : toInt (x1W (zWord (mant x))) * 7450580596923828125 +
        ln2kInt (evmClz x) + lnBiasI <
        (toInt (model_ln_wad_evm x) + 1) * 2 ^ 72 := by
      have e : (toInt (model_ln_wad_evm x) + 1) * 2 ^ 72 =
          toInt (model_ln_wad_evm x) * 2 ^ 72 + 2 ^ 72 := by
        rw [Int.add_mul, Int.one_mul]
      rw [e]
      simpa [lnBiasI] using hbr2
    obtain ⟨me, _hmlo, hmhi⟩ := mant_facts h1 h2
    have hmant_hi : mant x < MHI := by
      unfold mant
      rw [me]
      exact hmhi
    have hr0 := model_ln_wad_nonneg_of_clz_lt_160 h1 h2 hclt
    have hphase :
        posPhaseNatGe (mant x) (evmClz x) ≤ lnErrArg (toInt (model_ln_wad_evm x)) :=
      posPhaseNatGe_le_lnErrArg hge hmant_hi (by omega) hbrHi (by omega)
    have hineq : PosShiftGeBudgetIneqOk (mant x) (evmClz x) x
        (toInt (model_ln_wad_evm x)) := by
      change PosShiftGeBudgetIneqOk (mant x) (evmClz x)
        (posTopX (evmClz x) (mant x)) (toInt (lnTail (evmSub 160 (evmClz x)) (mant x))) at htopBudget
      rw [← htail] at htopBudget
      unfold PosShiftGeBudgetIneqOk at htopBudget ⊢
      have hnum : wadRayNum x ≤ wadRayNum (posTopX (evmClz x) (mant x)) := by
        unfold wadRayNum
        exact Nat.mul_le_mul_right (10 ^ 31) htop
      exact Nat.le_trans (Nat.mul_le_mul_right (posBaseWGe (evmClz x) * lnErrQ) hnum)
        htopBudget
    exact capLB_strict_to_exact
      (lo_ge_pos_budget_exact hge hmant_hi hclt ⟨hphase, hineq⟩)
  · unfold PosShiftTopDirectOk at hdirect
    exact pos_shift_direct_exact_of_sumGE h1 h2 hclt hdirect

theorem model_ln_wad_positive_shift_lt_top_or_direct {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hclt : evmClz x < 160) (hlt : mant x < Sc)
    (hcert : PosShiftLtTopBudgetIneqOk (mant x) (evmClz x) ∨
      PosShiftTopDirectOk 320 (mant x) (evmClz x)) :
    capLB (lnErrArg (toInt (model_ln_wad_evm x))) lnErrQ x (10 ^ 18) := by
  have hx256 : x < 2 ^ 256 := by omega
  have htail :
      model_ln_wad_evm x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
    rw [model_eq_tail hx256]
    rfl
  rcases hcert with htopBudget | hdirect
  · have htop : x ≤ posTopX (evmClz x) (mant x) := by
      have hw := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
      have hpos : 0 < (mant x + 1) * 2 ^ (160 - evmClz x) :=
        Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by decide))
      unfold posTopX
      omega
    obtain ⟨hbr1, hbr2⟩ := model_floor_bracket h1 h2 hne
    rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr1 hbr2
    have hbrHi : toInt (x1W (zWord (mant x))) * 7450580596923828125 +
        ln2kInt (evmClz x) + lnBiasI <
        (toInt (model_ln_wad_evm x) + 1) * 2 ^ 72 := by
      have e : (toInt (model_ln_wad_evm x) + 1) * 2 ^ 72 =
          toInt (model_ln_wad_evm x) * 2 ^ 72 + 2 ^ 72 := by
        rw [Int.add_mul, Int.one_mul]
      rw [e]
      simpa [lnBiasI] using hbr2
    obtain ⟨me, hmlo, _hmhi⟩ := mant_facts h1 h2
    have hmant_lo : MLO ≤ mant x := by
      unfold mant
      rw [me]
      exact hmlo
    have hX := x1_nonpos_ltF hmant_lo hlt
    have hr0 := model_ln_wad_nonneg_of_clz_lt_160 h1 h2 hclt
    have hV0 : 0 ≤ toInt (x1W (zWord (mant x))) * 7450580596923828125 +
        ln2kInt (evmClz x) + lnBiasI := by
      have hR0 : 0 ≤ toInt (model_ln_wad_evm x) * 2 ^ 72 :=
        Int.mul_nonneg hr0 (by decide)
      have h := Int.le_trans hR0 hbr1
      simpa [lnBiasI] using h
    have hneg := posNegXNat_le_posConstNat hX (by omega) hV0
    have hphase :
        posPhaseNatLt (mant x) (evmClz x) ≤ lnErrArg (toInt (model_ln_wad_evm x)) :=
      posPhaseNatLt_le_lnErrArg hX (by omega) hneg hbrHi (by omega)
    have hineq : PosShiftLtBudgetIneqOk (mant x) (evmClz x) x
        (toInt (model_ln_wad_evm x)) := by
      change PosShiftLtBudgetIneqOk (mant x) (evmClz x)
        (posTopX (evmClz x) (mant x)) (toInt (lnTail (evmSub 160 (evmClz x)) (mant x))) at htopBudget
      rw [← htail] at htopBudget
      unfold PosShiftLtBudgetIneqOk at htopBudget ⊢
      have hnum : wadRayNum x ≤ wadRayNum (posTopX (evmClz x) (mant x)) := by
        unfold wadRayNum
        exact Nat.mul_le_mul_right (10 ^ 31) htop
      exact Nat.le_trans (Nat.mul_le_mul_right (posBaseWLt (evmClz x) * lnErrQ) hnum)
        htopBudget
    exact capLB_strict_to_exact
      (lo_lt_pos_budget_exact hmant_lo hlt hclt ⟨hneg, hphase, hineq⟩)
  · unfold PosShiftTopDirectOk at hdirect
    exact pos_shift_direct_exact_of_sumGE h1 h2 hclt hdirect

theorem model_ln_wad_positive_shift_ge_residue_or_direct {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hclt : evmClz x < 160) (hge : Sc ≤ mant x)
    (hcert : PosShiftGeResidueOk (mant x) (evmClz x) (toInt (model_ln_wad_evm x)) ∨
      PosShiftTopDirectOk 320 (mant x) (evmClz x)) :
    capLB (lnErrArg (toInt (model_ln_wad_evm x))) lnErrQ x (10 ^ 18) := by
  rcases hcert with hres | hdirect
  · obtain ⟨_me, _hmlo, hmhi⟩ := mant_facts h1 h2
    have hmant_hi : mant x < MHI := by
      unfold mant
      rw [_me]
      exact hmhi
    obtain ⟨hc1, _hc255⟩ := clz_bounds h1 h2
    obtain ⟨_hw1, hw2⟩ := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
    have hr0 := model_ln_wad_nonneg_of_clz_lt_160 h1 h2 hclt
    exact capLB_strict_to_exact
      (lo_ge_pos_exact_ge_residue hge hmant_hi hc1 hclt hr0 hres hw2)
  · unfold PosShiftTopDirectOk at hdirect
    exact pos_shift_direct_exact_of_sumGE h1 h2 hclt hdirect

theorem model_ln_wad_positive_shift_lt_residue_or_direct {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hclt : evmClz x < 160) (hlt : mant x < Sc) (hband_lo : Sc - 45 ≤ mant x)
    (hcert : PosShiftResidueOk (mant x) (evmClz x) (toInt (model_ln_wad_evm x)) ∨
      PosShiftTopDirectOk 320 (mant x) (evmClz x)) :
    capLB (lnErrArg (toInt (model_ln_wad_evm x))) lnErrQ x (10 ^ 18) := by
  rcases hcert with hres | hdirect
  · obtain ⟨hbr1, _hbr2⟩ := model_floor_bracket h1 h2 hne
    rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr1
    obtain ⟨hc1, _hc255⟩ := clz_bounds h1 h2
    obtain ⟨_hw1, hw2⟩ := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
    have hr0 := model_ln_wad_nonneg_of_clz_lt_160 h1 h2 hclt
    exact capLB_strict_to_exact
      (lo_lt_pos_exact hband_lo hlt hc1 hclt hbr1 hr0 hres hw2)
  · unfold PosShiftTopDirectOk at hdirect
    exact pos_shift_direct_exact_of_sumGE h1 h2 hclt hdirect

theorem model_ln_wad_positive_shift_ge_phase_direct {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hclt : evmClz x < 160) (hge : Sc ≤ mant x)
    (hcert : PosShiftGePhaseDirectOk 320 (mant x) (evmClz x)) :
    capLB (lnErrArg (toInt (model_ln_wad_evm x))) lnErrQ x (10 ^ 18) := by
  obtain ⟨_hbr1, hbr2⟩ := model_floor_bracket h1 h2 hne
  rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr2
  have hbrHi : toInt (x1W (zWord (mant x))) * 7450580596923828125 +
      ln2kInt (evmClz x) + lnBiasI <
      (toInt (model_ln_wad_evm x) + 1) * 2 ^ 72 := by
    have e : (toInt (model_ln_wad_evm x) + 1) * 2 ^ 72 =
        toInt (model_ln_wad_evm x) * 2 ^ 72 + 2 ^ 72 := by
      rw [Int.add_mul, Int.one_mul]
    rw [e]
    simpa [lnBiasI] using hbr2
  obtain ⟨me, _hmlo, hmhi⟩ := mant_facts h1 h2
  have hmant_hi : mant x < MHI := by
    unfold mant
    rw [me]
    exact hmhi
  have hr0 := model_ln_wad_nonneg_of_clz_lt_160 h1 h2 hclt
  have hp := posPhaseNatGe_extra_le_lnErrArg hge hmant_hi (by omega) hbrHi (by omega)
  have cap0 : capLB (posPhaseNatGe (mant x) (evmClz x) + lnPhaseExtraArg)
      lnErrQ (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
    unfold PosShiftGePhaseDirectOk at hcert
    exact ⟨320, hcert⟩
  have capR : capLB (lnErrArg (toInt (model_ln_wad_evm x))) lnErrQ
      (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
    refine capLB_arg (q' := lnErrQ) (by unfold lnErrQ; decide) ?_ cap0
    exact Nat.mul_le_mul_right lnErrQ hp
  have htop : x ≤ posTopX (evmClz x) (mant x) := by
    have hw := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
    have hpos : 0 < (mant x + 1) * 2 ^ (160 - evmClz x) :=
      Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by decide))
    unfold posTopX
    omega
  refine capLB_weaken (p := lnErrArg (toInt (model_ln_wad_evm x))) (q := lnErrQ)
    (y := posTopX (evmClz x) (mant x)) (w := 10 ^ 18)
    (y' := x) (w' := 10 ^ 18) (by decide) capR ?_
  exact Nat.mul_le_mul_right (10 ^ 18) htop

theorem model_ln_wad_positive_shift_lt_phase_direct {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hclt : evmClz x < 160) (hlt : mant x < Sc)
    (hcert : PosShiftLtPhaseDirectOk 320 (mant x) (evmClz x)) :
    capLB (lnErrArg (toInt (model_ln_wad_evm x))) lnErrQ x (10 ^ 18) := by
  obtain ⟨hbr1, hbr2⟩ := model_floor_bracket h1 h2 hne
  rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr1 hbr2
  have hbrHi : toInt (x1W (zWord (mant x))) * 7450580596923828125 +
      ln2kInt (evmClz x) + lnBiasI <
      (toInt (model_ln_wad_evm x) + 1) * 2 ^ 72 := by
    have e : (toInt (model_ln_wad_evm x) + 1) * 2 ^ 72 =
        toInt (model_ln_wad_evm x) * 2 ^ 72 + 2 ^ 72 := by
      rw [Int.add_mul, Int.one_mul]
    rw [e]
    simpa [lnBiasI] using hbr2
  obtain ⟨me, hmlo, _hmhi⟩ := mant_facts h1 h2
  have hmant_lo : MLO ≤ mant x := by
    unfold mant
    rw [me]
    exact hmlo
  have hX := x1_nonpos_ltF hmant_lo hlt
  have hr0 := model_ln_wad_nonneg_of_clz_lt_160 h1 h2 hclt
  have hV0 : 0 ≤ toInt (x1W (zWord (mant x))) * 7450580596923828125 +
      ln2kInt (evmClz x) + lnBiasI := by
    have hR0 : 0 ≤ toInt (model_ln_wad_evm x) * 2 ^ 72 :=
      Int.mul_nonneg hr0 (by decide)
    have h := Int.le_trans hR0 hbr1
    simpa [lnBiasI] using h
  have hneg := posNegXNat_le_posConstNat hX (by omega) hV0
  have hp := posPhaseNatLt_extra_le_lnErrArg hX (by omega) hneg hbrHi (by omega)
  have cap0 : capLB (posPhaseNatLt (mant x) (evmClz x) + lnPhaseExtraArg)
      lnErrQ (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
    unfold PosShiftLtPhaseDirectOk at hcert
    exact ⟨320, hcert⟩
  have capR : capLB (lnErrArg (toInt (model_ln_wad_evm x))) lnErrQ
      (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
    refine capLB_arg (q' := lnErrQ) (by unfold lnErrQ; decide) ?_ cap0
    exact Nat.mul_le_mul_right lnErrQ hp
  have htop : x ≤ posTopX (evmClz x) (mant x) := by
    have hw := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
    have hpos : 0 < (mant x + 1) * 2 ^ (160 - evmClz x) :=
      Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by decide))
    unfold posTopX
    omega
  refine capLB_weaken (p := lnErrArg (toInt (model_ln_wad_evm x))) (q := lnErrQ)
    (y := posTopX (evmClz x) (mant x)) (w := 10 ^ 18)
    (y' := x) (w' := 10 ^ 18) (by decide) capR ?_
  exact Nat.mul_le_mul_right (10 ^ 18) htop

theorem model_ln_wad_positive_shift_ge_min_phase_direct {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hclt : evmClz x < 160) (hge : Sc ≤ mant x)
    (hcert : PosShiftGeMinPhaseDirectOk 320 (mant x) (evmClz x)) :
    capLB (lnErrArg (toInt (model_ln_wad_evm x))) lnErrQ x (10 ^ 18) := by
  have hx256 : x < 2 ^ 256 := by omega
  have htail :
      model_ln_wad_evm x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
    rw [model_eq_tail hx256]
    rfl
  obtain ⟨me, _hmlo, hmhi⟩ := mant_facts h1 h2
  have hmant_hi : mant x < MHI := by
    unfold mant
    rw [me]
    exact hmhi
  have hp := posPhaseNatGe_minAvail_le_lnErrArg hge hmant_hi hclt
  rw [← htail] at hp
  have cap0 : capLB (posPhaseNatGe (mant x) (evmClz x) + minPosAvail)
      lnErrQ (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
    unfold PosShiftGeMinPhaseDirectOk at hcert
    exact ⟨320, hcert⟩
  have capR : capLB (lnErrArg (toInt (model_ln_wad_evm x))) lnErrQ
      (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
    refine capLB_arg (q' := lnErrQ) (by unfold lnErrQ; decide) ?_ cap0
    exact Nat.mul_le_mul_right lnErrQ hp
  have htop : x ≤ posTopX (evmClz x) (mant x) := by
    have hw := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
    have hpos : 0 < (mant x + 1) * 2 ^ (160 - evmClz x) :=
      Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by decide))
    unfold posTopX
    omega
  refine capLB_weaken (p := lnErrArg (toInt (model_ln_wad_evm x))) (q := lnErrQ)
    (y := posTopX (evmClz x) (mant x)) (w := 10 ^ 18)
    (y' := x) (w' := 10 ^ 18) (by decide) capR ?_
  exact Nat.mul_le_mul_right (10 ^ 18) htop

theorem model_ln_wad_positive_shift_lt_min_phase_direct {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hclt : evmClz x < 160) (hlt : mant x < Sc)
    (hcert : PosShiftLtMinPhaseDirectOk 320 (mant x) (evmClz x)) :
    capLB (lnErrArg (toInt (model_ln_wad_evm x))) lnErrQ x (10 ^ 18) := by
  have hx256 : x < 2 ^ 256 := by omega
  have htail :
      model_ln_wad_evm x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
    rw [model_eq_tail hx256]
    rfl
  obtain ⟨me, hmlo, _hmhi⟩ := mant_facts h1 h2
  have hmant_lo : MLO ≤ mant x := by
    unfold mant
    rw [me]
    exact hmlo
  have hp := posPhaseNatLt_minAvail_le_lnErrArg hmant_lo hlt hclt
  rw [← htail] at hp
  have cap0 : capLB (posPhaseNatLt (mant x) (evmClz x) + minPosAvail)
      lnErrQ (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
    unfold PosShiftLtMinPhaseDirectOk at hcert
    exact ⟨320, hcert⟩
  have capR : capLB (lnErrArg (toInt (model_ln_wad_evm x))) lnErrQ
      (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
    refine capLB_arg (q' := lnErrQ) (by unfold lnErrQ; decide) ?_ cap0
    exact Nat.mul_le_mul_right lnErrQ hp
  have htop : x ≤ posTopX (evmClz x) (mant x) := by
    have hw := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
    have hpos : 0 < (mant x + 1) * 2 ^ (160 - evmClz x) :=
      Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by decide))
    unfold posTopX
    omega
  refine capLB_weaken (p := lnErrArg (toInt (model_ln_wad_evm x))) (q := lnErrQ)
    (y := posTopX (evmClz x) (mant x)) (w := 10 ^ 18)
    (y' := x) (w' := 10 ^ 18) (by decide) capR ?_
  exact Nat.mul_le_mul_right (10 ^ 18) htop

def PosShiftGeBranchCert (m c : Nat) (r : Int) : Prop :=
  PosShiftGeResidueOk m c r ∨
    PosShiftGeTopBudgetIneqOk m c ∨
      PosShiftTopDirectOk 320 m c ∨
        PosShiftGePhaseDirectOk 320 m c ∨
          (PosShiftDirectResidueGapOk m c r ∧ PosShiftGePhaseGapDirectOk 320 m c)

def PosShiftLtBranchCert (m c : Nat) (r : Int) : Prop :=
  PosShiftResidueOk m c r ∨
    PosShiftLtTopBudgetIneqOk m c ∨
      PosShiftTopDirectOk 320 m c ∨
        PosShiftLtPhaseDirectOk 320 m c ∨
          (PosShiftDirectResidueGapOk m c r ∧ PosShiftLtPhaseGapDirectOk 320 m c)

def posShiftGeTopBudgetIneqOkB (m c : Nat) : Bool :=
  decide (wadRayNum (posTopX c m) * (posBaseWGe c * lnErrQ) ≤
    (posBaseYGe m c *
      (lnErrQ + posAvailGe m c (toInt (lnTail (evmSub 160 c) m)))) *
        wadRayStrictDen)

def posShiftLtTopBudgetIneqOkB (m c : Nat) : Bool :=
  decide (wadRayNum (posTopX c m) * (posBaseWLt c * lnErrQ) ≤
    (posBaseYLt m c *
      (lnErrQ + posAvailLt m c (toInt (lnTail (evmSub 160 c) m)))) *
        wadRayStrictDen)

def posShiftTopDirectOkB (m c : Nat) : Bool :=
  sumGEB 320 (lnErrArg (toInt (lnTail (evmSub 160 c) m))) lnErrQ
    (posTopX c m) (10 ^ 18)

def posShiftGePhaseDirectOkB (m c : Nat) : Bool :=
  sumGEB 320 (posPhaseNatGe m c + lnPhaseExtraArg) lnErrQ
    (posTopX c m) (10 ^ 18)

def posShiftLtPhaseDirectOkB (m c : Nat) : Bool :=
  sumGEB 320 (posPhaseNatLt m c + lnPhaseExtraArg) lnErrQ
    (posTopX c m) (10 ^ 18)

def posShiftGeMinPhaseDirectOkB (m c : Nat) : Bool :=
  sumGEB 320 (posPhaseNatGe m c + minPosAvail) lnErrQ
    (posTopX c m) (10 ^ 18)

def posShiftLtMinPhaseDirectOkB (m c : Nat) : Bool :=
  sumGEB 320 (posPhaseNatLt m c + minPosAvail) lnErrQ
    (posTopX c m) (10 ^ 18)

def posShiftGePhaseGapDirectOkB (m c : Nat) : Bool :=
  sumGEB 320 (posPhaseNatGe m c + lnPhaseExtraArg + lnDirectGapArg) lnErrQ
    (posTopX c m) (10 ^ 18)

def posShiftLtPhaseGapDirectOkB (m c : Nat) : Bool :=
  sumGEB 320 (posPhaseNatLt m c + lnPhaseExtraArg + lnDirectGapArg) lnErrQ
    (posTopX c m) (10 ^ 18)

def posShiftGeBranchCertB (m c : Nat) (r : Int) : Bool :=
  geResidueGapOkB m c r ||
    (posShiftGeTopBudgetIneqOkB m c ||
      (posShiftTopDirectOkB m c ||
        (posShiftGePhaseDirectOkB m c ||
          (directResidueGapOkB m c r && posShiftGePhaseGapDirectOkB m c)
        )))

def posShiftLtBranchCertB (m c : Nat) (r : Int) : Bool :=
  residueGapOkB m c r ||
    (posShiftLtTopBudgetIneqOkB m c ||
      (posShiftTopDirectOkB m c ||
        (posShiftLtPhaseDirectOkB m c ||
          (directResidueGapOkB m c r && posShiftLtPhaseGapDirectOkB m c)
        )))

def hardMantissaLtGapBranchB (c : Nat) : Bool :=
  directResidueGapOkB lnErrorHardMantissa c
      (toInt (lnTail (evmSub 160 c) lnErrorHardMantissa)) &&
    posShiftLtPhaseGapDirectOkB lnErrorHardMantissa c

theorem hardMantissaLtGapBranch_all :
    (List.range 159).all (fun i => hardMantissaLtGapBranchB (i + 1)) = true := by
  decide +kernel

theorem hardMantissaLtGapBranch {c : Nat} (hc1 : 1 ≤ c) (hc : c < 160) :
    PosShiftDirectResidueGapOk lnErrorHardMantissa c
        (toInt (lnTail (evmSub 160 c) lnErrorHardMantissa)) ∧
      PosShiftLtPhaseGapDirectOk 320 lnErrorHardMantissa c := by
  have h := List.all_eq_true.mp hardMantissaLtGapBranch_all (c - 1)
    (List.mem_range.mpr (by omega : c - 1 < 159))
  rw [show c - 1 + 1 = c by omega] at h
  unfold hardMantissaLtGapBranchB at h
  rw [Bool.and_eq_true] at h
  exact ⟨PosShiftDirectResidueGapOk.of_bool h.1, by
    unfold posShiftLtPhaseGapDirectOkB at h
    unfold PosShiftLtPhaseGapDirectOk
    exact sumGE_of_sumGEB h.2⟩

theorem hardMantissaLtBranchCert {c : Nat} (hc1 : 1 ≤ c) (hc : c < 160) :
    PosShiftLtBranchCert lnErrorHardMantissa c
      (toInt (lnTail (evmSub 160 c) lnErrorHardMantissa)) := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (hardMantissaLtGapBranch hc1 hc))))

theorem posShiftGeBranchCert_of_bool {m c : Nat} {r : Int} (hc : c ≤ 160)
    (h : posShiftGeBranchCertB m c r = true) :
    PosShiftGeBranchCert m c r := by
  unfold posShiftGeBranchCertB at h
  unfold PosShiftGeBranchCert
  rw [Bool.or_eq_true] at h
  rcases h with hres | hrest
  · exact Or.inl (PosShiftGeResidueOk_of_gapB hc hres)
  · rw [Bool.or_eq_true] at hrest
    rcases hrest with htop | hrest
    · exact Or.inr (Or.inl (by
      unfold posShiftGeTopBudgetIneqOkB at htop
      unfold PosShiftGeTopBudgetIneqOk PosShiftGeBudgetIneqOk
      exact of_decide_eq_true htop))
    · rw [Bool.or_eq_true] at hrest
      rcases hrest with hdir | hrest
      · exact Or.inr (Or.inr (Or.inl (by
        unfold posShiftTopDirectOkB at hdir
        unfold PosShiftTopDirectOk
        exact sumGE_of_sumGEB hdir)))
      · rw [Bool.or_eq_true] at hrest
        rcases hrest with hphase | hgapBool
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by
        unfold posShiftGePhaseDirectOkB at hphase
        unfold PosShiftGePhaseDirectOk
        exact sumGE_of_sumGEB hphase))))
        · rw [Bool.and_eq_true] at hgapBool
          have hgap := hgapBool
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨PosShiftDirectResidueGapOk.of_bool hgap.1, by
        unfold posShiftGePhaseGapDirectOkB at hgap
        unfold PosShiftGePhaseGapDirectOk
        exact sumGE_of_sumGEB hgap.2⟩)))

theorem posShiftLtBranchCert_of_bool {m c : Nat} {r : Int}
    (hc : c ≤ 160)
    (h : posShiftLtBranchCertB m c r = true) :
    PosShiftLtBranchCert m c r := by
  unfold posShiftLtBranchCertB at h
  unfold PosShiftLtBranchCert
  rw [Bool.or_eq_true] at h
  rcases h with hres | hrest
  · exact Or.inl (PosShiftResidueOk_of_gapB hc hres)
  · rw [Bool.or_eq_true] at hrest
    rcases hrest with htop | hrest
    · exact Or.inr (Or.inl (by
      unfold posShiftLtTopBudgetIneqOkB at htop
      unfold PosShiftLtTopBudgetIneqOk PosShiftLtBudgetIneqOk
      exact of_decide_eq_true htop))
    · rw [Bool.or_eq_true] at hrest
      rcases hrest with hdir | hrest
      · exact Or.inr (Or.inr (Or.inl (by
        unfold posShiftTopDirectOkB at hdir
        unfold PosShiftTopDirectOk
        exact sumGE_of_sumGEB hdir)))
      · rw [Bool.or_eq_true] at hrest
        rcases hrest with hphase | hgapBool
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by
        unfold posShiftLtPhaseDirectOkB at hphase
        unfold PosShiftLtPhaseDirectOk
        exact sumGE_of_sumGEB hphase))))
        · rw [Bool.and_eq_true] at hgapBool
          have hgap := hgapBool
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨PosShiftDirectResidueGapOk.of_bool hgap.1, by
        unfold posShiftLtPhaseGapDirectOkB at hgap
        unfold PosShiftLtPhaseGapDirectOk
        exact sumGE_of_sumGEB hgap.2⟩)))

def directTopCellOkB (lo hi c : Nat) : Bool :=
  ({ c := c, lo := lo, hi := hi, n := 320 } : PosShiftDirectCell).okB

def geBranchCellOkB (lo hi c : Nat) : Bool :=
  geResidueRunCellOkB lo hi c ||
    (geResidueCellOkB lo hi c ||
      (geTopBudgetCoarseCellOkB lo hi c ||
        (geTopBudgetRunCellOkB lo hi c ||
          (directTopCellOkB lo hi c ||
            (gePhaseCellOkB lo hi c ||
              ((directResidueRunCellOkB lo hi c && gePhaseGapCellOkB lo hi c) ||
                (directResidueCellOkB lo hi c && gePhaseGapCellOkB lo hi c)))))))

def ltBranchCellOkB (lo hi c : Nat) : Bool :=
  residueRunCellOkB lo hi c ||
    (ltTopBudgetCoarseCellOkB lo hi c ||
      (ltTopBudgetRunCellOkB lo hi c ||
        (directTopCellOkB lo hi c ||
          (ltPhaseCellOkB lo hi c ||
            ((directResidueRunCellOkB lo hi c && ltPhaseGapCellOkB lo hi c) ||
              (directResidueCellOkB lo hi c && ltPhaseGapCellOkB lo hi c))))))

theorem geBranchCellOkB_sound {lo hi m c : Nat}
    (h : geBranchCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGeBranchCert m c (toInt (lnTail (evmSub 160 c) m)) := by
  unfold geBranchCellOkB at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with hrun | hrest
  · exact Or.inl (geResidueRunCellOkB_sound hrun hlom hmhi)
  rcases hrest with hres | hrest
  · exact Or.inl (geResidueCellOkB_sound hres hlom hmhi)
  rcases hrest with htop | hrest
  · exact Or.inr (Or.inl (geTopBudgetCoarseCellOkB_sound htop hlom hmhi))
  rcases hrest with htop | hrest
  · exact Or.inr (Or.inl (geTopBudgetRunCellOkB_sound htop hlom hmhi))
  rcases hrest with hdir | hrest
  · exact Or.inr (Or.inr (Or.inl
      (PosShiftDirectCell.sound (PosShiftDirectCell.ok_of_okB hdir)
        (by
          unfold PosShiftDirectCell.Covers directTopCellOkB at *
          exact ⟨rfl, hlom, hmhi⟩))))
  rcases hrest with hphase | hgap
  · exact Or.inr (Or.inr (Or.inr (Or.inl (gePhaseCell_sound hphase hlom hmhi))))
  · rcases hgap with hgapRun | hgapCell
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨directResidueRunCellOkB_sound hgapRun.1 hlom hmhi,
          gePhaseGapCell_sound hgapRun.2 hlom hmhi⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨directResidueCellOkB_sound hgapCell.1 hlom hmhi,
          gePhaseGapCell_sound hgapCell.2 hlom hmhi⟩)))

theorem ltBranchCellOkB_sound {lo hi m c : Nat}
    (h : ltBranchCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftLtBranchCert m c (toInt (lnTail (evmSub 160 c) m)) := by
  unfold ltBranchCellOkB at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with hres | hrest
  · exact Or.inl (residueRunCellOkB_sound hres hlom hmhi)
  rcases hrest with htop | hrest
  · exact Or.inr (Or.inl (ltTopBudgetCoarseCellOkB_sound htop hlom hmhi))
  rcases hrest with htop | hrest
  · exact Or.inr (Or.inl (ltTopBudgetRunCellOkB_sound htop hlom hmhi))
  rcases hrest with hdir | hrest
  · exact Or.inr (Or.inr (Or.inl
      (PosShiftDirectCell.sound (PosShiftDirectCell.ok_of_okB hdir)
        (by
          unfold PosShiftDirectCell.Covers directTopCellOkB at *
          exact ⟨rfl, hlom, hmhi⟩))))
  rcases hrest with hphase | hgap
  · exact Or.inr (Or.inr (Or.inr (Or.inl (ltPhaseCell_sound hphase hlom hmhi))))
  · rcases hgap with hgapRun | hgapCell
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨directResidueRunCellOkB_sound hgapRun.1 hlom hmhi,
          ltPhaseGapCell_sound hgapRun.2 hlom hmhi⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨directResidueCellOkB_sound hgapCell.1 hlom hmhi,
          ltPhaseGapCell_sound hgapCell.2 hlom hmhi⟩)))

def geBranchCellListCoverB (c : Nat) : Nat → Nat → List ResidueCell → Bool
  | lo, hi, [] => decide (hi < lo)
  | lo, hi, cell :: cells =>
      decide (cell.lo = lo) &&
        decide (lo ≤ cell.hi) &&
          decide (cell.hi ≤ hi) &&
            geBranchCellOkB cell.lo cell.hi c &&
              geBranchCellListCoverB c (cell.hi + 1) hi cells

def ltBranchCellListCoverB (c : Nat) : Nat → Nat → List ResidueCell → Bool
  | lo, hi, [] => decide (hi < lo)
  | lo, hi, cell :: cells =>
      decide (cell.lo = lo) &&
        decide (lo ≤ cell.hi) &&
          decide (cell.hi ≤ hi) &&
            ltBranchCellOkB cell.lo cell.hi c &&
              ltBranchCellListCoverB c (cell.hi + 1) hi cells

theorem geBranchCellListCoverB_sound {cells : List ResidueCell} {c lo hi m : Nat}
    (h : geBranchCellListCoverB c lo hi cells = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGeBranchCert m c (toInt (lnTail (evmSub 160 c) m)) := by
  induction cells generalizing lo with
  | nil =>
      unfold geBranchCellListCoverB at h
      have hlt : hi < lo := of_decide_eq_true h
      omega
  | cons cell cells ih =>
      unfold geBranchCellListCoverB at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hlo, _hlohi⟩, _hhihi⟩, hok⟩, hrest⟩ := h
      by_cases hmcell : m ≤ cell.hi
      · exact geBranchCellOkB_sound hok (by omega) hmcell
      · exact ih hrest (by omega)

theorem ltBranchCellListCoverB_sound {cells : List ResidueCell} {c lo hi m : Nat}
    (h : ltBranchCellListCoverB c lo hi cells = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftLtBranchCert m c (toInt (lnTail (evmSub 160 c) m)) := by
  induction cells generalizing lo with
  | nil =>
      unfold ltBranchCellListCoverB at h
      have hlt : hi < lo := of_decide_eq_true h
      omega
  | cons cell cells ih =>
      unfold ltBranchCellListCoverB at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hlo, _hlohi⟩, _hhihi⟩, hok⟩, hrest⟩ := h
      by_cases hmcell : m ≤ cell.hi
      · exact ltBranchCellOkB_sound hok (by omega) hmcell
      · exact ih hrest (by omega)

def geBranchCoverB : Nat → Nat → Nat → Nat → Bool
  | 0, _c, lo, hi => decide (hi < lo)
  | fuel + 1, c, lo, hi =>
      if hi < lo then
        true
      else
        let mx := phaseSearchMax phaseSearchFuel (fun h => geBranchCellOkB lo h c)
          lo hi (lo - 1)
        decide (lo ≤ mx) &&
          decide (mx ≤ hi) &&
            geBranchCellOkB lo mx c &&
              geBranchCoverB fuel c (mx + 1) hi

def ltBranchCoverB : Nat → Nat → Nat → Nat → Bool
  | 0, _c, lo, hi => decide (hi < lo)
  | fuel + 1, c, lo, hi =>
      if hi < lo then
        true
      else
        let mx := phaseSearchMax phaseSearchFuel (fun h => ltBranchCellOkB lo h c)
          lo hi (lo - 1)
        decide (lo ≤ mx) &&
          decide (mx ≤ hi) &&
            ltBranchCellOkB lo mx c &&
              ltBranchCoverB fuel c (mx + 1) hi

theorem geBranchCoverB_sound {fuel c lo hi m : Nat}
    (h : geBranchCoverB fuel c lo hi = true) (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGeBranchCert m c (toInt (lnTail (evmSub 160 c) m)) := by
  revert lo
  induction fuel with
  | zero =>
      intro lo h hlom
      unfold geBranchCoverB at h
      simp only [decide_eq_true_eq] at h
      omega
  | succ fuel ih =>
      intro lo h hlom
      unfold geBranchCoverB at h
      by_cases hdone : hi < lo
      · rw [if_pos hdone] at h
        omega
      · rw [if_neg hdone] at h
        let mx := phaseSearchMax phaseSearchFuel (fun h => geBranchCellOkB lo h c)
          lo hi (lo - 1)
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨hlmx, hmxhi⟩, hcell⟩, hrest⟩ := h
        by_cases hleft : m ≤ mx
        · exact geBranchCellOkB_sound hcell hlom hleft
        · exact ih (lo := mx + 1) hrest (by omega)

theorem ltBranchCoverB_sound {fuel c lo hi m : Nat}
    (h : ltBranchCoverB fuel c lo hi = true) (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftLtBranchCert m c (toInt (lnTail (evmSub 160 c) m)) := by
  revert lo
  induction fuel with
  | zero =>
      intro lo h hlom
      unfold ltBranchCoverB at h
      simp only [decide_eq_true_eq] at h
      omega
  | succ fuel ih =>
      intro lo h hlom
      unfold ltBranchCoverB at h
      by_cases hdone : hi < lo
      · rw [if_pos hdone] at h
        omega
      · rw [if_neg hdone] at h
        let mx := phaseSearchMax phaseSearchFuel (fun h => ltBranchCellOkB lo h c)
          lo hi (lo - 1)
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨hlmx, hmxhi⟩, hcell⟩, hrest⟩ := h
        by_cases hleft : m ≤ mx
        · exact ltBranchCellOkB_sound hcell hlom hleft
        · exact ih (lo := mx + 1) hrest (by omega)

def branchCoverFuel : Nat := 1024

def phaseYMax (n p q w : Nat) : Nat :=
  let s := expSumState p q n
  s.1 * w / s.2.1

def phaseTopMaxHi (n p q w c hi : Nat) : Nat :=
  min hi (((phaseYMax n p q w + 1) / 2 ^ (160 - c)) - 1)

def ltPhaseTopMaxHi (n p q w c lo hi : Nat) : Nat :=
  let mx := phaseTopMaxHi n p q w c hi
  if lo < lnErrorHardMantissa ∧ lnErrorHardMantissa ≤ mx then
    lnErrorHardMantissa - 1
  else
    mx

def gePhaseCoverFastB : Nat → Nat → Nat → Nat → Bool
  | 0, _c, lo, hi => decide (hi < lo)
  | fuel + 1, c, lo, hi =>
      if hi < lo then
        true
      else
        let mx := phaseTopMaxHi 320 (posPhaseNatGe lo c + lnPhaseExtraArg)
          lnErrQ (10 ^ 18) c hi
        decide (lo ≤ mx) &&
          gePhaseCellOkB lo mx c &&
            gePhaseCoverFastB fuel c (mx + 1) hi

def ltPhaseCoverFastB : Nat → Nat → Nat → Nat → Bool
  | 0, _c, lo, hi => decide (hi < lo)
  | fuel + 1, c, lo, hi =>
      if hi < lo then
        true
      else if lo = lnErrorHardMantissa then
        ltPhaseCoverFastB fuel c (lo + 1) hi
      else
        let mx := ltPhaseTopMaxHi 320 (posPhaseNatLt lo c + lnPhaseExtraArg)
          lnErrQ (10 ^ 18) c lo hi
        decide (lo ≤ mx) &&
          ltPhaseCellOkB lo mx c &&
            ltPhaseCoverFastB fuel c (mx + 1) hi

theorem gePhaseCoverFastB_sound {fuel c lo hi m : Nat}
    (h : gePhaseCoverFastB fuel c lo hi = true) (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGePhaseDirectOk 320 m c := by
  revert lo
  induction fuel with
  | zero =>
      intro lo h hlom
      unfold gePhaseCoverFastB at h
      simp only [decide_eq_true_eq] at h
      omega
  | succ fuel ih =>
      intro lo h hlom
      unfold gePhaseCoverFastB at h
      by_cases hdone : hi < lo
      · rw [if_pos hdone] at h
        omega
      · rw [if_neg hdone] at h
        let mx := phaseTopMaxHi 320 (posPhaseNatGe lo c + lnPhaseExtraArg)
          lnErrQ (10 ^ 18) c hi
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hlmx, hcell⟩, hrest⟩ := h
        by_cases hleft : m ≤ mx
        · exact gePhaseCell_sound hcell hlom hleft
        · exact ih (lo := mx + 1) hrest (by omega)

theorem ltPhaseCoverFastB_sound {fuel c lo hi m : Nat}
    (h : ltPhaseCoverFastB fuel c lo hi = true) (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    m = lnErrorHardMantissa ∨ PosShiftLtPhaseDirectOk 320 m c := by
  revert lo
  induction fuel with
  | zero =>
      intro lo h hlom
      unfold ltPhaseCoverFastB at h
      simp only [decide_eq_true_eq] at h
      omega
  | succ fuel ih =>
      intro lo h hlom
      unfold ltPhaseCoverFastB at h
      by_cases hdone : hi < lo
      · rw [if_pos hdone] at h
        omega
      · rw [if_neg hdone] at h
        by_cases hhard : lo = lnErrorHardMantissa
        · rw [if_pos hhard] at h
          by_cases hm : m = lo
          · exact Or.inl (by omega)
          · exact ih (lo := lo + 1) h (by omega)
        · rw [if_neg hhard] at h
          let mx := ltPhaseTopMaxHi 320 (posPhaseNatLt lo c + lnPhaseExtraArg)
            lnErrQ (10 ^ 18) c lo hi
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨hlmx, hcell⟩, hrest⟩ := h
          by_cases hleft : m ≤ mx
          · exact Or.inr (ltPhaseCell_sound hcell hlom hleft)
          · exact ih (lo := mx + 1) hrest (by omega)

theorem model_ln_wad_positive_shift_ge_branch_cert {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hclt : evmClz x < 160) (hge : Sc ≤ mant x)
    (hcert : PosShiftGeBranchCert (mant x) (evmClz x)
      (toInt (model_ln_wad_evm x))) :
    capLB (lnErrArg (toInt (model_ln_wad_evm x))) lnErrQ x (10 ^ 18) := by
  rcases hcert with hres | hrest
  · exact model_ln_wad_positive_shift_ge_residue_or_direct h1 h2 hclt hge
      (Or.inl hres)
  rcases hrest with htop | hrest
  · exact model_ln_wad_positive_shift_ge_top_or_direct h1 h2 hne hclt hge
      (Or.inl htop)
  rcases hrest with hdirect | hrest
  · exact model_ln_wad_positive_shift_ge_top_or_direct h1 h2 hne hclt hge
      (Or.inr hdirect)
  rcases hrest with hphase | hgap
  · exact model_ln_wad_positive_shift_ge_phase_direct h1 h2 hne hclt hge hphase
  · have hx256 : x < 2 ^ 256 := by omega
    have htail :
        model_ln_wad_evm x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
      rw [model_eq_tail hx256]
      rfl
    obtain ⟨me, _hmlo, hmhi⟩ := mant_facts h1 h2
    have hmant_hi : mant x < MHI := by
      unfold mant
      rw [me]
      exact hmhi
    have hX := x1_nonneg_geF hge hmant_hi
    have hr0 := model_ln_wad_nonneg_of_clz_lt_160 h1 h2 hclt
    have hc160 : evmClz x ≤ 160 :=
      Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hclt (by decide : 160 ≤ 161))
    have hrm1 : -1 ≤ toInt (model_ln_wad_evm x) :=
      Int.le_trans (by decide : (-1 : Int) ≤ 0) hr0
    have hsum := ge_phase_gap_direct_to_top
      (m := mant x) (c := evmClz x) (r := toInt (model_ln_wad_evm x))
      hX hc160 hrm1 hgap.1 hgap.2
    have hsumTail :
        sumGE 320
          (lnErrArg (toInt (lnTail (evmSub 160 (evmClz x)) (mant x)))) lnErrQ
          (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
      simpa [htail] using hsum
    exact pos_shift_direct_exact_of_sumGE h1 h2 hclt hsumTail

theorem model_ln_wad_positive_shift_lt_branch_cert {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hclt : evmClz x < 160) (hlt : mant x < Sc) (hband_lo : Sc - 45 ≤ mant x)
    (hcert : PosShiftLtBranchCert (mant x) (evmClz x)
      (toInt (model_ln_wad_evm x))) :
    capLB (lnErrArg (toInt (model_ln_wad_evm x))) lnErrQ x (10 ^ 18) := by
  rcases hcert with hres | hrest
  · exact model_ln_wad_positive_shift_lt_residue_or_direct h1 h2 hne hclt hlt hband_lo
      (Or.inl hres)
  rcases hrest with htop | hrest
  · exact model_ln_wad_positive_shift_lt_top_or_direct h1 h2 hne hclt hlt
      (Or.inl htop)
  rcases hrest with hdirect | hrest
  · exact model_ln_wad_positive_shift_lt_top_or_direct h1 h2 hne hclt hlt
      (Or.inr hdirect)
  rcases hrest with hphase | hgap
  · exact model_ln_wad_positive_shift_lt_phase_direct h1 h2 hne hclt hlt hphase
  · have hx256 : x < 2 ^ 256 := by omega
    have htail :
        model_ln_wad_evm x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
      rw [model_eq_tail hx256]
      rfl
    obtain ⟨hbr1, _hbr2⟩ := model_floor_bracket h1 h2 hne
    rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr1
    obtain ⟨me, hmlo, _hmhi⟩ := mant_facts h1 h2
    have hmant_lo : MLO ≤ mant x := by
      unfold mant
      rw [me]
      exact hmlo
    have hX := x1_nonpos_ltF hmant_lo hlt
    have hr0 := model_ln_wad_nonneg_of_clz_lt_160 h1 h2 hclt
    have hc160 : evmClz x ≤ 160 :=
      Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hclt (by decide : 160 ≤ 161))
    have hV0 : 0 ≤ toInt (x1W (zWord (mant x))) * 7450580596923828125 +
        ln2kInt (evmClz x) + lnBiasI := by
      have hR0 : 0 ≤ toInt (model_ln_wad_evm x) * 2 ^ 72 :=
        Int.mul_nonneg hr0 (by decide)
      have h := Int.le_trans hR0 hbr1
      simpa [lnBiasI] using h
    have hneg := posNegXNat_le_posConstNat hX hc160 hV0
    have hrm1 : -1 ≤ toInt (model_ln_wad_evm x) :=
      Int.le_trans (by decide : (-1 : Int) ≤ 0) hr0
    have hsum := lt_phase_gap_direct_to_top
      (m := mant x) (c := evmClz x) (r := toInt (model_ln_wad_evm x))
      hX hc160 hneg hrm1 hgap.1 hgap.2
    have hsumTail :
        sumGE 320
          (lnErrArg (toInt (lnTail (evmSub 160 (evmClz x)) (mant x)))) lnErrQ
          (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
      simpa [htail] using hsum
    exact pos_shift_direct_exact_of_sumGE h1 h2 hclt hsumTail


end LnFloorCert
