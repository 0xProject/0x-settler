import LnProof.ErrCertLt
import LnProof.FloorCertLtLo
import LnProof.LtFactoredCap

/-!
# Bridge from the lt error cell cover to the reduced error inequality

`errLt_nonneg` proves `0 ≤ evalPoly certErrLtLit m` over the lt domain
`[2^95, Sc-46]`.  Here we identify the literal cert with the symbolic margin
`certErrLt = errLtW·23!·ltTD^23 − errLtK·(m+1)·G` (an `evalPoly_ext` identity,
exactly as `ltLo_eval_eq`), and read off the reduced inequality that
`lt_pos_cut_reduced` consumes directly, with no `sumGE`/`expMarginPoly`
(the curved cap numerator `G` sits on the `(m+1)` side, its denominator
`23!·ltTD^23` on the bias side).

The constants are the octave-extracted cell parameters at the active
`lnErrorBoundNum = 1698600000`:
`errLtK = 10^31·(10^18·10^42)·lnErrQ·(10^40+160)` (`lnErrorBoundNum`-independent),
`errLtW = BIASCAPNUM·(lnErrQ+minPosAvail)·wadRayStrictDen·10^40`.
-/

namespace LnFloorCert

open LnYul LnPoly LnExp

set_option maxRecDepth 100000

def errLtK : Int :=
  63382530011411470074835160268800000001014120480182583521197362564300800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

/-- `errLtW = BIASCAPNUM · (lnErrQ + minPosAvail) · wadRayStrictDen · 10^40`,
derived from the tight bias cap and the published `minPosAvail` rather than
tracked as a literal. -/
def errLtW : Nat :=
  biasCapNum *
    (lnErrQ + minPosAvail) * wadRayStrictDen * 10 ^ 40

def certErrLt : List Int :=
  polyAdd (polyScale ((errLtW : Int) * (fact 23 : Int)) (polyPow ltTD 23))
    (polyScale (-errLtK) (polyMul [1, 1]
      (polyAdd (polyScale 23 (polyMul (expPolyNum ltTN ltTD 22) ltTD))
        (polyScale 2 (polyPow ltTN 23)))))

theorem errLt_eval_eq : ∀ x : Int, evalPoly certErrLt x = evalPoly certErrLtLit x := by
  refine evalPoly_ext (B := kB) certErrLt certErrLtLit ?_ ?_ ?_
  · -- ℓ1 bound on the symbolic margin via the homomorphism lemmas on the
    -- degree-12 literal bases; the full degree-277 poly is never reduced.
    show polyL1 certErrLt * 2 < 2 ^ kB
    have h1 := polyL1_polyAdd
      (polyScale ((errLtW : Int) * (fact 23 : Int)) (polyPow ltTDLit 23))
      (polyScale (-errLtK) (polyMul [1, 1] (polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)) (polyScale 2 (polyPow ltTNLit 23)))))
    have h2 := polyL1_polyScale ((errLtW : Int) * (fact 23 : Int)) (polyPow ltTDLit 23)
    have h3 := polyL1_polyPow ltTDLit 23
    have h4 : ((errLtW : Int) * (fact 23 : Int)).natAbs * polyL1 (polyPow ltTDLit 23) ≤
        ((errLtW : Int) * (fact 23 : Int)).natAbs * polyL1 ltTDLit ^ 23 :=
      Nat.mul_le_mul_left _ h3
    have h5 := polyL1_polyScale (-errLtK) (polyMul [1, 1] (polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)) (polyScale 2 (polyPow ltTNLit 23))))
    have h6 := polyL1_polyMul ([1, 1] : List Int) (polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)) (polyScale 2 (polyPow ltTNLit 23)))
    have h7 := polyL1_polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)) (polyScale 2 (polyPow ltTNLit 23))
    have h8 := polyL1_polyScale (23 : Int) (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)
    have h9 := polyL1_polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit
    have h10 := polyL1_expPolyNum ltTNLit ltTDLit 22
    have h11 : polyL1 (expPolyNum ltTNLit ltTDLit 22) * polyL1 ltTDLit ≤
        LnExp.expNum 22 (polyL1 ltTNLit) (polyL1 ltTDLit) * polyL1 ltTDLit :=
      Nat.mul_le_mul_right _ h10
    have h12 : (23 : Int).natAbs * polyL1 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit) ≤
        (23 : Int).natAbs * (LnExp.expNum 22 (polyL1 ltTNLit) (polyL1 ltTDLit) * polyL1 ltTDLit) :=
      Nat.mul_le_mul_left _ (Nat.le_trans h9 h11)
    have h13 := polyL1_polyScale (2 : Int) (polyPow ltTNLit 23)
    have h14 := polyL1_polyPow ltTNLit 23
    have h15 : (2 : Int).natAbs * polyL1 (polyPow ltTNLit 23) ≤
        (2 : Int).natAbs * polyL1 ltTNLit ^ 23 := Nat.mul_le_mul_left _ h14
    have h16 : polyL1 ([1, 1] : List Int) * polyL1 (polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)) (polyScale 2 (polyPow ltTNLit 23))) ≤
        polyL1 ([1, 1] : List Int) * ((23 : Int).natAbs * (LnExp.expNum 22 (polyL1 ltTNLit) (polyL1 ltTDLit) * polyL1 ltTDLit) + (2 : Int).natAbs * polyL1 ltTNLit ^ 23) := by
      refine Nat.mul_le_mul_left _ ?_
      have hx := Nat.le_trans h8 h12
      have hy := Nat.le_trans h13 h15
      omega
    have h17 : (-errLtK).natAbs * polyL1 (polyMul ([1, 1] : List Int) (polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)) (polyScale 2 (polyPow ltTNLit 23)))) ≤
        (-errLtK).natAbs * (polyL1 ([1, 1] : List Int) * ((23 : Int).natAbs * (LnExp.expNum 22 (polyL1 ltTNLit) (polyL1 ltTDLit) * polyL1 ltTDLit) + (2 : Int).natAbs * polyL1 ltTNLit ^ 23)) :=
      Nat.mul_le_mul_left _ (Nat.le_trans h6 h16)
    have hfin : (((errLtW : Int) * (fact 23 : Int)).natAbs * polyL1 ltTDLit ^ 23 +
        (-errLtK).natAbs * (polyL1 ([1, 1] : List Int) * ((23 : Int).natAbs * (LnExp.expNum 22 (polyL1 ltTNLit) (polyL1 ltTDLit) * polyL1 ltTDLit) + (2 : Int).natAbs * polyL1 ltTNLit ^ 23))) * 2 < 2 ^ kB := by
      decide +kernel
    have hA := Nat.le_trans h2 h4
    have hB := Nat.le_trans h5 h17
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 2 (Nat.le_trans h1 (Nat.add_le_add hA hB))) hfin
  · show polyL1 certErrLtLit * 2 < 2 ^ kB
    decide +kernel
  · show evalPoly certErrLt ((2 : Int) ^ kB) = evalPoly certErrLtLit ((2 : Int) ^ kB)
    rw [int_two_pow kB]
    unfold certErrLt
    rw [ltTN_eq_lit, ltTD_eq_lit]
    simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyMul,
      evalPoly_polyPow, evalPoly_expPolyNum]
    decide +kernel

/-- The lt cell cover proves the c-independent error-bound inequality, via the
`evalPoly_ext` identity and the direct `polySub` margin (no `sumGE`). -/
theorem errLt_reduced_ineq {m : Nat} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) :
    ((m + 1) * 10 ^ 31 * (10 ^ 18 * 10 ^ 42) *
        (expNum 22 (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat *
            (23 * (evalPoly ltTD (m : Int)).toNat) +
          2 * (evalPoly ltTN (m : Int)).toNat ^ 23) * lnErrQ) * (10 ^ 40 + 160) ≤
      (biasCapNum *
          (fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23) *
          (lnErrQ + minPosAvail) * wadRayStrictDen) * 10 ^ 40 := by
  have hw1 : (39614081257132168796771975168 : Int) ≤ (m : Int) := by
    simp only [MLO] at h1; omega
  have hw2 : (m : Int) ≤ 56022770974786139918731938181 := by
    simp only [Sc] at h2; omega
  have hTD : 0 < evalPoly ltTD (m : Int) := by
    have h := ltTD_nonneg hw1 hw2; rw [evalCertLtTD] at h; omega
  have hTN : 0 ≤ evalPoly ltTN (m : Int) := ltTN_nonneg hw1 hw2
  have herrK : (0 : Int) ≤ errLtK := by unfold errLtK; decide
  have hcert : 0 ≤ evalPoly certErrLt (m : Int) := by
    rw [errLt_eval_eq]; exact errLt_nonneg hw1 hw2
  -- expand the symbolic margin; cast the bracket evaluations to `Nat`
  unfold certErrLt at hcert
  simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyMul,
    evalPoly_polyPow, evalPoly_expPolyNum, evalPoly, Int.mul_zero, Int.add_zero,
    Int.mul_one] at hcert
  rw [← Int.toNat_of_nonneg hTN, ← Int.toNat_of_nonneg (Int.le_of_lt hTD),
    expNumI_eq_expNum] at hcert
  -- the two sides as casts of `Nat` products
  have hPA : ((errLtW * fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23 : Nat) : Int) =
      (errLtW : Int) * (fact 23 : Int) * ((evalPoly ltTD (m : Int)).toNat : Int) ^ 23 := by
    push_cast; rfl
  have hPB : ((errLtK.toNat * ((1 + m) *
        (23 * (expNum 22 (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat *
            (evalPoly ltTD (m : Int)).toNat) + 2 * (evalPoly ltTN (m : Int)).toNat ^ 23)) : Nat) : Int) =
      errLtK * (((1 : Int) + (m : Int)) *
        (23 * ((expNum 22 (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat : Int) *
            ((evalPoly ltTD (m : Int)).toNat : Int)) +
          2 * ((evalPoly ltTN (m : Int)).toNat : Int) ^ 23)) := by
    rw [show errLtK = ((errLtK.toNat : Nat) : Int) from (Int.toNat_of_nonneg herrK).symm]
    push_cast; rfl
  -- reduce to the `Nat` inequality `B ≤ A`
  have key : errLtK.toNat * ((1 + m) * (23 * (expNum 22 (evalPoly ltTN (m : Int)).toNat
        (evalPoly ltTD (m : Int)).toNat * (evalPoly ltTD (m : Int)).toNat) +
          2 * (evalPoly ltTN (m : Int)).toNat ^ 23))
      ≤ errLtW * fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23 := by
    refine Int.ofNat_le.mp ?_
    rw [Int.neg_mul, ← hPB, ← hPA] at hcert
    omega
  -- Close the reduced inequality by expanding the two scalar constants and AC.
  have eKn : errLtK.toNat = 10 ^ 31 * (10 ^ 18 * 10 ^ 42) * lnErrQ * (10 ^ 40 + 160) := by
    decide
  have eWn : errLtW = biasCapNum *
      (lnErrQ + minPosAvail) * wadRayStrictDen * 10 ^ 40 := by decide
  rw [show m + 1 = 1 + m from Nat.add_comm m 1]
  calc (1 + m) * 10 ^ 31 * (10 ^ 18 * 10 ^ 42) *
          (expNum 22 (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat *
              (23 * (evalPoly ltTD (m : Int)).toNat) +
            2 * (evalPoly ltTN (m : Int)).toNat ^ 23) * lnErrQ * (10 ^ 40 + 160)
      = errLtK.toNat * ((1 + m) * (23 * (expNum 22 (evalPoly ltTN (m : Int)).toNat
          (evalPoly ltTD (m : Int)).toNat * (evalPoly ltTD (m : Int)).toNat) +
            2 * (evalPoly ltTN (m : Int)).toNat ^ 23)) := by
        rw [eKn]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ errLtW * fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23 := key
    _ = biasCapNum *
          (fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23) * (lnErrQ + minPosAvail) *
          wadRayStrictDen * 10 ^ 40 := by
        rw [eWn]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

end LnFloorCert
