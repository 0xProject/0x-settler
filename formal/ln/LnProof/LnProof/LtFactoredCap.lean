import LnProof.FactoredCap

/-!
# Factored-octave cap primitive for the LT branch (capUB / error-bound direction)

The LT-branch error-bound cut needs an *upper* cap on `e^(|H|·part)` (because
`acc = −K·|H| + …`, so lower-bounding `acc` upper-bounds `|H|`).  This is the
`capUB` mirror of `ge_x1_cap_d22`: the tight degree-22 upper cap (with the
`2·tn^23` remainder tail) from `capUB22_of_int`, transported along
`bracket_lt_up` to the true argument `(−x1W)·10^27 / QS`.
-/

namespace LnFloorCert

open LnGeneratedModel LnFloor LnExp LnPoly

set_option maxRecDepth 100000

/-- Degree-22 curved upper cap for the LT x1/H part, transported along the floor
bracket `(−X1)·ltTD ≤ ltTN·2^99`.  capUB analog of `ge_x1_cap_d22`. -/
theorem lt_x1_cap_d22 {m : Nat} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) :
    capUB ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000) QS
      (expNum 22 (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat *
          (23 * (evalPoly ltTD (m : Int)).toNat) +
        2 * (evalPoly ltTN (m : Int)).toNat ^ 23)
      (fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23) := by
  have hw1 : (39614081257132168796771975168 : Int) ≤ (m : Int) := by
    simp only [MLO] at h1; omega
  have hw2 : (m : Int) ≤ 56022770974786139918731938181 := by
    simp only [Sc] at h2; omega
  have hTD : 0 < evalPoly ltTD (m : Int) := by
    have h := ltTD_nonneg hw1 hw2; rw [evalCertLtTD] at h; omega
  have hTN : 0 ≤ evalPoly ltTN (m : Int) := ltTN_nonneg hw1 hw2
  have hHc : 2 * evalPoly ltTN (m : Int) ≤ 24 * evalPoly ltTD (m : Int) := by
    have h := ltH_nonneg hw1 hw2; rw [evalCertLtH] at h; omega
  have hbr := bracket_lt_up h1 h2
  have hH : 0 ≤ -toInt (x1W (zWord m)) := by have := x1_nonpos_lt h1 h2; omega
  generalize hTNe : evalPoly ltTN (m : Int) = TN at hbr hTN hHc ⊢
  generalize hTDe : evalPoly ltTD (m : Int) = TD at hbr hTD hHc ⊢
  generalize hHe : -toInt (x1W (zWord m)) = H at hbr hH ⊢
  have hTDnat : 0 < TD.toNat := by rw [Int.lt_toNat]; simpa using hTD
  have etn : ((TN.toNat : Nat) : Int) = TN := Int.toNat_of_nonneg hTN
  have etd : ((TD.toNat : Nat) : Int) = TD := Int.toNat_of_nonneg (Int.le_of_lt hTD)
  -- self upper cap at the bracket (ltTN/ltTD)
  have hself : capUB TN.toNat TD.toNat
      (expNum 22 TN.toNat TD.toNat * (23 * TD.toNat) + 2 * TN.toNat ^ 23)
      (fact 23 * TD.toNat ^ 23) := by
    refine capUB22_of_int hTDnat ?_ ?_
    · -- convergence guard: 2·TN.toNat ≤ 24·TD.toNat
      refine Int.ofNat_le.mp ?_
      simp only [Int.natCast_mul, etn, etd]
      omega
    · -- self inequality: LHS = RHS (equality), via expNumI = expNum and fact 23
      rw [expNumI_eq_expNum, show (25852016738884976640000 : Int) = ((fact 23 : Nat) : Int) from by decide]
      simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_pow]
      generalize (((expNum 22 TN.toNat TD.toNat : Nat)) : Int) = E
      generalize ((TD.toNat : Nat) : Int) = D
      generalize ((TN.toNat : Nat) : Int) = T
      generalize ((fact 23 : Nat) : Int) = F
      exact Int.le_refl _
  -- transport down to the true argument (−x1W)·10^27 / QS
  refine capUB_arg (q' := TD.toNat) hTDnat ?_ hself
  -- Nat bracket  H.toNat·TD.toNat ≤ TN.toNat·2^99  from the Int bracket hbr
  have hbrN : H.toNat * TD.toNat ≤ TN.toNat * 2 ^ 99 := by
    refine Int.ofNat_le.mp ?_
    simp only [Int.natCast_mul, Int.natCast_pow, Int.toNat_of_nonneg hH,
      Int.toNat_of_nonneg hTN, Int.toNat_of_nonneg (Int.le_of_lt hTD)]
    simpa using hbr
  have hQSe : QS = 1000000000000000000000000000 * 2 ^ 99 := by decide
  -- goal (Nat): (H.toNat·10²⁷)·TD.toNat ≤ TN.toNat·QS
  calc H.toNat * 1000000000000000000000000000 * TD.toNat
      = H.toNat * TD.toNat * 1000000000000000000000000000 := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ TN.toNat * 2 ^ 99 * 1000000000000000000000000000 := Nat.mul_le_mul_right _ hbrN
    _ = TN.toNat * QS := by
        rw [hQSe]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

end LnFloorCert
