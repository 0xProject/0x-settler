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

/-- Factored LT positive-shift cut (capUB / error-bound direction).  capUB analog
of `ge_pos_cut_factored`: the curved degree-22 upper cap `lt_x1_cap_d22` (`G/V`)
and the sharp bias `capBLtight` are cancelled reciprocally via
`capLB_cancel_first_order_budget`, producing the upper-cut
`capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen`.  The surviving
`hbudget` is the per-`c` closing inequality; the octave power cancels in
`lt_pos_cut_reduced`. -/
theorem lt_pos_cut_factored {m c x : Nat} {r : Int}
    (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) (_hc : c < 160)
    (hneg_le : posNegXNat m ≤ posConstNat c)
    (hphase : posPhaseNatLt m c ≤ lnErrArg r)
    (hbudget :
      wadRayNum x *
          ((((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 42)) * lnErrQ) *
            (expNum 22 (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat *
                (23 * (evalPoly ltTD (m : Int)).toNat) +
              2 * (evalPoly ltTN (m : Int)).toNat ^ 23)) ≤
        (((2 * (10 ^ 40 - 1)) ^ (160 - c) *
              56022770974786139918731938207935451037280277068306373453512740455438595 *
              (lnErrQ + posAvailLt m c r)) *
            (fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23)) * wadRayStrictDen) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have hw1 : (39614081257132168796771975168 : Int) ≤ (m : Int) := by
    simp only [MLO] at h1; omega
  have hw2 : (m : Int) ≤ 56022770974786139918731938181 := by
    simp only [Sc] at h2; omega
  have hTD : 0 < evalPoly ltTD (m : Int) := by
    have h := ltTD_nonneg hw1 hw2; rw [evalCertLtTD] at h; omega
  have hTDnat : 0 < (evalPoly ltTD (m : Int)).toNat := by
    rw [Int.lt_toNat]; simpa using hTD
  have cap1 := capUB_lift_right (den := lnErrorBoundDen) QS_pos (lt_x1_cap_d22 h1 h2)
  have cap2LQ := capLB_lift_right (den := lnErrorBoundDen) QS_pos cap2L
  have cap2 := capLB_pow cap2LQ (160 - c)
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBLtight
  have hsum0 := capLB_mul cap2 capB
  change capUB (posNegXNat m) lnErrQ
    (expNum 22 (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat *
        (23 * (evalPoly ltTD (m : Int)).toNat) +
      2 * (evalPoly ltTN (m : Int)).toNat ^ 23)
    (fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23) at cap1
  change capLB (posConstNat c) lnErrQ
    ((2 * (10 ^ 40 - 1)) ^ (160 - c) *
      56022770974786139918731938207935451037280277068306373453512740455438595)
    ((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 42)) at hsum0
  exact capLB_cancel_first_order_budget
    (arg := lnErrArg r)
    (const := posConstNat c)
    (neg := posNegXNat m)
    (q := lnErrQ)
    (C := (2 * (10 ^ 40 - 1)) ^ (160 - c) *
      56022770974786139918731938207935451037280277068306373453512740455438595)
    (W := (10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 42))
    (G := expNum 22 (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat *
        (23 * (evalPoly ltTD (m : Int)).toNat) + 2 * (evalPoly ltTN (m : Int)).toNat ^ 23)
    (V := fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23)
    (yT := wadRayNum x)
    (wT := wadRayStrictDen)
    (by unfold lnErrQ; decide)
    hsum0 cap1 hneg_le hphase
    (Nat.mul_pos (Nat.pow_pos (show (0 : Nat) < 10 ^ 40 by decide))
      (show (0 : Nat) < 10 ^ 18 * 10 ^ 42 by decide))
    (Nat.lt_of_lt_of_le
      (Nat.mul_pos
        (@expNum_pos (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat hTDnat 22)
        (Nat.mul_pos (show (0 : Nat) < 23 by decide) hTDnat))
      (Nat.le_add_right _ _))
    hbudget

/-- C-independent reduction of `lt_pos_cut_factored`'s `hbudget` (capUB mirror of
`ge_pos_cut_reduced`).  min-phase, window-top and octave-collapse substitutions
fold all `c`/`r`/`x` dependence into the single inequality `hred`, which a
Kronecker cell cover discharges.  The curved cap numerator `G` sits on the
`(m+1)` side and its denominator `V = fact 23 · ltTD^23` on the bias side. -/
theorem lt_pos_cut_reduced {m c x : Nat} {r : Int}
    (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) (hc1 : 1 ≤ c) (hc : c < 160)
    (hmin : posPhaseNatLt m c + minPosAvail ≤ lnErrArg r)
    (hxtop : x ≤ posTopX c m)
    (hred :
      ((m + 1) * 10 ^ 31 * (10 ^ 18 * 10 ^ 42) *
          (expNum 22 (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat *
              (23 * (evalPoly ltTD (m : Int)).toNat) +
            2 * (evalPoly ltTN (m : Int)).toNat ^ 23) * lnErrQ) * (10 ^ 40 + 160) ≤
        (56022770974786139918731938207935451037280277068306373453512740455438595 *
            (fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23) *
            (lnErrQ + minPosAvail) * wadRayStrictDen) * 10 ^ 40) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have hmlt : m < Sc := by simp only [Sc] at h2 ⊢; omega
  have hmhi : m < MHI := by
    have hsc : Sc < MHI := by unfold Sc MHI; decide
    omega
  have hX := x1_nonpos_ltF h1 hmlt
  have hV0 : 0 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c + lnBiasI := by
    simpa [posAccI] using posAccI_nonneg h1 hmhi hc
  have hneg_le := posNegXNat_le_posConstNat hX (by omega : c ≤ 160) hV0
  have hphase : posPhaseNatLt m c ≤ lnErrArg r :=
    Nat.le_trans (Nat.le_add_right _ _) hmin
  have hmineq : minPosAvail ≤ posAvailLt m c r := by unfold posAvailLt; omega
  have hoct := octaveGeBound (k := 160 - c) (by omega)
  -- chain the octave bound with `hred`, then cancel the common `10^40`
  have keyineq :
      ((m + 1) * 10 ^ 31 * (10 ^ 18 * 10 ^ 42) *
          (expNum 22 (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat *
              (23 * (evalPoly ltTD (m : Int)).toNat) +
            2 * (evalPoly ltTN (m : Int)).toNat ^ 23) * lnErrQ) * (10 ^ 40) ^ (160 - c) ≤
        (56022770974786139918731938207935451037280277068306373453512740455438595 *
            (fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23) *
            (lnErrQ + minPosAvail) * wadRayStrictDen) * ((10 ^ 40 - 1) ^ (160 - c)) := by
    refine Nat.le_of_mul_le_mul_right ?_ (show 0 < 10 ^ 40 by decide)
    calc ((m + 1) * 10 ^ 31 * (10 ^ 18 * 10 ^ 42) *
            (expNum 22 (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat *
                (23 * (evalPoly ltTD (m : Int)).toNat) +
              2 * (evalPoly ltTN (m : Int)).toNat ^ 23) * lnErrQ) *
            (10 ^ 40) ^ (160 - c) * 10 ^ 40
        = ((m + 1) * 10 ^ 31 * (10 ^ 18 * 10 ^ 42) *
            (expNum 22 (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat *
                (23 * (evalPoly ltTD (m : Int)).toNat) +
              2 * (evalPoly ltTN (m : Int)).toNat ^ 23) * lnErrQ) *
            (10 ^ 40 * (10 ^ 40) ^ (160 - c)) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ ((m + 1) * 10 ^ 31 * (10 ^ 18 * 10 ^ 42) *
            (expNum 22 (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat *
                (23 * (evalPoly ltTD (m : Int)).toNat) +
              2 * (evalPoly ltTN (m : Int)).toNat ^ 23) * lnErrQ) *
              ((10 ^ 40 + 160) * (10 ^ 40 - 1) ^ (160 - c)) := Nat.mul_le_mul_left _ hoct
      _ = ((m + 1) * 10 ^ 31 * (10 ^ 18 * 10 ^ 42) *
            (expNum 22 (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat *
                (23 * (evalPoly ltTD (m : Int)).toNat) +
              2 * (evalPoly ltTN (m : Int)).toNat ^ 23) * lnErrQ) * (10 ^ 40 + 160) *
            (10 ^ 40 - 1) ^ (160 - c) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ (56022770974786139918731938207935451037280277068306373453512740455438595 *
            (fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23) *
            (lnErrQ + minPosAvail) * wadRayStrictDen) * 10 ^ 40 *
              (10 ^ 40 - 1) ^ (160 - c) := Nat.mul_le_mul_right _ hred
      _ = (56022770974786139918731938207935451037280277068306373453512740455438595 *
            (fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23) *
            (lnErrQ + minPosAvail) * wadRayStrictDen) * ((10 ^ 40 - 1) ^ (160 - c)) *
              10 ^ 40 := by simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  -- assemble `hbudget`
  refine lt_pos_cut_factored h1 h2 hc hneg_le hphase ?_
  -- lower the RHS phase-availability to the constant `minPosAvail`
  refine Nat.le_trans ?_
    (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl _)
      (Nat.add_le_add_left hmineq lnErrQ)) (Nat.le_refl _)) (Nat.le_refl wadRayStrictDen))
  -- bound `wadRayNum x` by the window top
  have hxw : wadRayNum x ≤ (m + 1) * 2 ^ (160 - c) * 10 ^ 31 := by
    unfold wadRayNum
    exact Nat.mul_le_mul_right _
      (Nat.le_trans (by unfold posTopX at hxtop; exact hxtop) (Nat.sub_le _ _))
  refine Nat.le_trans (Nat.mul_le_mul hxw (Nat.le_refl _)) ?_
  -- pure AC + `(2·y)^k = 2^k·y^k`, closed by `keyineq` scaled by `2^(160-c)`
  calc (m + 1) * 2 ^ (160 - c) * 10 ^ 31 *
          ((((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 42)) * lnErrQ) *
            (expNum 22 (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat *
                (23 * (evalPoly ltTD (m : Int)).toNat) +
              2 * (evalPoly ltTN (m : Int)).toNat ^ 23))
      = (((m + 1) * 10 ^ 31 * (10 ^ 18 * 10 ^ 42) *
            (expNum 22 (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat *
                (23 * (evalPoly ltTD (m : Int)).toNat) +
              2 * (evalPoly ltTN (m : Int)).toNat ^ 23) * lnErrQ) *
            (10 ^ 40) ^ (160 - c)) * 2 ^ (160 - c) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ ((56022770974786139918731938207935451037280277068306373453512740455438595 *
            (fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23) *
            (lnErrQ + minPosAvail) * wadRayStrictDen) * ((10 ^ 40 - 1) ^ (160 - c))) *
              2 ^ (160 - c) := Nat.mul_le_mul_right _ keyineq
    _ = (((2 * (10 ^ 40 - 1)) ^ (160 - c) *
            56022770974786139918731938207935451037280277068306373453512740455438595 *
            (lnErrQ + minPosAvail)) *
            (fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23)) * wadRayStrictDen := by
          simp only [Nat.mul_pow, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

end LnFloorCert
