import LnProof.Floor.CertLtLo
import LnProof.Error.Core.Residue
import LnProof.Error.Core.Budget
import LnProof.Error.Core.CutDefs
import LnProof.Cert.BiasCapNum

open FormalYul
open FormalYul.Preservation

/-!
# Factored-octave upper cap

The LT-branch error-bound cut needs an upper cap on `e^(|H|·part)` because
`acc = −K·|H| + …`. The tight degree-22 cap, including the `2·tn^23`
remainder tail, is transported along
`bracket_lt_up` to the true argument `(−x1W)·10^27 / QS`.
-/

namespace LnFloorCert

open LnYul LnFloor Common.Exp Common.Poly

set_option maxRecDepth 100000

theorem capBLtight :
    capLB (BIASc * 2 ^ 27) QS
      biasCapNum
      (10 ^ 18 * 10 ^ 42) :=
  ⟨130, by decide⟩

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
    (hX : int256 (x1W (zWord m)) ≤ 0) :
    ((posNegXNat m : Nat) : Int) =
      (-int256 (x1W (zWord m)) * lnPhaseScaleI) * (lnErrorBoundDen : Int) := by
  have hXn : (((-int256 (x1W (zWord m))).toNat : Nat) : Int) =
      -int256 (x1W (zWord m)) :=
    Int.toNat_of_nonneg (by omega)
  have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
  unfold posNegXNat
  simp only [Int.natCast_mul, hXn, hscale]

theorem posNegXNat_le_posConstNat {m c : Nat}
    (hX : int256 (x1W (zWord m)) ≤ 0) (hc : c ≤ 160)
    (hV0 : 0 ≤ int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI) :
    posNegXNat m ≤ posConstNat c := by
  have hVs := v_scale_pos (int256 (x1W (zWord m))) c hc
  have hV0s : 0 ≤ posPhaseI m c := by
    have hmul := Int.mul_nonneg hV0
      (by unfold twoPow27I; decide : 0 ≤ twoPow27I)
    change 0 ≤ (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI) * twoPow27I at hmul
    have hVs' :
        (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
            lnBiasI) * twoPow27I =
          int256 (x1W (zWord m)) * lnPhaseScaleI +
            ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
              lnBiasI * twoPow27I := by
      simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
    rw [hVs'] at hmul
    simpa [posPhaseI, lnPhaseScaleI, twoPow27I, lnBiasI] using hmul
  apply Int.ofNat_le.mp
  rw [posNegXNat_cast hX, posConstNat_cast c]
  unfold posPhaseI at hV0s
  have hmain :
      -int256 (x1W (zWord m)) * lnPhaseScaleI ≤
        ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
          lnBiasI * twoPow27I := by
    rw [show -int256 (x1W (zWord m)) * lnPhaseScaleI =
        -(int256 (x1W (zWord m)) * lnPhaseScaleI) by rw [Int.neg_mul]]
    generalize int256 (x1W (zWord m)) * lnPhaseScaleI = A at hV0s ⊢
    omega
  exact Int.mul_le_mul_of_nonneg_right hmain (Int.natCast_nonneg _)

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

theorem octaveBound_all :
    (List.range 160).all
      (fun k => decide (10 ^ 40 * (10 ^ 40) ^ k ≤ (10 ^ 40 + 160) * (10 ^ 40 - 1) ^ k))
      = true := by decide +kernel

theorem octaveBound {k : Nat} (hk : k ≤ 159) :
    10 ^ 40 * (10 ^ 40) ^ k ≤ (10 ^ 40 + 160) * (10 ^ 40 - 1) ^ k := by
  have h := List.all_eq_true.mp octaveBound_all k (List.mem_range.mpr (by omega))
  simp only [decide_eq_true_eq] at h
  exact h

/-- Degree-22 curved upper cap for the LT x1/H part, transported along the floor
bracket `(−X1)·ltTD ≤ ltTN·2^99`. -/
theorem lt_x1_cap_d22 {m : Nat} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) :
    capUB ((-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000) QS
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
  have hH : 0 ≤ -int256 (x1W (zWord m)) := by have := x1_nonpos_lt h1 h2; omega
  generalize hTNe : evalPoly ltTN (m : Int) = TN at hbr hTN hHc ⊢
  generalize hTDe : evalPoly ltTD (m : Int) = TD at hbr hTD hHc ⊢
  generalize hHe : -int256 (x1W (zWord m)) = H at hbr hH ⊢
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
        simp only [Nat.mul_assoc, Nat.mul_comm]
    _ ≤ TN.toNat * 2 ^ 99 * 1000000000000000000000000000 := Nat.mul_le_mul_right _ hbrN
    _ = TN.toNat * QS := by
        rw [hQSe]; simp only [Nat.mul_assoc, Nat.mul_comm]

/-- The curved degree-22 upper cap (`G/V`) and sharp bias cap are cancelled via
`capLB_cancel_first_order_budget`, producing the upper-cut
`capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen`.  The `hbudget`
hypothesis is the per-`c` closing inequality; the octave power cancels in
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
              biasCapNum *
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
      biasCapNum)
    ((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 42)) at hsum0
  exact capLB_cancel_first_order_budget
    (arg := lnErrArg r)
    (const := posConstNat c)
    (neg := posNegXNat m)
    (q := lnErrQ)
    (C := (2 * (10 ^ 40 - 1)) ^ (160 - c) *
      biasCapNum)
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

/-- C-independent reduction of `lt_pos_cut_factored`'s closing budget. The
monotone substitutions fold all `c`/`r`/`x`
dependence into a single inequality checked by the Kronecker cell cover.  The
curved cap numerator `G` sits on the `(m+1)` side and its denominator
`V = fact 23 · ltTD^23` on the bias side. -/
theorem lt_pos_cut_reduced {m c x : Nat} {r : Int}
    (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) (hc1 : 1 ≤ c) (hc : c < 160)
    (hmin : posPhaseNatLt m c + minPosAvail ≤ lnErrArg r)
    (hxtop : x ≤ posTopX c m)
    (hReduced :
      ((m + 1) * 10 ^ 31 * (10 ^ 18 * 10 ^ 42) *
          (expNum 22 (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat *
              (23 * (evalPoly ltTD (m : Int)).toNat) +
            2 * (evalPoly ltTN (m : Int)).toNat ^ 23) * lnErrQ) * (10 ^ 40 + 160) ≤
        (biasCapNum *
            (fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23) *
            (lnErrQ + minPosAvail) * wadRayStrictDen) * 10 ^ 40) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have hmlt : m < Sc := by simp only [Sc] at h2 ⊢; omega
  have hmhi : m < MHI := by
    have hsc : Sc < MHI := by unfold Sc MHI; decide
    omega
  have hX := x1_nonpos_ltF h1 hmlt
  have hV0 : 0 ≤ int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c + lnBiasI := by
    simpa [posAccI] using posAccI_nonneg h1 hmhi hc
  have hneg_le := posNegXNat_le_posConstNat hX (by omega : c ≤ 160) hV0
  have hphase : posPhaseNatLt m c ≤ lnErrArg r :=
    Nat.le_trans (Nat.le_add_right _ _) hmin
  have hmineq : minPosAvail ≤ posAvailLt m c r := by unfold posAvailLt; omega
  have hoct := octaveBound (k := 160 - c) (by omega)
  -- Chain the octave bound with the reduced inequality, then cancel the common `10^40`.
  have keyineq :
      ((m + 1) * 10 ^ 31 * (10 ^ 18 * 10 ^ 42) *
          (expNum 22 (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat *
              (23 * (evalPoly ltTD (m : Int)).toNat) +
            2 * (evalPoly ltTN (m : Int)).toNat ^ 23) * lnErrQ) * (10 ^ 40) ^ (160 - c) ≤
        (biasCapNum *
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
      _ ≤ (biasCapNum *
            (fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23) *
            (lnErrQ + minPosAvail) * wadRayStrictDen) * 10 ^ 40 *
              (10 ^ 40 - 1) ^ (160 - c) := Nat.mul_le_mul_right _ hReduced
      _ = (biasCapNum *
            (fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23) *
            (lnErrQ + minPosAvail) * wadRayStrictDen) * ((10 ^ 40 - 1) ^ (160 - c)) *
              10 ^ 40 := by simp only [Nat.mul_comm, Nat.mul_left_comm]
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
    _ ≤ ((biasCapNum *
            (fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23) *
            (lnErrQ + minPosAvail) * wadRayStrictDen) * ((10 ^ 40 - 1) ^ (160 - c))) *
              2 ^ (160 - c) := Nat.mul_le_mul_right _ keyineq
    _ = (((2 * (10 ^ 40 - 1)) ^ (160 - c) *
            biasCapNum *
            (lnErrQ + minPosAvail)) *
            (fact 23 * (evalPoly ltTD (m : Int)).toNat ^ 23)) * wadRayStrictDen := by
          simp only [Nat.mul_pow, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

end LnFloorCert
