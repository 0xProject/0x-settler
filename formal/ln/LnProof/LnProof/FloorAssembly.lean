import LnProof.FloorCaps
import LnProof.FloorBudget
import LnProof.FloorModel

/-!
# Floor-spec assembly: scale identities

`model_floor_bracket` brackets the model output `r` against the pre-shift
accumulator `V = X1·5^27 + ln2k + BIAS` at scale `2^72`. The caps live at
scale `QS = 10^27·2^99`, reached by multiplying `V` by `2^27`. This file
provides the exact decomposition of `V·2^27` into the three cap exponents
on each `clz` side.
-/

namespace LnFloorCert
open LnGeneratedModel LnPoly LnExp LnFloor

/-- `V·2^27` splits into the three cap exponents (positive binade shift). -/
theorem v_scale_pos (X1v : Int) (c : Nat) (hc : c ≤ 152) :
    (X1v * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 =
      X1v * 1000000000000000000000000000 +
        ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) +
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
  have hl : ln2kInt c = (LN2c : Int) * ((152 - c : Nat) : Int) := by
    unfold ln2kInt
    rw [if_pos hc]
  rw [hl, Int.add_mul, Int.add_mul, Int.mul_assoc,
    show (7450580596923828125 : Int) * 2 ^ 27 =
      1000000000000000000000000000 from by decide]
  have e : (LN2c : Int) * ((152 - c : Nat) : Int) * 2 ^ 27 =
      ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [e]

/-- `V·2^27` splits with the `ln 2` term on the other side (negative shift). -/
theorem v_scale_neg (X1v : Int) (c : Nat) (hc : 152 < c) :
    (X1v * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 +
        ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) =
      X1v * 1000000000000000000000000000 +
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
  have hl : ln2kInt c = -((LN2c : Int) * ((c - 152 : Nat) : Int)) := by
    unfold ln2kInt
    rw [if_neg (by omega)]
  rw [hl, Int.add_mul, Int.add_mul, Int.mul_assoc,
    show (7450580596923828125 : Int) * 2 ^ 27 =
      1000000000000000000000000000 from by decide]
  have e : -((LN2c : Int) * ((c - 152 : Nat) : Int)) * 2 ^ 27 +
      ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = 0 := by
    have e1 : (LN2c : Int) * ((c - 152 : Nat) : Int) * 2 ^ 27 =
        ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [Int.neg_mul, e1]
    omega
  generalize hgA : X1v * 1000000000000000000000000000 = A at *
  generalize hgL : -((LN2c : Int) * ((c - 152 : Nat) : Int)) * 2 ^ 27 = L1 at *
  generalize hgL2 : ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = L2 at *
  omega

/-! ## Master chains: caps at the model output -/

/-- Upper master chain, `m ≥ S` branch, nonnegative binade shift:
`e^(r/10^27) ≤ x/10^18` as a `capUB`, assembled from the `X1` cap, the
`2^k` cap, the bias cap, and the budget. -/
theorem up_ge_pos {m c x : Nat} {r : Int} (h1 : Sc + 46 ≤ m) (h2 : m < MHI)
    (hc1 : 1 ≤ c) (hc : c ≤ 152)
    (hup : 0 ≤ evalPoly certGeUp (m : Int))
    (hr : r * 2 ^ 72 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269)
    (hr0 : 0 ≤ r)
    (hmx : m * 2 ^ (152 - c) ≤ x) :
    capUB (r.toNat * 2 ^ 99) QS x (10 ^ 18) := by
  have cap1 := x1capGeUp h1 h2 hup
  rw [show (633825300114114700748351602688000000000000000000000000000 : Nat) = QS
    from by decide] at cap1
  have cap2 := capUB_pow QS_pos cap2U (152 - c)
  have cap12 := capUB_mul QS_pos cap1 cap2
  have cap123 := capUB_mul QS_pos cap12 capBU
  -- the exponent sum dominates r·2^99
  have hX1 := x1_nonneg_ge h1 h2
  have hVs := v_scale_pos (toInt (x1W (zWord m))) c hc
  have hple : r.toNat * 2 ^ 99 ≤
      (toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        (152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 := by
    have hsc : r * 2 ^ 72 * 2 ^ 27 ≤ (toInt (x1W (zWord m)) * 7450580596923828125 +
        ln2kInt c + 143060321855302967919159136223863753677754092301269) * 2 ^ 27 :=
      mul_le_mul_right_nonneg hr (by omega)
    rw [hVs] at hsc
    have hX1n : ((toInt (x1W (zWord m))).toNat : Int) = toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((152 - c) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    have e99 : r * 2 ^ 72 * 2 ^ 27 = r * 2 ^ 99 := by
      rw [Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from by decide]
    rw [e99] at hsc
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hsc
    generalize hgB : ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hsc hLc
    generalize hgC : (152 - c) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hVs hX1 cap1 cap2 cap12 cap123 hup hr h1 h2 hmx hc hc1
    omega
  have hmul : r.toNat * 2 ^ 99 * QS ≤
      ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        (152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27) * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capUB_arg QS_pos hmul cap123
  -- weaken to the x target through the budget
  refine capUB_weaken ?_ capR ?_
  · -- 0 < w
    have h1' : 0 < (1434182936954525181919537618622900000000000000000000000000000 : Nat) *
        ((10 ^ 40 : Nat) ^ (152 - c)) := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
    exact Nat.mul_pos h1' (by decide)
  · -- y·w' ≤ y'·w
    have hb := budgetU_le (k := 152 - c) (by omega)
    have hbm : m * (Sc * ((10 ^ 29 + 42) * (2 * (10 ^ 40 + 1)) ^ (152 - c) *
        (10 ^ 30 - 499) * 10 ^ 18)) ≤
        m * (Sc * (2 ^ (152 - c) * (10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb)
    have hxm : m * 2 ^ (152 - c) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) ≤
        x * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) :=
      Nat.mul_le_mul_right _ hmx
    have e1 : m * (10 ^ 29 + 42) * (2 * (10 ^ 40 + 1)) ^ (152 - c) *
        (Sc * (10 ^ 30 - 499)) * 10 ^ 18 =
        m * (Sc * ((10 ^ 29 + 42) * (2 * (10 ^ 40 + 1)) ^ (152 - c) *
          (10 ^ 30 - 499) * 10 ^ 18)) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have e2 : m * (Sc * (2 ^ (152 - c) * (10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) =
        m * 2 ^ (152 - c) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have e3 : x * (1434182936954525181919537618622900000000000000000000000000000 *
        (10 ^ 40 : Nat) ^ (152 - c) * (10 ^ 18 * 10 ^ 30)) =
        x * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) := by
      rw [show (1434182936954525181919537618622900000000000000000000000000000 : Nat) =
        Sc * 10 ^ 29 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have e3' : ∀ P : Nat, (10 : Nat) ^ 18 * ((10 : Nat) ^ 29 * ((10 : Nat) ^ 30 * P)) =
          (10 : Nat) ^ 77 * P := by
        intro P
        rw [← Nat.mul_assoc, ← Nat.mul_assoc,
          show ((10 : Nat) ^ 18 * 10 ^ 29 * 10 ^ 30) = 10 ^ 77 from by decide]
      rw [e3' ((10 ^ 40 : Nat) ^ (152 - c))]
    generalize hgY : m * (10 ^ 29 + 42) * (2 * (10 ^ 40 + 1)) ^ (152 - c) *
      (Sc * (10 ^ 30 - 499)) * 10 ^ 18 = Y at e1 ⊢
    generalize hg1 : m * (Sc * ((10 ^ 29 + 42) * (2 * (10 ^ 40 + 1)) ^ (152 - c) *
      (10 ^ 30 - 499) * 10 ^ 18)) = T1 at hbm e1
    generalize hg2 : m * (Sc * (2 ^ (152 - c) * (10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) =
      T2 at hbm e2
    generalize hg3 : m * 2 ^ (152 - c) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) =
      T3 at hxm e2
    generalize hg4 : x * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) = T4 at hxm e3
    generalize hg5 : x * (1434182936954525181919537618622900000000000000000000000000000 *
      (10 ^ 40 : Nat) ^ (152 - c) * (10 ^ 18 * 10 ^ 30)) = W4 at e3 ⊢
    omega

/-- The lower budget folds from the worst-case mantissa to any `m ≥ 2^103`:
`(m+1)·2^k·(10^40)^k·10^137 ≤ m·(lower-cap product)`. -/
theorem budgetL_fold {m k : Nat} (hm : 2 ^ 103 ≤ m) (hk : k ≤ 151) :
    (m + 1) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 137) ≤
      m * ((10 ^ 29 - 42) * (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 30 - 501) *
        (10 ^ 30 + 999) * (10 ^ 30 - 1) * 10 ^ 18) := by
  have hb := budgetL_le (k := k) hk
  -- (m+1)·2^103 ≤ m·(2^103+1) since 2^103 ≤ m
  have hcross : (m + 1) * 2 ^ 103 ≤ m * (2 ^ 103 + 1) := by
    have e1 : (m + 1) * 2 ^ 103 = m * 2 ^ 103 + 2 ^ 103 := by
      rw [Nat.add_mul, Nat.one_mul]
    have e2 : m * (2 ^ 103 + 1) = m * 2 ^ 103 + m := by
      rw [Nat.mul_add, Nat.mul_one]
    omega
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 2 ^ 103 by decide)
  calc 2 ^ 103 * ((m + 1) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 137))
      = ((m + 1) * 2 ^ 103) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 137) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (m * (2 ^ 103 + 1)) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 137) :=
        Nat.mul_le_mul_right _ hcross
    _ = m * ((2 ^ 103 + 1) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 137)) := by
        simp only [Nat.mul_assoc]
    _ = m * ((2 ^ 103 + 1) * 2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 137) := by
        simp only [Nat.mul_assoc]
    _ ≤ m * (2 ^ 103 * (10 ^ 29 - 42) * (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 30 - 501) *
          (10 ^ 30 + 999) * (10 ^ 30 - 1) * 10 ^ 18) :=
        Nat.mul_le_mul_left _ hb
    _ = 2 ^ 103 * (m * ((10 ^ 29 - 42) * (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 30 - 501) *
          (10 ^ 30 + 999) * (10 ^ 30 - 1) * 10 ^ 18)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Lower master chain, `m ≥ S` branch, nonnegative binade shift:
`x/10^18 < e^((r+2)/10^27)` as a `capLB` with one part in `10^30` of
strictness slack. -/
theorem lo_ge_pos {m c x : Nat} {r : Int} (h1 : Sc + 46 ≤ m) (h2 : m < MHI)
    (hc1 : 1 ≤ c) (hc : c ≤ 152)
    (hlo : 0 ≤ evalPoly certGeLo (m : Int))
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269 < (r + 1) * 2 ^ 72)
    (hr0 : 0 ≤ r)
    (hxm : x < (m + 1) * 2 ^ (152 - c)) :
    capLB ((r + 2).toNat * 2 ^ 99) QS (x * 10 ^ 30) (10 ^ 18 * (10 ^ 30 - 1)) := by
  have cap1 := x1capGeLo h1 h2 hlo
  rw [show (633825300114114700748351602688000000000000000000000000000 : Nat) = QS
    from by decide] at cap1
  have cap2 := capLB_pow cap2L (152 - c)
  have cap12 := capLB_mul cap1 cap2
  have cap123 := capLB_mul cap12 capBL
  have cap1234 := capLB_mul cap123 capEL
  -- (r+2)·2^99 dominates the exponent sum
  have hX1 := x1_nonneg_ge h1 h2
  have hVs := v_scale_pos (toInt (x1W (zWord m))) c hc
  have hple : (toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
      (152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99 ≤
      (r + 2).toNat * 2 ^ 99 := by
    have hsc : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 ≤
        ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 :=
      mul_le_mul_right_nonneg (by omega) (by omega)
    rw [hVs] at hsc
    have hX1n : ((toInt (x1W (zWord m))).toNat : Int) = toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((152 - c) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    have er : ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 = (r + 1) * 2 ^ 99 - 2 ^ 27 := by
      rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
        by decide]
      omega
    rw [er] at hsc
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hsc
    generalize hgB : ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hsc hLc
    generalize hgC : (152 - c) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hVs hX1 cap1 cap2 cap12 cap123 cap1234 hlo hr h1 h2 hxm hc hc1
    omega
  have hmul : ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
      (152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99) * QS ≤
      (r + 2).toNat * 2 ^ 99 * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capLB_arg QS_pos hmul cap1234
  -- weaken to the strict x target
  refine capLB_weaken ?_ capR ?_
  · have h1' : 0 < (1434182936954525181919537618622900000000000000000000000000000 : Nat) *
        ((10 ^ 40 : Nat) ^ (152 - c)) := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
    have h2' : 0 < (1434182936954525181919537618622900000000000000000000000000000 : Nat) *
        ((10 ^ 40 : Nat) ^ (152 - c)) * (10 ^ 18 * 10 ^ 30) :=
      Nat.mul_pos h1' (by decide)
    exact Nat.mul_pos h2' (by decide)
  · -- x·10^30·W ≤ Y·(10^18·(10^30−1))
    have hMLO : 2 ^ 103 ≤ m := by
      simp only [Sc] at h1
      omega
    have hb := budgetL_fold (k := 152 - c) hMLO (by omega)
    have hx1 : x + 1 ≤ (m + 1) * 2 ^ (152 - c) := by omega
    have hxw : (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 137)) ≤
        (m + 1) * 2 ^ (152 - c) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 137)) :=
      Nat.mul_le_mul_right _ hx1
    have hfold : (m + 1) * 2 ^ (152 - c) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) *
        10 ^ 137)) ≤
        m * ((10 ^ 29 - 42) * (2 * (10 ^ 40 - 1)) ^ (152 - c) * (10 ^ 30 - 501) *
          (10 ^ 30 + 999) * (10 ^ 30 - 1) * 10 ^ 18) * Sc := by
      have h := Nat.mul_le_mul_left Sc hb
      have e1 : Sc * ((m + 1) * (2 ^ (152 - c) * (10 ^ 40 : Nat) ^ (152 - c) *
          10 ^ 137)) =
          (m + 1) * 2 ^ (152 - c) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 137)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have e2 : Sc * (m * ((10 ^ 29 - 42) * (2 * (10 ^ 40 - 1)) ^ (152 - c) *
          (10 ^ 30 - 501) * (10 ^ 30 + 999) * (10 ^ 30 - 1) * 10 ^ 18)) =
          m * ((10 ^ 29 - 42) * (2 * (10 ^ 40 - 1)) ^ (152 - c) * (10 ^ 30 - 501) *
            (10 ^ 30 + 999) * (10 ^ 30 - 1) * 10 ^ 18) * Sc := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e1] at h
      rw [e2] at h
      exact h
    -- assemble: LHS = (x+1-free form) and the W/Y bookkeeping
    have eL : x * 10 ^ 30 * (1434182936954525181919537618622900000000000000000000000000000 *
        (10 ^ 40 : Nat) ^ (152 - c) * (10 ^ 18 * 10 ^ 30) * 10 ^ 30) ≤
        (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 137)) := by
      rw [show (1434182936954525181919537618622900000000000000000000000000000 : Nat) =
        Sc * 10 ^ 29 from by decide]
      have eAC : x * 10 ^ 30 * (Sc * 10 ^ 29 * (10 ^ 40 : Nat) ^ (152 - c) *
          (10 ^ 18 * 10 ^ 30) * 10 ^ 30) =
          x * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * ((10 : Nat) ^ 30 * (10 ^ 29 *
            (10 ^ 18 * 10 ^ 30 * 10 ^ 30))))) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [eAC, show ((10 : Nat) ^ 30 * (10 ^ 29 * (10 ^ 18 * 10 ^ 30 * 10 ^ 30))) =
        10 ^ 137 from by decide]
      have : x * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 137)) ≤
          (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 137)) :=
        Nat.mul_le_mul_right _ (by omega)
      exact this
    have eR : m * ((10 ^ 29 - 42) * (2 * (10 ^ 40 - 1)) ^ (152 - c) * (10 ^ 30 - 501) *
        (10 ^ 30 + 999) * (10 ^ 30 - 1) * 10 ^ 18) * Sc =
        m * 99999999999999999999999999958 * (2 * (10 ^ 40 - 1)) ^ (152 - c) *
          (Sc * (10 ^ 30 - 501)) * (10 ^ 30 + 999) * (10 ^ 18 * (10 ^ 30 - 1)) := by
      rw [show (99999999999999999999999999958 : Nat) = 10 ^ 29 - 42 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    generalize hT1 : x * 10 ^ 30 *
      (1434182936954525181919537618622900000000000000000000000000000 *
        (10 ^ 40 : Nat) ^ (152 - c) * (10 ^ 18 * 10 ^ 30) * 10 ^ 30) = T1 at eL ⊢
    generalize hT2 : (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 137)) = T2
      at eL hxw
    generalize hT3 : (m + 1) * 2 ^ (152 - c) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) *
      10 ^ 137)) = T3 at hxw hfold
    generalize hT4 : m * ((10 ^ 29 - 42) * (2 * (10 ^ 40 - 1)) ^ (152 - c) *
      (10 ^ 30 - 501) * (10 ^ 30 + 999) * (10 ^ 30 - 1) * 10 ^ 18) * Sc = T4
      at hfold eR
    generalize hT5 : m * 99999999999999999999999999958 *
      (2 * (10 ^ 40 - 1)) ^ (152 - c) * (Sc * (10 ^ 30 - 501)) * (10 ^ 30 + 999) *
      (10 ^ 18 * (10 ^ 30 - 1)) = T5 at eR ⊢
    omega

/-- Upper master chain, `m ≥ S` branch, negative binade shift
(`c > 152`, exact mantissa `m = x·2^(c-152)`). -/
theorem up_ge_neg {m c x : Nat} {r : Int} (h1 : Sc + 46 ≤ m) (h2 : m < MHI)
    (hc : 152 < c) (hc2 : c ≤ 255)
    (hup : 0 ≤ evalPoly certGeUp (m : Int))
    (hr : r * 2 ^ 72 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269)
    (hr0 : 0 ≤ r)
    (hmx : m = x * 2 ^ (c - 152)) :
    capUB (r.toNat * 2 ^ 99) QS x (10 ^ 18) := by
  have cap1 := x1capGeUp h1 h2 hup
  rw [show (633825300114114700748351602688000000000000000000000000000 : Nat) = QS
    from by decide] at cap1
  have cap1B := capUB_mul QS_pos cap1 capBU
  have hX1 := x1_nonneg_ge h1 h2
  have hVs := v_scale_neg (toInt (x1W (zWord m))) c hc
  -- the Nat split: X1·E + BIAS = pa + j·L with pa ≥ r·2^99
  have hsplit : (toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
      BIASc * 2 ^ 27 =
      ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        BIASc * 2 ^ 27 - (c - 152) * (LN2c * 2 ^ 27)) +
        (c - 152) * (LN2c * 2 ^ 27) := by
    -- j·L ≤ X1·E + BIAS since V ≥ r ≥ 0
    have hX1n : ((toInt (x1W (zWord m))).toNat : Int) = toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 152) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    have hV0 : 0 ≤ (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 := by
      have hm := mul_le_mul_right_nonneg hr (show (0 : Int) ≤ 2 ^ 27 by omega)
      have h0 : 0 ≤ r * 2 ^ 72 * 2 ^ 27 :=
        Int.mul_nonneg (Int.mul_nonneg hr0 (by omega)) (by omega)
      generalize hgV' : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hm ⊢
      generalize hgR : r * 2 ^ 72 * 2 ^ 27 = R27 at hm h0
      clear cap1 cap1B hup hX1 hVs hX1n hBc hLc h1 h2 hmx hc hc2 hr hr0
      omega
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hV0 hVs
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 152) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 cap1B hup hr h1 h2 hc hc2 hmx
    omega
  rw [hsplit] at cap1B
  have capV := capUB_cancel QS_pos cap1B (capLB_pow cap2L (c - 152))
  -- bring the exponent down to r·2^99
  have hple : r.toNat * 2 ^ 99 ≤
      (toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        BIASc * 2 ^ 27 - (c - 152) * (LN2c * 2 ^ 27) := by
    have hsc : r * 2 ^ 72 * 2 ^ 27 + ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) ≤
        toInt (x1W (zWord m)) * 1000000000000000000000000000 +
          143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      have h := mul_le_mul_right_nonneg hr (show (0 : Int) ≤ 2 ^ 27 by omega)
      generalize hgL : ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = L at hVs ⊢
      generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs ⊢
      generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hVs h
      omega
    have hX1n : ((toInt (x1W (zWord m))).toNat : Int) = toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 152) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    have e99 : r * 2 ^ 72 * 2 ^ 27 = r * 2 ^ 99 := by
      rw [Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from by decide]
    rw [e99] at hsc
    generalize hgB : ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hsc hLc
    generalize hgC : (c - 152) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hsc
    generalize hgD : (toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hVs hX1 cap1 cap1B capV hup hr h1 h2 hc hc2 hmx hsplit
    omega
  have hmul : r.toNat * 2 ^ 99 * QS ≤
      ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        BIASc * 2 ^ 27 - (c - 152) * (LN2c * 2 ^ 27)) * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capUB_arg QS_pos hmul capV
  refine capUB_weaken ?_ capR ?_
  · have h1' : 0 < (1434182936954525181919537618622900000000000000000000000000000 : Nat) *
        (10 ^ 18 * 10 ^ 30) := by decide
    exact Nat.mul_pos h1' (Nat.pow_pos (by decide))
  · -- m = x·2^j folding through budgetUn
    have hb := budgetUn_le (j := c - 152) (by omega)
    have hbf : x * 2 ^ (c - 152) * ((10 ^ 29 + 42) * (10 ^ 30 - 499) *
        (10 ^ 40 : Nat) ^ (c - 152) * 10 ^ 18 * Sc) ≤
        x * (10 ^ 77 * (2 * (10 ^ 40 - 1)) ^ (c - 152) * Sc) := by
      have h := Nat.mul_le_mul_left (x * Sc) hb
      have e1 : x * Sc * ((10 ^ 29 + 42) * (10 ^ 30 - 499) *
          (10 ^ 40 : Nat) ^ (c - 152) * 2 ^ (c - 152) * 10 ^ 18) =
          x * 2 ^ (c - 152) * ((10 ^ 29 + 42) * (10 ^ 30 - 499) *
            (10 ^ 40 : Nat) ^ (c - 152) * 10 ^ 18 * Sc) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have e2 : x * Sc * (10 ^ 77 * (2 * (10 ^ 40 - 1)) ^ (c - 152)) =
          x * (10 ^ 77 * (2 * (10 ^ 40 - 1)) ^ (c - 152) * Sc) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e1] at h
      rw [e2] at h
      exact h
    have eY : m * 100000000000000000000000000042 * (Sc * (10 ^ 30 - 499)) *
        ((10 ^ 40 : Nat) ^ (c - 152)) * 10 ^ 18 =
        x * 2 ^ (c - 152) * ((10 ^ 29 + 42) * (10 ^ 30 - 499) *
          (10 ^ 40 : Nat) ^ (c - 152) * 10 ^ 18 * Sc) := by
      rw [hmx, show (100000000000000000000000000042 : Nat) = 10 ^ 29 + 42 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have eW : x * (1434182936954525181919537618622900000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 30) * (2 * (10 ^ 40 - 1)) ^ (c - 152)) =
        x * (10 ^ 77 * (2 * (10 ^ 40 - 1)) ^ (c - 152) * Sc) := by
      rw [show (1434182936954525181919537618622900000000000000000000000000000 : Nat) =
        Sc * 10 ^ 29 from by decide]
      have e' : ∀ P : Nat, (10 : Nat) ^ 18 * ((10 : Nat) ^ 29 * ((10 : Nat) ^ 30 * P)) =
          (10 : Nat) ^ 77 * P := by
        intro P
        rw [← Nat.mul_assoc, ← Nat.mul_assoc,
          show ((10 : Nat) ^ 18 * 10 ^ 29 * 10 ^ 30) = 10 ^ 77 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e' ((2 * (10 ^ 40 - 1)) ^ (c - 152))]
    generalize hT1 : m * 100000000000000000000000000042 * (Sc * (10 ^ 30 - 499)) *
      ((10 ^ 40 : Nat) ^ (c - 152)) * 10 ^ 18 = T1 at eY ⊢
    generalize hT2 : x * 2 ^ (c - 152) * ((10 ^ 29 + 42) * (10 ^ 30 - 499) *
      (10 ^ 40 : Nat) ^ (c - 152) * 10 ^ 18 * Sc) = T2 at eY hbf
    generalize hT3 : x * (10 ^ 77 * (2 * (10 ^ 40 - 1)) ^ (c - 152) * Sc) = T3 at hbf eW
    generalize hT4 : x * (1434182936954525181919537618622900000000000000000000000000000 *
      (10 ^ 18 * 10 ^ 30) * (2 * (10 ^ 40 - 1)) ^ (c - 152)) = T4 at eW ⊢
    omega

/-- Lower master chain, `m ≥ S` branch, negative binade shift. -/
theorem lo_ge_neg {m c x : Nat} {r : Int} (h1 : Sc + 46 ≤ m) (h2 : m < MHI)
    (hc : 152 < c) (hc2 : c ≤ 255)
    (hlo : 0 ≤ evalPoly certGeLo (m : Int))
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269 < (r + 1) * 2 ^ 72)
    (hrlo : r * 2 ^ 72 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269)
    (hr0 : 0 ≤ r)
    (hmx : m = x * 2 ^ (c - 152)) :
    capLB ((r + 2).toNat * 2 ^ 99) QS (x * 10 ^ 30) (10 ^ 18 * (10 ^ 30 - 1)) := by
  have cap1 := x1capGeLo h1 h2 hlo
  rw [show (633825300114114700748351602688000000000000000000000000000 : Nat) = QS
    from by decide] at cap1
  have cap1B := capLB_mul cap1 capBL
  have cap1BE := capLB_mul cap1B capEL
  have hX1 := x1_nonneg_ge h1 h2
  have hVs := v_scale_neg (toInt (x1W (zWord m))) c hc
  have hVnn : 0 ≤ (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 := by
    have h0 : 0 ≤ r * 2 ^ 72 := Int.mul_nonneg hr0 (by omega)
    have : 0 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269 := by
      generalize hgV : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269 = V at hrlo ⊢
      omega
    generalize hgV : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269 = V at this ⊢
    have h27 : (0 : Int) ≤ 2 ^ 27 := by omega
    exact Int.mul_nonneg this h27
  have hsplit : (toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
      BIASc * 2 ^ 27 + 2 ^ 99 =
      ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        BIASc * 2 ^ 27 + 2 ^ 99 - (c - 152) * (LN2c * 2 ^ 27)) +
        (c - 152) * (LN2c * 2 ^ 27) := by
    have hX1n : ((toInt (x1W (zWord m))).toNat : Int) = toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 152) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hVnn hVs
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 152) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 cap1B cap1BE hlo hr h1 h2 hc hc2 hmx
    omega
  rw [hsplit] at cap1BE
  have capV := capLB_cancel QS_pos cap1BE (capUB_pow QS_pos cap2U (c - 152))
  have hple : (toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
      BIASc * 2 ^ 27 + 2 ^ 99 - (c - 152) * (LN2c * 2 ^ 27) ≤
      (r + 2).toNat * 2 ^ 99 := by
    have hsc : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 ≤
        ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 :=
      mul_le_mul_right_nonneg (by omega) (by omega)
    have er : ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 = (r + 1) * 2 ^ 99 - 2 ^ 27 := by
      rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
        by decide]
      omega
    rw [er] at hsc
    have hX1n : ((toInt (x1W (zWord m))).toNat : Int) = toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 152) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hsc hVs hVnn
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 152) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 cap1B cap1BE capV hlo hr h1 h2 hc hc2 hmx hsplit
    omega
  have hmul : ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
      BIASc * 2 ^ 27 + 2 ^ 99 - (c - 152) * (LN2c * 2 ^ 27)) * QS ≤
      (r + 2).toNat * 2 ^ 99 * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capLB_arg QS_pos hmul capV
  refine capLB_weaken ?_ capR ?_
  · have h1' : 0 < (1434182936954525181919537618622900000000000000000000000000000 : Nat) *
        (10 ^ 18 * 10 ^ 30) * 10 ^ 30 := by decide
    exact Nat.mul_pos h1' (Nat.pow_pos (by decide))
  · -- x·10^30·W ≤ Y·(10^18·(10^30−1)) with exact mantissa
    have hb := budgetLn_le (j := c - 152) (by omega)
    have hbf := Nat.mul_le_mul_left (x * Sc) hb
    have eL : x * 10 ^ 30 *
        (1434182936954525181919537618622900000000000000000000000000000 *
          (10 ^ 18 * 10 ^ 30) * 10 ^ 30 * (2 * (10 ^ 40 + 1)) ^ (c - 152)) =
        x * Sc * ((10 : Nat) ^ 137 * (2 * (10 ^ 40 + 1)) ^ (c - 152)) := by
      rw [show (1434182936954525181919537618622900000000000000000000000000000 : Nat) =
        Sc * 10 ^ 29 from by decide]
      have e' : ∀ P : Nat, (10 : Nat) ^ 18 * ((10 : Nat) ^ 29 * ((10 : Nat) ^ 30 *
          ((10 : Nat) ^ 30 * ((10 : Nat) ^ 30 * P)))) = (10 : Nat) ^ 137 * P := by
        intro P
        rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc,
          show ((10 : Nat) ^ 18 * 10 ^ 29 * 10 ^ 30 * 10 ^ 30 * 10 ^ 30) = 10 ^ 137
            from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e' ((2 * (10 ^ 40 + 1)) ^ (c - 152))]
    have eR : m * 99999999999999999999999999958 * (Sc * (10 ^ 30 - 501)) *
        (10 ^ 30 + 999) * ((10 ^ 40 : Nat) ^ (c - 152)) * (10 ^ 18 * (10 ^ 30 - 1)) =
        x * Sc * (2 ^ (c - 152) * (10 ^ 40 : Nat) ^ (c - 152) * (10 ^ 29 - 42) *
          (10 ^ 30 - 501) * (10 ^ 30 + 999) * (10 ^ 30 - 1) * 10 ^ 18) := by
      rw [hmx, show (99999999999999999999999999958 : Nat) = 10 ^ 29 - 42 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    generalize hT1 : x * 10 ^ 30 *
      (1434182936954525181919537618622900000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 30) * 10 ^ 30 * (2 * (10 ^ 40 + 1)) ^ (c - 152)) = T1 at eL ⊢
    generalize hT2 : x * Sc * ((10 : Nat) ^ 137 * (2 * (10 ^ 40 + 1)) ^ (c - 152)) = T2
      at eL hbf
    generalize hT3 : x * Sc * (2 ^ (c - 152) * (10 ^ 40 : Nat) ^ (c - 152) *
      (10 ^ 29 - 42) * (10 ^ 30 - 501) * (10 ^ 30 + 999) * (10 ^ 30 - 1) * 10 ^ 18) = T3
      at eR hbf
    generalize hT4 : m * 99999999999999999999999999958 * (Sc * (10 ^ 30 - 501)) *
      (10 ^ 30 + 999) * ((10 ^ 40 : Nat) ^ (c - 152)) * (10 ^ 18 * (10 ^ 30 - 1)) = T4
      at eR ⊢
    omega

/-- Upper master chain, `m < S` branch, nonnegative binade shift. -/
theorem up_lt_pos {m c x : Nat} {r : Int} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc)
    (hc1 : 1 ≤ c) (hc : c ≤ 152)
    (hup : 0 ≤ evalPoly certLtUp (m : Int))
    (hr : r * 2 ^ 72 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269)
    (hr0 : 0 ≤ r)
    (hmx : m * 2 ^ (152 - c) ≤ x) :
    capUB (r.toNat * 2 ^ 99) QS x (10 ^ 18) := by
  have cap1 := x1capLtUp h1 h2 hup
  rw [show (633825300114114700748351602688000000000000000000000000000 : Nat) = QS
    from by decide] at cap1
  have hsum := capUB_mul QS_pos (capUB_pow QS_pos cap2U (152 - c)) capBU
  have hX1 := x1_nonpos_lt h1 h2
  have hVs := v_scale_pos (toInt (x1W (zWord m))) c hc
  -- split: kL + B = pa + |X1|·E with pa = V·2^27 ≥ 0
  have hsplit : (152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 =
      ((152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 -
        (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000) +
        (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 := by
    have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) = -toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((152 - c) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    have hV0 : 0 ≤ (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 := by
      have hm := mul_le_mul_right_nonneg hr (show (0 : Int) ≤ 2 ^ 27 by omega)
      have h0 : 0 ≤ r * 2 ^ 72 * 2 ^ 27 :=
        Int.mul_nonneg (Int.mul_nonneg hr0 (by omega)) (by omega)
      generalize hgV' : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hm ⊢
      generalize hgR : r * 2 ^ 72 * 2 ^ 27 = R27 at hm h0
      clear cap1 hsum hup hX1 hVs hX1n hBc hLc h1 h2 hmx hc hc1 hr hr0
      omega
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hV0 hVs
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (152 - c) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-toInt (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(toInt (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 hsum hup hr h1 h2 hc hc1 hmx
    omega
  rw [hsplit] at hsum
  have capV := capUB_cancel QS_pos hsum cap1
  have hple : r.toNat * 2 ^ 99 ≤
      (152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 -
        (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 := by
    have hsc : r * 2 ^ 72 * 2 ^ 27 ≤ (toInt (x1W (zWord m)) * 7450580596923828125 +
        ln2kInt c + 143060321855302967919159136223863753677754092301269) * 2 ^ 27 :=
      mul_le_mul_right_nonneg hr (by omega)
    have e99 : r * 2 ^ 72 * 2 ^ 27 = r * 2 ^ 99 := by
      rw [Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from by decide]
    rw [e99] at hsc
    have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) = -toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((152 - c) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hsc hVs
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (152 - c) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-toInt (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(toInt (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 hsum capV hup hr h1 h2 hc hc1 hmx hsplit
    omega
  have hmul : r.toNat * 2 ^ 99 * QS ≤
      ((152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 -
        (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000) * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capUB_arg QS_pos hmul capV
  refine capUB_weaken ?_ capR ?_
  · have h1' : 0 < (10 ^ 40 : Nat) ^ (152 - c) * (10 ^ 18 * 10 ^ 30) :=
      Nat.mul_pos (Nat.pow_pos (by decide)) (by decide)
    exact Nat.mul_pos h1' (by decide)
  · have hb := budgetU_le (k := 152 - c) (by omega)
    have hbm : m * (Sc * ((10 ^ 29 + 42) * (2 * (10 ^ 40 + 1)) ^ (152 - c) *
        (10 ^ 30 - 499) * 10 ^ 18)) ≤
        m * (Sc * (2 ^ (152 - c) * (10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb)
    have hxm : m * 2 ^ (152 - c) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) ≤
        x * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) :=
      Nat.mul_le_mul_right _ hmx
    have e1 : (2 * (10 ^ 40 + 1)) ^ (152 - c) * (Sc * (10 ^ 30 - 499)) *
        (m * 100000000000000000000000000042) * 10 ^ 18 =
        m * (Sc * ((10 ^ 29 + 42) * (2 * (10 ^ 40 + 1)) ^ (152 - c) *
          (10 ^ 30 - 499) * 10 ^ 18)) := by
      rw [show (100000000000000000000000000042 : Nat) = 10 ^ 29 + 42 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have e2 : m * (Sc * (2 ^ (152 - c) * (10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) =
        m * 2 ^ (152 - c) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have e3 : x * ((10 ^ 40 : Nat) ^ (152 - c) * (10 ^ 18 * 10 ^ 30) *
        1434182936954525181919537618622900000000000000000000000000000) =
        x * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) := by
      rw [show (1434182936954525181919537618622900000000000000000000000000000 : Nat) =
        Sc * 10 ^ 29 from by decide]
      have e' : ∀ P : Nat, (10 : Nat) ^ 18 * ((10 : Nat) ^ 29 * ((10 : Nat) ^ 30 * P)) =
          (10 : Nat) ^ 77 * P := by
        intro P
        rw [← Nat.mul_assoc, ← Nat.mul_assoc,
          show ((10 : Nat) ^ 18 * 10 ^ 29 * 10 ^ 30) = 10 ^ 77 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e' ((10 ^ 40 : Nat) ^ (152 - c))]
    generalize hgY : (2 * (10 ^ 40 + 1)) ^ (152 - c) * (Sc * (10 ^ 30 - 499)) *
      (m * 100000000000000000000000000042) * 10 ^ 18 = Y at e1 ⊢
    generalize hg1 : m * (Sc * ((10 ^ 29 + 42) * (2 * (10 ^ 40 + 1)) ^ (152 - c) *
      (10 ^ 30 - 499) * 10 ^ 18)) = T1 at hbm e1
    generalize hg2 : m * (Sc * (2 ^ (152 - c) * (10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) =
      T2 at hbm e2
    generalize hg3 : m * 2 ^ (152 - c) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) =
      T3 at hxm e2
    generalize hg4 : x * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) = T4 at hxm e3
    generalize hg5 : x * ((10 ^ 40 : Nat) ^ (152 - c) * (10 ^ 18 * 10 ^ 30) *
      1434182936954525181919537618622900000000000000000000000000000) = W4 at e3 ⊢
    omega

/-- Lower master chain, `m < S` branch, nonnegative binade shift. -/
theorem lo_lt_pos {m c x : Nat} {r : Int} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc)
    (hc1 : 1 ≤ c) (hc : c ≤ 152)
    (hlo : 0 ≤ evalPoly certLtLo (m : Int))
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269 < (r + 1) * 2 ^ 72)
    (hrlo : r * 2 ^ 72 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269)
    (hr0 : 0 ≤ r)
    (hxm : x < (m + 1) * 2 ^ (152 - c)) :
    capLB ((r + 2).toNat * 2 ^ 99) QS (x * 10 ^ 30) (10 ^ 18 * (10 ^ 30 - 1)) := by
  have cap1 := x1capLtLo h1 h2 hlo
  rw [show (633825300114114700748351602688000000000000000000000000000 : Nat) = QS
    from by decide] at cap1
  have hsum := capLB_mul (capLB_mul (capLB_pow cap2L (152 - c)) capBL) capEL
  have hX1 := x1_nonpos_lt h1 h2
  have hVs := v_scale_pos (toInt (x1W (zWord m))) c hc
  have hVnn : 0 ≤ (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 := by
    have h0 : 0 ≤ r * 2 ^ 72 := Int.mul_nonneg hr0 (by omega)
    have hg : 0 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269 := by
      generalize hgV : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269 = V at hrlo ⊢
      omega
    generalize hgV : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269 = V at hg ⊢
    exact Int.mul_nonneg hg (by omega)
  have hsplit : (152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99 =
      ((152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99 -
        (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000) +
        (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 := by
    have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) = -toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((152 - c) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hVnn hVs
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (152 - c) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-toInt (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(toInt (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 hsum hlo hr h1 h2 hc hc1 hxm hrlo
    omega
  rw [hsplit] at hsum
  have capV := capLB_cancel QS_pos hsum cap1
  have hple : (152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99 -
      (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 ≤
      (r + 2).toNat * 2 ^ 99 := by
    have hsc : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 ≤
        ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 :=
      mul_le_mul_right_nonneg (by omega) (by omega)
    have er : ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 = (r + 1) * 2 ^ 99 - 2 ^ 27 := by
      rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
        by decide]
      omega
    rw [er] at hsc
    have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) = -toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((152 - c) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hsc hVs hVnn
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (152 - c) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-toInt (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(toInt (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 hsum capV hlo hr h1 h2 hc hc1 hxm hsplit hrlo
    omega
  have hmul : ((152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99 -
      (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000) * QS ≤
      (r + 2).toNat * 2 ^ 99 * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capLB_arg QS_pos hmul capV
  refine capLB_weaken ?_ capR ?_
  · have h1' : 0 < (10 ^ 40 : Nat) ^ (152 - c) * (10 ^ 18 * 10 ^ 30) * 10 ^ 30 :=
      Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by decide)) (by decide)) (by decide)
    exact Nat.mul_pos h1' (by decide)
  · have hMLO : 2 ^ 103 ≤ m := by
      simp only [MLO] at h1
      omega
    have hb := budgetL_fold (k := 152 - c) hMLO (by omega)
    have hx1 : x + 1 ≤ (m + 1) * 2 ^ (152 - c) := by omega
    have hxw : (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 137)) ≤
        (m + 1) * 2 ^ (152 - c) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 137)) :=
      Nat.mul_le_mul_right _ hx1
    have hfold : (m + 1) * 2 ^ (152 - c) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) *
        10 ^ 137)) ≤
        m * ((10 ^ 29 - 42) * (2 * (10 ^ 40 - 1)) ^ (152 - c) * (10 ^ 30 - 501) *
          (10 ^ 30 + 999) * (10 ^ 30 - 1) * 10 ^ 18) * Sc := by
      have h := Nat.mul_le_mul_left Sc hb
      have e1 : Sc * ((m + 1) * (2 ^ (152 - c) * (10 ^ 40 : Nat) ^ (152 - c) *
          10 ^ 137)) =
          (m + 1) * 2 ^ (152 - c) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 137)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have e2 : Sc * (m * ((10 ^ 29 - 42) * (2 * (10 ^ 40 - 1)) ^ (152 - c) *
          (10 ^ 30 - 501) * (10 ^ 30 + 999) * (10 ^ 30 - 1) * 10 ^ 18)) =
          m * ((10 ^ 29 - 42) * (2 * (10 ^ 40 - 1)) ^ (152 - c) * (10 ^ 30 - 501) *
            (10 ^ 30 + 999) * (10 ^ 30 - 1) * 10 ^ 18) * Sc := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e1] at h
      rw [e2] at h
      exact h
    have eL : x * 10 ^ 30 * ((10 ^ 40 : Nat) ^ (152 - c) * (10 ^ 18 * 10 ^ 30) *
        10 ^ 30 * 1434182936954525181919537618622900000000000000000000000000000) ≤
        (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 137)) := by
      rw [show (1434182936954525181919537618622900000000000000000000000000000 : Nat) =
        Sc * 10 ^ 29 from by decide]
      have eAC : x * 10 ^ 30 * ((10 ^ 40 : Nat) ^ (152 - c) * (10 ^ 18 * 10 ^ 30) *
          10 ^ 30 * (Sc * 10 ^ 29)) =
          x * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * ((10 : Nat) ^ 18 * ((10 : Nat) ^ 29 *
            ((10 : Nat) ^ 30 * ((10 : Nat) ^ 30 * (10 : Nat) ^ 30)))))) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [eAC, show ((10 : Nat) ^ 18 * ((10 : Nat) ^ 29 * ((10 : Nat) ^ 30 *
        ((10 : Nat) ^ 30 * (10 : Nat) ^ 30)))) = 10 ^ 137 from by decide]
      have : x * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 137)) ≤
          (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 137)) :=
        Nat.mul_le_mul_right _ (by omega)
      exact this
    have eR : (2 * (10 ^ 40 - 1)) ^ (152 - c) * (Sc * (10 ^ 30 - 501)) *
        (10 ^ 30 + 999) * (m * 99999999999999999999999999958) *
        (10 ^ 18 * (10 ^ 30 - 1)) =
        m * ((10 ^ 29 - 42) * (2 * (10 ^ 40 - 1)) ^ (152 - c) * (10 ^ 30 - 501) *
          (10 ^ 30 + 999) * (10 ^ 30 - 1) * 10 ^ 18) * Sc := by
      rw [show (99999999999999999999999999958 : Nat) = 10 ^ 29 - 42 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    generalize hT1 : x * 10 ^ 30 * ((10 ^ 40 : Nat) ^ (152 - c) * (10 ^ 18 * 10 ^ 30) *
      10 ^ 30 * 1434182936954525181919537618622900000000000000000000000000000) = T1
      at eL ⊢
    generalize hT2 : (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 137)) = T2
      at eL hxw
    generalize hT3 : (m + 1) * 2 ^ (152 - c) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) *
      10 ^ 137)) = T3 at hxw hfold
    generalize hT4 : m * ((10 ^ 29 - 42) * (2 * (10 ^ 40 - 1)) ^ (152 - c) *
      (10 ^ 30 - 501) * (10 ^ 30 + 999) * (10 ^ 30 - 1) * 10 ^ 18) * Sc = T4
      at hfold eR
    generalize hT5 : (2 * (10 ^ 40 - 1)) ^ (152 - c) * (Sc * (10 ^ 30 - 501)) *
      (10 ^ 30 + 999) * (m * 99999999999999999999999999958) *
      (10 ^ 18 * (10 ^ 30 - 1)) = T5 at eR ⊢
    omega

/-- Upper master chain, `m < S` branch, negative binade shift
(exact mantissa). -/
theorem up_lt_neg {m c x : Nat} {r : Int} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc)
    (hc : 152 < c) (hc2 : c ≤ 255)
    (hup : 0 ≤ evalPoly certLtUp (m : Int))
    (hr : r * 2 ^ 72 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269)
    (hr0 : 0 ≤ r)
    (hmx : m = x * 2 ^ (c - 152)) :
    capUB (r.toNat * 2 ^ 99) QS x (10 ^ 18) := by
  have cap1 := x1capLtUp h1 h2 hup
  rw [show (633825300114114700748351602688000000000000000000000000000 : Nat) = QS
    from by decide] at cap1
  have hb := capLB_mul cap1 (capLB_pow cap2L (c - 152))
  have hX1 := x1_nonpos_lt h1 h2
  have hVs := v_scale_neg (toInt (x1W (zWord m))) c hc
  -- split: B = pa + (|X1|·E + j·L) with pa = V·2^27 ≥ 0
  have hsplit : BIASc * 2 ^ 27 =
      (BIASc * 2 ^ 27 - ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        (c - 152) * (LN2c * 2 ^ 27))) +
        ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
          (c - 152) * (LN2c * 2 ^ 27)) := by
    have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) = -toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 152) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    have hV0 : 0 ≤ (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 := by
      have hm := mul_le_mul_right_nonneg hr (show (0 : Int) ≤ 2 ^ 27 by omega)
      have h0 : 0 ≤ r * 2 ^ 72 * 2 ^ 27 :=
        Int.mul_nonneg (Int.mul_nonneg hr0 (by omega)) (by omega)
      generalize hgV' : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hm ⊢
      generalize hgR : r * 2 ^ 72 * 2 ^ 27 = R27 at hm h0
      clear cap1 hb hup hX1 hVs hX1n hBc hLc h1 h2 hmx hc hc2 hr hr0
      omega
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hV0 hVs
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 152) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-toInt (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(toInt (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 hb hup hr h1 h2 hc hc2 hmx
    omega
  have hsumB : capUB (BIASc * 2 ^ 27) QS (Sc * (10 ^ 30 - 499)) (10 ^ 18 * 10 ^ 30) :=
    capBU
  rw [hsplit] at hsumB
  have capV := capUB_cancel QS_pos hsumB hb
  have hple : r.toNat * 2 ^ 99 ≤
      BIASc * 2 ^ 27 - ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        (c - 152) * (LN2c * 2 ^ 27)) := by
    have hsc : r * 2 ^ 72 * 2 ^ 27 ≤ (toInt (x1W (zWord m)) * 7450580596923828125 +
        ln2kInt c + 143060321855302967919159136223863753677754092301269) * 2 ^ 27 :=
      mul_le_mul_right_nonneg hr (by omega)
    have e99 : r * 2 ^ 72 * 2 ^ 27 = r * 2 ^ 99 := by
      rw [Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from by decide]
    rw [e99] at hsc
    have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) = -toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 152) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hsc hVs
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 152) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-toInt (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(toInt (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 hb capV hup hr h1 h2 hc hc2 hmx hsplit
    omega
  have hmul : r.toNat * 2 ^ 99 * QS ≤
      (BIASc * 2 ^ 27 - ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        (c - 152) * (LN2c * 2 ^ 27))) * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capUB_arg QS_pos hmul capV
  refine capUB_weaken ?_ capR ?_
  · have h1' : 0 < (10 ^ 18 * 10 ^ 30 : Nat) *
        (1434182936954525181919537618622900000000000000000000000000000 *
          (2 * (10 ^ 40 - 1)) ^ (c - 152)) :=
      Nat.mul_pos (by decide) (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))
    exact h1'
  · have hbg := budgetUn_le (j := c - 152) (by omega)
    have hbf := Nat.mul_le_mul_left (x * Sc) hbg
    have eY : Sc * (10 ^ 30 - 499) * (m * 100000000000000000000000000042 *
        (10 ^ 40 : Nat) ^ (c - 152)) * 10 ^ 18 =
        x * Sc * ((10 ^ 29 + 42) * (10 ^ 30 - 499) * (10 ^ 40 : Nat) ^ (c - 152) *
          2 ^ (c - 152) * 10 ^ 18) := by
      rw [hmx, show (100000000000000000000000000042 : Nat) = 10 ^ 29 + 42 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have eW : x * (10 ^ 18 * 10 ^ 30 *
        (1434182936954525181919537618622900000000000000000000000000000 *
          (2 * (10 ^ 40 - 1)) ^ (c - 152))) =
        x * Sc * (10 ^ 77 * (2 * (10 ^ 40 - 1)) ^ (c - 152)) := by
      rw [show (1434182936954525181919537618622900000000000000000000000000000 : Nat) =
        Sc * 10 ^ 29 from by decide]
      have e' : ∀ P : Nat, (10 : Nat) ^ 18 * ((10 : Nat) ^ 29 * ((10 : Nat) ^ 30 * P)) =
          (10 : Nat) ^ 77 * P := by
        intro P
        rw [← Nat.mul_assoc, ← Nat.mul_assoc,
          show ((10 : Nat) ^ 18 * 10 ^ 29 * 10 ^ 30) = 10 ^ 77 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e' ((2 * (10 ^ 40 - 1)) ^ (c - 152))]
    generalize hT1 : Sc * (10 ^ 30 - 499) * (m * 100000000000000000000000000042 *
      (10 ^ 40 : Nat) ^ (c - 152)) * 10 ^ 18 = T1 at eY ⊢
    generalize hT2 : x * Sc * ((10 ^ 29 + 42) * (10 ^ 30 - 499) *
      (10 ^ 40 : Nat) ^ (c - 152) * 2 ^ (c - 152) * 10 ^ 18) = T2 at eY hbf
    generalize hT3 : x * Sc * (10 ^ 77 * (2 * (10 ^ 40 - 1)) ^ (c - 152)) = T3 at hbf eW
    generalize hT4 : x * (10 ^ 18 * 10 ^ 30 *
      (1434182936954525181919537618622900000000000000000000000000000 *
        (2 * (10 ^ 40 - 1)) ^ (c - 152))) = T4 at eW ⊢
    omega

/-- Lower master chain, `m < S` branch, negative binade shift
(exact mantissa). -/
theorem lo_lt_neg {m c x : Nat} {r : Int} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc)
    (hc : 152 < c) (hc2 : c ≤ 255)
    (hlo : 0 ≤ evalPoly certLtLo (m : Int))
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269 < (r + 1) * 2 ^ 72)
    (hrlo : r * 2 ^ 72 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269)
    (hr0 : 0 ≤ r)
    (hmx : m = x * 2 ^ (c - 152)) :
    capLB ((r + 2).toNat * 2 ^ 99) QS (x * 10 ^ 30) (10 ^ 18 * (10 ^ 30 - 1)) := by
  have cap1 := x1capLtLo h1 h2 hlo
  rw [show (633825300114114700748351602688000000000000000000000000000 : Nat) = QS
    from by decide] at cap1
  have hb := capUB_mul QS_pos cap1 (capUB_pow QS_pos cap2U (c - 152))
  have hsum := capLB_mul capBL capEL
  have hX1 := x1_nonpos_lt h1 h2
  have hVs := v_scale_neg (toInt (x1W (zWord m))) c hc
  have hVnn : 0 ≤ (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 := by
    have h0 : 0 ≤ r * 2 ^ 72 := Int.mul_nonneg hr0 (by omega)
    have hg : 0 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269 := by
      generalize hgV : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269 = V at hrlo ⊢
      omega
    generalize hgV : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269 = V at hg ⊢
    exact Int.mul_nonneg hg (by omega)
  have hsplit : BIASc * 2 ^ 27 + 2 ^ 99 =
      (BIASc * 2 ^ 27 + 2 ^ 99 -
        ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
          (c - 152) * (LN2c * 2 ^ 27))) +
        ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
          (c - 152) * (LN2c * 2 ^ 27)) := by
    have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) = -toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 152) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hVnn hVs
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 152) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-toInt (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(toInt (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 hb hsum hlo hr h1 h2 hc hc2 hmx hrlo
    omega
  rw [hsplit] at hsum
  have capV := capLB_cancel QS_pos hsum hb
  have hple : BIASc * 2 ^ 27 + 2 ^ 99 -
      ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        (c - 152) * (LN2c * 2 ^ 27)) ≤
      (r + 2).toNat * 2 ^ 99 := by
    have hsc : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 ≤
        ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 :=
      mul_le_mul_right_nonneg (by omega) (by omega)
    have er : ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 = (r + 1) * 2 ^ 99 - 2 ^ 27 := by
      rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
        by decide]
      omega
    rw [er] at hsc
    have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) = -toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 152) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hsc hVs hVnn
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 152) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-toInt (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(toInt (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 hb hsum capV hlo hr h1 h2 hc hc2 hmx hsplit hrlo
    omega
  have hmul : (BIASc * 2 ^ 27 + 2 ^ 99 -
      ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        (c - 152) * (LN2c * 2 ^ 27))) * QS ≤
      (r + 2).toNat * 2 ^ 99 * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capLB_arg QS_pos hmul capV
  refine capLB_weaken ?_ capR ?_
  · have h1' : 0 < (10 ^ 18 * 10 ^ 30 * 10 ^ 30 : Nat) *
        (1434182936954525181919537618622900000000000000000000000000000 *
          (2 * (10 ^ 40 + 1)) ^ (c - 152)) :=
      Nat.mul_pos (by decide) (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))
    exact h1'
  · have hbg := budgetLn_le (j := c - 152) (by omega)
    have hbf := Nat.mul_le_mul_left (x * Sc) hbg
    have eL : x * 10 ^ 30 * (10 ^ 18 * 10 ^ 30 * 10 ^ 30 *
        (1434182936954525181919537618622900000000000000000000000000000 *
          (2 * (10 ^ 40 + 1)) ^ (c - 152))) =
        x * Sc * ((10 : Nat) ^ 137 * (2 * (10 ^ 40 + 1)) ^ (c - 152)) := by
      rw [show (1434182936954525181919537618622900000000000000000000000000000 : Nat) =
        Sc * 10 ^ 29 from by decide]
      have e' : ∀ P : Nat, (10 : Nat) ^ 18 * ((10 : Nat) ^ 29 * ((10 : Nat) ^ 30 *
          ((10 : Nat) ^ 30 * ((10 : Nat) ^ 30 * P)))) = (10 : Nat) ^ 137 * P := by
        intro P
        rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc,
          show ((10 : Nat) ^ 18 * 10 ^ 29 * 10 ^ 30 * 10 ^ 30 * 10 ^ 30) = 10 ^ 137
            from by decide]
      have eAC : x * 10 ^ 30 * (10 ^ 18 * 10 ^ 30 * 10 ^ 30 * (Sc * 10 ^ 29 *
          (2 * (10 ^ 40 + 1)) ^ (c - 152))) =
          x * (Sc * ((10 : Nat) ^ 18 * ((10 : Nat) ^ 29 * ((10 : Nat) ^ 30 *
            ((10 : Nat) ^ 30 * ((10 : Nat) ^ 30 *
              (2 * (10 ^ 40 + 1)) ^ (c - 152))))))) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [eAC, e' ((2 * (10 ^ 40 + 1)) ^ (c - 152))]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have eR : Sc * (10 ^ 30 - 501) * (10 ^ 30 + 999) *
        (m * 99999999999999999999999999958 * (10 ^ 40 : Nat) ^ (c - 152)) *
        (10 ^ 18 * (10 ^ 30 - 1)) =
        x * Sc * (2 ^ (c - 152) * (10 ^ 40 : Nat) ^ (c - 152) * (10 ^ 29 - 42) *
          (10 ^ 30 - 501) * (10 ^ 30 + 999) * (10 ^ 30 - 1) * 10 ^ 18) := by
      rw [hmx, show (99999999999999999999999999958 : Nat) = 10 ^ 29 - 42 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    generalize hT1 : x * 10 ^ 30 * (10 ^ 18 * 10 ^ 30 * 10 ^ 30 *
      (1434182936954525181919537618622900000000000000000000000000000 *
        (2 * (10 ^ 40 + 1)) ^ (c - 152))) = T1 at eL ⊢
    generalize hT2 : x * Sc * ((10 : Nat) ^ 137 * (2 * (10 ^ 40 + 1)) ^ (c - 152)) = T2
      at eL hbf
    generalize hT3 : x * Sc * (2 ^ (c - 152) * (10 ^ 40 : Nat) ^ (c - 152) *
      (10 ^ 29 - 42) * (10 ^ 30 - 501) * (10 ^ 30 + 999) * (10 ^ 30 - 1) * 10 ^ 18) = T3
      at eR hbf
    generalize hT4 : Sc * (10 ^ 30 - 501) * (10 ^ 30 + 999) *
      (m * 99999999999999999999999999958 * (10 ^ 40 : Nat) ^ (c - 152)) *
      (10 ^ 18 * (10 ^ 30 - 1)) = T4 at eR ⊢
    omega

/-- A-atom master for negative outputs, `m < S` branch, `k ≥ 0`:
`e^(|r|/10^27) ≥ 10^18/x`. -/
theorem an_lt_pos {m c x : Nat} {r : Int} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc)
    (hc1 : 1 ≤ c) (hc : c ≤ 152)
    (hup : 0 ≤ evalPoly certLtUp (m : Int))
    (hrlo : r * 2 ^ 72 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269)
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269 < (r + 1) * 2 ^ 72)
    (hrneg : r < 0)
    (hmx : m * 2 ^ (152 - c) ≤ x) :
    capLB ((-r).toNat * 2 ^ 99) QS (10 ^ 18) x := by
  have cap1 := x1capLtUp h1 h2 hup
  rw [show (633825300114114700748351602688000000000000000000000000000 : Nat) = QS
    from by decide] at cap1
  have hb := capUB_mul QS_pos (capUB_pow QS_pos cap2U (152 - c)) capBU
  have hX1 := x1_nonpos_lt h1 h2
  have hVs := v_scale_pos (toInt (x1W (zWord m))) c hc
  -- split: |X1|·E = pa + (kL + B) with pa = -V·2^27 ≥ 0
  have hsplit : (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 =
      ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 -
        ((152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27)) +
        ((152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27) := by
    have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) = -toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((152 - c) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    have hV0 : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 ≤ 0 := by
      have hm := mul_le_mul_right_nonneg (show toInt (x1W (zWord m)) *
        7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269 ≤ 0 from by
          generalize hgV' : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
            143060321855302967919159136223863753677754092301269 = V at hr ⊢
          generalize hgR : (r + 1) * 2 ^ 72 = R at hr
          have : R ≤ 0 := by
            rw [← hgR]
            have : r + 1 ≤ 0 := by omega
            have := mul_le_mul_right_nonneg this (show (0 : Int) ≤ 2 ^ 72 by omega)
            generalize hgT : (r + 1) * 2 ^ 72 = T at this ⊢
            omega
          omega) (show (0 : Int) ≤ 2 ^ 27 by omega)
      generalize hgV' : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hm ⊢
      clear cap1 hb hX1 hVs hup hrlo hr h1 h2 hmx hX1n hBc hLc
      omega
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hV0 hVs
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (152 - c) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-toInt (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(toInt (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 hb hup hr h1 h2 hc hc1 hmx hrlo hrneg
    omega
  rw [hsplit] at cap1
  have capV := capLB_cancel QS_pos cap1 hb
  have hple : (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 -
      ((152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27) ≤ (-r).toNat * 2 ^ 99 := by
    have hsc : (-r) * 2 ^ 72 * 2 ^ 27 ≥ -(toInt (x1W (zWord m)) * 7450580596923828125 +
        ln2kInt c + 143060321855302967919159136223863753677754092301269) * 2 ^ 27 := by
      have h := mul_le_mul_right_nonneg hrlo (show (0 : Int) ≤ 2 ^ 27 by omega)
      generalize hgV' : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) = V at h ⊢
      generalize hgR : r * 2 ^ 72 * 2 ^ 27 = R at h
      have e1 : (-r) * 2 ^ 72 * 2 ^ 27 = -(r * 2 ^ 72 * 2 ^ 27) := by
        rw [Int.neg_mul, Int.neg_mul]
      have e2 : -V * 2 ^ 27 = -(V * 2 ^ 27) := Int.neg_mul _ _
      generalize hgV2 : V * 2 ^ 27 = V27 at h e2 ⊢
      omega
    have e99 : (-r) * 2 ^ 72 * 2 ^ 27 = (-r) * 2 ^ 99 := by
      rw [Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from by decide]
    rw [e99] at hsc
    have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) = -toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((152 - c) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    have hnegV : -(toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 =
        -((toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
          143060321855302967919159136223863753677754092301269) * 2 ^ 27) :=
      Int.neg_mul _ _
    rw [hnegV] at hsc
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hsc hVs
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (152 - c) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-toInt (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(toInt (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 hb capV hup hr h1 h2 hc hc1 hmx hsplit hrlo
    omega
  have hmul : ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 -
      ((152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27)) * QS ≤
      (-r).toNat * 2 ^ 99 * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capLB_arg QS_pos hmul capV
  refine capLB_weaken ?_ capR ?_
  · have h1' : 0 < m * 100000000000000000000000000042 := by
      have : 0 < m := by simp only [MLO] at h1; omega
      exact Nat.mul_pos this (by decide)
    exact Nat.mul_pos h1' (Nat.mul_pos (Nat.pow_pos (by decide)) (by decide))
  · have hbg := budgetU_le (k := 152 - c) (by omega)
    have hbm : m * (Sc * ((10 ^ 29 + 42) * (2 * (10 ^ 40 + 1)) ^ (152 - c) *
        (10 ^ 30 - 499) * 10 ^ 18)) ≤
        m * (Sc * (2 ^ (152 - c) * (10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hbg)
    have hxm : m * 2 ^ (152 - c) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) ≤
        x * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) :=
      Nat.mul_le_mul_right _ hmx
    have e1 : 10 ^ 18 * (m * 100000000000000000000000000042 *
        ((2 * (10 ^ 40 + 1)) ^ (152 - c) * (Sc * (10 ^ 30 - 499)))) =
        m * (Sc * ((10 ^ 29 + 42) * (2 * (10 ^ 40 + 1)) ^ (152 - c) *
          (10 ^ 30 - 499) * 10 ^ 18)) := by
      rw [show (100000000000000000000000000042 : Nat) = 10 ^ 29 + 42 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have e2 : m * (Sc * (2 ^ (152 - c) * (10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) =
        m * 2 ^ (152 - c) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have e3 : 1434182936954525181919537618622900000000000000000000000000000 *
        ((10 ^ 40 : Nat) ^ (152 - c) * (10 ^ 18 * 10 ^ 30)) * x =
        x * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) := by
      rw [show (1434182936954525181919537618622900000000000000000000000000000 : Nat) =
        Sc * 10 ^ 29 from by decide]
      have e' : ∀ P : Nat, (10 : Nat) ^ 18 * ((10 : Nat) ^ 29 * ((10 : Nat) ^ 30 * P)) =
          (10 : Nat) ^ 77 * P := by
        intro P
        rw [← Nat.mul_assoc, ← Nat.mul_assoc,
          show ((10 : Nat) ^ 18 * 10 ^ 29 * 10 ^ 30) = 10 ^ 77 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e' ((10 ^ 40 : Nat) ^ (152 - c))]
    generalize hT1 : 10 ^ 18 * (m * 100000000000000000000000000042 *
      ((2 * (10 ^ 40 + 1)) ^ (152 - c) * (Sc * (10 ^ 30 - 499)))) = T1 at e1 ⊢
    generalize hT2 : m * (Sc * ((10 ^ 29 + 42) * (2 * (10 ^ 40 + 1)) ^ (152 - c) *
      (10 ^ 30 - 499) * 10 ^ 18)) = T2 at hbm e1
    generalize hT3 : m * (Sc * (2 ^ (152 - c) * (10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) =
      T3 at hbm e2
    generalize hT4 : m * 2 ^ (152 - c) * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) =
      T4 at hxm e2
    generalize hT5 : x * (Sc * ((10 ^ 40 : Nat) ^ (152 - c) * 10 ^ 77)) = T5 at hxm e3
    generalize hT6 : 1434182936954525181919537618622900000000000000000000000000000 *
      ((10 ^ 40 : Nat) ^ (152 - c) * (10 ^ 18 * 10 ^ 30)) * x = T6 at e3 ⊢
    omega

/-- A-atom master for negative outputs, `m ≥ S` branch, negative shift
(exact mantissa). -/
theorem an_ge_neg {m c x : Nat} {r : Int} (h1 : Sc + 46 ≤ m) (h2 : m < MHI)
    (hc : 152 < c) (hc2 : c ≤ 255)
    (hup : 0 ≤ evalPoly certGeUp (m : Int))
    (hrlo : r * 2 ^ 72 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269)
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269 < (r + 1) * 2 ^ 72)
    (hrneg : r < 0)
    (hmx : m = x * 2 ^ (c - 152)) :
    capLB ((-r).toNat * 2 ^ 99) QS (10 ^ 18) x := by
  have cap1 := x1capGeUp h1 h2 hup
  rw [show (633825300114114700748351602688000000000000000000000000000 : Nat) = QS
    from by decide] at cap1
  have hb := capUB_mul QS_pos cap1 capBU
  have hsum := capLB_pow cap2L (c - 152)
  have hX1 := x1_nonneg_ge h1 h2
  have hVs := v_scale_neg (toInt (x1W (zWord m))) c hc
  -- split: jL = pa + (X1·E + B) with pa = -V·2^27 ≥ 0
  have hsplit : (c - 152) * (LN2c * 2 ^ 27) =
      ((c - 152) * (LN2c * 2 ^ 27) -
        ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
          BIASc * 2 ^ 27)) +
        ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
          BIASc * 2 ^ 27) := by
    have hX1n : ((toInt (x1W (zWord m))).toNat : Int) = toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 152) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    have hV0 : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 ≤ 0 := by
      have hVle : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
          143060321855302967919159136223863753677754092301269 ≤ 0 := by
        have hR : (r + 1) * 2 ^ 72 ≤ 0 := by
          have hle : r + 1 ≤ 0 := by omega
          have := mul_le_mul_right_nonneg hle (show (0 : Int) ≤ 2 ^ 72 by omega)
          generalize hgT : (r + 1) * 2 ^ 72 = T at this ⊢
          omega
        generalize hgV' : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
          143060321855302967919159136223863753677754092301269 = V at hr ⊢
        clear cap1 hb hsum hX1 hVs hup hrlo h1 h2 hmx hX1n hBc hLc
        omega
      have := mul_le_mul_right_nonneg hVle (show (0 : Int) ≤ 2 ^ 27 by omega)
      generalize hgV' : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at this ⊢
      clear cap1 hb hsum hX1 hVs hup hrlo hr h1 h2 hmx hX1n hBc hLc
      omega
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hV0 hVs
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 152) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 hb hsum hup hr h1 h2 hc hc2 hmx hrlo hrneg
    omega
  rw [hsplit] at hsum
  have capV := capLB_cancel QS_pos hsum hb
  have hple : (c - 152) * (LN2c * 2 ^ 27) -
      ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        BIASc * 2 ^ 27) ≤ (-r).toNat * 2 ^ 99 := by
    have hsc := mul_le_mul_right_nonneg hrlo (show (0 : Int) ≤ 2 ^ 27 by omega)
    have hX1n : ((toInt (x1W (zWord m))).toNat : Int) = toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 152) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    have er : r * 2 ^ 72 * 2 ^ 27 = r * 2 ^ 99 := by
      rw [Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from by decide]
    rw [er] at hsc
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hsc hVs
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 152) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 hb hsum capV hup hr h1 h2 hc hc2 hmx hsplit hrlo
    omega
  have hmul : ((c - 152) * (LN2c * 2 ^ 27) -
      ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        BIASc * 2 ^ 27)) * QS ≤ (-r).toNat * 2 ^ 99 * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capLB_arg QS_pos hmul capV
  refine capLB_weaken ?_ capR ?_
  · have hm0 : 0 < m := by simp only [Sc] at h1; omega
    have hScp : 0 < Sc := by simp only [Sc]; omega
    exact Nat.mul_pos (Nat.pow_pos (by omega))
      (Nat.mul_pos (Nat.mul_pos hm0 (by omega)) (Nat.mul_pos hScp (by omega)))
  · have hbg := budgetUn_le (j := c - 152) (by omega)
    have hbf := Nat.mul_le_mul_left (x * Sc) hbg
    have eL : 10 ^ 18 * ((10 ^ 40 : Nat) ^ (c - 152) *
        (m * 100000000000000000000000000042 * (Sc * (10 ^ 30 - 499)))) =
        x * Sc * ((10 ^ 29 + 42) * (10 ^ 30 - 499) * (10 ^ 40 : Nat) ^ (c - 152) *
          2 ^ (c - 152) * 10 ^ 18) := by
      rw [hmx, show (100000000000000000000000000042 : Nat) = 10 ^ 29 + 42 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have eR : (2 * (10 ^ 40 - 1)) ^ (c - 152) *
        (1434182936954525181919537618622900000000000000000000000000000 *
          (10 ^ 18 * 10 ^ 30)) * x =
        x * Sc * (10 ^ 77 * (2 * (10 ^ 40 - 1)) ^ (c - 152)) := by
      rw [show (1434182936954525181919537618622900000000000000000000000000000 : Nat) =
        Sc * 10 ^ 29 from by decide]
      have e' : ∀ P : Nat, (10 : Nat) ^ 18 * ((10 : Nat) ^ 29 * ((10 : Nat) ^ 30 * P)) =
          (10 : Nat) ^ 77 * P := by
        intro P
        rw [← Nat.mul_assoc, ← Nat.mul_assoc,
          show ((10 : Nat) ^ 18 * 10 ^ 29 * 10 ^ 30) = 10 ^ 77 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e' ((2 * (10 ^ 40 - 1)) ^ (c - 152))]
    generalize hT1 : 10 ^ 18 * ((10 ^ 40 : Nat) ^ (c - 152) *
      (m * 100000000000000000000000000042 * (Sc * (10 ^ 30 - 499)))) = T1 at eL ⊢
    generalize hT2 : x * Sc * ((10 ^ 29 + 42) * (10 ^ 30 - 499) *
      (10 ^ 40 : Nat) ^ (c - 152) * 2 ^ (c - 152) * 10 ^ 18) = T2 at eL hbf
    generalize hT3 : x * Sc * (10 ^ 77 * (2 * (10 ^ 40 - 1)) ^ (c - 152)) = T3 at hbf eR
    generalize hT4 : (2 * (10 ^ 40 - 1)) ^ (c - 152) *
      (1434182936954525181919537618622900000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 30)) * x = T4 at eR ⊢
    omega

/-- A-atom master for negative outputs, `m < S` branch, negative shift
(exact mantissa). -/
theorem an_lt_neg {m c x : Nat} {r : Int} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc)
    (hc : 152 < c) (hc2 : c ≤ 255)
    (hup : 0 ≤ evalPoly certLtUp (m : Int))
    (hrlo : r * 2 ^ 72 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269)
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269 < (r + 1) * 2 ^ 72)
    (hrneg : r < 0)
    (hmx : m = x * 2 ^ (c - 152)) :
    capLB ((-r).toNat * 2 ^ 99) QS (10 ^ 18) x := by
  have cap1 := x1capLtUp h1 h2 hup
  rw [show (633825300114114700748351602688000000000000000000000000000 : Nat) = QS
    from by decide] at cap1
  have hsum := capLB_mul cap1 (capLB_pow cap2L (c - 152))
  have hX1 := x1_nonpos_lt h1 h2
  have hVs := v_scale_neg (toInt (x1W (zWord m))) c hc
  have hsplit : (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
      (c - 152) * (LN2c * 2 ^ 27) =
      ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        (c - 152) * (LN2c * 2 ^ 27) - BIASc * 2 ^ 27) + BIASc * 2 ^ 27 := by
    have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) = -toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 152) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    have hV0 : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 ≤ 0 := by
      have hVle : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
          143060321855302967919159136223863753677754092301269 ≤ 0 := by
        have hR : (r + 1) * 2 ^ 72 ≤ 0 := by
          have hle : r + 1 ≤ 0 := by omega
          have := mul_le_mul_right_nonneg hle (show (0 : Int) ≤ 2 ^ 72 by omega)
          generalize hgT : (r + 1) * 2 ^ 72 = T at this ⊢
          omega
        generalize hgV' : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
          143060321855302967919159136223863753677754092301269 = V at hr ⊢
        clear cap1 hsum hX1 hVs hup hrlo h1 h2 hmx hX1n hBc hLc
        omega
      have := mul_le_mul_right_nonneg hVle (show (0 : Int) ≤ 2 ^ 27 by omega)
      generalize hgV' : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at this ⊢
      clear cap1 hsum hX1 hVs hup hrlo hr h1 h2 hmx hX1n hBc hLc
      omega
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hV0 hVs
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 152) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-toInt (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(toInt (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 hsum hup hr h1 h2 hc hc2 hmx hrlo hrneg
    omega
  rw [hsplit] at hsum
  have capV := capLB_cancel QS_pos hsum capBU
  have hple : (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
      (c - 152) * (LN2c * 2 ^ 27) - BIASc * 2 ^ 27 ≤ (-r).toNat * 2 ^ 99 := by
    have hsc := mul_le_mul_right_nonneg hrlo (show (0 : Int) ≤ 2 ^ 27 by omega)
    have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) = -toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 152) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    have er : r * 2 ^ 72 * 2 ^ 27 = r * 2 ^ 99 := by
      rw [Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from by decide]
    rw [er] at hsc
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hsc hVs
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 152) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-toInt (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(toInt (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 hsum capV hup hr h1 h2 hc hc2 hmx hsplit hrlo
    omega
  have hmul : ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
      (c - 152) * (LN2c * 2 ^ 27) - BIASc * 2 ^ 27) * QS ≤
      (-r).toNat * 2 ^ 99 * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capLB_arg QS_pos hmul capV
  refine capLB_weaken ?_ capR ?_
  · have hm0 : 0 < m := by simp only [MLO] at h1; omega
    have hScp : 0 < Sc := by simp only [Sc]; omega
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hm0 (by omega)) (Nat.pow_pos (by omega)))
      (Nat.mul_pos hScp (by omega))
  · have hbg := budgetUn_le (j := c - 152) (by omega)
    have hbf := Nat.mul_le_mul_left (x * Sc) hbg
    have eL : 10 ^ 18 * (m * 100000000000000000000000000042 *
        (10 ^ 40 : Nat) ^ (c - 152) * (Sc * (10 ^ 30 - 499))) =
        x * Sc * ((10 ^ 29 + 42) * (10 ^ 30 - 499) * (10 ^ 40 : Nat) ^ (c - 152) *
          2 ^ (c - 152) * 10 ^ 18) := by
      rw [hmx, show (100000000000000000000000000042 : Nat) = 10 ^ 29 + 42 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have eR : 1434182936954525181919537618622900000000000000000000000000000 *
        (2 * (10 ^ 40 - 1)) ^ (c - 152) * (10 ^ 18 * 10 ^ 30) * x =
        x * Sc * (10 ^ 77 * (2 * (10 ^ 40 - 1)) ^ (c - 152)) := by
      rw [show (1434182936954525181919537618622900000000000000000000000000000 : Nat) =
        Sc * 10 ^ 29 from by decide]
      have e' : ∀ P : Nat, (10 : Nat) ^ 18 * ((10 : Nat) ^ 29 * ((10 : Nat) ^ 30 * P)) =
          (10 : Nat) ^ 77 * P := by
        intro P
        rw [← Nat.mul_assoc, ← Nat.mul_assoc,
          show ((10 : Nat) ^ 18 * 10 ^ 29 * 10 ^ 30) = 10 ^ 77 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e' ((2 * (10 ^ 40 - 1)) ^ (c - 152))]
    generalize hT1 : 10 ^ 18 * (m * 100000000000000000000000000042 *
      (10 ^ 40 : Nat) ^ (c - 152) * (Sc * (10 ^ 30 - 499))) = T1 at eL ⊢
    generalize hT2 : x * Sc * ((10 ^ 29 + 42) * (10 ^ 30 - 499) *
      (10 ^ 40 : Nat) ^ (c - 152) * 2 ^ (c - 152) * 10 ^ 18) = T2 at eL hbf
    generalize hT3 : x * Sc * (10 ^ 77 * (2 * (10 ^ 40 - 1)) ^ (c - 152)) = T3 at hbf eR
    generalize hT4 : 1434182936954525181919537618622900000000000000000000000000000 *
      (2 * (10 ^ 40 - 1)) ^ (c - 152) * (10 ^ 18 * 10 ^ 30) * x = T4 at eR ⊢
    omega

/-- The reciprocal strict budget folds from the worst-case mantissa. -/
theorem budgetB_fold {m k : Nat} (hm : 2 ^ 103 ≤ m) (hk : k ≤ 151) :
    (m + 1) * 2 ^ k * ((10 : Nat) ^ 29 * (10 ^ 40 : Nat) ^ k * (10 ^ 18 * 10 ^ 30) *
      10 ^ 30 * 10 ^ 30) ≤
    m * (10 ^ 18 * (10 ^ 30 - 1) * (10 ^ 29 - 42) * (2 * (10 ^ 40 - 1)) ^ k *
      (10 ^ 30 - 501) * (10 ^ 30 + 999)) := by
  have hb := budgetB_le (k := k) hk
  have hcross : (m + 1) * 2 ^ 103 ≤ m * (2 ^ 103 + 1) := by
    have e1 : (m + 1) * 2 ^ 103 = m * 2 ^ 103 + 2 ^ 103 := by
      rw [Nat.add_mul, Nat.one_mul]
    have e2 : m * (2 ^ 103 + 1) = m * 2 ^ 103 + m := by
      rw [Nat.mul_add, Nat.mul_one]
    omega
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 2 ^ 103 by decide)
  calc 2 ^ 103 * ((m + 1) * 2 ^ k * ((10 : Nat) ^ 29 * (10 ^ 40 : Nat) ^ k *
        (10 ^ 18 * 10 ^ 30) * 10 ^ 30 * 10 ^ 30))
      = ((m + 1) * 2 ^ 103) * (2 ^ k * ((10 : Nat) ^ 29 * (10 ^ 40 : Nat) ^ k *
          (10 ^ 18 * 10 ^ 30) * 10 ^ 30 * 10 ^ 30)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (m * (2 ^ 103 + 1)) * (2 ^ k * ((10 : Nat) ^ 29 * (10 ^ 40 : Nat) ^ k *
          (10 ^ 18 * 10 ^ 30) * 10 ^ 30 * 10 ^ 30)) :=
        Nat.mul_le_mul_right _ hcross
    _ = m * ((10 : Nat) ^ 29 * (10 ^ 40 : Nat) ^ k * (10 ^ 18 * 10 ^ 30) * 10 ^ 30 *
          ((2 ^ 103 + 1) * 2 ^ k) * 10 ^ 30) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ m * (10 ^ 18 * (10 ^ 30 - 1) * 2 ^ 103 * (10 ^ 29 - 42) *
          (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 30 - 501) * (10 ^ 30 + 999)) :=
        Nat.mul_le_mul_left _ hb
    _ = 2 ^ 103 * (m * (10 ^ 18 * (10 ^ 30 - 1) * (10 ^ 29 - 42) *
          (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 30 - 501) * (10 ^ 30 + 999))) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- B-atom master for `r + 2 ≤ 0`, `m < S` branch, `k ≥ 0`. -/
theorem bn_lt_pos {m c x : Nat} {r : Int} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc)
    (hc1 : 1 ≤ c) (hc : c ≤ 152)
    (hlo : 0 ≤ evalPoly certLtLo (m : Int))
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269 < (r + 1) * 2 ^ 72)
    (hrneg : r + 2 ≤ 0)
    (hxm : x < (m + 1) * 2 ^ (152 - c)) :
    capUB ((-(r + 2)).toNat * 2 ^ 99) QS (10 ^ 18 * (10 ^ 30 - 1)) (x * 10 ^ 30) := by
  have cap1 := x1capLtLo h1 h2 hlo
  rw [show (633825300114114700748351602688000000000000000000000000000 : Nat) = QS
    from by decide] at cap1
  have hb := capLB_mul (capLB_mul (capLB_pow cap2L (152 - c)) capBL) capEL
  have hX1 := x1_nonpos_lt h1 h2
  have hVs := v_scale_pos (toInt (x1W (zWord m))) c hc
  -- the exponent gap: -V·2^27 ≥ (|r+2|+1)·2^99 + 2^27
  have hgap : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 ≤
      (r + 1) * 2 ^ 99 - 2 ^ 27 := by
    have hsc := mul_le_mul_right_nonneg
      (show toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269 ≤ (r + 1) * 2 ^ 72 - 1
        from by omega) (show (0 : Int) ≤ 2 ^ 27 by omega)
    have er : ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 = (r + 1) * 2 ^ 99 - 2 ^ 27 := by
      rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
        by decide]
      omega
    rw [er] at hsc
    exact hsc
  have hsplit : (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 =
      ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 -
        ((152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99)) +
        ((152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99) := by
    have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) = -toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((152 - c) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    have hr99 : (r + 1) * 2 ^ 99 ≤ -(2 ^ 99) := by
      have hle : r + 1 ≤ -1 := by omega
      have := mul_le_mul_right_nonneg hle (show (0 : Int) ≤ 2 ^ 99 by omega)
      generalize hgT : (r + 1) * 2 ^ 99 = T at this ⊢
      omega
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hgap hVs
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (152 - c) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-toInt (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(toInt (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    generalize hgR : (r + 1) * 2 ^ 99 = R99 at hgap hr99
    clear hX1n hX1 cap1 hb hlo hr h1 h2 hc hc1 hxm hrneg
    omega
  rw [hsplit] at cap1
  have capV := capUB_cancel QS_pos cap1 hb
  have hple : (-(r + 2)).toNat * 2 ^ 99 ≤
      (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 -
        ((152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99) := by
    have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) = -toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((152 - c) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hgap hVs
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (152 - c) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-toInt (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(toInt (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    have hr99 : (r + 1) * 2 ^ 99 = r * 2 ^ 99 + 2 ^ 99 := by
      rw [Int.add_mul, Int.one_mul]
    generalize hgR : (r + 1) * 2 ^ 99 = R99 at hgap hr99
    generalize hgr : r * 2 ^ 99 = R at hr99
    clear hX1n hX1 cap1 hb capV hlo hr h1 h2 hc hc1 hxm hsplit
    omega
  have hmul : (-(r + 2)).toNat * 2 ^ 99 * QS ≤
      ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 -
        ((152 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99)) * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capUB_arg QS_pos hmul capV
  refine capUB_weaken ?_ capR ?_
  · have hm0 : 0 < m := by simp only [MLO] at h1; omega
    exact Nat.mul_pos (Nat.mul_pos hm0 (by omega))
      (Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)) (by omega))
  · have hMLO : 2 ^ 103 ≤ m := by
      simp only [MLO] at h1
      omega
    have hbf := budgetB_fold (k := 152 - c) hMLO (by omega)
    have hScf := Nat.mul_le_mul_left Sc hbf
    have hx1 : x + 1 ≤ (m + 1) * 2 ^ (152 - c) := by omega
    have hxw : (x + 1) * (Sc * ((10 : Nat) ^ 29 * (10 ^ 40 : Nat) ^ (152 - c) *
        (10 ^ 18 * 10 ^ 30) * 10 ^ 30 * 10 ^ 30)) ≤
        (m + 1) * 2 ^ (152 - c) * (Sc * ((10 : Nat) ^ 29 * (10 ^ 40 : Nat) ^ (152 - c) *
          (10 ^ 18 * 10 ^ 30) * 10 ^ 30 * 10 ^ 30)) :=
      Nat.mul_le_mul_right _ hx1
    have eSc1 : Sc * ((m + 1) * 2 ^ (152 - c) * ((10 : Nat) ^ 29 *
        (10 ^ 40 : Nat) ^ (152 - c) * (10 ^ 18 * 10 ^ 30) * 10 ^ 30 * 10 ^ 30)) =
        (m + 1) * 2 ^ (152 - c) * (Sc * ((10 : Nat) ^ 29 * (10 ^ 40 : Nat) ^ (152 - c) *
          (10 ^ 18 * 10 ^ 30) * 10 ^ 30 * 10 ^ 30)) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have eSc2 : Sc * (m * (10 ^ 18 * (10 ^ 30 - 1) * (10 ^ 29 - 42) *
        (2 * (10 ^ 40 - 1)) ^ (152 - c) * (10 ^ 30 - 501) * (10 ^ 30 + 999))) =
        m * (Sc * (10 ^ 18 * (10 ^ 30 - 1) * (10 ^ 29 - 42) *
          (2 * (10 ^ 40 - 1)) ^ (152 - c) * (10 ^ 30 - 501) * (10 ^ 30 + 999))) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [eSc1, eSc2] at hScf
    have eL : 1434182936954525181919537618622900000000000000000000000000000 *
        ((10 ^ 40 : Nat) ^ (152 - c) * (10 ^ 18 * 10 ^ 30) * 10 ^ 30) * (x * 10 ^ 30) ≤
        (x + 1) * (Sc * ((10 : Nat) ^ 29 * (10 ^ 40 : Nat) ^ (152 - c) *
          (10 ^ 18 * 10 ^ 30) * 10 ^ 30 * 10 ^ 30)) := by
      rw [show (1434182936954525181919537618622900000000000000000000000000000 : Nat) =
        Sc * 10 ^ 29 from by decide]
      have eAC : Sc * 10 ^ 29 * ((10 ^ 40 : Nat) ^ (152 - c) * (10 ^ 18 * 10 ^ 30) *
          10 ^ 30) * (x * 10 ^ 30) =
          x * (Sc * ((10 : Nat) ^ 29 * (10 ^ 40 : Nat) ^ (152 - c) *
            (10 ^ 18 * 10 ^ 30) * 10 ^ 30 * 10 ^ 30)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [eAC]
      exact Nat.mul_le_mul_right _ (by omega)
    have eR : m * (Sc * (10 ^ 18 * (10 ^ 30 - 1) * (10 ^ 29 - 42) *
        (2 * (10 ^ 40 - 1)) ^ (152 - c) * (10 ^ 30 - 501) * (10 ^ 30 + 999))) =
        10 ^ 18 * (10 ^ 30 - 1) * (m * 99999999999999999999999999958 *
          ((2 * (10 ^ 40 - 1)) ^ (152 - c) * (Sc * (10 ^ 30 - 501)) * (10 ^ 30 + 999))) := by
      rw [show (99999999999999999999999999958 : Nat) = 10 ^ 29 - 42 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    generalize hT1 : 1434182936954525181919537618622900000000000000000000000000000 *
      ((10 ^ 40 : Nat) ^ (152 - c) * (10 ^ 18 * 10 ^ 30) * 10 ^ 30) * (x * 10 ^ 30) = T1
      at eL ⊢
    generalize hT2 : (x + 1) * (Sc * ((10 : Nat) ^ 29 * (10 ^ 40 : Nat) ^ (152 - c) *
      (10 ^ 18 * 10 ^ 30) * 10 ^ 30 * 10 ^ 30)) = T2 at eL hxw
    generalize hT3 : (m + 1) * 2 ^ (152 - c) * (Sc * ((10 : Nat) ^ 29 *
      (10 ^ 40 : Nat) ^ (152 - c) * (10 ^ 18 * 10 ^ 30) * 10 ^ 30 * 10 ^ 30)) = T3
      at hxw hScf
    generalize hT4 : m * (Sc * (10 ^ 18 * (10 ^ 30 - 1) * (10 ^ 29 - 42) *
      (2 * (10 ^ 40 - 1)) ^ (152 - c) * (10 ^ 30 - 501) * (10 ^ 30 + 999))) = T4
      at hScf eR
    generalize hT5 : 10 ^ 18 * (10 ^ 30 - 1) * (m * 99999999999999999999999999958 *
      ((2 * (10 ^ 40 - 1)) ^ (152 - c) * (Sc * (10 ^ 30 - 501)) * (10 ^ 30 + 999))) = T5
      at eR ⊢
    omega

/-- B-atom master for `r + 2 ≤ 0`, `m ≥ S` branch, negative shift
(exact mantissa). -/
theorem bn_ge_neg {m c x : Nat} {r : Int} (h1 : Sc + 46 ≤ m) (h2 : m < MHI)
    (hc : 152 < c) (hc2 : c ≤ 255)
    (hlo : 0 ≤ evalPoly certGeLo (m : Int))
    (hr : toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269 < (r + 1) * 2 ^ 72)
    (hrneg : r + 2 ≤ 0)
    (hmx : m = x * 2 ^ (c - 152)) :
    capUB ((-(r + 2)).toNat * 2 ^ 99) QS (10 ^ 18 * (10 ^ 30 - 1)) (x * 10 ^ 30) := by
  have cap1 := x1capGeLo h1 h2 hlo
  rw [show (633825300114114700748351602688000000000000000000000000000 : Nat) = QS
    from by decide] at cap1
  have hb := capLB_mul (capLB_mul cap1 capBL) capEL
  have hsum := capUB_pow QS_pos cap2U (c - 152)
  have hX1 := x1_nonneg_ge h1 h2
  have hVs := v_scale_neg (toInt (x1W (zWord m))) c hc
  have hgap : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 ≤
      (r + 1) * 2 ^ 99 - 2 ^ 27 := by
    have hsc := mul_le_mul_right_nonneg
      (show toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269 ≤ (r + 1) * 2 ^ 72 - 1
        from by omega) (show (0 : Int) ≤ 2 ^ 27 by omega)
    have er : ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 = (r + 1) * 2 ^ 99 - 2 ^ 27 := by
      rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
        by decide]
      omega
    rw [er] at hsc
    exact hsc
  have hsplit : (c - 152) * (LN2c * 2 ^ 27) =
      ((c - 152) * (LN2c * 2 ^ 27) -
        ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
          BIASc * 2 ^ 27 + 2 ^ 99)) +
        ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
          BIASc * 2 ^ 27 + 2 ^ 99) := by
    have hX1n : ((toInt (x1W (zWord m))).toNat : Int) = toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 152) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    have hr99 : (r + 1) * 2 ^ 99 ≤ -(2 ^ 99) := by
      have hle : r + 1 ≤ -1 := by omega
      have := mul_le_mul_right_nonneg hle (show (0 : Int) ≤ 2 ^ 99 by omega)
      generalize hgT : (r + 1) * 2 ^ 99 = T at this ⊢
      omega
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hgap hVs
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 152) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    generalize hgR : (r + 1) * 2 ^ 99 = R99 at hgap hr99
    clear hX1n hX1 cap1 hb hsum hlo hr h1 h2 hc hc2 hmx hrneg
    omega
  rw [hsplit] at hsum
  have capV := capUB_cancel QS_pos hsum hb
  have hple : (-(r + 2)).toNat * 2 ^ 99 ≤
      (c - 152) * (LN2c * 2 ^ 27) -
        ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
          BIASc * 2 ^ 27 + 2 ^ 99) := by
    have hX1n : ((toInt (x1W (zWord m))).toNat : Int) = toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 152) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    generalize hgV : (toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      143060321855302967919159136223863753677754092301269) * 2 ^ 27 = V27 at hgap hVs
    generalize hgA : toInt (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 152) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    have hr99 : (r + 1) * 2 ^ 99 = r * 2 ^ 99 + 2 ^ 99 := by
      rw [Int.add_mul, Int.one_mul]
    generalize hgR : (r + 1) * 2 ^ 99 = R99 at hgap hr99
    generalize hgr : r * 2 ^ 99 = R at hr99
    clear hX1n hX1 cap1 hb hsum capV hlo hr h1 h2 hc hc2 hmx hsplit
    omega
  have hmul : (-(r + 2)).toNat * 2 ^ 99 * QS ≤
      ((c - 152) * (LN2c * 2 ^ 27) -
        ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000 +
          BIASc * 2 ^ 27 + 2 ^ 99)) * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capUB_arg QS_pos hmul capV
  refine capUB_weaken ?_ capR ?_
  · have hm0 : 0 < m := by simp only [Sc] at h1; omega
    have hScp : 0 < Sc := by simp only [Sc]; omega
    exact Nat.mul_pos (Nat.pow_pos (by omega))
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hm0 (by omega))
        (Nat.mul_pos hScp (by omega))) (by omega))
  · have hbg := budgetBn_le (j := c - 152) (by omega)
    have hbf := Nat.mul_le_mul_left (x * Sc) hbg
    have eL : (2 * (10 ^ 40 + 1)) ^ (c - 152) *
        (1434182936954525181919537618622900000000000000000000000000000 *
          (10 ^ 18 * 10 ^ 30) * 10 ^ 30) * (x * 10 ^ 30) =
        x * Sc * ((2 * (10 ^ 40 + 1)) ^ (c - 152) * (10 : Nat) ^ 29 *
          (10 ^ 18 * 10 ^ 30) * 10 ^ 30 * 10 ^ 30) := by
      rw [show (1434182936954525181919537618622900000000000000000000000000000 : Nat) =
        Sc * 10 ^ 29 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have eR : 10 ^ 18 * (10 ^ 30 - 1) * ((10 ^ 40 : Nat) ^ (c - 152) *
        (m * 99999999999999999999999999958 * (Sc * (10 ^ 30 - 501)) *
          (10 ^ 30 + 999))) =
        x * Sc * (10 ^ 18 * (10 ^ 30 - 1) * (10 ^ 40 : Nat) ^ (c - 152) * 2 ^ (c - 152) *
          (10 ^ 29 - 42) * (10 ^ 30 - 501) * (10 ^ 30 + 999)) := by
      rw [hmx, show (99999999999999999999999999958 : Nat) = 10 ^ 29 - 42 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    generalize hT1 : (2 * (10 ^ 40 + 1)) ^ (c - 152) *
      (1434182936954525181919537618622900000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 30) * 10 ^ 30) * (x * 10 ^ 30) = T1 at eL ⊢
    generalize hT2 : x * Sc * ((2 * (10 ^ 40 + 1)) ^ (c - 152) * (10 : Nat) ^ 29 *
      (10 ^ 18 * 10 ^ 30) * 10 ^ 30 * 10 ^ 30) = T2 at eL hbf
    generalize hT3 : x * Sc * (10 ^ 18 * (10 ^ 30 - 1) * (10 ^ 40 : Nat) ^ (c - 152) *
      2 ^ (c - 152) * (10 ^ 29 - 42) * (10 ^ 30 - 501) * (10 ^ 30 + 999)) = T3 at eR hbf
    generalize hT4 : 10 ^ 18 * (10 ^ 30 - 1) * ((10 ^ 40 : Nat) ^ (c - 152) *
      (m * 99999999999999999999999999958 * (Sc * (10 ^ 30 - 501)) *
        (10 ^ 30 + 999))) = T4 at eR ⊢
    omega

end LnFloorCert
