import LnProof.Floor.Caps
import LnProof.Floor.Budget
import LnProof.Floor.Model
import LnProof.Floor.Window

open FormalYul
open FormalYul.Preservation

/-!
# Strict-margin floor/error-bound cap assembly

`lnWadToRayBody_floor_bracket` brackets the body output `r` against the pre-shift
accumulator `V = X1·5^27 + ln2k + BIAS` at scale `2^72`. The caps live at
scale `QS = 10^27·2^99`, reached by multiplying `V` by `2^27`. The shared
scale identities feed the `FloorSpecB` strict-margin chains for positive and
nonpositive output exponents.
-/

namespace LnFloorCert
open LnYul Common.Poly Common.Exp LnFloor

/-- `V·2^27` splits into the three cap exponents (positive binade shift). -/
theorem v_scale_pos (X1v : Int) (c : Nat) (hc : c ≤ 160) :
    (X1v * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551560854268589826112230) * 2 ^ 27 =
      X1v * 1000000000000000000000000000 +
        ((160 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) +
        116873961749927929127912020551560854268589826112230 * 2 ^ 27 := by
  have hl : ln2kInt c = (LN2c : Int) * ((160 - c : Nat) : Int) := by
    unfold ln2kInt
    rw [if_pos hc]
  rw [hl, Int.add_mul, Int.add_mul, Int.mul_assoc,
    show (7450580596923828125 : Int) * 2 ^ 27 =
      1000000000000000000000000000 from by decide]
  have e : (LN2c : Int) * ((160 - c : Nat) : Int) * 2 ^ 27 =
      ((160 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [e]

/-- `V·2^27` splits with the `ln 2` term on the other side (negative shift). -/
theorem v_scale_neg (X1v : Int) (c : Nat) (hc : 160 < c) :
    (X1v * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551560854268589826112230) * 2 ^ 27 +
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) =
      X1v * 1000000000000000000000000000 +
        116873961749927929127912020551560854268589826112230 * 2 ^ 27 := by
  have hl : ln2kInt c = -((LN2c : Int) * ((c - 160 : Nat) : Int)) := by
    unfold ln2kInt
    rw [if_neg (by omega)]
  rw [hl, Int.add_mul, Int.add_mul, Int.mul_assoc,
    show (7450580596923828125 : Int) * 2 ^ 27 =
      1000000000000000000000000000 from by decide]
  have e : -((LN2c : Int) * ((c - 160 : Nat) : Int)) * 2 ^ 27 +
      ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = 0 := by
    have e1 : (LN2c : Int) * ((c - 160 : Nat) : Int) * 2 ^ 27 =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [Int.neg_mul, e1]
    omega
  generalize hgA : X1v * 1000000000000000000000000000 = A at *
  generalize hgL : -((LN2c : Int) * ((c - 160 : Nat) : Int)) * 2 ^ 27 = L1 at *
  generalize hgL2 : ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = L2 at *
  omega

/-! ## Strict-margin chains at the body output -/

/-- The lower budget folds from the worst-case mantissa to any `m ≥ 2^95`:
`(m+1)·2^k·(10^40)^k·10^142 ≤ m·(lower-cap product)`. -/
theorem budgetL_fold {m k : Nat} (hm : 2 ^ 95 ≤ m) (hk : k ≤ 159) :
    (m + 1) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) ≤
      m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 31 - 3384) *
        (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18) := by
  have hb := budgetL_le (k := k) hk
  -- (m+1)·2^95 ≤ m·(2^95+1) since 2^95 ≤ m
  have hcross : (m + 1) * 2 ^ 95 ≤ m * (2 ^ 95 + 1) := by
    have e1 : (m + 1) * 2 ^ 95 = m * 2 ^ 95 + 2 ^ 95 := by
      rw [Nat.add_mul, Nat.one_mul]
    have e2 : m * (2 ^ 95 + 1) = m * 2 ^ 95 + m := by
      rw [Nat.mul_add, Nat.mul_one]
    omega
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 2 ^ 95 by decide)
  calc 2 ^ 95 * ((m + 1) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142))
      = ((m + 1) * 2 ^ 95) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm]
    _ ≤ (m * (2 ^ 95 + 1)) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) :=
        Nat.mul_le_mul_right _ hcross
    _ = m * ((2 ^ 95 + 1) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142)) := by
        simp only [Nat.mul_assoc]
    _ = m * ((2 ^ 95 + 1) * 2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) := by
        simp only [Nat.mul_assoc]
    _ ≤ m * (2 ^ 95 * (10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 31 - 3384) *
          (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18) :=
        Nat.mul_le_mul_left _ hb
    _ = 2 ^ 95 * (m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 31 - 3384) *
          (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Lower master chain, `m ≥ S` branch, nonnegative binade shift:
`x/10^18 < e^((r+2)/10^27)` as a `capLB` with one part in `10^30` of
strictness slack. -/
theorem lo_ge_pos {m c x : Nat} {r : Int} (h1 : Sc ≤ m) (h2 : m < MHI)
    (hc1 : 1 ≤ c) (hc : c ≤ 160)
    (hr : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230 < (r + 1) * 2 ^ 72)
    (hr0 : -1 ≤ r)
    (hxm : x < (m + 1) * 2 ^ (160 - c)) :
    capLB ((r + 2).toNat * 2 ^ 99) QS (x * 10 ^ 31) (10 ^ 18 * (10 ^ 31 - 10)) := by
  have cap1 := x1capGeLoF h1 h2
  have cap2 := capLB_pow cap2L (160 - c)
  have cap12 := capLB_mul cap1 cap2
  have cap123 := capLB_mul cap12 capBL
  have cap1234 := capLB_mul cap123 capEL
  -- (r+2)·2^99 dominates the exponent sum
  have hX1 := x1_nonneg_geF h1 h2
  have hVs := v_scale_pos (int256 (x1W (zWord m))) c hc
  have hple : (int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
      (160 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99 ≤
      (r + 2).toNat * 2 ^ 99 := by
    have hsc : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551560854268589826112230) * 2 ^ 27 ≤
        ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 :=
      mul_le_mul_right_nonneg (by omega) (by omega)
    rw [hVs] at hsc
    have hX1n : ((int256 (x1W (zWord m))).toNat : Int) = int256 (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        116873961749927929127912020551560854268589826112230 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((160 - c) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((160 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    have er : ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 = (r + 1) * 2 ^ 99 - 2 ^ 27 := by
      rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
        by decide]
      omega
    rw [er] at hsc
    generalize hgA : int256 (x1W (zWord m)) * 1000000000000000000000000000 = A at hsc
    generalize hgB : ((160 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hsc hLc
    generalize hgC : (160 - c) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hVs hX1 cap1 cap2 cap12 cap123 cap1234 hr h1 h2 hxm hc hc1
    omega
  have hmul : ((int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
      (160 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99) * QS ≤
      (r + 2).toNat * 2 ^ 99 * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capLB_arg QS_pos hmul cap1234
  -- weaken to the strict x target
  refine capLB_weaken ?_ capR ?_
  · have h1' : 0 < (560227709747861399187319382270000000000000000000000000000000 : Nat) *
        ((10 ^ 40 : Nat) ^ (160 - c)) := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
    have h2' : 0 < (560227709747861399187319382270000000000000000000000000000000 : Nat) *
        ((10 ^ 40 : Nat) ^ (160 - c)) * (10 ^ 18 * 10 ^ 31) :=
      Nat.mul_pos h1' (by decide)
    exact Nat.mul_pos h2' (by decide)
  · -- x·10^30·W ≤ Y·(10^18·(10^30−1))
    have hMLO : 2 ^ 95 ≤ m := by
      simp only [Sc] at h1
      omega
    have hb := budgetL_fold (k := 160 - c) hMLO (by omega)
    have hx1 : x + 1 ≤ (m + 1) * 2 ^ (160 - c) := by omega
    have hxw : (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) ≤
        (m + 1) * 2 ^ (160 - c) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) :=
      Nat.mul_le_mul_right _ hx1
    have hfold : (m + 1) * 2 ^ (160 - c) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) *
        10 ^ 142)) ≤
        m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) * (10 ^ 31 - 3384) *
          (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
      have h := Nat.mul_le_mul_left Sc hb
      have e1 : Sc * ((m + 1) * (2 ^ (160 - c) * (10 ^ 40 : Nat) ^ (160 - c) *
          10 ^ 142)) =
          (m + 1) * 2 ^ (160 - c) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have e2 : Sc * (m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
          (10 ^ 31 - 3384) * (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18)) =
          m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) * (10 ^ 31 - 3384) *
            (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e1] at h
      rw [e2] at h
      exact h
    -- assemble: LHS = (x+1-free form) and the W/Y bookkeeping
    have eL : x * 10 ^ 31 * (560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31) * 10 ^ 31) ≤
        (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * 10 ^ 31 from by decide]
      have eAC : x * 10 ^ 31 * (Sc * 10 ^ 31 * (10 ^ 40 : Nat) ^ (160 - c) *
          (10 ^ 18 * 10 ^ 31) * 10 ^ 31) =
          x * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * ((10 : Nat) ^ 31 * (10 ^ 31 *
            (10 ^ 18 * 10 ^ 31 * 10 ^ 31))))) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [eAC, show ((10 : Nat) ^ 31 * (10 ^ 31 * (10 ^ 18 * 10 ^ 31 * 10 ^ 31))) =
        10 ^ 142 from by decide]
      have : x * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) ≤
          (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) :=
        Nat.mul_le_mul_right _ (by omega)
      exact this
    have eR : m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) * (10 ^ 31 - 3384) *
        (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18) * Sc =
        m * 9999999999999999999999999996615 * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
          (Sc * (10 ^ 31 - 3384)) * (10 ^ 31 + 9990) * (10 ^ 18 * (10 ^ 31 - 10)) := by
      rw [show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    generalize hT1 : x * 10 ^ 31 *
      (560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31) * 10 ^ 31) = T1 at eL ⊢
    generalize hT2 : (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) = T2
      at eL hxw
    generalize hT3 : (m + 1) * 2 ^ (160 - c) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) *
      10 ^ 142)) = T3 at hxw hfold
    generalize hT4 : m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
      (10 ^ 31 - 3384) * (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18) * Sc = T4
      at hfold eR
    generalize hT5 : m * 9999999999999999999999999996615 *
      (2 * (10 ^ 40 - 1)) ^ (160 - c) * (Sc * (10 ^ 31 - 3384)) * (10 ^ 31 + 9990) *
      (10 ^ 18 * (10 ^ 31 - 10)) = T5 at eR ⊢
    omega

/-- Lower master chain, `m ≥ S` branch, negative binade shift. -/
theorem lo_ge_neg {m c x : Nat} {r : Int} (h1 : Sc ≤ m) (h2 : m < MHI)
    (hc : 160 < c) (hc2 : c ≤ 255)
    (hr : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230 < (r + 1) * 2 ^ 72)
    (hrlo : r * 2 ^ 72 ≤ int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230)
    (hr0 : -1 ≤ r)
    (hmx : m = x * 2 ^ (c - 160)) :
    capLB ((r + 2).toNat * 2 ^ 99) QS (x * 10 ^ 31) (10 ^ 18 * (10 ^ 31 - 10)) := by
  have cap1 := x1capGeLoF h1 h2
  have cap1B := capLB_mul cap1 capBL
  have cap1BE := capLB_mul cap1B capEL
  have hX1 := x1_nonneg_geF h1 h2
  have hVs := v_scale_neg (int256 (x1W (zWord m))) c hc
  have hVnn : -(2 ^ 99) ≤ (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 := by
    have h0 : -(2 ^ 72) ≤ r * 2 ^ 72 := by
      have := mul_le_mul_right_nonneg (show (-1 : Int) ≤ r from hr0)
        (show (0 : Int) ≤ 2 ^ 72 by omega)
      generalize hgT : r * 2 ^ 72 = T at this ⊢
      omega
    have hg : -(2 ^ 72) ≤ int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551560854268589826112230 := by
      generalize hgV : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551560854268589826112230 = V at hrlo ⊢
      omega
    have := mul_le_mul_right_nonneg hg (show (0 : Int) ≤ 2 ^ 27 by omega)
    generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 = V27 at this ⊢
    have e : (-(2 ^ 72) : Int) * 2 ^ 27 = -(2 ^ 99) := by decide
    omega
  have hsplit : (int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
      BIASc * 2 ^ 27 + 2 ^ 99 =
      ((int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        BIASc * 2 ^ 27 + 2 ^ 99 - (c - 160) * (LN2c * 2 ^ 27)) +
        (c - 160) * (LN2c * 2 ^ 27) := by
    have hX1n : ((int256 (x1W (zWord m))).toNat : Int) = int256 (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        116873961749927929127912020551560854268589826112230 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 160) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 = V27 at hVnn hVs
    generalize hgA : int256 (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 160) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 cap1B cap1BE hr h1 h2 hc hc2 hmx
    omega
  rw [hsplit] at cap1BE
  have capV := capLB_cancel QS_pos cap1BE (capUB_pow QS_pos cap2U (c - 160))
  have hple : (int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
      BIASc * 2 ^ 27 + 2 ^ 99 - (c - 160) * (LN2c * 2 ^ 27) ≤
      (r + 2).toNat * 2 ^ 99 := by
    have hsc : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551560854268589826112230) * 2 ^ 27 ≤
        ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 :=
      mul_le_mul_right_nonneg (by omega) (by omega)
    have er : ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 = (r + 1) * 2 ^ 99 - 2 ^ 27 := by
      rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
        by decide]
      omega
    rw [er] at hsc
    have hX1n : ((int256 (x1W (zWord m))).toNat : Int) = int256 (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        116873961749927929127912020551560854268589826112230 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 160) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 = V27 at hsc hVs hVnn
    generalize hgA : int256 (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 160) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 cap1B cap1BE capV hr h1 h2 hc hc2 hmx hsplit
    omega
  have hmul : ((int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
      BIASc * 2 ^ 27 + 2 ^ 99 - (c - 160) * (LN2c * 2 ^ 27)) * QS ≤
      (r + 2).toNat * 2 ^ 99 * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capLB_arg QS_pos hmul capV
  refine capLB_weaken ?_ capR ?_
  · have h1' : 0 < (560227709747861399187319382270000000000000000000000000000000 : Nat) *
        (10 ^ 18 * 10 ^ 31) * 10 ^ 31 := by decide
    exact Nat.mul_pos h1' (Nat.pow_pos (by decide))
  · -- x·10^30·W ≤ Y·(10^18·(10^30−1)) with exact mantissa
    have hb := budgetLn_le (j := c - 160) (by omega)
    have hbf := Nat.mul_le_mul_left (x * Sc) hb
    have eL : x * 10 ^ 31 *
        (560227709747861399187319382270000000000000000000000000000000 *
          (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * (2 * (10 ^ 40 + 1)) ^ (c - 160)) =
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
    have eR : m * 9999999999999999999999999996615 * (Sc * (10 ^ 31 - 3384)) *
        (10 ^ 31 + 9990) * ((10 ^ 40 : Nat) ^ (c - 160)) * (10 ^ 18 * (10 ^ 31 - 10)) =
        x * Sc * (2 ^ (c - 160) * (10 ^ 40 : Nat) ^ (c - 160) * (10 ^ 31 - 3385) *
          (10 ^ 31 - 3384) * (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18) := by
      rw [hmx, show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    generalize hT1 : x * 10 ^ 31 *
      (560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * (2 * (10 ^ 40 + 1)) ^ (c - 160)) = T1 at eL ⊢
    generalize hT2 : x * Sc * ((10 : Nat) ^ 142 * (2 * (10 ^ 40 + 1)) ^ (c - 160)) = T2
      at eL hbf
    generalize hT3 : x * Sc * (2 ^ (c - 160) * (10 ^ 40 : Nat) ^ (c - 160) *
      (10 ^ 31 - 3385) * (10 ^ 31 - 3384) * (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18) = T3
      at eR hbf
    generalize hT4 : m * 9999999999999999999999999996615 * (Sc * (10 ^ 31 - 3384)) *
      (10 ^ 31 + 9990) * ((10 ^ 40 : Nat) ^ (c - 160)) * (10 ^ 18 * (10 ^ 31 - 10)) = T4
      at eR ⊢
    omega

/-- Lower master chain, `m < S` branch, nonnegative binade shift. -/
theorem lo_lt_pos {m c x : Nat} {r : Int} (h1 : MLO ≤ m) (h2 : m < Sc)
    (hc1 : 1 ≤ c) (hc : c ≤ 160)
    (hr : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230 < (r + 1) * 2 ^ 72)
    (hrlo : r * 2 ^ 72 ≤ int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230)
    (hr0 : -1 ≤ r)
    (hxm : x < (m + 1) * 2 ^ (160 - c)) :
    capLB ((r + 2).toNat * 2 ^ 99) QS (x * 10 ^ 31) (10 ^ 18 * (10 ^ 31 - 10)) := by
  have cap1 := x1capLtLoF h1 h2
  have hsum := capLB_mul (capLB_mul (capLB_pow cap2L (160 - c)) capBL) capEL
  have hX1 := x1_nonpos_ltF h1 h2
  have hVs := v_scale_pos (int256 (x1W (zWord m))) c hc
  have hVnn : -(2 ^ 99) ≤ (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 := by
    have h0 : -(2 ^ 72) ≤ r * 2 ^ 72 := by
      have := mul_le_mul_right_nonneg (show (-1 : Int) ≤ r from hr0)
        (show (0 : Int) ≤ 2 ^ 72 by omega)
      generalize hgT : r * 2 ^ 72 = T at this ⊢
      omega
    have hg : -(2 ^ 72) ≤ int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551560854268589826112230 := by
      generalize hgV : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551560854268589826112230 = V at hrlo ⊢
      omega
    have := mul_le_mul_right_nonneg hg (show (0 : Int) ≤ 2 ^ 27 by omega)
    generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 = V27 at this ⊢
    have e : (-(2 ^ 72) : Int) * 2 ^ 27 = -(2 ^ 99) := by decide
    omega
  have hsplit : (160 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99 =
      ((160 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99 -
        (-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000) +
        (-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 := by
    have hX1n : (((-int256 (x1W (zWord m))).toNat : Nat) : Int) = -int256 (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        116873961749927929127912020551560854268589826112230 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((160 - c) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((160 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 = V27 at hVnn hVs
    generalize hgA : int256 (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((160 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (160 - c) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-int256 (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(int256 (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 hsum hr h1 h2 hc hc1 hxm hrlo
    omega
  rw [hsplit] at hsum
  have capV := capLB_cancel QS_pos hsum cap1
  have hple : (160 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99 -
      (-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 ≤
      (r + 2).toNat * 2 ^ 99 := by
    have hsc : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551560854268589826112230) * 2 ^ 27 ≤
        ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 :=
      mul_le_mul_right_nonneg (by omega) (by omega)
    have er : ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 = (r + 1) * 2 ^ 99 - 2 ^ 27 := by
      rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
        by decide]
      omega
    rw [er] at hsc
    have hX1n : (((-int256 (x1W (zWord m))).toNat : Nat) : Int) = -int256 (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        116873961749927929127912020551560854268589826112230 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((160 - c) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((160 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 = V27 at hsc hVs hVnn
    generalize hgA : int256 (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((160 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (160 - c) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-int256 (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(int256 (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 hsum capV hr h1 h2 hc hc1 hxm hsplit hrlo
    omega
  have hmul : ((160 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99 -
      (-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000) * QS ≤
      (r + 2).toNat * 2 ^ 99 * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capLB_arg QS_pos hmul capV
  refine capLB_weaken ?_ capR ?_
  · have h1' : 0 < (10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31) * 10 ^ 31 :=
      Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by decide)) (by decide)) (by decide)
    exact Nat.mul_pos h1' (by decide)
  · have hMLO : 2 ^ 95 ≤ m := by
      simp only [MLO] at h1
      omega
    have hb := budgetL_fold (k := 160 - c) hMLO (by omega)
    have hx1 : x + 1 ≤ (m + 1) * 2 ^ (160 - c) := by omega
    have hxw : (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) ≤
        (m + 1) * 2 ^ (160 - c) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) :=
      Nat.mul_le_mul_right _ hx1
    have hfold : (m + 1) * 2 ^ (160 - c) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) *
        10 ^ 142)) ≤
        m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) * (10 ^ 31 - 3384) *
          (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
      have h := Nat.mul_le_mul_left Sc hb
      have e1 : Sc * ((m + 1) * (2 ^ (160 - c) * (10 ^ 40 : Nat) ^ (160 - c) *
          10 ^ 142)) =
          (m + 1) * 2 ^ (160 - c) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have e2 : Sc * (m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
          (10 ^ 31 - 3384) * (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18)) =
          m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) * (10 ^ 31 - 3384) *
            (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e1] at h
      rw [e2] at h
      exact h
    have eL : x * 10 ^ 31 * ((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31) *
        10 ^ 31 * 560227709747861399187319382270000000000000000000000000000000) ≤
        (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * 10 ^ 31 from by decide]
      have eAC : x * 10 ^ 31 * ((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31) *
          10 ^ 31 * (Sc * 10 ^ 31)) =
          x * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * ((10 : Nat) ^ 18 * ((10 : Nat) ^ 31 *
            ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 * (10 : Nat) ^ 31)))))) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [eAC, show ((10 : Nat) ^ 18 * ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 *
        ((10 : Nat) ^ 31 * (10 : Nat) ^ 31)))) = 10 ^ 142 from by decide]
      have : x * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) ≤
          (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) :=
        Nat.mul_le_mul_right _ (by omega)
      exact this
    have eR : (2 * (10 ^ 40 - 1)) ^ (160 - c) * (Sc * (10 ^ 31 - 3384)) *
        (10 ^ 31 + 9990) * (m * 9999999999999999999999999996615) *
        (10 ^ 18 * (10 ^ 31 - 10)) =
        m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) * (10 ^ 31 - 3384) *
          (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
      rw [show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    generalize hT1 : x * 10 ^ 31 * ((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31) *
      10 ^ 31 * 560227709747861399187319382270000000000000000000000000000000) = T1
      at eL ⊢
    generalize hT2 : (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) = T2
      at eL hxw
    generalize hT3 : (m + 1) * 2 ^ (160 - c) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) *
      10 ^ 142)) = T3 at hxw hfold
    generalize hT4 : m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
      (10 ^ 31 - 3384) * (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18) * Sc = T4
      at hfold eR
    generalize hT5 : (2 * (10 ^ 40 - 1)) ^ (160 - c) * (Sc * (10 ^ 31 - 3384)) *
      (10 ^ 31 + 9990) * (m * 9999999999999999999999999996615) *
      (10 ^ 18 * (10 ^ 31 - 10)) = T5 at eR ⊢
    omega

/-- Lower master chain, `m < S` branch, negative binade shift
(exact mantissa). -/
theorem lo_lt_neg {m c x : Nat} {r : Int} (h1 : MLO ≤ m) (h2 : m < Sc)
    (hc : 160 < c) (hc2 : c ≤ 255)
    (hr : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230 < (r + 1) * 2 ^ 72)
    (hrlo : r * 2 ^ 72 ≤ int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230)
    (hr0 : -1 ≤ r)
    (hmx : m = x * 2 ^ (c - 160)) :
    capLB ((r + 2).toNat * 2 ^ 99) QS (x * 10 ^ 31) (10 ^ 18 * (10 ^ 31 - 10)) := by
  have cap1 := x1capLtLoF h1 h2
  have hb := capUB_mul QS_pos cap1 (capUB_pow QS_pos cap2U (c - 160))
  have hsum := capLB_mul capBL capEL
  have hX1 := x1_nonpos_ltF h1 h2
  have hVs := v_scale_neg (int256 (x1W (zWord m))) c hc
  have hVnn : -(2 ^ 99) ≤ (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 := by
    have h0 : -(2 ^ 72) ≤ r * 2 ^ 72 := by
      have := mul_le_mul_right_nonneg (show (-1 : Int) ≤ r from hr0)
        (show (0 : Int) ≤ 2 ^ 72 by omega)
      generalize hgT : r * 2 ^ 72 = T at this ⊢
      omega
    have hg : -(2 ^ 72) ≤ int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551560854268589826112230 := by
      generalize hgV : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551560854268589826112230 = V at hrlo ⊢
      omega
    have := mul_le_mul_right_nonneg hg (show (0 : Int) ≤ 2 ^ 27 by omega)
    generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 = V27 at this ⊢
    have e : (-(2 ^ 72) : Int) * 2 ^ 27 = -(2 ^ 99) := by decide
    omega
  have hsplit : BIASc * 2 ^ 27 + 2 ^ 99 =
      (BIASc * 2 ^ 27 + 2 ^ 99 -
        ((-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
          (c - 160) * (LN2c * 2 ^ 27))) +
        ((-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
          (c - 160) * (LN2c * 2 ^ 27)) := by
    have hX1n : (((-int256 (x1W (zWord m))).toNat : Nat) : Int) = -int256 (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        116873961749927929127912020551560854268589826112230 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 160) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 = V27 at hVnn hVs
    generalize hgA : int256 (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 160) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-int256 (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(int256 (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 hb hsum hr h1 h2 hc hc2 hmx hrlo
    omega
  rw [hsplit] at hsum
  have capV := capLB_cancel QS_pos hsum hb
  have hple : BIASc * 2 ^ 27 + 2 ^ 99 -
      ((-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        (c - 160) * (LN2c * 2 ^ 27)) ≤
      (r + 2).toNat * 2 ^ 99 := by
    have hsc : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551560854268589826112230) * 2 ^ 27 ≤
        ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 :=
      mul_le_mul_right_nonneg (by omega) (by omega)
    have er : ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 = (r + 1) * 2 ^ 99 - 2 ^ 27 := by
      rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
        by decide]
      omega
    rw [er] at hsc
    have hX1n : (((-int256 (x1W (zWord m))).toNat : Nat) : Int) = -int256 (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        116873961749927929127912020551560854268589826112230 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 160) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 = V27 at hsc hVs hVnn
    generalize hgA : int256 (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 160) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-int256 (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(int256 (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    clear hX1n hX1 cap1 hb hsum capV hr h1 h2 hc hc2 hmx hsplit hrlo
    omega
  have hmul : (BIASc * 2 ^ 27 + 2 ^ 99 -
      ((-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        (c - 160) * (LN2c * 2 ^ 27))) * QS ≤
      (r + 2).toNat * 2 ^ 99 * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capLB_arg QS_pos hmul capV
  refine capLB_weaken ?_ capR ?_
  · have h1' : 0 < (10 ^ 18 * 10 ^ 31 * 10 ^ 31 : Nat) *
        (560227709747861399187319382270000000000000000000000000000000 *
          (2 * (10 ^ 40 + 1)) ^ (c - 160)) :=
      Nat.mul_pos (by decide) (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))
    exact h1'
  · have hbg := budgetLn_le (j := c - 160) (by omega)
    have hbf := Nat.mul_le_mul_left (x * Sc) hbg
    have eL : x * 10 ^ 31 * (10 ^ 18 * 10 ^ 31 * 10 ^ 31 *
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
      have eAC : x * 10 ^ 31 * (10 ^ 18 * 10 ^ 31 * 10 ^ 31 * (Sc * 10 ^ 31 *
          (2 * (10 ^ 40 + 1)) ^ (c - 160))) =
          x * (Sc * ((10 : Nat) ^ 18 * ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 *
            ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 *
              (2 * (10 ^ 40 + 1)) ^ (c - 160))))))) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [eAC, e' ((2 * (10 ^ 40 + 1)) ^ (c - 160))]
      simp only [Nat.mul_assoc]
    have eR : Sc * (10 ^ 31 - 3384) * (10 ^ 31 + 9990) *
        (m * 9999999999999999999999999996615 * (10 ^ 40 : Nat) ^ (c - 160)) *
        (10 ^ 18 * (10 ^ 31 - 10)) =
        x * Sc * (2 ^ (c - 160) * (10 ^ 40 : Nat) ^ (c - 160) * (10 ^ 31 - 3385) *
          (10 ^ 31 - 3384) * (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18) := by
      rw [hmx, show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    generalize hT1 : x * 10 ^ 31 * (10 ^ 18 * 10 ^ 31 * 10 ^ 31 *
      (560227709747861399187319382270000000000000000000000000000000 *
        (2 * (10 ^ 40 + 1)) ^ (c - 160))) = T1 at eL ⊢
    generalize hT2 : x * Sc * ((10 : Nat) ^ 142 * (2 * (10 ^ 40 + 1)) ^ (c - 160)) = T2
      at eL hbf
    generalize hT3 : x * Sc * (2 ^ (c - 160) * (10 ^ 40 : Nat) ^ (c - 160) *
      (10 ^ 31 - 3385) * (10 ^ 31 - 3384) * (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18) = T3
      at eR hbf
    generalize hT4 : Sc * (10 ^ 31 - 3384) * (10 ^ 31 + 9990) *
      (m * 9999999999999999999999999996615 * (10 ^ 40 : Nat) ^ (c - 160)) *
      (10 ^ 18 * (10 ^ 31 - 10)) = T4 at eR ⊢
    omega

/-- The reciprocal strict budget folds from the worst-case mantissa. -/
theorem budgetB_fold {m k : Nat} (hm : 2 ^ 95 ≤ m) (hk : k ≤ 159) :
    (m + 1) * 2 ^ k * ((10 : Nat) ^ 31 * (10 ^ 40 : Nat) ^ k * (10 ^ 18 * 10 ^ 31) *
      10 ^ 31 * 10 ^ 31) ≤
    m * (10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k *
      (10 ^ 31 - 3384) * (10 ^ 31 + 9990)) := by
  have hb := budgetB_le (k := k) hk
  have hcross : (m + 1) * 2 ^ 95 ≤ m * (2 ^ 95 + 1) := by
    have e1 : (m + 1) * 2 ^ 95 = m * 2 ^ 95 + 2 ^ 95 := by
      rw [Nat.add_mul, Nat.one_mul]
    have e2 : m * (2 ^ 95 + 1) = m * 2 ^ 95 + m := by
      rw [Nat.mul_add, Nat.mul_one]
    omega
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 2 ^ 95 by decide)
  calc 2 ^ 95 * ((m + 1) * 2 ^ k * ((10 : Nat) ^ 31 * (10 ^ 40 : Nat) ^ k *
        (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31))
      = ((m + 1) * 2 ^ 95) * (2 ^ k * ((10 : Nat) ^ 31 * (10 ^ 40 : Nat) ^ k *
          (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (m * (2 ^ 95 + 1)) * (2 ^ k * ((10 : Nat) ^ 31 * (10 ^ 40 : Nat) ^ k *
          (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31)) :=
        Nat.mul_le_mul_right _ hcross
    _ = m * ((10 : Nat) ^ 31 * (10 ^ 40 : Nat) ^ k * (10 ^ 18 * 10 ^ 31) * 10 ^ 31 *
          ((2 ^ 95 + 1) * 2 ^ k) * 10 ^ 31) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ m * (10 ^ 18 * (10 ^ 31 - 10) * 2 ^ 95 * (10 ^ 31 - 3385) *
          (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 31 - 3384) * (10 ^ 31 + 9990)) :=
        Nat.mul_le_mul_left _ hb
    _ = 2 ^ 95 * (m * (10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 31 - 3385) *
          (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 31 - 3384) * (10 ^ 31 + 9990))) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- B-atom master for `r + 2 ≤ 0`, `m < S` branch, `k ≥ 0`. -/
theorem bn_lt_pos {m c x : Nat} {r : Int} (h1 : MLO ≤ m) (h2 : m < Sc)
    (hc1 : 1 ≤ c) (hc : c ≤ 160)
    (hr : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230 < (r + 1) * 2 ^ 72)
    (hrneg : r + 2 ≤ 0)
    (hxm : x < (m + 1) * 2 ^ (160 - c)) :
    capUB ((-(r + 2)).toNat * 2 ^ 99) QS (10 ^ 18 * (10 ^ 31 - 10)) (x * 10 ^ 31) := by
  have cap1 := x1capLtLoF h1 h2
  have hb := capLB_mul (capLB_mul (capLB_pow cap2L (160 - c)) capBL) capEL
  have hX1 := x1_nonpos_ltF h1 h2
  have hVs := v_scale_pos (int256 (x1W (zWord m))) c hc
  -- the exponent gap: -V·2^27 ≥ (|r+2|+1)·2^99 + 2^27
  have hgap : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 ≤
      (r + 1) * 2 ^ 99 - 2 ^ 27 := by
    have hsc := mul_le_mul_right_nonneg
      (show int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551560854268589826112230 ≤ (r + 1) * 2 ^ 72 - 1
        from by omega) (show (0 : Int) ≤ 2 ^ 27 by omega)
    have er : ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 = (r + 1) * 2 ^ 99 - 2 ^ 27 := by
      rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
        by decide]
      omega
    rw [er] at hsc
    exact hsc
  have hsplit : (-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 =
      ((-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 -
        ((160 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99)) +
        ((160 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99) := by
    have hX1n : (((-int256 (x1W (zWord m))).toNat : Nat) : Int) = -int256 (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        116873961749927929127912020551560854268589826112230 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((160 - c) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((160 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    have hr99 : (r + 1) * 2 ^ 99 ≤ -(2 ^ 99) := by
      have hle : r + 1 ≤ -1 := by omega
      have := mul_le_mul_right_nonneg hle (show (0 : Int) ≤ 2 ^ 99 by omega)
      generalize hgT : (r + 1) * 2 ^ 99 = T at this ⊢
      omega
    generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 = V27 at hgap hVs
    generalize hgA : int256 (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((160 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (160 - c) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-int256 (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(int256 (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    generalize hgR : (r + 1) * 2 ^ 99 = R99 at hgap hr99
    clear hX1n hX1 cap1 hb hr h1 h2 hc hc1 hxm hrneg
    omega
  rw [hsplit] at cap1
  have capV := capUB_cancel QS_pos cap1 hb
  have hple : (-(r + 2)).toNat * 2 ^ 99 ≤
      (-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 -
        ((160 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99) := by
    have hX1n : (((-int256 (x1W (zWord m))).toNat : Nat) : Int) = -int256 (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        116873961749927929127912020551560854268589826112230 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((160 - c) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((160 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 = V27 at hgap hVs
    generalize hgA : int256 (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((160 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (160 - c) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-int256 (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(int256 (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    have hr99 : (r + 1) * 2 ^ 99 = r * 2 ^ 99 + 2 ^ 99 := by
      rw [Int.add_mul, Int.one_mul]
    generalize hgR : (r + 1) * 2 ^ 99 = R99 at hgap hr99
    generalize hgr : r * 2 ^ 99 = R at hr99
    clear hX1n hX1 cap1 hb capV hr h1 h2 hc hc1 hxm hsplit
    omega
  have hmul : (-(r + 2)).toNat * 2 ^ 99 * QS ≤
      ((-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 -
        ((160 - c) * (LN2c * 2 ^ 27) + BIASc * 2 ^ 27 + 2 ^ 99)) * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capUB_arg QS_pos hmul capV
  refine capUB_weaken ?_ capR ?_
  · have hm0 : 0 < m := by simp only [MLO] at h1; omega
    exact Nat.mul_pos (Nat.mul_pos hm0 (by omega))
      (Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)) (by omega))
  · have hMLO : 2 ^ 95 ≤ m := by
      simp only [MLO] at h1
      omega
    have hbf := budgetB_fold (k := 160 - c) hMLO (by omega)
    have hScf := Nat.mul_le_mul_left Sc hbf
    have hx1 : x + 1 ≤ (m + 1) * 2 ^ (160 - c) := by omega
    have hxw : (x + 1) * (Sc * ((10 : Nat) ^ 31 * (10 ^ 40 : Nat) ^ (160 - c) *
        (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31)) ≤
        (m + 1) * 2 ^ (160 - c) * (Sc * ((10 : Nat) ^ 31 * (10 ^ 40 : Nat) ^ (160 - c) *
          (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31)) :=
      Nat.mul_le_mul_right _ hx1
    have eSc1 : Sc * ((m + 1) * 2 ^ (160 - c) * ((10 : Nat) ^ 31 *
        (10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31)) =
        (m + 1) * 2 ^ (160 - c) * (Sc * ((10 : Nat) ^ 31 * (10 ^ 40 : Nat) ^ (160 - c) *
          (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31)) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have eSc2 : Sc * (m * (10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 31 - 3385) *
        (2 * (10 ^ 40 - 1)) ^ (160 - c) * (10 ^ 31 - 3384) * (10 ^ 31 + 9990))) =
        m * (Sc * (10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 31 - 3385) *
          (2 * (10 ^ 40 - 1)) ^ (160 - c) * (10 ^ 31 - 3384) * (10 ^ 31 + 9990))) := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm]
    rw [eSc1, eSc2] at hScf
    have eL : 560227709747861399187319382270000000000000000000000000000000 *
        ((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31) * 10 ^ 31) * (x * 10 ^ 31) ≤
        (x + 1) * (Sc * ((10 : Nat) ^ 31 * (10 ^ 40 : Nat) ^ (160 - c) *
          (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31)) := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * 10 ^ 31 from by decide]
      have eAC : Sc * 10 ^ 31 * ((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31) *
          10 ^ 31) * (x * 10 ^ 31) =
          x * (Sc * ((10 : Nat) ^ 31 * (10 ^ 40 : Nat) ^ (160 - c) *
            (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [eAC]
      exact Nat.mul_le_mul_right _ (by omega)
    have eR : m * (Sc * (10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 31 - 3385) *
        (2 * (10 ^ 40 - 1)) ^ (160 - c) * (10 ^ 31 - 3384) * (10 ^ 31 + 9990))) =
        10 ^ 18 * (10 ^ 31 - 10) * (m * 9999999999999999999999999996615 *
          ((2 * (10 ^ 40 - 1)) ^ (160 - c) * (Sc * (10 ^ 31 - 3384)) * (10 ^ 31 + 9990))) := by
      rw [show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_left_comm]
    generalize hT1 : 560227709747861399187319382270000000000000000000000000000000 *
      ((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31) * 10 ^ 31) * (x * 10 ^ 31) = T1
      at eL ⊢
    generalize hT2 : (x + 1) * (Sc * ((10 : Nat) ^ 31 * (10 ^ 40 : Nat) ^ (160 - c) *
      (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31)) = T2 at eL hxw
    generalize hT3 : (m + 1) * 2 ^ (160 - c) * (Sc * ((10 : Nat) ^ 31 *
      (10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31)) = T3
      at hxw hScf
    generalize hT4 : m * (Sc * (10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 31 - 3385) *
      (2 * (10 ^ 40 - 1)) ^ (160 - c) * (10 ^ 31 - 3384) * (10 ^ 31 + 9990))) = T4
      at hScf eR
    generalize hT5 : 10 ^ 18 * (10 ^ 31 - 10) * (m * 9999999999999999999999999996615 *
      ((2 * (10 ^ 40 - 1)) ^ (160 - c) * (Sc * (10 ^ 31 - 3384)) * (10 ^ 31 + 9990))) = T5
      at eR ⊢
    omega

/-- B-atom master for `r + 2 ≤ 0`, `m ≥ S` branch, negative shift
(exact mantissa). -/
theorem bn_ge_neg {m c x : Nat} {r : Int} (h1 : Sc ≤ m) (h2 : m < MHI)
    (hc : 160 < c) (hc2 : c ≤ 255)
    (hr : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230 < (r + 1) * 2 ^ 72)
    (hrneg : r + 2 ≤ 0)
    (hmx : m = x * 2 ^ (c - 160)) :
    capUB ((-(r + 2)).toNat * 2 ^ 99) QS (10 ^ 18 * (10 ^ 31 - 10)) (x * 10 ^ 31) := by
  have cap1 := x1capGeLoF h1 h2
  have hb := capLB_mul (capLB_mul cap1 capBL) capEL
  have hsum := capUB_pow QS_pos cap2U (c - 160)
  have hX1 := x1_nonneg_geF h1 h2
  have hVs := v_scale_neg (int256 (x1W (zWord m))) c hc
  have hgap : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 ≤
      (r + 1) * 2 ^ 99 - 2 ^ 27 := by
    have hsc := mul_le_mul_right_nonneg
      (show int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551560854268589826112230 ≤ (r + 1) * 2 ^ 72 - 1
        from by omega) (show (0 : Int) ≤ 2 ^ 27 by omega)
    have er : ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 = (r + 1) * 2 ^ 99 - 2 ^ 27 := by
      rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
        by decide]
      omega
    rw [er] at hsc
    exact hsc
  have hsplit : (c - 160) * (LN2c * 2 ^ 27) =
      ((c - 160) * (LN2c * 2 ^ 27) -
        ((int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
          BIASc * 2 ^ 27 + 2 ^ 99)) +
        ((int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
          BIASc * 2 ^ 27 + 2 ^ 99) := by
    have hX1n : ((int256 (x1W (zWord m))).toNat : Int) = int256 (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        116873961749927929127912020551560854268589826112230 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 160) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    have hr99 : (r + 1) * 2 ^ 99 ≤ -(2 ^ 99) := by
      have hle : r + 1 ≤ -1 := by omega
      have := mul_le_mul_right_nonneg hle (show (0 : Int) ≤ 2 ^ 99 by omega)
      generalize hgT : (r + 1) * 2 ^ 99 = T at this ⊢
      omega
    generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 = V27 at hgap hVs
    generalize hgA : int256 (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 160) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    generalize hgR : (r + 1) * 2 ^ 99 = R99 at hgap hr99
    clear hX1n hX1 cap1 hb hsum hr h1 h2 hc hc2 hmx hrneg
    omega
  rw [hsplit] at hsum
  have capV := capUB_cancel QS_pos hsum hb
  have hple : (-(r + 2)).toNat * 2 ^ 99 ≤
      (c - 160) * (LN2c * 2 ^ 27) -
        ((int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
          BIASc * 2 ^ 27 + 2 ^ 99) := by
    have hX1n : ((int256 (x1W (zWord m))).toNat : Int) = int256 (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        116873961749927929127912020551560854268589826112230 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 160) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 = V27 at hgap hVs
    generalize hgA : int256 (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 160) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    have hr99 : (r + 1) * 2 ^ 99 = r * 2 ^ 99 + 2 ^ 99 := by
      rw [Int.add_mul, Int.one_mul]
    generalize hgR : (r + 1) * 2 ^ 99 = R99 at hgap hr99
    generalize hgr : r * 2 ^ 99 = R at hr99
    clear hX1n hX1 cap1 hb hsum capV hr h1 h2 hc hc2 hmx hsplit
    omega
  have hmul : (-(r + 2)).toNat * 2 ^ 99 * QS ≤
      ((c - 160) * (LN2c * 2 ^ 27) -
        ((int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
          BIASc * 2 ^ 27 + 2 ^ 99)) * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capUB_arg QS_pos hmul capV
  refine capUB_weaken ?_ capR ?_
  · have hm0 : 0 < m := by simp only [Sc] at h1; omega
    have hScp : 0 < Sc := by simp only [Sc]; omega
    exact Nat.mul_pos (Nat.pow_pos (by omega))
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hm0 (by omega))
        (Nat.mul_pos hScp (by omega))) (by omega))
  · have hbg := budgetBn_le (j := c - 160) (by omega)
    have hbf := Nat.mul_le_mul_left (x * Sc) hbg
    have eL : (2 * (10 ^ 40 + 1)) ^ (c - 160) *
        (560227709747861399187319382270000000000000000000000000000000 *
          (10 ^ 18 * 10 ^ 31) * 10 ^ 31) * (x * 10 ^ 31) =
        x * Sc * ((2 * (10 ^ 40 + 1)) ^ (c - 160) * (10 : Nat) ^ 31 *
          (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31) := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * 10 ^ 31 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have eR : 10 ^ 18 * (10 ^ 31 - 10) * ((10 ^ 40 : Nat) ^ (c - 160) *
        (m * 9999999999999999999999999996615 * (Sc * (10 ^ 31 - 3384)) *
          (10 ^ 31 + 9990))) =
        x * Sc * (10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 40 : Nat) ^ (c - 160) * 2 ^ (c - 160) *
          (10 ^ 31 - 3385) * (10 ^ 31 - 3384) * (10 ^ 31 + 9990)) := by
      rw [hmx, show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    generalize hT1 : (2 * (10 ^ 40 + 1)) ^ (c - 160) *
      (560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31) * 10 ^ 31) * (x * 10 ^ 31) = T1 at eL ⊢
    generalize hT2 : x * Sc * ((2 * (10 ^ 40 + 1)) ^ (c - 160) * (10 : Nat) ^ 31 *
      (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31) = T2 at eL hbf
    generalize hT3 : x * Sc * (10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 40 : Nat) ^ (c - 160) *
      2 ^ (c - 160) * (10 ^ 31 - 3385) * (10 ^ 31 - 3384) * (10 ^ 31 + 9990)) = T3 at eR hbf
    generalize hT4 : 10 ^ 18 * (10 ^ 31 - 10) * ((10 ^ 40 : Nat) ^ (c - 160) *
      (m * 9999999999999999999999999996615 * (Sc * (10 ^ 31 - 3384)) *
        (10 ^ 31 + 9990))) = T4 at eR ⊢
    omega

/-- B-atom master for `r + 2 ≤ 0`, `m < S` branch, negative shift
(exact mantissa). -/
theorem bn_lt_neg {m c x : Nat} {r : Int} (h1 : MLO ≤ m) (h2 : m < Sc)
    (hc : 160 < c) (hc2 : c ≤ 255)
    (hr : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230 < (r + 1) * 2 ^ 72)
    (hrneg : r + 2 ≤ 0)
    (hmx : m = x * 2 ^ (c - 160)) :
    capUB ((-(r + 2)).toNat * 2 ^ 99) QS (10 ^ 18 * (10 ^ 31 - 10)) (x * 10 ^ 31) := by
  have cap1 := x1capLtLoF h1 h2
  have hsum := capUB_mul QS_pos cap1 (capUB_pow QS_pos cap2U (c - 160))
  have hb := capLB_mul capBL capEL
  have hX1 := x1_nonpos_ltF h1 h2
  have hVs := v_scale_neg (int256 (x1W (zWord m))) c hc
  have hgap : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 ≤
      (r + 1) * 2 ^ 99 - 2 ^ 27 := by
    have hsc := mul_le_mul_right_nonneg
      (show int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551560854268589826112230 ≤ (r + 1) * 2 ^ 72 - 1
        from by omega) (show (0 : Int) ≤ 2 ^ 27 by omega)
    have er : ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 = (r + 1) * 2 ^ 99 - 2 ^ 27 := by
      rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
        by decide]
      omega
    rw [er] at hsc
    exact hsc
  have hsplit : (-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
      (c - 160) * (LN2c * 2 ^ 27) =
      ((-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        (c - 160) * (LN2c * 2 ^ 27) - (BIASc * 2 ^ 27 + 2 ^ 99)) +
        (BIASc * 2 ^ 27 + 2 ^ 99) := by
    have hX1n : (((-int256 (x1W (zWord m))).toNat : Nat) : Int) = -int256 (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        116873961749927929127912020551560854268589826112230 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 160) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    have hr99 : (r + 1) * 2 ^ 99 ≤ -(2 ^ 99) := by
      have hle : r + 1 ≤ -1 := by omega
      have := mul_le_mul_right_nonneg hle (show (0 : Int) ≤ 2 ^ 99 by omega)
      generalize hgT : (r + 1) * 2 ^ 99 = T at this ⊢
      omega
    generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 = V27 at hgap hVs
    generalize hgA : int256 (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 160) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-int256 (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(int256 (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    generalize hgR : (r + 1) * 2 ^ 99 = R99 at hgap hr99
    clear hX1n hX1 cap1 hsum hb hr h1 h2 hc hc2 hmx hrneg
    omega
  rw [hsplit] at hsum
  have capV := capUB_cancel QS_pos hsum hb
  have hple : (-(r + 2)).toNat * 2 ^ 99 ≤
      (-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        (c - 160) * (LN2c * 2 ^ 27) - (BIASc * 2 ^ 27 + 2 ^ 99) := by
    have hX1n : (((-int256 (x1W (zWord m))).toNat : Nat) : Int) = -int256 (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * 2 ^ 27 : Nat) : Int) =
        116873961749927929127912020551560854268589826112230 * 2 ^ 27 := by
      decide +kernel
    have hLc : (((c - 160) * (LN2c * 2 ^ 27) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.natCast_mul]
      rfl
    generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 = V27 at hgap hVs
    generalize hgA : int256 (x1W (zWord m)) * 1000000000000000000000000000 = A at hVs
    generalize hgB : ((c - 160 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = B at hVs hLc
    generalize hgC : (c - 160) * (LN2c * 2 ^ 27) = Cn at hLc ⊢
    generalize hgD : (-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n]
      rw [show (-int256 (x1W (zWord m))) * ((1000000000000000000000000000 : Nat) : Int) =
        -(int256 (x1W (zWord m)) * ((1000000000000000000000000000 : Nat) : Int)) from by
          rw [Int.neg_mul]]
      rfl
    generalize hgE : (BIASc * 2 ^ 27 : Nat) = E at hBc ⊢
    have hr99 : (r + 1) * 2 ^ 99 = r * 2 ^ 99 + 2 ^ 99 := by
      rw [Int.add_mul, Int.one_mul]
    generalize hgR : (r + 1) * 2 ^ 99 = R99 at hgap hr99
    generalize hgr : r * 2 ^ 99 = R at hr99
    clear hX1n hX1 cap1 hsum hb capV hr h1 h2 hc hc2 hmx hsplit
    omega
  have hmul : (-(r + 2)).toNat * 2 ^ 99 * QS ≤
      ((-int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
        (c - 160) * (LN2c * 2 ^ 27) - (BIASc * 2 ^ 27 + 2 ^ 99)) * QS :=
    Nat.mul_le_mul_right _ hple
  have capR := capUB_arg QS_pos hmul capV
  refine capUB_weaken ?_ capR ?_
  · have hm0 : 0 < m := by simp only [MLO] at h1; omega
    have hScp : 0 < Sc := by simp only [Sc]; omega
    exact Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos hm0 (by omega)) (Nat.pow_pos (by omega)))
      (Nat.mul_pos (Nat.mul_pos hScp (by omega)) (by omega))
  · have hbg := budgetBn_le (j := c - 160) (by omega)
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
        (10 ^ 40 : Nat) ^ (c - 160) * (Sc * (10 ^ 31 - 3384) * (10 ^ 31 + 9990))) =
        x * Sc * (10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 40 : Nat) ^ (c - 160) * 2 ^ (c - 160) *
          (10 ^ 31 - 3385) * (10 ^ 31 - 3384) * (10 ^ 31 + 9990)) := by
      rw [hmx, show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    generalize hT1 : 560227709747861399187319382270000000000000000000000000000000 *
      (2 * (10 ^ 40 + 1)) ^ (c - 160) * ((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
      (x * 10 ^ 31) = T1 at eL ⊢
    generalize hT2 : x * Sc * ((2 * (10 ^ 40 + 1)) ^ (c - 160) * (10 : Nat) ^ 31 *
      (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31) = T2 at eL hbf
    generalize hT3 : x * Sc * (10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 40 : Nat) ^ (c - 160) *
      2 ^ (c - 160) * (10 ^ 31 - 3385) * (10 ^ 31 - 3384) * (10 ^ 31 + 9990)) = T3 at eR hbf
    generalize hT4 : 10 ^ 18 * (10 ^ 31 - 10) * (m * 9999999999999999999999999996615 *
      (10 ^ 40 : Nat) ^ (c - 160) * (Sc * (10 ^ 31 - 3384) * (10 ^ 31 + 9990))) = T4
      at eR ⊢
    omega

end LnFloorCert
