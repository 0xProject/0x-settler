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

end LnFloorCert
