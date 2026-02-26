/-
  Step monotonicity for overestimates.
  When z² > x, the Babylonian step is non-decreasing in z.
-/
import Init
import SqrtProof.FloorBound

def babylonStep (x z : Nat) : Nat := (z + x / z) / 2

-- ============================================================================
-- Core: x/z ≤ x/(z+1) + 1 for overestimates
-- ============================================================================

theorem div_drop_le_one (x z : Nat) (hz : 0 < z) (hov : x < z * z) :
    x / z ≤ x / (z + 1) + 1 := by
  by_cases hq : x / z = 0
  · -- 0 ≤ anything + 1
    rw [hq]; exact Nat.zero_le _
  · have hq_pos : 0 < x / z := Nat.pos_of_ne_zero hq
    have hq_lt : x / z < z := Nat.div_lt_of_lt_mul hov
    have h_mul_le : z * (x / z) ≤ x := Nat.mul_div_le x z
    have h_x_ge_z : z ≤ x := Nat.le_trans (Nat.le_mul_of_pos_right z hq_pos) h_mul_le
    -- Show (x/z - 1) * (z+1) ≤ x, then by le_div_iff: x/z - 1 ≤ x/(z+1).
    -- Expand: (x/z - 1) * (z+1) = (x/z - 1) * z + (x/z - 1) * 1
    -- Part 1: (x/z - 1) * z = z * (x/z) - z * 1 ≤ x - z
    have h_part1 : (x / z - 1) * z ≤ x - z := by
      rw [Nat.mul_comm (x / z - 1) z, Nat.mul_sub z (x / z) 1, Nat.mul_one]
      exact Nat.sub_le_sub_right h_mul_le z
    -- Part 2: (x/z - 1) ≤ z - 2
    -- Combined: (x/z-1)*z + (x/z-1) ≤ (x-z) + (z-2) ≤ x
    have h_prod : (x / z - 1) * (z + 1) ≤ x := by
      rw [Nat.mul_add, Nat.mul_one]
      -- (x/z-1)*z + (x/z - 1) ≤ (x - z) + (z - 2) = x - 2 ≤ x
      -- Need: (x/z - 1) ≤ z - 2 and x - z + (z - 2) ≤ x
      -- x/z - 1 ≤ z - 2: from x/z ≤ z - 1 (i.e., x/z < z)
      -- x - z + (z - 2) = x - 2 ≤ x: true for x ≥ 0
      -- But Nat subtraction: x - z + (z - 2) might not equal x - 2.
      -- Instead: (x/z-1)*z ≤ x - z and x/z - 1 ≤ z - 2.
      -- sum ≤ x - z + z - 2 = x - 2 ≤ x (for z ≥ 2)
      -- For z = 1: x/z = x, hq_lt says x < 1, so x = 0 and hq says x/1 = 0. Contradiction.
      have hz2 : z ≥ 2 := by omega  -- from hq_pos (x/z ≥ 1) and hq_lt (x/z < z)
      -- (x/z-1)*z + (x/z-1) ≤ (x-z) + (z-2)
      have : x / z - 1 ≤ z - 2 := by omega
      -- Need: x - z + (z - 2) ≤ x. Since z ≥ 2: z - 2 ≤ z, x - z + (z-2) ≤ x - 2 ≤ x.
      omega
    have := (Nat.le_div_iff_mul_le (by omega : 0 < z + 1)).mpr h_prod
    omega

theorem sum_nondec_step (x z : Nat) (hz : 0 < z) (hov : x < z * z) :
    z + x / z ≤ (z + 1) + x / (z + 1) := by
  have := div_drop_le_one x z hz hov; omega

-- ============================================================================
-- Step monotonicity
-- ============================================================================

theorem babylonStep_mono_x {x₁ x₂ z : Nat} (hx : x₁ ≤ x₂) (hz : 0 < z) :
    babylonStep x₁ z ≤ babylonStep x₂ z := by
  unfold babylonStep
  have : x₁ / z ≤ x₂ / z := Nat.div_le_div_right hx; omega

theorem babylonStep_mono_z (x z₁ z₂ : Nat) (hz : 0 < z₁)
    (hov : x < z₁ * z₁) (hle : z₁ ≤ z₂) :
    babylonStep x z₁ ≤ babylonStep x z₂ := by
  unfold babylonStep
  suffices z₁ + x / z₁ ≤ z₂ + x / z₂ by
    exact Nat.div_le_div_right this
  induction z₂ with
  | zero => omega
  | succ n ih =>
    by_cases h : z₁ ≤ n
    · have hn : 0 < n := by omega
      have hov_n : x < n * n :=
        Nat.lt_of_lt_of_le hov (Nat.mul_le_mul h h)
      exact Nat.le_trans (ih h) (sum_nondec_step x n hn hov_n)
    · have h_eq : z₁ = n + 1 := by omega
      subst h_eq; omega

theorem babylonStep_lt_of_overestimate (x z : Nat) (hz : 0 < z) (hov : x < z * z) :
    babylonStep x z < z := by
  unfold babylonStep
  have : x / z < z := Nat.div_lt_of_lt_mul hov; omega
