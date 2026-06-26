/-
  Full correctness proof of Cbrt.sol:_cbrt and cbrt.

  This file contains a concrete integer cube-root function `icbrt` with formal
  floor specification and named correctness theorems for `innerCbrt` and
  `floorCbrt`, parameterized by the upper-bound hypothesis
  `innerCbrt x ≤ icbrt x + 1`.
-/
import Init
import Mathlib.Data.Nat.Find
import CbrtProof.FloorBound

set_option maxHeartbeats 2000000

-- ============================================================================
-- Definitions matching Cbrt.sol EVM semantics
-- ============================================================================

/-- One Newton-Raphson step for cube root: ⌊(⌊x/z²⌋ + 2z) / 3⌋.
    Matches EVM: div(add(add(div(x, mul(z, z)), z), z), 3) -/
def cbrtStep (x z : Nat) : Nat := (x / (z * z) + 2 * z) / 3

/-- Run five cbrt Newton steps from an explicit starting point. -/
def run5From (x z : Nat) : Nat :=
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  z

/-- Run four cbrt Newton steps from an explicit starting point. -/
def run4From (x z : Nat) : Nat :=
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  z

/-- Run six cbrt Newton steps from an explicit starting point. -/
def run6From (x z : Nat) : Nat :=
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  z

/-- run5From = cbrtStep after run4From (definitional). -/
theorem run5_eq_step_run4 (x z : Nat) :
    run5From x z = cbrtStep x (run4From x z) := rfl

/-- run6From = cbrtStep after run5From (definitional). -/
theorem run6_eq_step_run5 (x z : Nat) :
    run6From x z = cbrtStep x (run5From x z) := rfl

/-- Fixed-point multiplier selected by `log2(x) % 3`. -/
def cbrtSeedMultiplier (y : Nat) : Nat :=
  #[0x8e, 0xb4, 0xe8][y % 3]!

/-- The cbrt seed:
    z = ⌊c * 2^q / 128⌋ where y = log2(x), q = ⌊y / 3⌋, and
    c is selected from [0x8e, 0xb4, 0xe8] by y % 3. -/
def cbrtSeed (x : Nat) : Nat :=
  (cbrtSeedMultiplier (Nat.log2 x) <<< (Nat.log2 x / 3)) >>> 7

/-- _cbrt: seed + 5 Newton-Raphson steps. -/
def innerCbrt (x : Nat) : Nat :=
  let z := cbrtSeed x
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  z

/-- cbrt: _cbrt with floor correction.
    Matches: z := sub(z, lt(div(x, mul(z, z)), z)) -/
def floorCbrt (x : Nat) : Nat :=
  let z := innerCbrt x
  if x / (z * z) < z then z - 1 else z

private theorem log2_eq_of_pow_bounds {n k : Nat}
    (hlo : 2 ^ k ≤ n) (hhi : n < 2 ^ (k + 1)) :
    Nat.log2 n = k := by
  have hn : n ≠ 0 :=
    Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.two_pow_pos k) hlo)
  apply Nat.le_antisymm
  · exact Nat.lt_succ_iff.mp ((Nat.log2_lt hn).2 hhi)
  · exact (Nat.le_log2 hn).2 hlo

-- ============================================================================
-- Reference integer cube root (floor)
-- ============================================================================

/-- Reference integer cube root (floor). -/
def icbrt (x : Nat) : Nat :=
  Nat.findGreatest (fun m => m * m * m ≤ x) x

theorem cube_monotone {a b : Nat} (h : a ≤ b) :
    a * a * a ≤ b * b * b := by
  have h1 : a * a * a ≤ b * a * a := by
    have hmul : a * a ≤ b * a := Nat.mul_le_mul_right a h
    exact Nat.mul_le_mul_right a hmul
  have h2 : b * a * a ≤ b * b * a := by
    have hmul : b * a ≤ b * b := Nat.mul_le_mul_left b h
    exact Nat.mul_le_mul_right a hmul
  have h3 : b * b * a ≤ b * b * b := by
    exact Nat.mul_le_mul_left (b * b) h
  exact Nat.le_trans h1 (Nat.le_trans h2 h3)

private theorem le_cube_of_pos {a : Nat} (ha : 0 < a) :
    a ≤ a * a * a := by
  have h1 : 1 ≤ a := Nat.succ_le_of_lt ha
  have h2 : a ≤ a * a := by
    simpa [Nat.mul_one] using (Nat.mul_le_mul_left a h1)
  have h3 : a * a ≤ a * a * a := by
    simpa [Nat.mul_one, Nat.mul_assoc] using (Nat.mul_le_mul_left (a * a) h1)
  exact Nat.le_trans h2 h3

/-- Lower half of the floor specification: `icbrt(x)^3 ≤ x`. -/
theorem icbrt_cube_le (x : Nat) :
    icbrt x * icbrt x * icbrt x ≤ x := by
  unfold icbrt
  exact Nat.findGreatest_spec (P := fun m => m * m * m ≤ x) (m := 0) (n := x)
    (Nat.zero_le x) (by simp)

/-- Upper half of the floor specification: `x < (icbrt(x)+1)^3`. -/
theorem icbrt_lt_succ_cube (x : Nat) :
    x < (icbrt x + 1) * (icbrt x + 1) * (icbrt x + 1) := by
  by_cases hlt : x < (icbrt x + 1) * (icbrt x + 1) * (icbrt x + 1)
  · exact hlt
  · have hle : (icbrt x + 1) * (icbrt x + 1) * (icbrt x + 1) ≤ x := Nat.le_of_not_lt hlt
    have hpos : 0 < icbrt x + 1 := by omega
    have hmx : icbrt x + 1 ≤ x := by
      have hleCube : icbrt x + 1 ≤ (icbrt x + 1) * (icbrt x + 1) * (icbrt x + 1) :=
        le_cube_of_pos hpos
      exact Nat.le_trans hleCube hle
    have hmax : icbrt x + 1 ≤ icbrt x := by
      exact Nat.le_findGreatest (P := fun m => m * m * m ≤ x)
        (m := icbrt x + 1) (n := x) hmx hle
    exact False.elim ((Nat.not_succ_le_self (icbrt x)) hmax)

/-- Uniqueness: any `r` satisfying the floor specification equals `icbrt(x)`. -/
theorem icbrt_eq_of_bounds (x r : Nat)
    (hlo : r * r * r ≤ x)
    (hhi : x < (r + 1) * (r + 1) * (r + 1)) :
    r = icbrt x := by
  have hrx : r ≤ x := by
    by_cases hr0 : r = 0
    · omega
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
      have hrle : r ≤ r * r * r := le_cube_of_pos hrpos
      exact Nat.le_trans hrle hlo
  have h1 : r ≤ icbrt x := by
    exact Nat.le_findGreatest (P := fun m => m * m * m ≤ x)
      (m := r) (n := x) hrx hlo
  have h2 : icbrt x ≤ r := by
    by_cases hic : icbrt x ≤ r
    · exact hic
    · have hr1_le : r + 1 ≤ icbrt x := Nat.succ_le_of_lt (Nat.lt_of_not_ge hic)
      have hmono : (r + 1) * (r + 1) * (r + 1) ≤ icbrt x * icbrt x * icbrt x :=
        cube_monotone hr1_le
      have hicbrt : icbrt x * icbrt x * icbrt x ≤ x := icbrt_cube_le x
      have : (r + 1) * (r + 1) * (r + 1) ≤ x := Nat.le_trans hmono hicbrt
      exact False.elim (Nat.not_le_of_lt hhi this)
  exact Nat.le_antisymm h1 h2

-- ============================================================================
-- Seed and step positivity
-- ============================================================================

/-- The cbrt seed is always positive. -/
theorem cbrtSeed_pos (x : Nat) : 0 < cbrtSeed x := by
  unfold cbrtSeed
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  unfold cbrtSeedMultiplier
  have hCases : Nat.log2 x % 3 = 0 ∨ Nat.log2 x % 3 = 1 ∨ Nat.log2 x % 3 = 2 := by
    omega
  rcases hCases with h | h | h <;> simp [h] <;>
    have hpow : 1 ≤ 2 ^ (Nat.log2 x / 3) := Nat.succ_le_of_lt (Nat.two_pow_pos _) <;>
    omega

/-- cbrtStep preserves positivity when x > 0 and z > 0. -/
theorem cbrtStep_pos (x z : Nat) (hx : 0 < x) (hz : 0 < z) : 0 < cbrtStep x z := by
  unfold cbrtStep
  -- Numerator = x/(z*z) + 2*z ≥ 2*z ≥ 2.
  -- For z = 1: numerator = x + 2 ≥ 3, so /3 ≥ 1.
  -- For z ≥ 2: numerator ≥ 4, so /3 ≥ 1.
  have hzz : 0 < z * z := Nat.mul_pos hz hz
  by_cases h : z = 1
  · -- z = 1: numerator = x/1 + 2 = x + 2 ≥ 3, so /3 ≥ 1
    subst h; simp
    -- goal: 0 < (x / 1 + 2) / 3 or similar. omega handles.
    omega
  · -- z ≥ 2: numerator ≥ 0 + 2z ≥ 4, so /3 ≥ 1
    have hz2 : z ≥ 2 := by omega
    -- x/(z*z) is a Nat ≥ 0. 2*z ≥ 4. Sum ≥ 4. 4/3 = 1 > 0.
    have h_num_ge : x / (z * z) + 2 * z ≥ 3 := by
      have : 2 * z ≥ 4 := by omega
      have : x / (z * z) ≥ 0 := Nat.zero_le _
      omega
    omega

-- ============================================================================
-- Upper bound machinery (one-step contraction)
-- ============================================================================

/-- Integer polynomial identity used to upper-bound one cbrt Newton step. -/
private theorem int_poly_identity (m d q r : Int)
    (hd2 : d * d = m * q + r) :
    ((m - 2 * d + 3 * q + 6) * ((m + d) * (m + d)) - (m + 1) * (m + 1) * (m + 1))
      =
    q * (3 * m * q + 6 * m + 3 * r + 4 * d * m)
      + (-2 * d * r + 12 * d * m + 3 * m * m - 3 * m * r - 3 * m + 6 * r - 1) := by
  ring_nf at hd2 ⊢
  have hd3 : d ^ 3 = d * (m * q + r) := by
    rw [← hd2]
    ring_nf
  rw [hd2, hd3]
  ring_nf

/-- Product form of the one-step upper bound (core arithmetic bridge). -/
private theorem one_step_prod_bound (m d : Nat) (hm2 : 2 ≤ m) :
    (m + 1) * (m + 1) * (m + 1) ≤
      (m - 2 * d + 3 * (d * d / m) + 6) * ((m + d) * (m + d)) := by
  let q : Nat := d * d / m
  let r : Nat := d * d % m
  have hm : 0 < m := by omega
  have hr : r < m := by
    dsimp [r]
    exact Nat.mod_lt _ hm
  have hd2 : d * d = m * q + r := by
    dsimp [q, r]
    exact (Nat.div_add_mod (d * d) m).symm

  have hd2i : (d : Int) * (d : Int) = (m : Int) * (q : Int) + (r : Int) := by
    exact_mod_cast hd2

  have hEqInt :
      (((m : Int) - 2 * (d : Int) + 3 * (q : Int) + 6) *
          (((m : Int) + (d : Int)) * ((m : Int) + (d : Int)))
        - ((m : Int) + 1) * ((m : Int) + 1) * ((m : Int) + 1))
      =
      (q : Int) * (3 * (m : Int) * (q : Int) + 6 * (m : Int) + 3 * (r : Int) + 4 * (d : Int) * (m : Int))
        + (-2 * (d : Int) * (r : Int) + 12 * (d : Int) * (m : Int)
            + 3 * (m : Int) * (m : Int) - 3 * (m : Int) * (r : Int)
            - 3 * (m : Int) + 6 * (r : Int) - 1) := by
    exact int_poly_identity (m := (m : Int)) (d := (d : Int)) (q := (q : Int)) (r := (r : Int)) hd2i

  have hm_nonneg : 0 ≤ (m : Int) := Int.natCast_nonneg m
  have hq_nonneg : 0 ≤ (q : Int) := Int.natCast_nonneg q
  have hr_nonneg : 0 ≤ (r : Int) := Int.natCast_nonneg r
  have hd_nonneg : 0 ≤ (d : Int) := Int.natCast_nonneg d

  have h3_nonneg : (0 : Int) ≤ 3 := by decide
  have h4_nonneg : (0 : Int) ≤ 4 := by decide
  have h6_nonneg : (0 : Int) ≤ 6 := by decide
  have h10_nonneg : (0 : Int) ≤ 10 := by decide
  have h2_nonneg : (0 : Int) ≤ 2 := by decide

  have h3m_nonneg : 0 ≤ 3 * (m : Int) := Int.mul_nonneg h3_nonneg hm_nonneg
  have h6m_nonneg : 0 ≤ 6 * (m : Int) := Int.mul_nonneg h6_nonneg hm_nonneg
  have h3r_nonneg : 0 ≤ 3 * (r : Int) := Int.mul_nonneg h3_nonneg hr_nonneg
  have h4d_nonneg : 0 ≤ 4 * (d : Int) := Int.mul_nonneg h4_nonneg hd_nonneg

  have h1_nonneg : 0 ≤ 3 * (m : Int) * (q : Int) := Int.mul_nonneg h3m_nonneg hq_nonneg
  have h4_nonneg' : 0 ≤ 4 * (d : Int) * (m : Int) := Int.mul_nonneg h4d_nonneg hm_nonneg

  have hfac_nonneg : 0 ≤ 3 * (m : Int) * (q : Int) + 6 * (m : Int) + 3 * (r : Int) + 4 * (d : Int) * (m : Int) := by
    omega

  have hQ_nonneg :
      0 ≤ (q : Int) * (3 * (m : Int) * (q : Int) + 6 * (m : Int) + 3 * (r : Int) + 4 * (d : Int) * (m : Int)) := by
    exact Int.mul_nonneg hq_nonneg hfac_nonneg

  have hc_nonpos : -2 * (d : Int) - 3 * (m : Int) + 6 ≤ 0 := by
    have hm_ge_two : (2 : Int) ≤ (m : Int) := by exact_mod_cast hm2
    omega

  have hr_le : (r : Int) ≤ ((m - 1 : Nat) : Int) := by
    have : r ≤ m - 1 := by omega
    exact Int.ofNat_le.mpr this

  have h_mul_lower :
      ((m - 1 : Nat) : Int) * (-2 * (d : Int) - 3 * (m : Int) + 6)
        ≤ (r : Int) * (-2 * (d : Int) - 3 * (m : Int) + 6) := by
    exact Int.mul_le_mul_of_nonpos_right hr_le hc_nonpos

  have h_rewrite :
      (-2 * (d : Int) * (r : Int) + 12 * (d : Int) * (m : Int)
        + 3 * (m : Int) * (m : Int) - 3 * (m : Int) * (r : Int)
        - 3 * (m : Int) + 6 * (r : Int) - 1)
      = (12 * (d : Int) * (m : Int) + 3 * (m : Int) * (m : Int) - 3 * (m : Int) - 1)
        + (r : Int) * (-2 * (d : Int) - 3 * (m : Int) + 6) := by
    ring_nf

  have h_rewrite0 :
      (12 * (d : Int) * (m : Int) + 3 * (m : Int) * (m : Int) - 3 * (m : Int) - 1)
        + ((m - 1 : Nat) : Int) * (-2 * (d : Int) - 3 * (m : Int) + 6)
      = 10 * (d : Int) * (m : Int) + 2 * (d : Int) + 6 * (m : Int) - 7 := by
    have ht : ((m - 1 : Nat) : Int) = (m : Int) - 1 := by omega
    rw [ht]
    ring_nf

  have h10dm_nonneg : 0 ≤ 10 * (d : Int) * (m : Int) := by
    have h10d_nonneg : 0 ≤ 10 * (d : Int) := Int.mul_nonneg h10_nonneg hd_nonneg
    exact Int.mul_nonneg h10d_nonneg hm_nonneg
  have h2d_nonneg : 0 ≤ 2 * (d : Int) := Int.mul_nonneg h2_nonneg hd_nonneg
  have h6m_minus7_nonneg : 0 ≤ 6 * (m : Int) - 7 := by
    have hm_ge_two : (2 : Int) ≤ (m : Int) := by exact_mod_cast hm2
    omega

  have h0 :
      0 ≤ (12 * (d : Int) * (m : Int) + 3 * (m : Int) * (m : Int) - 3 * (m : Int) - 1)
            + ((m - 1 : Nat) : Int) * (-2 * (d : Int) - 3 * (m : Int) + 6) := by
    rw [h_rewrite0]
    omega

  have hLin :
      0 ≤ (-2 * (d : Int) * (r : Int) + 12 * (d : Int) * (m : Int)
            + 3 * (m : Int) * (m : Int) - 3 * (m : Int) * (r : Int)
            - 3 * (m : Int) + 6 * (r : Int) - 1) := by
    rw [h_rewrite]
    have h_add :
        (12 * (d : Int) * (m : Int) + 3 * (m : Int) * (m : Int) - 3 * (m : Int) - 1)
          + ((m - 1 : Nat) : Int) * (-2 * (d : Int) - 3 * (m : Int) + 6)
        ≤
        (12 * (d : Int) * (m : Int) + 3 * (m : Int) * (m : Int) - 3 * (m : Int) - 1)
          + (r : Int) * (-2 * (d : Int) - 3 * (m : Int) + 6) := by
      exact Int.add_le_add_left h_mul_lower _
    exact Int.le_trans h0 h_add

  have hdiff_nonneg :
      0 ≤ (((m : Int) - 2 * (d : Int) + 3 * (q : Int) + 6) *
              (((m : Int) + (d : Int)) * ((m : Int) + (d : Int)))
            - ((m : Int) + 1) * ((m : Int) + 1) * ((m : Int) + 1)) := by
    rw [hEqInt]
    exact Int.add_nonneg hQ_nonneg hLin

  have hIntMain :
      ((m : Int) + 1) * ((m : Int) + 1) * ((m : Int) + 1) ≤
        ((m : Int) - 2 * (d : Int) + 3 * (q : Int) + 6) *
          (((m : Int) + (d : Int)) * ((m : Int) + (d : Int))) := by
    omega

  have hCoeffLe :
      ((m : Int) - 2 * (d : Int) + 3 * (q : Int) + 6)
        ≤ ((m - 2 * d + 3 * q + 6 : Nat) : Int) := by
    omega

  have hz_nonneg : 0 ≤ (((m : Int) + (d : Int)) * ((m : Int) + (d : Int))) := by
    have : 0 ≤ (m : Int) + (d : Int) := Int.add_nonneg hm_nonneg hd_nonneg
    exact Int.mul_nonneg this this

  have hIntNatCoeff :
      ((m : Int) + 1) * ((m : Int) + 1) * ((m : Int) + 1)
        ≤ ((m - 2 * d + 3 * q + 6 : Nat) : Int) *
            (((m : Int) + (d : Int)) * ((m : Int) + (d : Int))) := by
    exact Int.le_trans hIntMain (Int.mul_le_mul_of_nonneg_right hCoeffLe hz_nonneg)

  exact_mod_cast hIntNatCoeff

/-- Division form of the one-step upper bound. -/
private theorem one_step_div_bound (m d : Nat) (hm2 : 2 ≤ m) :
    (((m + 1) * (m + 1) * (m + 1) - 1) / ((m + d) * (m + d)))
      ≤ m - 2 * d + 3 * (d * d / m) + 5 := by
  let A : Nat := m - 2 * d + 3 * (d * d / m) + 5
  let B : Nat := (m + d) * (m + d)
  have hBpos : 0 < B := by
    dsimp [B]
    exact Nat.mul_pos (by omega) (by omega)
  have hprod : (m + 1) * (m + 1) * (m + 1) ≤ (A + 1) * B := by
    dsimp [A, B]
    simpa [Nat.add_assoc] using one_step_prod_bound m d hm2
  have hpred : (m + 1) * (m + 1) * (m + 1) - 1 < (m + 1) * (m + 1) * (m + 1) := by
    have hpos : 0 < (m + 1) * (m + 1) * (m + 1) := by
      have hm1 : 0 < m + 1 := by omega
      exact Nat.mul_pos (Nat.mul_pos hm1 hm1) hm1
    exact Nat.sub_lt hpos (by omega)
  have hlt : (m + 1) * (m + 1) * (m + 1) - 1 < (A + 1) * B :=
    Nat.lt_of_lt_of_le hpred hprod
  have hdivlt : (((m + 1) * (m + 1) * (m + 1) - 1) / B) < A + 1 := by
    exact (Nat.div_lt_iff_lt_mul hBpos).2 hlt
  have hdivle : (((m + 1) * (m + 1) * (m + 1) - 1) / B) ≤ A := by
    exact Nat.lt_succ_iff.mp hdivlt
  simpa [A, B]

/-- If `x < (m+1)^3` and `z = m+d` with `2d ≤ m`, one cbrt step keeps
    the overestimate within `d^2/m + 1`. -/
private theorem cbrtStep_upper_of_delta
    (x m d : Nat)
    (hm2 : 2 ≤ m)
    (h2d : 2 * d ≤ m)
    (hx : x < (m + 1) * (m + 1) * (m + 1)) :
    cbrtStep x (m + d) ≤ m + (d * d / m) + 1 := by
  let q : Nat := d * d / m
  let z : Nat := m + d
  have hxle : x ≤ (m + 1) * (m + 1) * (m + 1) - 1 := by omega
  have hdiv_x : x / (z * z) ≤ ((m + 1) * (m + 1) * (m + 1) - 1) / (z * z) :=
    Nat.div_le_div_right hxle
  have hdiv_m :
      ((m + 1) * (m + 1) * (m + 1) - 1) / (z * z) ≤ m - 2 * d + 3 * q + 5 := by
    simpa [z, q, Nat.mul_assoc] using one_step_div_bound m d hm2
  have hdiv : x / (z * z) ≤ m - 2 * d + 3 * q + 5 := Nat.le_trans hdiv_x hdiv_m
  unfold cbrtStep
  have hsum : x / (z * z) + 2 * z ≤ (m - 2 * d + 3 * q + 5) + 2 * z := by
    exact Nat.add_le_add_right hdiv _
  have hdiv3 :
      (x / (z * z) + 2 * z) / 3
        ≤ ((m - 2 * d + 3 * q + 5) + 2 * z) / 3 :=
    Nat.div_le_div_right hsum
  have hfinal : ((m - 2 * d + 3 * q + 5) + 2 * z) / 3 ≤ m + q + 1 := by
    omega
  have hz : z = m + d := by rfl
  rw [hz] at hdiv3 hfinal
  simpa [q] using Nat.le_trans hdiv3 hfinal

/-- Upper-bound transfer form: if `z` is between `m` and `m+d`, one cbrt step is
    bounded by the same `d^2/m + 1` expression. -/
theorem cbrtStep_upper_of_le
    (x m z d : Nat)
    (hm2 : 2 ≤ m)
    (hmz : m ≤ z)
    (hzd : z ≤ m + d)
    (h2d : 2 * d ≤ m)
    (hx : x < (m + 1) * (m + 1) * (m + 1)) :
    cbrtStep x z ≤ m + (d * d / m) + 1 := by
  let d' : Nat := z - m
  have hz_eq : z = m + d' := by
    dsimp [d']
    omega
  have hd'_le : d' ≤ d := by
    dsimp [d']
    omega
  have h2d' : 2 * d' ≤ m := Nat.le_trans (Nat.mul_le_mul_left 2 hd'_le) h2d
  have hstep' : cbrtStep x z ≤ m + (d' * d' / m) + 1 := by
    rw [hz_eq]
    exact cbrtStep_upper_of_delta x m d' hm2 h2d' hx
  have hsq : d' * d' ≤ d * d := Nat.mul_le_mul hd'_le hd'_le
  have hdiv : d' * d' / m ≤ d * d / m := Nat.div_le_div_right hsq
  have hmono : m + (d' * d' / m) + 1 ≤ m + (d * d / m) + 1 := by
    exact Nat.add_le_add_left (Nat.add_le_add_right hdiv 1) m
  exact Nat.le_trans hstep' hmono

-- ============================================================================
-- innerCbrt structure
-- ============================================================================

/-- `_cbrt` is exactly `run5From` from the seed (definitional). -/
theorem innerCbrt_eq_run5From_seed (x : Nat) :
    innerCbrt x = run5From x (cbrtSeed x) := rfl

/-- `_cbrt` is `cbrtStep` applied to `run4From` of the seed (definitional). -/
theorem innerCbrt_eq_step_run4_seed (x : Nat) :
    innerCbrt x = cbrtStep x (run4From x (cbrtSeed x)) := rfl

set_option maxRecDepth 1000000 in
/-- Direct finite check for small inputs. -/
theorem innerCbrt_upper_of_lt_256 (x : Nat) (hx : x < 256) :
    innerCbrt x ≤ icbrt x + 1 := by
  match x with
  | 0 =>
    unfold innerCbrt cbrtSeed
    rw [Nat.log2_zero]
    decide
  | 1 =>
    have hlog : Nat.log2 1 = 0 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 2 =>
    have hlog : Nat.log2 2 = 1 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 3 =>
    have hlog : Nat.log2 3 = 1 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 4 =>
    have hlog : Nat.log2 4 = 2 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 5 =>
    have hlog : Nat.log2 5 = 2 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 6 =>
    have hlog : Nat.log2 6 = 2 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 7 =>
    have hlog : Nat.log2 7 = 2 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 8 =>
    have hlog : Nat.log2 8 = 3 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 9 =>
    have hlog : Nat.log2 9 = 3 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 10 =>
    have hlog : Nat.log2 10 = 3 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 11 =>
    have hlog : Nat.log2 11 = 3 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 12 =>
    have hlog : Nat.log2 12 = 3 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 13 =>
    have hlog : Nat.log2 13 = 3 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 14 =>
    have hlog : Nat.log2 14 = 3 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 15 =>
    have hlog : Nat.log2 15 = 3 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 16 =>
    have hlog : Nat.log2 16 = 4 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 17 =>
    have hlog : Nat.log2 17 = 4 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 18 =>
    have hlog : Nat.log2 18 = 4 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 19 =>
    have hlog : Nat.log2 19 = 4 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 20 =>
    have hlog : Nat.log2 20 = 4 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 21 =>
    have hlog : Nat.log2 21 = 4 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 22 =>
    have hlog : Nat.log2 22 = 4 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 23 =>
    have hlog : Nat.log2 23 = 4 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 24 =>
    have hlog : Nat.log2 24 = 4 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 25 =>
    have hlog : Nat.log2 25 = 4 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 26 =>
    have hlog : Nat.log2 26 = 4 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 27 =>
    have hlog : Nat.log2 27 = 4 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 28 =>
    have hlog : Nat.log2 28 = 4 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 29 =>
    have hlog : Nat.log2 29 = 4 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 30 =>
    have hlog : Nat.log2 30 = 4 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 31 =>
    have hlog : Nat.log2 31 = 4 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 32 =>
    have hlog : Nat.log2 32 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 33 =>
    have hlog : Nat.log2 33 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 34 =>
    have hlog : Nat.log2 34 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 35 =>
    have hlog : Nat.log2 35 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 36 =>
    have hlog : Nat.log2 36 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 37 =>
    have hlog : Nat.log2 37 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 38 =>
    have hlog : Nat.log2 38 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 39 =>
    have hlog : Nat.log2 39 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 40 =>
    have hlog : Nat.log2 40 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 41 =>
    have hlog : Nat.log2 41 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 42 =>
    have hlog : Nat.log2 42 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 43 =>
    have hlog : Nat.log2 43 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 44 =>
    have hlog : Nat.log2 44 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 45 =>
    have hlog : Nat.log2 45 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 46 =>
    have hlog : Nat.log2 46 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 47 =>
    have hlog : Nat.log2 47 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 48 =>
    have hlog : Nat.log2 48 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 49 =>
    have hlog : Nat.log2 49 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 50 =>
    have hlog : Nat.log2 50 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 51 =>
    have hlog : Nat.log2 51 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 52 =>
    have hlog : Nat.log2 52 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 53 =>
    have hlog : Nat.log2 53 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 54 =>
    have hlog : Nat.log2 54 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 55 =>
    have hlog : Nat.log2 55 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 56 =>
    have hlog : Nat.log2 56 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 57 =>
    have hlog : Nat.log2 57 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 58 =>
    have hlog : Nat.log2 58 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 59 =>
    have hlog : Nat.log2 59 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 60 =>
    have hlog : Nat.log2 60 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 61 =>
    have hlog : Nat.log2 61 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 62 =>
    have hlog : Nat.log2 62 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 63 =>
    have hlog : Nat.log2 63 = 5 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 64 =>
    have hlog : Nat.log2 64 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 65 =>
    have hlog : Nat.log2 65 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 66 =>
    have hlog : Nat.log2 66 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 67 =>
    have hlog : Nat.log2 67 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 68 =>
    have hlog : Nat.log2 68 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 69 =>
    have hlog : Nat.log2 69 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 70 =>
    have hlog : Nat.log2 70 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 71 =>
    have hlog : Nat.log2 71 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 72 =>
    have hlog : Nat.log2 72 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 73 =>
    have hlog : Nat.log2 73 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 74 =>
    have hlog : Nat.log2 74 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 75 =>
    have hlog : Nat.log2 75 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 76 =>
    have hlog : Nat.log2 76 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 77 =>
    have hlog : Nat.log2 77 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 78 =>
    have hlog : Nat.log2 78 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 79 =>
    have hlog : Nat.log2 79 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 80 =>
    have hlog : Nat.log2 80 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 81 =>
    have hlog : Nat.log2 81 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 82 =>
    have hlog : Nat.log2 82 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 83 =>
    have hlog : Nat.log2 83 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 84 =>
    have hlog : Nat.log2 84 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 85 =>
    have hlog : Nat.log2 85 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 86 =>
    have hlog : Nat.log2 86 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 87 =>
    have hlog : Nat.log2 87 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 88 =>
    have hlog : Nat.log2 88 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 89 =>
    have hlog : Nat.log2 89 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 90 =>
    have hlog : Nat.log2 90 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 91 =>
    have hlog : Nat.log2 91 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 92 =>
    have hlog : Nat.log2 92 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 93 =>
    have hlog : Nat.log2 93 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 94 =>
    have hlog : Nat.log2 94 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 95 =>
    have hlog : Nat.log2 95 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 96 =>
    have hlog : Nat.log2 96 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 97 =>
    have hlog : Nat.log2 97 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 98 =>
    have hlog : Nat.log2 98 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 99 =>
    have hlog : Nat.log2 99 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 100 =>
    have hlog : Nat.log2 100 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 101 =>
    have hlog : Nat.log2 101 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 102 =>
    have hlog : Nat.log2 102 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 103 =>
    have hlog : Nat.log2 103 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 104 =>
    have hlog : Nat.log2 104 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 105 =>
    have hlog : Nat.log2 105 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 106 =>
    have hlog : Nat.log2 106 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 107 =>
    have hlog : Nat.log2 107 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 108 =>
    have hlog : Nat.log2 108 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 109 =>
    have hlog : Nat.log2 109 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 110 =>
    have hlog : Nat.log2 110 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 111 =>
    have hlog : Nat.log2 111 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 112 =>
    have hlog : Nat.log2 112 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 113 =>
    have hlog : Nat.log2 113 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 114 =>
    have hlog : Nat.log2 114 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 115 =>
    have hlog : Nat.log2 115 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 116 =>
    have hlog : Nat.log2 116 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 117 =>
    have hlog : Nat.log2 117 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 118 =>
    have hlog : Nat.log2 118 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 119 =>
    have hlog : Nat.log2 119 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 120 =>
    have hlog : Nat.log2 120 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 121 =>
    have hlog : Nat.log2 121 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 122 =>
    have hlog : Nat.log2 122 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 123 =>
    have hlog : Nat.log2 123 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 124 =>
    have hlog : Nat.log2 124 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 125 =>
    have hlog : Nat.log2 125 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 126 =>
    have hlog : Nat.log2 126 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 127 =>
    have hlog : Nat.log2 127 = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 128 =>
    have hlog : Nat.log2 128 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 129 =>
    have hlog : Nat.log2 129 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 130 =>
    have hlog : Nat.log2 130 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 131 =>
    have hlog : Nat.log2 131 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 132 =>
    have hlog : Nat.log2 132 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 133 =>
    have hlog : Nat.log2 133 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 134 =>
    have hlog : Nat.log2 134 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 135 =>
    have hlog : Nat.log2 135 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 136 =>
    have hlog : Nat.log2 136 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 137 =>
    have hlog : Nat.log2 137 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 138 =>
    have hlog : Nat.log2 138 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 139 =>
    have hlog : Nat.log2 139 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 140 =>
    have hlog : Nat.log2 140 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 141 =>
    have hlog : Nat.log2 141 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 142 =>
    have hlog : Nat.log2 142 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 143 =>
    have hlog : Nat.log2 143 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 144 =>
    have hlog : Nat.log2 144 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 145 =>
    have hlog : Nat.log2 145 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 146 =>
    have hlog : Nat.log2 146 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 147 =>
    have hlog : Nat.log2 147 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 148 =>
    have hlog : Nat.log2 148 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 149 =>
    have hlog : Nat.log2 149 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 150 =>
    have hlog : Nat.log2 150 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 151 =>
    have hlog : Nat.log2 151 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 152 =>
    have hlog : Nat.log2 152 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 153 =>
    have hlog : Nat.log2 153 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 154 =>
    have hlog : Nat.log2 154 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 155 =>
    have hlog : Nat.log2 155 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 156 =>
    have hlog : Nat.log2 156 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 157 =>
    have hlog : Nat.log2 157 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 158 =>
    have hlog : Nat.log2 158 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 159 =>
    have hlog : Nat.log2 159 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 160 =>
    have hlog : Nat.log2 160 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 161 =>
    have hlog : Nat.log2 161 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 162 =>
    have hlog : Nat.log2 162 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 163 =>
    have hlog : Nat.log2 163 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 164 =>
    have hlog : Nat.log2 164 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 165 =>
    have hlog : Nat.log2 165 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 166 =>
    have hlog : Nat.log2 166 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 167 =>
    have hlog : Nat.log2 167 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 168 =>
    have hlog : Nat.log2 168 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 169 =>
    have hlog : Nat.log2 169 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 170 =>
    have hlog : Nat.log2 170 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 171 =>
    have hlog : Nat.log2 171 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 172 =>
    have hlog : Nat.log2 172 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 173 =>
    have hlog : Nat.log2 173 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 174 =>
    have hlog : Nat.log2 174 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 175 =>
    have hlog : Nat.log2 175 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 176 =>
    have hlog : Nat.log2 176 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 177 =>
    have hlog : Nat.log2 177 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 178 =>
    have hlog : Nat.log2 178 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 179 =>
    have hlog : Nat.log2 179 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 180 =>
    have hlog : Nat.log2 180 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 181 =>
    have hlog : Nat.log2 181 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 182 =>
    have hlog : Nat.log2 182 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 183 =>
    have hlog : Nat.log2 183 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 184 =>
    have hlog : Nat.log2 184 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 185 =>
    have hlog : Nat.log2 185 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 186 =>
    have hlog : Nat.log2 186 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 187 =>
    have hlog : Nat.log2 187 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 188 =>
    have hlog : Nat.log2 188 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 189 =>
    have hlog : Nat.log2 189 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 190 =>
    have hlog : Nat.log2 190 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 191 =>
    have hlog : Nat.log2 191 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 192 =>
    have hlog : Nat.log2 192 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 193 =>
    have hlog : Nat.log2 193 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 194 =>
    have hlog : Nat.log2 194 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 195 =>
    have hlog : Nat.log2 195 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 196 =>
    have hlog : Nat.log2 196 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 197 =>
    have hlog : Nat.log2 197 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 198 =>
    have hlog : Nat.log2 198 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 199 =>
    have hlog : Nat.log2 199 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 200 =>
    have hlog : Nat.log2 200 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 201 =>
    have hlog : Nat.log2 201 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 202 =>
    have hlog : Nat.log2 202 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 203 =>
    have hlog : Nat.log2 203 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 204 =>
    have hlog : Nat.log2 204 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 205 =>
    have hlog : Nat.log2 205 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 206 =>
    have hlog : Nat.log2 206 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 207 =>
    have hlog : Nat.log2 207 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 208 =>
    have hlog : Nat.log2 208 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 209 =>
    have hlog : Nat.log2 209 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 210 =>
    have hlog : Nat.log2 210 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 211 =>
    have hlog : Nat.log2 211 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 212 =>
    have hlog : Nat.log2 212 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 213 =>
    have hlog : Nat.log2 213 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 214 =>
    have hlog : Nat.log2 214 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 215 =>
    have hlog : Nat.log2 215 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 216 =>
    have hlog : Nat.log2 216 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 217 =>
    have hlog : Nat.log2 217 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 218 =>
    have hlog : Nat.log2 218 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 219 =>
    have hlog : Nat.log2 219 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 220 =>
    have hlog : Nat.log2 220 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 221 =>
    have hlog : Nat.log2 221 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 222 =>
    have hlog : Nat.log2 222 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 223 =>
    have hlog : Nat.log2 223 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 224 =>
    have hlog : Nat.log2 224 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 225 =>
    have hlog : Nat.log2 225 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 226 =>
    have hlog : Nat.log2 226 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 227 =>
    have hlog : Nat.log2 227 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 228 =>
    have hlog : Nat.log2 228 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 229 =>
    have hlog : Nat.log2 229 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 230 =>
    have hlog : Nat.log2 230 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 231 =>
    have hlog : Nat.log2 231 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 232 =>
    have hlog : Nat.log2 232 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 233 =>
    have hlog : Nat.log2 233 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 234 =>
    have hlog : Nat.log2 234 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 235 =>
    have hlog : Nat.log2 235 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 236 =>
    have hlog : Nat.log2 236 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 237 =>
    have hlog : Nat.log2 237 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 238 =>
    have hlog : Nat.log2 238 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 239 =>
    have hlog : Nat.log2 239 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 240 =>
    have hlog : Nat.log2 240 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 241 =>
    have hlog : Nat.log2 241 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 242 =>
    have hlog : Nat.log2 242 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 243 =>
    have hlog : Nat.log2 243 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 244 =>
    have hlog : Nat.log2 244 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 245 =>
    have hlog : Nat.log2 245 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 246 =>
    have hlog : Nat.log2 246 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 247 =>
    have hlog : Nat.log2 247 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 248 =>
    have hlog : Nat.log2 248 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 249 =>
    have hlog : Nat.log2 249 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 250 =>
    have hlog : Nat.log2 250 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 251 =>
    have hlog : Nat.log2 251 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 252 =>
    have hlog : Nat.log2 252 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 253 =>
    have hlog : Nat.log2 253 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 254 =>
    have hlog : Nat.log2 254 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 255 =>
    have hlog : Nat.log2 255 = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | _ + 256 => omega

private theorem innerCbrt_upper_fin256 :
    ∀ i : Fin 256, innerCbrt i.val ≤ icbrt i.val + 1 := by
  intro i
  exact innerCbrt_upper_of_lt_256 i.val i.2

/-- innerCbrt gives a lower bound: for any m with m³ ≤ x, m ≤ innerCbrt(x). -/
theorem innerCbrt_lower (x m : Nat) (hx : 0 < x)
    (hm : m * m * m ≤ x) : m ≤ innerCbrt x := by
  unfold innerCbrt
  have hs := cbrtSeed_pos x
  have h1 := cbrtStep_pos x _ hx hs
  have h2 := cbrtStep_pos x _ hx h1
  have h3 := cbrtStep_pos x _ hx h2
  have h4 := cbrtStep_pos x _ hx h3
  exact cbrt_step_floor_bound x _ m h4 hm

-- ============================================================================
-- Correctness theorems under explicit upper-bound hypothesis
-- ============================================================================

/-- Positivity of `innerCbrt` for positive `x`. -/
theorem innerCbrt_pos (x : Nat) (hx : 0 < x) : 0 < innerCbrt x := by
  have h1 : (1 : Nat) * 1 * 1 ≤ x := by omega
  have h := innerCbrt_lower x 1 hx h1
  omega

/-- If `innerCbrt x` is at most `icbrt x + 1`, then it is exactly one of those two values. -/
theorem innerCbrt_correct_of_upper (x : Nat) (hx : 0 < x)
    (hupper : innerCbrt x ≤ icbrt x + 1) :
    innerCbrt x = icbrt x ∨ innerCbrt x = icbrt x + 1 := by
  have hlow : icbrt x ≤ innerCbrt x := innerCbrt_lower x (icbrt x) hx (icbrt_cube_le x)
  by_cases heq : innerCbrt x = icbrt x
  · exact Or.inl heq
  · have hneq : icbrt x ≠ innerCbrt x := by
      intro h'
      exact heq h'.symm
    have hlt : icbrt x < innerCbrt x := Nat.lt_of_le_of_ne hlow hneq
    have hge : icbrt x + 1 ≤ innerCbrt x := Nat.succ_le_of_lt hlt
    exact Or.inr (Nat.le_antisymm hupper hge)

/-- Useful consequence of the upper-bound hypothesis: `(innerCbrt x - 1)^3 ≤ x`. -/
theorem innerCbrt_pred_cube_le_of_upper (x : Nat)
    (hupper : innerCbrt x ≤ icbrt x + 1) :
    (innerCbrt x - 1) * (innerCbrt x - 1) * (innerCbrt x - 1) ≤ x := by
  have hpred_le : innerCbrt x - 1 ≤ icbrt x := by omega
  have hmono :
      (innerCbrt x - 1) * (innerCbrt x - 1) * (innerCbrt x - 1) ≤
      icbrt x * icbrt x * icbrt x := cube_monotone hpred_le
  exact Nat.le_trans hmono (icbrt_cube_le x)

/-- For positive `x`, `x` is strictly below `(innerCbrt x + 1)^3`. -/
theorem innerCbrt_lt_succ_cube (x : Nat) (hx : 0 < x) :
    x < (innerCbrt x + 1) * (innerCbrt x + 1) * (innerCbrt x + 1) := by
  by_cases hlt : x < (innerCbrt x + 1) * (innerCbrt x + 1) * (innerCbrt x + 1)
  · exact hlt
  · have hle : (innerCbrt x + 1) * (innerCbrt x + 1) * (innerCbrt x + 1) ≤ x := Nat.le_of_not_lt hlt
    have hcontra : innerCbrt x + 1 ≤ innerCbrt x := innerCbrt_lower x (innerCbrt x + 1) hx hle
    exact False.elim ((Nat.not_succ_le_self (innerCbrt x)) hcontra)

-- ============================================================================
-- Perfect-cube exactness (innerCbrt(m³) = m)
-- ============================================================================

/-- cbrtStep is a fixed point at the exact cube root: cbrtStep(m³, m) = m. -/
theorem cbrtStep_fixed_point_on_perfect_cube
    (m : Nat) (hm : 0 < m) :
    cbrtStep (m * m * m) m = m := by
  unfold cbrtStep
  have hzz : 0 < m * m := Nat.mul_pos hm hm
  have hdiv : m * m * m / (m * m) = m := by
    rw [Nat.mul_assoc]
    exact Nat.mul_div_cancel m hzz
  rw [hdiv]
  omega

/-- On a perfect cube, cbrtStep from m+d with d² < m gives exactly m.
    Key: m³ < (m-2d+3)(m+d)², so floor(m³/(m+d)²) ≤ m-2d+2,
    giving numerator ≤ 3m+2, so step = m.
    The strict inequality follows from 3(m+d)² > d²(3m+2d) when d² < m. -/
theorem cbrtStep_eq_on_perfect_cube_of_sq_lt
    (m d : Nat) (hm : 2 ≤ m) (h2d : 2 * d ≤ m) (hdsq : d * d < m) :
    cbrtStep (m * m * m) (m + d) = m := by
  by_cases hd0 : d = 0
  · subst hd0; simp only [Nat.add_zero]
    exact cbrtStep_fixed_point_on_perfect_cube m (by omega)
  · have hd : 0 < d := Nat.pos_of_ne_zero hd0
    -- Lower bound from floor bound
    have hlo : m ≤ cbrtStep (m * m * m) (m + d) :=
      cbrt_step_floor_bound (m * m * m) (m + d) m (by omega) (Nat.le_refl _)
    -- Upper bound: suffices numerator ≤ 3m+2
    suffices hup : cbrtStep (m * m * m) (m + d) ≤ m by omega
    unfold cbrtStep
    let z := m + d
    have hz : 0 < z := by omega
    have hzz : 0 < z * z := Nat.mul_pos hz hz
    -- Goal: (m*m*m / (z*z) + 2*z) / 3 ≤ m, i.e., numerator ≤ 3m+2
    -- Strategy: show m³ < (m-2d+3)*z², so m³/z² ≤ m-2d+2, so num ≤ 3m+2, so step ≤ m.
    -- Key inequality using d² < m: d²(3m+2d) < 3z².
    have hkey : d * d * (3 * m + 2 * d) < 3 * (z * z) := by
      -- d²(3m+2d) < m(3m+2d) ≤ 3(m+d)²
      have h3m2d : 0 < 3 * m + 2 * d := by omega
      have hstep1 : d * d * (3 * m + 2 * d) < m * (3 * m + 2 * d) :=
        Nat.mul_lt_mul_of_pos_right hdsq h3m2d
      -- m(3m+2d) ≤ 3(m+d)²: expand both sides to mm + md + dd terms
      have hstep2 : m * (3 * m + 2 * d) ≤ 3 * (z * z) := by
        show m * (3 * m + 2 * d) ≤ 3 * ((m + d) * (m + d))
        -- LHS = 3mm + 2md. RHS = 3mm + 6md + 3dd. Diff = 4md + 3dd ≥ 0.
        have hLmm : m * (3 * m) = 3 * (m * m) := by
          rw [← Nat.mul_assoc, Nat.mul_comm m 3, Nat.mul_assoc]
        have hLmd : m * (2 * d) = 2 * (m * d) := by
          rw [← Nat.mul_assoc, Nat.mul_comm m 2, Nat.mul_assoc]
        have hR : (m + d) * (m + d) = m * m + 2 * (m * d) + d * d := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm d m]; omega
        rw [Nat.mul_add m, hLmm, hLmd, hR]; omega
      exact Nat.lt_of_lt_of_le hstep1 hstep2
    -- Polynomial identity: m³ = z²(m-2d) + d²(3m+2d).
    -- Substitute a = m - 2d to eliminate Nat subtraction, then expand both sides.
    have hident : m * m * m = z * z * (m - 2 * d) + d * d * (3 * m + 2 * d) := by
      show m * m * m = (m + d) * (m + d) * (m - 2 * d) + d * d * (3 * m + 2 * d)
      generalize ha : m - 2 * d = a
      have hm_eq : m = a + 2 * d := by omega
      subst hm_eq
      -- Both sides expand to a³+6a²d+12ad²+8d³
      have h3 : (a + 2 * d) + d = a + 3 * d := by omega
      have h8 : 3 * (a + 2 * d) + 2 * d = 3 * a + 8 * d := by omega
      rw [h3, h8]
      rw [show 2 * d = d + d from by omega,
          show 3 * d = d + (d + d) from by omega,
          show 3 * a = a + (a + a) from by omega,
          show 8 * d = d + (d + (d + (d + (d + (d + (d + d)))))) from by omega]
      simp only [Nat.add_mul, Nat.mul_add]
      simp only [Nat.mul_assoc]
      simp only [Nat.mul_comm d a, Nat.mul_left_comm d a]
      omega
    -- Combine the identity and key inequality to get m³ < (m-2d+3)*z².
    have hlt : m * m * m < (m - 2 * d + 3) * (z * z) := by
      calc m * m * m
          = z * z * (m - 2 * d) + d * d * (3 * m + 2 * d) := hident
        _ < z * z * (m - 2 * d) + 3 * (z * z) := Nat.add_lt_add_left hkey _
        _ = z * z * (m - 2 * d) + z * z * 3 := by rw [Nat.mul_comm 3 _]
        _ = z * z * (m - 2 * d + 3) := by rw [← Nat.mul_add]
        _ = (m - 2 * d + 3) * (z * z) := Nat.mul_comm _ _
    -- Divide by z² to get m³/z² < m-2d+3, hence m³/z² ≤ m-2d+2.
    have hdiv_lt : m * m * m / (z * z) < m - 2 * d + 3 :=
      (Nat.div_lt_iff_lt_mul hzz).2 hlt
    have hdiv_le : m * m * m / (z * z) ≤ m - 2 * d + 2 := by omega
    -- numerator = floor(m³/z²) + 2z ≤ (m-2d+2) + 2(m+d) = 3m+2
    have hnum_le : m * m * m / (z * z) + 2 * z ≤ 3 * m + 2 := by omega
    -- (3m+2)/3 ≤ m: use Nat.div_le_div_right on the numerator bound
    exact Nat.le_trans (Nat.div_le_div_right hnum_le) (by omega)

set_option maxRecDepth 1000000 in
/-- Finite check: innerCbrt(m³) = m for all m ≤ 255 (m³ < 2^24). -/
theorem innerCbrt_on_perfect_cube_small_nat (m : Nat) (hm : m < 256) :
    innerCbrt (m * m * m) = m := by
  match m with
  | 0 =>
    unfold innerCbrt cbrtSeed
    rw [Nat.log2_zero]
    decide
  | 1 =>
    have hlog : Nat.log2 (1 * 1 * 1) = 0 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 2 =>
    have hlog : Nat.log2 (2 * 2 * 2) = 3 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 3 =>
    have hlog : Nat.log2 (3 * 3 * 3) = 4 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 4 =>
    have hlog : Nat.log2 (4 * 4 * 4) = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 5 =>
    have hlog : Nat.log2 (5 * 5 * 5) = 6 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 6 =>
    have hlog : Nat.log2 (6 * 6 * 6) = 7 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 7 =>
    have hlog : Nat.log2 (7 * 7 * 7) = 8 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 8 =>
    have hlog : Nat.log2 (8 * 8 * 8) = 9 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 9 =>
    have hlog : Nat.log2 (9 * 9 * 9) = 9 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 10 =>
    have hlog : Nat.log2 (10 * 10 * 10) = 9 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 11 =>
    have hlog : Nat.log2 (11 * 11 * 11) = 10 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 12 =>
    have hlog : Nat.log2 (12 * 12 * 12) = 10 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 13 =>
    have hlog : Nat.log2 (13 * 13 * 13) = 11 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 14 =>
    have hlog : Nat.log2 (14 * 14 * 14) = 11 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 15 =>
    have hlog : Nat.log2 (15 * 15 * 15) = 11 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 16 =>
    have hlog : Nat.log2 (16 * 16 * 16) = 12 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 17 =>
    have hlog : Nat.log2 (17 * 17 * 17) = 12 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 18 =>
    have hlog : Nat.log2 (18 * 18 * 18) = 12 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 19 =>
    have hlog : Nat.log2 (19 * 19 * 19) = 12 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 20 =>
    have hlog : Nat.log2 (20 * 20 * 20) = 12 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 21 =>
    have hlog : Nat.log2 (21 * 21 * 21) = 13 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 22 =>
    have hlog : Nat.log2 (22 * 22 * 22) = 13 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 23 =>
    have hlog : Nat.log2 (23 * 23 * 23) = 13 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 24 =>
    have hlog : Nat.log2 (24 * 24 * 24) = 13 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 25 =>
    have hlog : Nat.log2 (25 * 25 * 25) = 13 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 26 =>
    have hlog : Nat.log2 (26 * 26 * 26) = 14 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 27 =>
    have hlog : Nat.log2 (27 * 27 * 27) = 14 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 28 =>
    have hlog : Nat.log2 (28 * 28 * 28) = 14 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 29 =>
    have hlog : Nat.log2 (29 * 29 * 29) = 14 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 30 =>
    have hlog : Nat.log2 (30 * 30 * 30) = 14 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 31 =>
    have hlog : Nat.log2 (31 * 31 * 31) = 14 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 32 =>
    have hlog : Nat.log2 (32 * 32 * 32) = 15 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 33 =>
    have hlog : Nat.log2 (33 * 33 * 33) = 15 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 34 =>
    have hlog : Nat.log2 (34 * 34 * 34) = 15 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 35 =>
    have hlog : Nat.log2 (35 * 35 * 35) = 15 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 36 =>
    have hlog : Nat.log2 (36 * 36 * 36) = 15 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 37 =>
    have hlog : Nat.log2 (37 * 37 * 37) = 15 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 38 =>
    have hlog : Nat.log2 (38 * 38 * 38) = 15 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 39 =>
    have hlog : Nat.log2 (39 * 39 * 39) = 15 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 40 =>
    have hlog : Nat.log2 (40 * 40 * 40) = 15 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 41 =>
    have hlog : Nat.log2 (41 * 41 * 41) = 16 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 42 =>
    have hlog : Nat.log2 (42 * 42 * 42) = 16 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 43 =>
    have hlog : Nat.log2 (43 * 43 * 43) = 16 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 44 =>
    have hlog : Nat.log2 (44 * 44 * 44) = 16 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 45 =>
    have hlog : Nat.log2 (45 * 45 * 45) = 16 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 46 =>
    have hlog : Nat.log2 (46 * 46 * 46) = 16 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 47 =>
    have hlog : Nat.log2 (47 * 47 * 47) = 16 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 48 =>
    have hlog : Nat.log2 (48 * 48 * 48) = 16 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 49 =>
    have hlog : Nat.log2 (49 * 49 * 49) = 16 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 50 =>
    have hlog : Nat.log2 (50 * 50 * 50) = 16 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 51 =>
    have hlog : Nat.log2 (51 * 51 * 51) = 17 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 52 =>
    have hlog : Nat.log2 (52 * 52 * 52) = 17 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 53 =>
    have hlog : Nat.log2 (53 * 53 * 53) = 17 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 54 =>
    have hlog : Nat.log2 (54 * 54 * 54) = 17 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 55 =>
    have hlog : Nat.log2 (55 * 55 * 55) = 17 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 56 =>
    have hlog : Nat.log2 (56 * 56 * 56) = 17 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 57 =>
    have hlog : Nat.log2 (57 * 57 * 57) = 17 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 58 =>
    have hlog : Nat.log2 (58 * 58 * 58) = 17 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 59 =>
    have hlog : Nat.log2 (59 * 59 * 59) = 17 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 60 =>
    have hlog : Nat.log2 (60 * 60 * 60) = 17 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 61 =>
    have hlog : Nat.log2 (61 * 61 * 61) = 17 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 62 =>
    have hlog : Nat.log2 (62 * 62 * 62) = 17 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 63 =>
    have hlog : Nat.log2 (63 * 63 * 63) = 17 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 64 =>
    have hlog : Nat.log2 (64 * 64 * 64) = 18 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 65 =>
    have hlog : Nat.log2 (65 * 65 * 65) = 18 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 66 =>
    have hlog : Nat.log2 (66 * 66 * 66) = 18 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 67 =>
    have hlog : Nat.log2 (67 * 67 * 67) = 18 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 68 =>
    have hlog : Nat.log2 (68 * 68 * 68) = 18 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 69 =>
    have hlog : Nat.log2 (69 * 69 * 69) = 18 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 70 =>
    have hlog : Nat.log2 (70 * 70 * 70) = 18 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 71 =>
    have hlog : Nat.log2 (71 * 71 * 71) = 18 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 72 =>
    have hlog : Nat.log2 (72 * 72 * 72) = 18 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 73 =>
    have hlog : Nat.log2 (73 * 73 * 73) = 18 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 74 =>
    have hlog : Nat.log2 (74 * 74 * 74) = 18 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 75 =>
    have hlog : Nat.log2 (75 * 75 * 75) = 18 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 76 =>
    have hlog : Nat.log2 (76 * 76 * 76) = 18 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 77 =>
    have hlog : Nat.log2 (77 * 77 * 77) = 18 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 78 =>
    have hlog : Nat.log2 (78 * 78 * 78) = 18 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 79 =>
    have hlog : Nat.log2 (79 * 79 * 79) = 18 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 80 =>
    have hlog : Nat.log2 (80 * 80 * 80) = 18 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 81 =>
    have hlog : Nat.log2 (81 * 81 * 81) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 82 =>
    have hlog : Nat.log2 (82 * 82 * 82) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 83 =>
    have hlog : Nat.log2 (83 * 83 * 83) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 84 =>
    have hlog : Nat.log2 (84 * 84 * 84) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 85 =>
    have hlog : Nat.log2 (85 * 85 * 85) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 86 =>
    have hlog : Nat.log2 (86 * 86 * 86) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 87 =>
    have hlog : Nat.log2 (87 * 87 * 87) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 88 =>
    have hlog : Nat.log2 (88 * 88 * 88) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 89 =>
    have hlog : Nat.log2 (89 * 89 * 89) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 90 =>
    have hlog : Nat.log2 (90 * 90 * 90) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 91 =>
    have hlog : Nat.log2 (91 * 91 * 91) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 92 =>
    have hlog : Nat.log2 (92 * 92 * 92) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 93 =>
    have hlog : Nat.log2 (93 * 93 * 93) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 94 =>
    have hlog : Nat.log2 (94 * 94 * 94) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 95 =>
    have hlog : Nat.log2 (95 * 95 * 95) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 96 =>
    have hlog : Nat.log2 (96 * 96 * 96) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 97 =>
    have hlog : Nat.log2 (97 * 97 * 97) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 98 =>
    have hlog : Nat.log2 (98 * 98 * 98) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 99 =>
    have hlog : Nat.log2 (99 * 99 * 99) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 100 =>
    have hlog : Nat.log2 (100 * 100 * 100) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 101 =>
    have hlog : Nat.log2 (101 * 101 * 101) = 19 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 102 =>
    have hlog : Nat.log2 (102 * 102 * 102) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 103 =>
    have hlog : Nat.log2 (103 * 103 * 103) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 104 =>
    have hlog : Nat.log2 (104 * 104 * 104) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 105 =>
    have hlog : Nat.log2 (105 * 105 * 105) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 106 =>
    have hlog : Nat.log2 (106 * 106 * 106) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 107 =>
    have hlog : Nat.log2 (107 * 107 * 107) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 108 =>
    have hlog : Nat.log2 (108 * 108 * 108) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 109 =>
    have hlog : Nat.log2 (109 * 109 * 109) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 110 =>
    have hlog : Nat.log2 (110 * 110 * 110) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 111 =>
    have hlog : Nat.log2 (111 * 111 * 111) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 112 =>
    have hlog : Nat.log2 (112 * 112 * 112) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 113 =>
    have hlog : Nat.log2 (113 * 113 * 113) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 114 =>
    have hlog : Nat.log2 (114 * 114 * 114) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 115 =>
    have hlog : Nat.log2 (115 * 115 * 115) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 116 =>
    have hlog : Nat.log2 (116 * 116 * 116) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 117 =>
    have hlog : Nat.log2 (117 * 117 * 117) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 118 =>
    have hlog : Nat.log2 (118 * 118 * 118) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 119 =>
    have hlog : Nat.log2 (119 * 119 * 119) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 120 =>
    have hlog : Nat.log2 (120 * 120 * 120) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 121 =>
    have hlog : Nat.log2 (121 * 121 * 121) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 122 =>
    have hlog : Nat.log2 (122 * 122 * 122) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 123 =>
    have hlog : Nat.log2 (123 * 123 * 123) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 124 =>
    have hlog : Nat.log2 (124 * 124 * 124) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 125 =>
    have hlog : Nat.log2 (125 * 125 * 125) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 126 =>
    have hlog : Nat.log2 (126 * 126 * 126) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 127 =>
    have hlog : Nat.log2 (127 * 127 * 127) = 20 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 128 =>
    have hlog : Nat.log2 (128 * 128 * 128) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 129 =>
    have hlog : Nat.log2 (129 * 129 * 129) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 130 =>
    have hlog : Nat.log2 (130 * 130 * 130) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 131 =>
    have hlog : Nat.log2 (131 * 131 * 131) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 132 =>
    have hlog : Nat.log2 (132 * 132 * 132) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 133 =>
    have hlog : Nat.log2 (133 * 133 * 133) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 134 =>
    have hlog : Nat.log2 (134 * 134 * 134) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 135 =>
    have hlog : Nat.log2 (135 * 135 * 135) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 136 =>
    have hlog : Nat.log2 (136 * 136 * 136) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 137 =>
    have hlog : Nat.log2 (137 * 137 * 137) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 138 =>
    have hlog : Nat.log2 (138 * 138 * 138) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 139 =>
    have hlog : Nat.log2 (139 * 139 * 139) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 140 =>
    have hlog : Nat.log2 (140 * 140 * 140) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 141 =>
    have hlog : Nat.log2 (141 * 141 * 141) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 142 =>
    have hlog : Nat.log2 (142 * 142 * 142) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 143 =>
    have hlog : Nat.log2 (143 * 143 * 143) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 144 =>
    have hlog : Nat.log2 (144 * 144 * 144) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 145 =>
    have hlog : Nat.log2 (145 * 145 * 145) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 146 =>
    have hlog : Nat.log2 (146 * 146 * 146) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 147 =>
    have hlog : Nat.log2 (147 * 147 * 147) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 148 =>
    have hlog : Nat.log2 (148 * 148 * 148) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 149 =>
    have hlog : Nat.log2 (149 * 149 * 149) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 150 =>
    have hlog : Nat.log2 (150 * 150 * 150) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 151 =>
    have hlog : Nat.log2 (151 * 151 * 151) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 152 =>
    have hlog : Nat.log2 (152 * 152 * 152) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 153 =>
    have hlog : Nat.log2 (153 * 153 * 153) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 154 =>
    have hlog : Nat.log2 (154 * 154 * 154) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 155 =>
    have hlog : Nat.log2 (155 * 155 * 155) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 156 =>
    have hlog : Nat.log2 (156 * 156 * 156) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 157 =>
    have hlog : Nat.log2 (157 * 157 * 157) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 158 =>
    have hlog : Nat.log2 (158 * 158 * 158) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 159 =>
    have hlog : Nat.log2 (159 * 159 * 159) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 160 =>
    have hlog : Nat.log2 (160 * 160 * 160) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 161 =>
    have hlog : Nat.log2 (161 * 161 * 161) = 21 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 162 =>
    have hlog : Nat.log2 (162 * 162 * 162) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 163 =>
    have hlog : Nat.log2 (163 * 163 * 163) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 164 =>
    have hlog : Nat.log2 (164 * 164 * 164) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 165 =>
    have hlog : Nat.log2 (165 * 165 * 165) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 166 =>
    have hlog : Nat.log2 (166 * 166 * 166) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 167 =>
    have hlog : Nat.log2 (167 * 167 * 167) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 168 =>
    have hlog : Nat.log2 (168 * 168 * 168) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 169 =>
    have hlog : Nat.log2 (169 * 169 * 169) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 170 =>
    have hlog : Nat.log2 (170 * 170 * 170) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 171 =>
    have hlog : Nat.log2 (171 * 171 * 171) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 172 =>
    have hlog : Nat.log2 (172 * 172 * 172) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 173 =>
    have hlog : Nat.log2 (173 * 173 * 173) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 174 =>
    have hlog : Nat.log2 (174 * 174 * 174) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 175 =>
    have hlog : Nat.log2 (175 * 175 * 175) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 176 =>
    have hlog : Nat.log2 (176 * 176 * 176) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 177 =>
    have hlog : Nat.log2 (177 * 177 * 177) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 178 =>
    have hlog : Nat.log2 (178 * 178 * 178) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 179 =>
    have hlog : Nat.log2 (179 * 179 * 179) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 180 =>
    have hlog : Nat.log2 (180 * 180 * 180) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 181 =>
    have hlog : Nat.log2 (181 * 181 * 181) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 182 =>
    have hlog : Nat.log2 (182 * 182 * 182) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 183 =>
    have hlog : Nat.log2 (183 * 183 * 183) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 184 =>
    have hlog : Nat.log2 (184 * 184 * 184) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 185 =>
    have hlog : Nat.log2 (185 * 185 * 185) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 186 =>
    have hlog : Nat.log2 (186 * 186 * 186) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 187 =>
    have hlog : Nat.log2 (187 * 187 * 187) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 188 =>
    have hlog : Nat.log2 (188 * 188 * 188) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 189 =>
    have hlog : Nat.log2 (189 * 189 * 189) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 190 =>
    have hlog : Nat.log2 (190 * 190 * 190) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 191 =>
    have hlog : Nat.log2 (191 * 191 * 191) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 192 =>
    have hlog : Nat.log2 (192 * 192 * 192) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 193 =>
    have hlog : Nat.log2 (193 * 193 * 193) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 194 =>
    have hlog : Nat.log2 (194 * 194 * 194) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 195 =>
    have hlog : Nat.log2 (195 * 195 * 195) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 196 =>
    have hlog : Nat.log2 (196 * 196 * 196) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 197 =>
    have hlog : Nat.log2 (197 * 197 * 197) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 198 =>
    have hlog : Nat.log2 (198 * 198 * 198) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 199 =>
    have hlog : Nat.log2 (199 * 199 * 199) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 200 =>
    have hlog : Nat.log2 (200 * 200 * 200) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 201 =>
    have hlog : Nat.log2 (201 * 201 * 201) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 202 =>
    have hlog : Nat.log2 (202 * 202 * 202) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 203 =>
    have hlog : Nat.log2 (203 * 203 * 203) = 22 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 204 =>
    have hlog : Nat.log2 (204 * 204 * 204) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 205 =>
    have hlog : Nat.log2 (205 * 205 * 205) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 206 =>
    have hlog : Nat.log2 (206 * 206 * 206) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 207 =>
    have hlog : Nat.log2 (207 * 207 * 207) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 208 =>
    have hlog : Nat.log2 (208 * 208 * 208) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 209 =>
    have hlog : Nat.log2 (209 * 209 * 209) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 210 =>
    have hlog : Nat.log2 (210 * 210 * 210) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 211 =>
    have hlog : Nat.log2 (211 * 211 * 211) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 212 =>
    have hlog : Nat.log2 (212 * 212 * 212) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 213 =>
    have hlog : Nat.log2 (213 * 213 * 213) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 214 =>
    have hlog : Nat.log2 (214 * 214 * 214) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 215 =>
    have hlog : Nat.log2 (215 * 215 * 215) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 216 =>
    have hlog : Nat.log2 (216 * 216 * 216) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 217 =>
    have hlog : Nat.log2 (217 * 217 * 217) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 218 =>
    have hlog : Nat.log2 (218 * 218 * 218) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 219 =>
    have hlog : Nat.log2 (219 * 219 * 219) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 220 =>
    have hlog : Nat.log2 (220 * 220 * 220) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 221 =>
    have hlog : Nat.log2 (221 * 221 * 221) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 222 =>
    have hlog : Nat.log2 (222 * 222 * 222) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 223 =>
    have hlog : Nat.log2 (223 * 223 * 223) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 224 =>
    have hlog : Nat.log2 (224 * 224 * 224) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 225 =>
    have hlog : Nat.log2 (225 * 225 * 225) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 226 =>
    have hlog : Nat.log2 (226 * 226 * 226) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 227 =>
    have hlog : Nat.log2 (227 * 227 * 227) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 228 =>
    have hlog : Nat.log2 (228 * 228 * 228) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 229 =>
    have hlog : Nat.log2 (229 * 229 * 229) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 230 =>
    have hlog : Nat.log2 (230 * 230 * 230) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 231 =>
    have hlog : Nat.log2 (231 * 231 * 231) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 232 =>
    have hlog : Nat.log2 (232 * 232 * 232) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 233 =>
    have hlog : Nat.log2 (233 * 233 * 233) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 234 =>
    have hlog : Nat.log2 (234 * 234 * 234) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 235 =>
    have hlog : Nat.log2 (235 * 235 * 235) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 236 =>
    have hlog : Nat.log2 (236 * 236 * 236) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 237 =>
    have hlog : Nat.log2 (237 * 237 * 237) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 238 =>
    have hlog : Nat.log2 (238 * 238 * 238) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 239 =>
    have hlog : Nat.log2 (239 * 239 * 239) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 240 =>
    have hlog : Nat.log2 (240 * 240 * 240) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 241 =>
    have hlog : Nat.log2 (241 * 241 * 241) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 242 =>
    have hlog : Nat.log2 (242 * 242 * 242) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 243 =>
    have hlog : Nat.log2 (243 * 243 * 243) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 244 =>
    have hlog : Nat.log2 (244 * 244 * 244) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 245 =>
    have hlog : Nat.log2 (245 * 245 * 245) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 246 =>
    have hlog : Nat.log2 (246 * 246 * 246) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 247 =>
    have hlog : Nat.log2 (247 * 247 * 247) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 248 =>
    have hlog : Nat.log2 (248 * 248 * 248) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 249 =>
    have hlog : Nat.log2 (249 * 249 * 249) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 250 =>
    have hlog : Nat.log2 (250 * 250 * 250) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 251 =>
    have hlog : Nat.log2 (251 * 251 * 251) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 252 =>
    have hlog : Nat.log2 (252 * 252 * 252) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 253 =>
    have hlog : Nat.log2 (253 * 253 * 253) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 254 =>
    have hlog : Nat.log2 (254 * 254 * 254) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | 255 =>
    have hlog : Nat.log2 (255 * 255 * 255) = 23 :=
      log2_eq_of_pow_bounds (by decide) (by decide)
    unfold innerCbrt cbrtSeed
    rw [hlog]
    decide
  | _ + 256 => omega

theorem innerCbrt_on_perfect_cube_small :
    ∀ i : Fin 256, innerCbrt (i.val * i.val * i.val) = i.val := by
  intro i
  exact innerCbrt_on_perfect_cube_small_nat i.val i.2

-- ============================================================================
-- Floor correction
-- ============================================================================

/-- The cbrt floor correction is correct.
    Given z > 0, (z-1)³ ≤ x < (z+1)³, the correction gives icbrt(x).
    Correction: if x/(z*z) < z then z-1 else z.
    When x/(z*z) < z: z³ > x, so z is a ceiling → return z-1.
    When x/(z*z) ≥ z: z³ ≤ x, so z is the floor → return z. -/
theorem cbrt_floor_correction (x z : Nat) (hz : 0 < z)
    (hlo : (z - 1) * (z - 1) * (z - 1) ≤ x)
    (hhi : x < (z + 1) * (z + 1) * (z + 1)) :
    let r := if x / (z * z) < z then z - 1 else z
    r * r * r ≤ x ∧ x < (r + 1) * (r + 1) * (r + 1) := by
  simp only
  have hzz : 0 < z * z := Nat.mul_pos hz hz
  by_cases h_lt : x / (z * z) < z
  · -- x/(z²) < z means z³ > x
    simp [h_lt]
    have h_zcube : x < z * z * z := by
      have h_euc := Nat.div_add_mod x (z * z)
      have h_mod := Nat.mod_lt x hzz
      have h1 : x < (z * z) * (x / (z * z) + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
      have h2 : x / (z * z) + 1 ≤ z := by omega
      calc x < z * z * (x / (z * z) + 1) := h1
        _ ≤ z * z * z := Nat.mul_le_mul_left (z * z) h2
    constructor
    · exact hlo
    · have : z - 1 + 1 = z := by omega
      rw [this]; exact h_zcube
  · -- x/(z²) ≥ z means z³ ≤ x
    simp [h_lt]
    simp only [Nat.not_lt] at h_lt
    have h_zcube : z * z * z ≤ x := by
      have h_div_le : z * z * (x / (z * z)) ≤ x := Nat.mul_div_le x (z * z)
      calc z * z * z
          ≤ z * z * (x / (z * z)) := Nat.mul_le_mul_left (z * z) h_lt
        _ ≤ x := h_div_le
    exact ⟨h_zcube, hhi⟩

/-- If `innerCbrt` is bracketed by ±1 around the true floor root, floor correction returns `icbrt`. -/
private theorem floorCbrt_eq_icbrt_of_bounds (x : Nat)
    (hz : 0 < innerCbrt x)
    (hlo : (innerCbrt x - 1) * (innerCbrt x - 1) * (innerCbrt x - 1) ≤ x)
    (hhi : x < (innerCbrt x + 1) * (innerCbrt x + 1) * (innerCbrt x + 1)) :
    floorCbrt x = icbrt x := by
  let r := if x / (innerCbrt x * innerCbrt x) < innerCbrt x then innerCbrt x - 1 else innerCbrt x
  have hcorr : r * r * r ≤ x ∧ x < (r + 1) * (r + 1) * (r + 1) := by
    simpa [r] using cbrt_floor_correction x (innerCbrt x) hz hlo hhi
  have hr : floorCbrt x = r := by
    unfold floorCbrt
    rfl
  exact hr.trans (icbrt_eq_of_bounds x r hcorr.1 hcorr.2)

/-- End-to-end floor correctness, with the remaining upper-bound link explicit. -/
theorem floorCbrt_correct_of_upper (x : Nat) (hx : 0 < x)
    (hupper : innerCbrt x ≤ icbrt x + 1) :
    floorCbrt x = icbrt x := by
  have hz := innerCbrt_pos x hx
  have hlo := innerCbrt_pred_cube_le_of_upper x hupper
  have hhi := innerCbrt_lt_succ_cube x hx
  exact floorCbrt_eq_icbrt_of_bounds x hz hlo hhi
