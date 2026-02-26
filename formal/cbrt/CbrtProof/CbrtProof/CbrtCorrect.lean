/-
  Full correctness proof of Cbrt.sol:_cbrt and cbrt.

  This file now includes:
  1) A concrete integer cube-root function `icbrt` with formal floor specification.
  2) Explicit (named) correctness theorems for `innerCbrt` and `floorCbrt`,
     parameterized by the remaining upper-bound hypothesis
     `innerCbrt x ≤ icbrt x + 1`.
-/
import Init
import CbrtProof.FloorBound

-- ============================================================================
-- Part 1: Definitions matching Cbrt.sol EVM semantics
-- ============================================================================

/-- One Newton-Raphson step for cube root: ⌊(⌊x/z²⌋ + 2z) / 3⌋.
    Matches EVM: div(add(add(div(x, mul(z, z)), z), z), 3) -/
def cbrtStep (x z : Nat) : Nat := (x / (z * z) + 2 * z) / 3

/-- The cbrt seed. For x > 0:
    z = ⌊233 * 2^q / 256⌋ + 1  where q = ⌊(log2(x) + 2) / 3⌋.
    Matches EVM: add(shr(8, shl(div(sub(257, clz(x)), 3), 0xe9)), lt(0x00, x)) -/
def cbrtSeed (x : Nat) : Nat :=
  if x = 0 then 0
  else (0xe9 <<< ((Nat.log2 x + 2) / 3)) >>> 8 + 1

/-- _cbrt: seed + 6 Newton-Raphson steps. -/
def innerCbrt (x : Nat) : Nat :=
  if x = 0 then 0
  else
    let z := cbrtSeed x
    let z := cbrtStep x z
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
  if z = 0 then 0
  else if x / (z * z) < z then z - 1 else z

-- ============================================================================
-- Part 1b: Reference integer cube root (floor)
-- ============================================================================

/-- `r` is the integer floor cube root of `x`. -/
def IsICbrt (x r : Nat) : Prop :=
  r * r * r ≤ x ∧ x < (r + 1) * (r + 1) * (r + 1)

/-- Search helper: largest `m ≤ n` such that `m^3 ≤ x`. -/
def icbrtAux (x n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => if (n + 1) * (n + 1) * (n + 1) ≤ x then n + 1 else icbrtAux x n

/-- Reference integer cube root (floor). -/
def icbrt (x : Nat) : Nat :=
  icbrtAux x x

private theorem cube_monotone {a b : Nat} (h : a ≤ b) :
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

private theorem icbrtAux_cube_le (x n : Nat) :
    icbrtAux x n * icbrtAux x n * icbrtAux x n ≤ x := by
  induction n with
  | zero => simp [icbrtAux]
  | succ n ih =>
      by_cases h : (n + 1) * (n + 1) * (n + 1) ≤ x
      · simp [icbrtAux, h]
      · simpa [icbrtAux, h] using ih

private theorem icbrtAux_greatest (x : Nat) :
    ∀ n m, m ≤ n → m * m * m ≤ x → m ≤ icbrtAux x n := by
  intro n
  induction n with
  | zero =>
      intro m hmn hm
      have hm0 : m = 0 := by omega
      subst hm0
      simp [icbrtAux]
  | succ n ih =>
      intro m hmn hm
      by_cases h : (n + 1) * (n + 1) * (n + 1) ≤ x
      · simp [icbrtAux, h]
        exact hmn
      · have hm_le_n : m ≤ n := by
          by_cases hm_eq : m = n + 1
          · subst hm_eq
            exact False.elim (h hm)
          · omega
        have hm_le_aux : m ≤ icbrtAux x n := ih m hm_le_n hm
        simpa [icbrtAux, h] using hm_le_aux

/-- Lower half of the floor specification: `icbrt(x)^3 ≤ x`. -/
theorem icbrt_cube_le (x : Nat) :
    icbrt x * icbrt x * icbrt x ≤ x := by
  unfold icbrt
  exact icbrtAux_cube_le x x

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
      unfold icbrt
      exact icbrtAux_greatest x x (icbrt x + 1) hmx hle
    exact False.elim ((Nat.not_succ_le_self (icbrt x)) hmax)

/-- `icbrt` satisfies the exact floor-cube-root predicate. -/
theorem icbrt_spec (x : Nat) : IsICbrt x (icbrt x) := by
  exact ⟨icbrt_cube_le x, icbrt_lt_succ_cube x⟩

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
    unfold icbrt
    exact icbrtAux_greatest x x r hrx hlo
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
-- Part 2: Computational verification of convergence (upper bound)
-- ============================================================================

/-- Compute the max-propagation upper bound for octave n.
    Uses x_max = 2^(n+1) - 1 and the seed for 2^n. -/
def cbrtMaxProp (n : Nat) : Nat :=
  let x_max := 2 ^ (n + 1) - 1
  let z := cbrtSeed (2 ^ n)
  let z := cbrtStep x_max z
  let z := cbrtStep x_max z
  let z := cbrtStep x_max z
  let z := cbrtStep x_max z
  let z := cbrtStep x_max z
  let z := cbrtStep x_max z
  z

/-- Check convergence for octave n:
    (Z₆ - 1)³ ≤ x_max  (Z₆ is at most icbrt(x_max) + 1)
    AND Z₆ > 0         (division safety) -/
def cbrtCheckOctave (n : Nat) : Bool :=
  let x_max := 2 ^ (n + 1) - 1
  let z := cbrtMaxProp n
  (z - 1) * ((z - 1) * (z - 1)) ≤ x_max && z > 0

/-- Check that the cbrt seed is positive for all octaves. -/
def cbrtCheckSeedPos (n : Nat) : Bool :=
  cbrtSeed (2 ^ n) > 0

/-- The critical computational check: all 256 octaves converge. -/
theorem cbrt_all_octaves_pass : ∀ i : Fin 256, cbrtCheckOctave i.val = true := by
  native_decide

/-- Seeds are always positive. -/
theorem cbrt_all_seeds_pos : ∀ i : Fin 256, cbrtCheckSeedPos i.val = true := by
  native_decide

-- ============================================================================
-- Part 3: Lower bound (composing cbrt_step_floor_bound)
-- ============================================================================

/-- The cbrt seed is positive for x > 0. -/
theorem cbrtSeed_pos (x : Nat) (hx : 0 < x) : 0 < cbrtSeed x := by
  unfold cbrtSeed
  simp [Nat.ne_of_gt hx]

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

/-- innerCbrt gives a lower bound: for any m with m³ ≤ x, m ≤ innerCbrt(x). -/
theorem innerCbrt_lower (x m : Nat) (hx : 0 < x)
    (hm : m * m * m ≤ x) : m ≤ innerCbrt x := by
  unfold innerCbrt
  simp [Nat.ne_of_gt hx]
  have hs := cbrtSeed_pos x hx
  have h1 := cbrtStep_pos x _ hx hs
  have h2 := cbrtStep_pos x _ hx h1
  have h3 := cbrtStep_pos x _ hx h2
  have h4 := cbrtStep_pos x _ hx h3
  have h5 := cbrtStep_pos x _ hx h4
  exact cbrt_step_floor_bound x _ m h5 hm

-- ============================================================================
-- Part 4: Main correctness theorems (under explicit upper-bound hypothesis)
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
-- Part 5: Floor correction (local lemma)
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
theorem floorCbrt_eq_icbrt_of_bounds (x : Nat)
    (hz : 0 < innerCbrt x)
    (hlo : (innerCbrt x - 1) * (innerCbrt x - 1) * (innerCbrt x - 1) ≤ x)
    (hhi : x < (innerCbrt x + 1) * (innerCbrt x + 1) * (innerCbrt x + 1)) :
    floorCbrt x = icbrt x := by
  let r := if x / (innerCbrt x * innerCbrt x) < innerCbrt x then innerCbrt x - 1 else innerCbrt x
  have hcorr : r * r * r ≤ x ∧ x < (r + 1) * (r + 1) * (r + 1) := by
    simpa [r] using cbrt_floor_correction x (innerCbrt x) hz hlo hhi
  have hr : floorCbrt x = r := by
    unfold floorCbrt
    simp [Nat.ne_of_gt hz, r]
  exact hr.trans (icbrt_eq_of_bounds x r hcorr.1 hcorr.2)

/-- End-to-end floor correctness, with the remaining upper-bound link explicit. -/
theorem floorCbrt_correct_of_upper (x : Nat) (hx : 0 < x)
    (hupper : innerCbrt x ≤ icbrt x + 1) :
    floorCbrt x = icbrt x := by
  have hz := innerCbrt_pos x hx
  have hlo := innerCbrt_pred_cube_le_of_upper x hupper
  have hhi := innerCbrt_lt_succ_cube x hx
  exact floorCbrt_eq_icbrt_of_bounds x hz hlo hhi

-- ============================================================================
-- Summary
-- ============================================================================

/-
  PROOF STATUS (0 sorry):

  ✓ Cubic AM-GM: cubic_am_gm
  ✓ Floor Bound: cbrt_step_floor_bound
  ✓ Reference floor root: icbrt, icbrt_spec, icbrt_eq_of_bounds
  ✓ Computational Verification: cbrt_all_octaves_pass (native_decide, 256 cases)
  ✓ Seed Positivity: cbrt_all_seeds_pos (native_decide, 256 cases)
  ✓ Lower Bound Chain: innerCbrt_lower (6x cbrt_step_floor_bound)
  ✓ Floor Correction: cbrt_floor_correction (case split on x/(z²) < z)
  ✓ Named correctness statements:
      - innerCbrt_correct_of_upper
      - floorCbrt_correct_of_upper

  Remaining external link:
    proving `innerCbrt x ≤ icbrt x + 1` end-to-end from the octave check for all x.
-/
