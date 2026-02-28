/-
  Full correctness proof of Cbrt.sol:_cbrt and cbrt.

  This file includes:
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

/-- Run five cbrt Newton steps from an explicit starting point. -/
def run5From (x z : Nat) : Nat :=
  let z := cbrtStep x z
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

/-- run6From = cbrtStep after run5From (definitional). -/
theorem run6_eq_step_run5 (x z : Nat) :
    run6From x z = cbrtStep x (run5From x z) := rfl

/-- The cbrt seed:
    z = ⌊233 * 2^q / 256⌋ + 1  where q = ⌊(log2(x) + 2) / 3⌋.
    Matches EVM: add(shr(8, shl(div(sub(257, clz(x)), 3), 0xe9)), lt(0x00, x)) -/
def cbrtSeed (x : Nat) : Nat :=
  (0xe9 <<< ((Nat.log2 x + 2) / 3)) >>> 8 + 1

/-- _cbrt: seed + 6 Newton-Raphson steps. -/
def innerCbrt (x : Nat) : Nat :=
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
  if x / (z * z) < z then z - 1 else z

-- ============================================================================
-- Part 1b: Reference integer cube root (floor)
-- ============================================================================

/-- Search helper: largest `m ≤ n` such that `m^3 ≤ x`. -/
def icbrtAux (x n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => if (n + 1) * (n + 1) * (n + 1) ≤ x then n + 1 else icbrtAux x n

/-- Reference integer cube root (floor). -/
def icbrt (x : Nat) : Nat :=
  icbrtAux x x

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
-- Part 2: Seed and step positivity
-- ============================================================================

/-- The cbrt seed is always positive (due to the +1 term). -/
theorem cbrtSeed_pos (x : Nat) : 0 < cbrtSeed x := by
  unfold cbrtSeed
  exact Nat.succ_pos _

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
-- Part 3: Upper bound machinery (one-step contraction)
-- ============================================================================

/-- Integer polynomial identity used to upper-bound one cbrt Newton step. -/
private theorem pullCoeff (x y c : Int) : x * (y * c) = c * (x * y) := by
  rw [← Int.mul_assoc x y c]
  rw [Int.mul_comm (x * y) c]

private theorem pullCoeffNested (x y z c : Int) : x * (y * (z * c)) = c * (x * (y * z)) := by
  rw [← Int.mul_assoc y z c]
  rw [pullCoeff x (y * z) c]

private theorem int_poly_identity (m d q r : Int)
    (hd2 : d * d = m * q + r) :
    ((m - 2 * d + 3 * q + 6) * ((m + d) * (m + d)) - (m + 1) * (m + 1) * (m + 1))
      =
    q * (3 * m * q + 6 * m + 3 * r + 4 * d * m)
      + (-2 * d * r + 12 * d * m + 3 * m * m - 3 * m * r - 3 * m + 6 * r - 1) := by
  simp [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  repeat rw [Int.mul_neg]
  repeat rw [Int.neg_mul]
  have hddx (x : Int) : d * (d * x) = (d * d) * x := by
    rw [← Int.mul_assoc]
  simp [hddx, hd2, Int.add_mul, Int.mul_add,
    Int.mul_assoc, Int.mul_left_comm]
  -- Normalize monomials with numeric coefficients.
  rw [pullCoeffNested m m d 2]
  rw [pullCoeffNested m m q 2]
  rw [pullCoeff m r 2]
  rw [pullCoeffNested m d q 2]
  rw [pullCoeff d r 2]
  rw [pullCoeffNested m m q 3]
  rw [pullCoeffNested m d q 3]
  rw [pullCoeff m m 6]
  rw [pullCoeff m d 6]
  rw [pullCoeff m q 6]
  rw [pullCoeff m d 12]
  rw [pullCoeffNested m d q 4]
  rw [pullCoeff m r 3]
  rw [pullCoeff m m 3]
  -- Collapse the expanded `(m + 1)^3` chunk.
  have hcube :
      m * (m * m) + m * m + (m * m + m) + (m * m + m + (m + 1))
        = m * (m * m) + 3 * (m * m) + 3 * m + 1 := by
    omega
  rw [hcube]
  omega

private theorem neg3_mul_mul (m r : Int) : -3 * m * r = -(3 * m * r) := by
  calc
    -3 * m * r = (-3 * m) * r := by rw [Int.mul_assoc]
    _ = (-(3 * m)) * r := by rw [Int.neg_mul]
    _ = -(3 * m * r) := by rw [Int.neg_mul, Int.mul_assoc]

private theorem mul_coeff_expand (m d r : Int) :
    r * (-2 * d - 3 * m + 6) = -2 * d * r - 3 * m * r + 6 * r := by
  rw [Int.mul_add]
  have hsum : -2 * d - 3 * m = (-2 * d) + (-3 * m) := by omega
  rw [hsum, Int.mul_add]
  rw [Int.mul_comm r (-2 * d), Int.mul_comm r (-3 * m), Int.mul_comm r 6]
  repeat rw [Int.sub_eq_add_neg]
  rw [neg3_mul_mul]

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
    rw [mul_coeff_expand (m := (m : Int)) (d := (d : Int)) (r := (r : Int))]
    repeat rw [Int.sub_eq_add_neg]
    ac_rfl

  have h_rewrite0 :
      (12 * (d : Int) * (m : Int) + 3 * (m : Int) * (m : Int) - 3 * (m : Int) - 1)
        + ((m - 1 : Nat) : Int) * (-2 * (d : Int) - 3 * (m : Int) + 6)
      = 10 * (d : Int) * (m : Int) + 2 * (d : Int) + 6 * (m : Int) - 7 := by
    have hm1 : 1 ≤ m := Nat.le_trans (by decide : 1 ≤ 2) hm2
    have ht : ((m - 1 : Nat) : Int) = (m : Int) - 1 := by omega
    rw [ht, Int.sub_mul, Int.one_mul]
    rw [mul_coeff_expand (m := (m : Int)) (d := (d : Int)) (r := (m : Int))]
    repeat rw [Int.sub_eq_add_neg]
    have hneg : -(-2 * (d : Int) + -(3 * (m : Int)) + 6) = 2 * (d : Int) + 3 * (m : Int) - 6 := by
      omega
    rw [hneg]
    rw [Int.mul_assoc 12 (d : Int) (m : Int)]
    rw [Int.mul_assoc (-2) (d : Int) (m : Int)]
    rw [Int.mul_assoc 10 (d : Int) (m : Int)]
    rw [Int.mul_assoc 3 (m : Int) (m : Int)]
    omega

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
-- Part 4: innerCbrt structure
-- ============================================================================

/-- `_cbrt` is exactly `run6From` from the seed (definitional). -/
theorem innerCbrt_eq_run6From_seed (x : Nat) :
    innerCbrt x = run6From x (cbrtSeed x) := rfl

/-- `_cbrt` is `cbrtStep` applied to `run5From` of the seed (definitional). -/
theorem innerCbrt_eq_step_run5_seed (x : Nat) :
    innerCbrt x = cbrtStep x (run5From x (cbrtSeed x)) := rfl

set_option maxRecDepth 1000000 in
/-- Direct finite check for small inputs. -/
private theorem innerCbrt_upper_fin256 :
    ∀ i : Fin 256, innerCbrt i.val ≤ icbrt i.val + 1 := by
  decide

/-- Small-range corollary (used for base cases). -/
theorem innerCbrt_upper_of_lt_256 (x : Nat) (hx : x < 256) :
    innerCbrt x ≤ icbrt x + 1 := by
  simpa using innerCbrt_upper_fin256 ⟨x, hx⟩

/-- innerCbrt gives a lower bound: for any m with m³ ≤ x, m ≤ innerCbrt(x). -/
theorem innerCbrt_lower (x m : Nat) (hx : 0 < x)
    (hm : m * m * m ≤ x) : m ≤ innerCbrt x := by
  unfold innerCbrt
  have hs := cbrtSeed_pos x
  have h1 := cbrtStep_pos x _ hx hs
  have h2 := cbrtStep_pos x _ hx h1
  have h3 := cbrtStep_pos x _ hx h2
  have h4 := cbrtStep_pos x _ hx h3
  have h5 := cbrtStep_pos x _ hx h4
  exact cbrt_step_floor_bound x _ m h5 hm

-- ============================================================================
-- Part 5: Main correctness theorems (under explicit upper-bound hypothesis)
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
-- Part 6: Perfect-cube exactness (innerCbrt(m³) = m)
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
    -- Step 1: d²(3m+2d) < 3z² (the key inequality using d² < m)
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
    -- Step 2: polynomial identity m³ = z²(m-2d) + d²(3m+2d)
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
    -- Step 3: combine identity + key inequality to get m³ < (m-2d+3)*z²
    have hlt : m * m * m < (m - 2 * d + 3) * (z * z) := by
      calc m * m * m
          = z * z * (m - 2 * d) + d * d * (3 * m + 2 * d) := hident
        _ < z * z * (m - 2 * d) + 3 * (z * z) := Nat.add_lt_add_left hkey _
        _ = z * z * (m - 2 * d) + z * z * 3 := by rw [Nat.mul_comm 3 _]
        _ = z * z * (m - 2 * d + 3) := by rw [← Nat.mul_add]
        _ = (m - 2 * d + 3) * (z * z) := Nat.mul_comm _ _
    -- Step 4: from m³ < (m-2d+3)*z², derive m³/z² < m-2d+3, so m³/z² ≤ m-2d+2
    have hdiv_lt : m * m * m / (z * z) < m - 2 * d + 3 :=
      (Nat.div_lt_iff_lt_mul hzz).2 hlt
    have hdiv_le : m * m * m / (z * z) ≤ m - 2 * d + 2 := by omega
    -- numerator = floor(m³/z²) + 2z ≤ (m-2d+2) + 2(m+d) = 3m+2
    have hnum_le : m * m * m / (z * z) + 2 * z ≤ 3 * m + 2 := by omega
    -- (3m+2)/3 ≤ m: use Nat.div_le_div_right on the numerator bound
    exact Nat.le_trans (Nat.div_le_div_right hnum_le) (by omega)

set_option maxRecDepth 1000000 in
/-- Finite check: innerCbrt(m³) = m for all m ≤ 255 (m³ < 2^24). -/
theorem innerCbrt_on_perfect_cube_small :
    ∀ i : Fin 256, innerCbrt (i.val * i.val * i.val) = i.val := by
  decide

-- ============================================================================
-- Part 7: Floor correction
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
