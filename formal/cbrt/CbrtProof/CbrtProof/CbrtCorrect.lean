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

/-- Run three cbrt Newton steps from an explicit starting point. -/
private def run3From (x z : Nat) : Nat :=
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
-- Part 1c: Reference integer 8th root (for stage thresholds)
-- ============================================================================

/-- 8th power helper. -/
def pow8 (n : Nat) : Nat := n * n * n * n * n * n * n * n

/-- 4th power helper. -/
private def pow4 (n : Nat) : Nat := (n * n) * (n * n)

/-- Search helper: largest `m ≤ n` such that `m^8 ≤ x`. -/
def i8rtAux (x n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => if pow8 (n + 1) ≤ x then n + 1 else i8rtAux x n

/-- Reference integer floor 8th root. -/
def i8rt (x : Nat) : Nat := i8rtAux x x

private theorem pow8_eq4 (n : Nat) :
    pow8 n = ((n * n) * (n * n)) * ((n * n) * (n * n)) := by
  unfold pow8
  simp [Nat.mul_left_comm, Nat.mul_comm]

private theorem pow8_eq_pow4 (n : Nat) : pow8 n = pow4 n * pow4 n := by
  simp [pow4, pow8_eq4]

private theorem pow8_monotone {a b : Nat} (h : a ≤ b) : pow8 a ≤ pow8 b := by
  have h2 : a * a ≤ b * b := Nat.mul_le_mul h h
  have h4 : (a * a) * (a * a) ≤ (b * b) * (b * b) := Nat.mul_le_mul h2 h2
  have h8 : ((a * a) * (a * a)) * ((a * a) * (a * a)) ≤
      ((b * b) * (b * b)) * ((b * b) * (b * b)) := Nat.mul_le_mul h4 h4
  simpa [pow8_eq4] using h8

private theorem le_pow8_of_pos {a : Nat} (ha : 0 < a) : a ≤ pow8 a := by
  have h1 : 1 ≤ a := Nat.succ_le_of_lt ha
  have ha2_pos : 0 < a * a := Nat.mul_pos ha ha
  have h2 : 1 ≤ a * a := Nat.succ_le_of_lt ha2_pos
  have hsq : a ≤ a * a := by
    simpa [Nat.mul_one] using (Nat.mul_le_mul_left a h1)
  have h4 : a * a ≤ (a * a) * (a * a) := by
    simpa [Nat.mul_one] using (Nat.mul_le_mul_left (a * a) h2)
  have h8 : (a * a) * (a * a) ≤ ((a * a) * (a * a)) * ((a * a) * (a * a)) := by
    have h2' : 1 ≤ (a * a) * (a * a) := by
      exact Nat.succ_le_of_lt (Nat.mul_pos ha2_pos ha2_pos)
    simpa [Nat.mul_one] using (Nat.mul_le_mul_left ((a * a) * (a * a)) h2')
  calc
    a ≤ a * a := hsq
    _ ≤ (a * a) * (a * a) := h4
    _ ≤ ((a * a) * (a * a)) * ((a * a) * (a * a)) := h8
    _ = pow8 a := by simp [pow8_eq4]

private theorem i8rtAux_pow8_le (x n : Nat) :
    pow8 (i8rtAux x n) ≤ x := by
  induction n with
  | zero => simp [i8rtAux, pow8]
  | succ n ih =>
      by_cases h : pow8 (n + 1) ≤ x
      · simp [i8rtAux, h]
      · simpa [i8rtAux, h] using ih

private theorem i8rtAux_greatest (x : Nat) :
    ∀ n m, m ≤ n → pow8 m ≤ x → m ≤ i8rtAux x n := by
  intro n
  induction n with
  | zero =>
      intro m hmn hm
      have hm0 : m = 0 := by omega
      subst hm0
      simp [i8rtAux]
  | succ n ih =>
      intro m hmn hm
      by_cases h : pow8 (n + 1) ≤ x
      · simp [i8rtAux, h]
        exact hmn
      · have hm_le_n : m ≤ n := by
          by_cases hm_eq : m = n + 1
          · subst hm_eq
            exact False.elim (h hm)
          · omega
        have hm_le_aux : m ≤ i8rtAux x n := ih m hm_le_n hm
        simpa [i8rtAux, h] using hm_le_aux

/-- Lower floor-spec half: `pow8 (i8rt x) ≤ x`. -/
theorem i8rt_pow8_le (x : Nat) :
    pow8 (i8rt x) ≤ x := by
  unfold i8rt
  exact i8rtAux_pow8_le x x

/-- Upper floor-spec half: `x < pow8 (i8rt x + 1)`. -/
theorem i8rt_lt_succ_pow8 (x : Nat) :
    x < pow8 (i8rt x + 1) := by
  by_cases hlt : x < pow8 (i8rt x + 1)
  · exact hlt
  · have hle : pow8 (i8rt x + 1) ≤ x := Nat.le_of_not_lt hlt
    have hpos : 0 < i8rt x + 1 := by omega
    have hmx : i8rt x + 1 ≤ x := by
      have hlePow : i8rt x + 1 ≤ pow8 (i8rt x + 1) := le_pow8_of_pos hpos
      exact Nat.le_trans hlePow hle
    have hmax : i8rt x + 1 ≤ i8rt x := by
      unfold i8rt
      exact i8rtAux_greatest x x (i8rt x + 1) hmx hle
    exact False.elim ((Nat.not_succ_le_self (i8rt x)) hmax)

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

set_option maxRecDepth 1000000 in
/-- The critical computational check: all 256 octaves converge. -/
theorem cbrt_all_octaves_pass : ∀ i : Fin 256, cbrtCheckOctave i.val = true := by
  decide

set_option maxRecDepth 1000000 in
/-- Seeds are always positive. -/
theorem cbrt_all_seeds_pos : ∀ i : Fin 256, cbrtCheckSeedPos i.val = true := by
  decide

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

/-- Division helper:
    `((m/a)^2)/m ≤ m/(a^2)` for positive `a`. -/
private theorem div_sq_div_bound (m a : Nat) (ha : 0 < a) :
    ((m / a) * (m / a)) / m ≤ m / (a * a) := by
  by_cases hq0 : m / a = 0
  · simp [hq0]
  · have hqpos : 0 < m / a := Nat.pos_of_ne_zero hq0
    have hqa : (m / a) * a ≤ m := by
      simpa [Nat.mul_comm] using (Nat.mul_div_le m a)
    have hdiv1 : ((m / a) * (m / a)) / m ≤ ((m / a) * (m / a)) / ((m / a) * a) :=
      Nat.div_le_div_left hqa (Nat.mul_pos hqpos ha)
    have hcancel : ((m / a) * (m / a)) / ((m / a) * a) = (m / a) / a := by
      simpa [Nat.mul_assoc] using (Nat.mul_div_mul_left (m / a) a hqpos)
    have hqq : ((m / a) * (m / a)) / m ≤ (m / a) / a := by
      exact Nat.le_trans hdiv1 (by simp [hcancel])
    have hqa2 : (m / a) / a = m / (a * a) := by
      simpa [Nat.mul_comm] using (Nat.div_div_eq_div_mul m a a)
    exact Nat.le_trans hqq (by simp [hqa2])

/-- Division helper with +1:
    `((m/a + 1)^2)/m ≤ m/(a^2) + 1` for `m>0` and `a>2`. -/
private theorem div_sq_succ_div_bound (m a : Nat) (hm : 0 < m) (ha3 : 2 < a) :
    ((m / a + 1) * (m / a + 1)) / m ≤ m / (a * a) + 1 := by
  have h3a : 3 ≤ a := Nat.succ_le_of_lt ha3
  have hq_le_third : m / a ≤ m / 3 := by
    simpa using (Nat.div_le_div_left (a := m) h3a (by decide : 0 < (3 : Nat)))
  have hsmall : 2 * (m / a) + 1 ≤ m := by
    by_cases hm3 : m < 3
    · have hq0 : m / a = 0 := by
        exact Nat.div_eq_zero_iff.mpr (Or.inr (Nat.lt_of_lt_of_le hm3 h3a))
      rw [hq0]
      exact Nat.succ_le_of_lt hm
    · have hm3ge : 3 ≤ m := Nat.le_of_not_lt hm3
      have hdiv3pos : 0 < m / 3 := Nat.div_pos hm3ge (by decide : 0 < (3 : Nat))
      have h2third : 2 * (m / 3) + 1 ≤ 3 * (m / 3) := by omega
      calc
        2 * (m / a) + 1 ≤ 2 * (m / 3) + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left 2 hq_le_third) 1
        _ ≤ 3 * (m / 3) := h2third
        _ ≤ m := by simpa [Nat.mul_comm] using (Nat.mul_div_le m 3)
  have hpre : (m / a + 1) * (m / a + 1) = (m / a) * (m / a) + (2 * (m / a) + 1) := by
    calc
      (m / a + 1) * (m / a + 1)
          = (m / a) * (m / a + 1) + (1 * (m / a + 1)) := by
              rw [Nat.add_mul]
      _ = ((m / a) * (m / a) + (m / a)) + ((m / a) + 1) := by
              rw [Nat.mul_add, Nat.mul_one, Nat.one_mul]
      _ = (m / a) * (m / a) + (2 * (m / a) + 1) := by
              omega
  have hnum : (m / a + 1) * (m / a + 1) ≤ (m / a) * (m / a) + m := by
    rw [hpre]
    omega
  have hdiv : ((m / a + 1) * (m / a + 1)) / m ≤ (((m / a) * (m / a) + m) / m) :=
    Nat.div_le_div_right hnum
  have hsplit : (((m / a) * (m / a) + m) / m) = ((m / a) * (m / a)) / m + 1 := by
    simpa [Nat.mul_comm] using (Nat.add_mul_div_right ((m / a) * (m / a)) 1 hm)
  have hmain : ((m / a + 1) * (m / a + 1)) / m ≤ ((m / a) * (m / a)) / m + 1 := by
    exact Nat.le_trans hdiv (by simp [hsplit])
  have hbase : ((m / a) * (m / a)) / m ≤ m / (a * a) :=
    div_sq_div_bound m a (Nat.lt_trans (by decide : 0 < (2 : Nat)) ha3)
  exact Nat.le_trans hmain (Nat.add_le_add_right hbase 1)

/-- `cbrtStep` is monotone in `x` for fixed `z`. -/
theorem cbrtStep_mono_x (x y z : Nat) (hxy : x ≤ y) :
    cbrtStep x z ≤ cbrtStep y z := by
  unfold cbrtStep
  have hdiv : x / (z * z) ≤ y / (z * z) := Nat.div_le_div_right hxy
  have hnum : x / (z * z) + 2 * z ≤ y / (z * z) + 2 * z := Nat.add_le_add_right hdiv (2 * z)
  exact Nat.div_le_div_right hnum

/-- Error recurrence used by the arithmetic bridge. -/
private def nextDelta (m d : Nat) : Nat := d * d / m + 1

/-- Three iterations of `nextDelta`. -/
private def nextDelta3 (m d : Nat) : Nat :=
  nextDelta m (nextDelta m (nextDelta m d))

/-- `nextDelta` is monotone in its error input. -/
private theorem nextDelta_mono_d (m d1 d2 : Nat) (h : d1 ≤ d2) :
    nextDelta m d1 ≤ nextDelta m d2 := by
  unfold nextDelta
  have hsq : d1 * d1 ≤ d2 * d2 := Nat.mul_le_mul h h
  have hdiv : d1 * d1 / m ≤ d2 * d2 / m := Nat.div_le_div_right hsq
  exact Nat.add_le_add_right hdiv 1

/-- Bridge chaining theorem:
    if after 3 steps we have `z₃ ≤ m + d₀`, then under per-step side conditions
    and `nextDelta3 m d₀ ≤ 1`, three additional steps give `z₆ ≤ m + 1`. -/
private theorem run3_to_run6_of_delta
    (x m z3 d0 : Nat)
    (hm2 : 2 ≤ m)
    (hmlo : m * m * m ≤ x)
    (hxhi : x < (m + 1) * (m + 1) * (m + 1))
    (hmz3 : m ≤ z3)
    (hz3d : z3 ≤ m + d0)
    (h2d0 : 2 * d0 ≤ m)
    (h2d1 : 2 * nextDelta m d0 ≤ m)
    (h2d2 : 2 * nextDelta m (nextDelta m d0) ≤ m)
    (hcontract : nextDelta3 m d0 ≤ 1) :
    cbrtStep x (cbrtStep x (cbrtStep x z3)) ≤ m + 1 := by
  have hmpos : 0 < m := by omega
  have hz3pos : 0 < z3 := by omega

  let d1 : Nat := nextDelta m d0
  let d2 : Nat := nextDelta m d1
  let d3 : Nat := nextDelta m d2

  have hz4ub : cbrtStep x z3 ≤ m + d1 := by
    have hz4ub' :
        cbrtStep x z3 ≤ m + (d0 * d0 / m) + 1 :=
      cbrtStep_upper_of_le x m z3 d0 hm2 hmz3 hz3d h2d0 hxhi
    simpa [d1, nextDelta, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hz4ub'

  have hmz4 : m ≤ cbrtStep x z3 := cbrt_step_floor_bound x z3 m hz3pos hmlo
  have hz4pos : 0 < cbrtStep x z3 := by omega

  have hz5ub : cbrtStep x (cbrtStep x z3) ≤ m + d2 := by
    have hz5ub' :
        cbrtStep x (cbrtStep x z3) ≤ m + (d1 * d1 / m) + 1 :=
      cbrtStep_upper_of_le x m (cbrtStep x z3) d1 hm2 hmz4 (by
        simpa [d1] using hz4ub) h2d1 hxhi
    simpa [d2, d1, nextDelta, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hz5ub'

  have hmz5 : m ≤ cbrtStep x (cbrtStep x z3) := cbrt_step_floor_bound x (cbrtStep x z3) m hz4pos hmlo

  have hz6ub : cbrtStep x (cbrtStep x (cbrtStep x z3)) ≤ m + d3 := by
    have hz6ub' :
        cbrtStep x (cbrtStep x (cbrtStep x z3)) ≤ m + (d2 * d2 / m) + 1 :=
      cbrtStep_upper_of_le x m (cbrtStep x (cbrtStep x z3)) d2 hm2 hmz5 (by
        simpa [d2] using hz5ub) h2d2 hxhi
    simpa [d3, d2, nextDelta, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hz6ub'

  have hz6final : cbrtStep x (cbrtStep x (cbrtStep x z3)) ≤ m + 1 := by
    have : m + d3 ≤ m + 1 := Nat.add_le_add_left hcontract m
    exact Nat.le_trans hz6ub this

  exact hz6final

/-- Convenience wrapper: apply `run3_to_run6_of_delta` starting from a
    precomputed `run3From`. -/
private theorem run6From_upper_of_run3_bound
    (x z0 m d0 : Nat)
    (hm2 : 2 ≤ m)
    (hmlo : m * m * m ≤ x)
    (hxhi : x < (m + 1) * (m + 1) * (m + 1))
    (h3lo : m ≤ run3From x z0)
    (h3hi : run3From x z0 ≤ m + d0)
    (h2d0 : 2 * d0 ≤ m)
    (h2d1 : 2 * nextDelta m d0 ≤ m)
    (h2d2 : 2 * nextDelta m (nextDelta m d0) ≤ m)
    (hcontract : nextDelta3 m d0 ≤ 1) :
    run6From x z0 ≤ m + 1 := by
  have h3lo' : m ≤ cbrtStep x (cbrtStep x (cbrtStep x z0)) := by
    simpa [run3From] using h3lo
  have h3hi' : cbrtStep x (cbrtStep x (cbrtStep x z0)) ≤ m + d0 := by
    simpa [run3From] using h3hi
  have hmain :
      cbrtStep x (cbrtStep x (cbrtStep x (cbrtStep x (cbrtStep x (cbrtStep x z0))))) ≤ m + 1 := by
    simpa using
      (run3_to_run6_of_delta x m (cbrtStep x (cbrtStep x (cbrtStep x z0))) d0
        hm2 hmlo hxhi h3lo' h3hi' h2d0 h2d1 h2d2 hcontract)
  simpa [run6From] using hmain

/-- For positive `x`, `_cbrt` is exactly `run6From` from the seed. -/
theorem innerCbrt_eq_run6From_seed (x : Nat) (hx : 0 < x) :
    innerCbrt x = run6From x (cbrtSeed x) := by
  unfold innerCbrt run6From
  simp [Nat.ne_of_gt hx]

/-- Three-step lower bound from any positive start. -/
private theorem run3From_lower
    (x z m : Nat)
    (hx : 0 < x)
    (hz : 0 < z)
    (hm : m * m * m ≤ x) :
    m ≤ run3From x z := by
  unfold run3From
  have hz1 : 0 < cbrtStep x z := cbrtStep_pos x z hx hz
  have hz2 : 0 < cbrtStep x (cbrtStep x z) := cbrtStep_pos x _ hx hz1
  exact cbrt_step_floor_bound x (cbrtStep x (cbrtStep x z)) m hz2 hm

/-- Seeded bridge theorem: from a stage-1 run3 upper bound and arithmetic
    side conditions, conclude the final `_cbrt` upper bound `≤ m+1`. -/
private theorem innerCbrt_upper_of_stage
    (x m d0 : Nat)
    (hx : 0 < x)
    (hm2 : 2 ≤ m)
    (hmlo : m * m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1) * (m + 1))
    (hstage : run3From x (cbrtSeed x) ≤ m + d0)
    (h2d0 : 2 * d0 ≤ m)
    (h2d1 : 2 * nextDelta m d0 ≤ m)
    (h2d2 : 2 * nextDelta m (nextDelta m d0) ≤ m)
    (hcontract : nextDelta3 m d0 ≤ 1) :
    innerCbrt x ≤ m + 1 := by
  have hseed : 0 < cbrtSeed x := cbrtSeed_pos x hx
  have h3lo : m ≤ run3From x (cbrtSeed x) := run3From_lower x (cbrtSeed x) m hx hseed hmlo
  have hrun6 : run6From x (cbrtSeed x) ≤ m + 1 :=
    run6From_upper_of_run3_bound x (cbrtSeed x) m d0
      hm2 hmlo hmhi h3lo hstage h2d0 h2d1 h2d2 hcontract
  simpa [innerCbrt_eq_run6From_seed x hx] using hrun6

/-- Canonical stage width for the arithmetic bridge. -/
private def stageDelta (m : Nat) : Nat := m / (i8rt m + 2)

/-- The stage width is always at most half of `m`. -/
private theorem stageDelta_two_mul_le (m : Nat) :
    2 * stageDelta m ≤ m := by
  have hden : 2 ≤ i8rt m + 2 := by omega
  have hdiv : stageDelta m ≤ m / 2 := by
    unfold stageDelta
    simpa using (Nat.div_le_div_left (a := m) hden (by decide : 0 < (2 : Nat)))
  calc
    2 * stageDelta m ≤ 2 * (m / 2) := Nat.mul_le_mul_left 2 hdiv
    _ ≤ m := by simpa [Nat.mul_comm] using (Nat.mul_div_le m 2)

/-- First recurrence bound from the stage width. -/
private theorem stageDelta_next1_le (m : Nat) :
    nextDelta m (stageDelta m) ≤ m / ((i8rt m + 2) * (i8rt m + 2)) + 1 := by
  unfold stageDelta nextDelta
  have hbase : ((m / (i8rt m + 2)) * (m / (i8rt m + 2))) / m ≤
      m / ((i8rt m + 2) * (i8rt m + 2)) := by
    exact div_sq_div_bound m (i8rt m + 2) (by omega)
  exact Nat.add_le_add_right hbase 1

/-- Second recurrence bound from the stage width. -/
private theorem stageDelta_next2_le (m : Nat) (hm : 0 < m) :
    nextDelta m (nextDelta m (stageDelta m)) ≤
      m / (((i8rt m + 2) * (i8rt m + 2)) * ((i8rt m + 2) * (i8rt m + 2))) + 2 := by
  let a : Nat := (i8rt m + 2) * (i8rt m + 2)
  have h1 : nextDelta m (stageDelta m) ≤ m / a + 1 := by
    simpa [a, Nat.mul_assoc] using stageDelta_next1_le m
  have hmono :
      nextDelta m (nextDelta m (stageDelta m)) ≤ nextDelta m (m / a + 1) := by
    exact nextDelta_mono_d m _ _ h1
  have h2 : nextDelta m (m / a + 1) ≤ m / (a * a) + 2 := by
    unfold nextDelta
    have ha3 : 2 < a := by
      dsimp [a]
      have hk2 : 2 ≤ i8rt m + 2 := by omega
      have h4 : 4 ≤ (i8rt m + 2) * (i8rt m + 2) := by
        have hmul : 2 * 2 ≤ (i8rt m + 2) * (i8rt m + 2) := Nat.mul_le_mul hk2 hk2
        simpa using hmul
      exact Nat.lt_of_lt_of_le (by decide : 2 < 4) h4
    have hbase : ((m / a + 1) * (m / a + 1)) / m ≤ m / (a * a) + 1 :=
      div_sq_succ_div_bound m a hm ha3
    omega
  exact Nat.le_trans hmono (by simpa [a] using h2)

/-- For `m ≥ 256`, `i8rt m` is at least 2. -/
private theorem i8rt_ge_two_of_ge_256 (m : Nat) (hm256 : 256 ≤ m) :
    2 ≤ i8rt m := by
  have hpow2 : pow8 2 ≤ m := by
    -- `pow8 2 = 256`
    simpa [pow8] using hm256
  have h2m : 2 ≤ m := Nat.le_trans (by decide : 2 ≤ 256) hm256
  unfold i8rt
  exact i8rtAux_greatest m m 2 h2m hpow2

/-- First side-condition for the bridge, derived from `m ≥ 256`. -/
private theorem stageDelta_h2d1_of_ge_256 (m : Nat) (hm256 : 256 ≤ m) :
    2 * nextDelta m (stageDelta m) ≤ m := by
  have hk2 : 2 ≤ i8rt m := i8rt_ge_two_of_ge_256 m hm256
  have hden16 : 16 ≤ (i8rt m + 2) * (i8rt m + 2) := by
    have hk4 : 4 ≤ i8rt m + 2 := by omega
    have hmul : 4 * 4 ≤ (i8rt m + 2) * (i8rt m + 2) := Nat.mul_le_mul hk4 hk4
    simpa using hmul
  have h1 : nextDelta m (stageDelta m) ≤ m / ((i8rt m + 2) * (i8rt m + 2)) + 1 :=
    stageDelta_next1_le m
  have hdiv : m / ((i8rt m + 2) * (i8rt m + 2)) ≤ m / 16 := by
    simpa using (Nat.div_le_div_left (a := m) hden16 (by decide : 0 < (16 : Nat)))
  have hbound : nextDelta m (stageDelta m) ≤ m / 16 + 1 := by
    exact Nat.le_trans h1 (Nat.add_le_add_right hdiv 1)
  have hfinal : 2 * (m / 16 + 1) ≤ m := by
    omega
  exact Nat.le_trans (Nat.mul_le_mul_left 2 hbound) hfinal

/-- Second side-condition for the bridge, derived from `m ≥ 256`. -/
private theorem stageDelta_h2d2_of_ge_256 (m : Nat) (hm256 : 256 ≤ m) :
    2 * nextDelta m (nextDelta m (stageDelta m)) ≤ m := by
  have hm : 0 < m := by omega
  have hk2 : 2 ≤ i8rt m := i8rt_ge_two_of_ge_256 m hm256
  have hden256 :
      256 ≤ ((i8rt m + 2) * (i8rt m + 2)) * ((i8rt m + 2) * (i8rt m + 2)) := by
    have hk4 : 4 ≤ i8rt m + 2 := by omega
    have hden16 : 16 ≤ (i8rt m + 2) * (i8rt m + 2) := by
      have hmul : 4 * 4 ≤ (i8rt m + 2) * (i8rt m + 2) := Nat.mul_le_mul hk4 hk4
      simpa using hmul
    have hmul256 :
        16 * 16 ≤ ((i8rt m + 2) * (i8rt m + 2)) * ((i8rt m + 2) * (i8rt m + 2)) :=
      Nat.mul_le_mul hden16 hden16
    simpa using hmul256
  have h2 :
      nextDelta m (nextDelta m (stageDelta m)) ≤
        m / (((i8rt m + 2) * (i8rt m + 2)) * ((i8rt m + 2) * (i8rt m + 2))) + 2 :=
    stageDelta_next2_le m hm
  have hdiv :
      m / (((i8rt m + 2) * (i8rt m + 2)) * ((i8rt m + 2) * (i8rt m + 2))) ≤ m / 256 := by
    simpa using (Nat.div_le_div_left (a := m) hden256 (by decide : 0 < (256 : Nat)))
  have hbound : nextDelta m (nextDelta m (stageDelta m)) ≤ m / 256 + 2 := by
    exact Nat.le_trans h2 (Nat.add_le_add_right hdiv 2)
  have hfinal : 2 * (m / 256 + 2) ≤ m := by
    omega
  exact Nat.le_trans (Nat.mul_le_mul_left 2 hbound) hfinal

private theorem pow4_mono (a b : Nat) (h : a ≤ b) : pow4 a ≤ pow4 b := by
  unfold pow4
  have h2 : a * a ≤ b * b := Nat.mul_le_mul h h
  exact Nat.mul_le_mul h2 h2

private theorem pow4_step_gap (k : Nat) :
    pow4 (k + 1) + 15 ≤ pow4 (k + 2) := by
  unfold pow4
  let b : Nat := (k + 1) * (k + 1)
  let a : Nat := (k + 2) * (k + 2)
  have hb1 : 1 ≤ b := by
    dsimp [b]
    have hk1 : 1 ≤ k + 1 := by omega
    exact Nat.mul_le_mul hk1 hk1
  have hsq : (k + 2) * (k + 2) = (k + 1) * (k + 1) + (2 * (k + 1) + 1) := by
    have h : k + 2 = (k + 1) + 1 := by omega
    rw [h, h]
    rw [Nat.add_mul, Nat.mul_add]
    omega
  have ha_ge : b + 3 ≤ a := by
    dsimp [a, b]
    rw [hsq]
    have : 3 ≤ 2 * (k + 1) + 1 := by omega
    omega
  have hsq_mono : (b + 3) * (b + 3) ≤ a * a := Nat.mul_le_mul ha_ge ha_ge
  have hinc : b * b + 15 ≤ (b + 3) * (b + 3) := by
    have h_expand : (b + 3) * (b + 3) = b * b + (6 * b + 9) := by
      rw [Nat.add_mul, Nat.mul_add]
      omega
    rw [h_expand]
    have h6b9 : 15 ≤ 6 * b + 9 := by
      have : 6 ≤ 6 * b := Nat.mul_le_mul_left 6 hb1
      omega
    omega
  have hfinal : b * b + 15 ≤ a * a := Nat.le_trans hinc hsq_mono
  simpa [a, b] using hfinal

private theorem pow8_succ_le_pow4_mul_sub8 (k : Nat) :
    pow8 (k + 1) ≤ pow4 (k + 2) * (pow4 (k + 2) - 8) := by
  have hgap : pow4 (k + 1) + 15 ≤ pow4 (k + 2) := pow4_step_gap k
  have hle : pow4 (k + 1) ≤ pow4 (k + 2) - 15 := by
    omega
  have hsq : pow4 (k + 1) * pow4 (k + 1) ≤
      (pow4 (k + 2) - 15) * (pow4 (k + 2) - 15) := Nat.mul_le_mul hle hle
  have hleft : (pow4 (k + 2) - 15) * (pow4 (k + 2) - 15) ≤
      pow4 (k + 2) * (pow4 (k + 2) - 15) := by
    exact Nat.mul_le_mul_right (pow4 (k + 2) - 15) (by omega)
  have hright : pow4 (k + 2) * (pow4 (k + 2) - 15) ≤
      pow4 (k + 2) * (pow4 (k + 2) - 8) := by
    exact Nat.mul_le_mul_left (pow4 (k + 2)) (by omega)
  have hmain : pow4 (k + 1) * pow4 (k + 1) ≤
      pow4 (k + 2) * (pow4 (k + 2) - 8) := Nat.le_trans hsq (Nat.le_trans hleft hright)
  simpa [pow8_eq_pow4] using hmain

private theorem pow4_add2_le_pow8 (k : Nat) (hk2 : 2 ≤ k) :
    pow4 (k + 2) ≤ pow8 k := by
  have hk : k + 2 ≤ 2 * k := by omega
  have hmono : pow4 (k + 2) ≤ pow4 (2 * k) := pow4_mono (k + 2) (2 * k) hk
  have h2k_le_kk : 2 * k ≤ k * k := by
    simpa [Nat.mul_comm] using (Nat.mul_le_mul_right k hk2)
  have hsq1 : (2 * k) * (2 * k) ≤ (k * k) * (k * k) := Nat.mul_le_mul h2k_le_kk h2k_le_kk
  have hsq2 : ((2 * k) * (2 * k)) * ((2 * k) * (2 * k)) ≤
      ((k * k) * (k * k)) * ((k * k) * (k * k)) := Nat.mul_le_mul hsq1 hsq1
  have h2kp4 : pow4 (2 * k) ≤ pow8 k := by
    simpa [pow4, pow8_eq4] using hsq2
  exact Nat.le_trans hmono h2kp4

private theorem div_plus_two_sq_lt_of_i8rt_bucket
    (m k : Nat)
    (hk2 : 2 ≤ k)
    (hklo : pow8 k ≤ m)
    (hkhi : m < pow8 (k + 1)) :
    (m / pow4 (k + 2) + 2) * (m / pow4 (k + 2) + 2) < m := by
  let B : Nat := pow4 (k + 2)
  let y : Nat := m / B
  have hBpos : 0 < B := by
    dsimp [B, pow4]
    have hk2pos : 0 < k + 2 := by omega
    have hsq : 0 < (k + 2) * (k + 2) := Nat.mul_pos hk2pos hk2pos
    exact Nat.mul_pos hsq hsq
  have hB_le_m : B ≤ m := Nat.le_trans (pow4_add2_le_pow8 k hk2) hklo
  have hy1 : 1 ≤ y := by
    dsimp [y]
    exact Nat.div_pos hB_le_m hBpos
  have hbucket : m < B * (B - 8) := by
    have hpow : pow8 (k + 1) ≤ B * (B - 8) := by
      simpa [B] using pow8_succ_le_pow4_mul_sub8 k
    exact Nat.lt_of_lt_of_le hkhi hpow
  have hylt : y < B - 8 := by
    dsimp [y]
    have hbucket' : m < (B - 8) * B := by
      simpa [Nat.mul_comm] using hbucket
    exact (Nat.div_lt_iff_lt_mul hBpos).2 hbucket'
  have hy9 : y + 9 ≤ B := by
    omega
  have hyB : (y + 2) * (y + 2) + 1 ≤ y * B := by
    have h5y : 5 ≤ 5 * y := by
      have : 1 * 5 ≤ y * 5 := Nat.mul_le_mul_right 5 hy1
      simpa [Nat.mul_comm] using this
    have h49 : 4 * y + 5 ≤ 9 * y := by
      omega
    calc
      (y + 2) * (y + 2) + 1 = y * y + (4 * y + 5) := by
        rw [Nat.add_mul, Nat.mul_add]
        omega
      _ ≤ y * y + 9 * y := Nat.add_le_add_left h49 (y * y)
      _ = y * (y + 9) := by
        rw [Nat.mul_add, Nat.mul_comm y 9]
      _ ≤ y * B := Nat.mul_le_mul_left y hy9
  have hym : y * B ≤ m := by
    dsimp [y]
    simpa [Nat.mul_comm] using (Nat.mul_div_le m B)
  have hmain : (y + 2) * (y + 2) < m := by
    calc
      (y + 2) * (y + 2) < (y + 2) * (y + 2) + 1 := Nat.lt_succ_self _
      _ ≤ y * B := hyB
      _ ≤ m := hym
  simpa [B, y]

private theorem stageDelta_hcontract_of_ge_256 (m : Nat) (hm256 : 256 ≤ m) :
    nextDelta3 m (stageDelta m) ≤ 1 := by
  let k : Nat := i8rt m
  let d2 : Nat := nextDelta m (nextDelta m (stageDelta m))
  have hm : 0 < m := by omega
  have hk2 : 2 ≤ k := by
    simpa [k] using i8rt_ge_two_of_ge_256 m hm256
  have hklo : pow8 k ≤ m := by
    simpa [k] using i8rt_pow8_le m
  have hkhi : m < pow8 (k + 1) := by
    simpa [k] using i8rt_lt_succ_pow8 m
  have hd2ub : d2 ≤ m / pow4 (k + 2) + 2 := by
    dsimp [d2, k]
    simpa [pow4, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using stageDelta_next2_le m hm
  have hsq_lt : (m / pow4 (k + 2) + 2) * (m / pow4 (k + 2) + 2) < m :=
    div_plus_two_sq_lt_of_i8rt_bucket m k hk2 hklo hkhi
  have hd2sq_lt : d2 * d2 < m := Nat.lt_of_le_of_lt (Nat.mul_le_mul hd2ub hd2ub) hsq_lt
  have hdiv0 : d2 * d2 / m = 0 := Nat.div_eq_of_lt hd2sq_lt
  have hlast : nextDelta m d2 = 1 := by
    unfold nextDelta
    simp [hdiv0]
  have hfinal : nextDelta m d2 ≤ 1 := by
    simp [hlast]
  unfold nextDelta3
  simpa [d2] using hfinal

set_option maxRecDepth 1000000 in
private theorem stageDelta_h2d1_fin256 :
    ∀ i : Fin 256, 2 ≤ i.val → 2 * nextDelta i.val (stageDelta i.val) ≤ i.val := by
  decide

set_option maxRecDepth 1000000 in
private theorem stageDelta_h2d2_fin256 :
    ∀ i : Fin 256, 2 ≤ i.val →
      2 * nextDelta i.val (nextDelta i.val (stageDelta i.val)) ≤ i.val := by
  decide

set_option maxRecDepth 1000000 in
private theorem stageDelta_hcontract_fin256 :
    ∀ i : Fin 256, 2 ≤ i.val → nextDelta3 i.val (stageDelta i.val) ≤ 1 := by
  decide

private theorem stageDelta_h2d1_of_ge_two (m : Nat) (hm2 : 2 ≤ m) :
    2 * nextDelta m (stageDelta m) ≤ m := by
  by_cases hm256 : 256 ≤ m
  · exact stageDelta_h2d1_of_ge_256 m hm256
  · have hm_lt : m < 256 := Nat.lt_of_not_ge hm256
    exact stageDelta_h2d1_fin256 ⟨m, hm_lt⟩ hm2

private theorem stageDelta_h2d2_of_ge_two (m : Nat) (hm2 : 2 ≤ m) :
    2 * nextDelta m (nextDelta m (stageDelta m)) ≤ m := by
  by_cases hm256 : 256 ≤ m
  · exact stageDelta_h2d2_of_ge_256 m hm256
  · have hm_lt : m < 256 := Nat.lt_of_not_ge hm256
    exact stageDelta_h2d2_fin256 ⟨m, hm_lt⟩ hm2

private theorem stageDelta_hcontract_of_ge_two (m : Nat) (hm2 : 2 ≤ m) :
    nextDelta3 m (stageDelta m) ≤ 1 := by
  by_cases hm256 : 256 ≤ m
  · exact stageDelta_hcontract_of_ge_256 m hm256
  · have hm_lt : m < 256 := Nat.lt_of_not_ge hm256
    exact stageDelta_hcontract_fin256 ⟨m, hm_lt⟩ hm2

private theorem icbrt_ge_of_cube_le (x m : Nat) (hmx : m * m * m ≤ x) :
    m ≤ icbrt x := by
  have hm_le_x : m ≤ x := by
    by_cases hm0 : m = 0
    · omega
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      exact Nat.le_trans (le_cube_of_pos hmpos) hmx
  unfold icbrt
  exact icbrtAux_greatest x x m hm_le_x hmx

private theorem icbrt_ge_256_of_ge_2pow24 (x : Nat) (hx24 : 16777216 ≤ x) :
    256 ≤ icbrt x := by
  have hcube : 256 * 256 * 256 ≤ x := by
    have hconst : 256 * 256 * 256 = 16777216 := by decide
    omega
  exact icbrt_ge_of_cube_le x 256 hcube

/-- Bridge wrapper at `m = icbrt x`: this isolates the remaining obligations
    (stage-1 run3 bound + delta side conditions). -/
private theorem innerCbrt_upper_of_stage_icbrt
    (x : Nat)
    (hx : 0 < x)
    (hm2 : 2 ≤ icbrt x)
    (hstage : run3From x (cbrtSeed x) ≤ icbrt x + stageDelta (icbrt x))
    (h2d1 : 2 * nextDelta (icbrt x) (stageDelta (icbrt x)) ≤ icbrt x)
    (h2d2 : 2 * nextDelta (icbrt x) (nextDelta (icbrt x) (stageDelta (icbrt x))) ≤ icbrt x)
    (hcontract : nextDelta3 (icbrt x) (stageDelta (icbrt x)) ≤ 1) :
    innerCbrt x ≤ icbrt x + 1 := by
  have hmlo : icbrt x * icbrt x * icbrt x ≤ x := icbrt_cube_le x
  have hmhi : x < (icbrt x + 1) * (icbrt x + 1) * (icbrt x + 1) := icbrt_lt_succ_cube x
  have h2d0 : 2 * stageDelta (icbrt x) ≤ icbrt x := stageDelta_two_mul_le (icbrt x)
  exact innerCbrt_upper_of_stage x (icbrt x) (stageDelta (icbrt x))
    hx hm2 hmlo hmhi hstage h2d0 h2d1 h2d2 hcontract

private theorem innerCbrt_upper_of_stage_icbrt_of_ge_256
    (x : Nat)
    (hx : 0 < x)
    (hm256 : 256 ≤ icbrt x)
    (hstage : run3From x (cbrtSeed x) ≤ icbrt x + stageDelta (icbrt x)) :
    innerCbrt x ≤ icbrt x + 1 := by
  have hm2 : 2 ≤ icbrt x := Nat.le_trans (by decide : 2 ≤ 256) hm256
  have h2d1 : 2 * nextDelta (icbrt x) (stageDelta (icbrt x)) ≤ icbrt x :=
    stageDelta_h2d1_of_ge_256 (icbrt x) hm256
  have h2d2 : 2 * nextDelta (icbrt x) (nextDelta (icbrt x) (stageDelta (icbrt x))) ≤ icbrt x :=
    stageDelta_h2d2_of_ge_256 (icbrt x) hm256
  have hcontract : nextDelta3 (icbrt x) (stageDelta (icbrt x)) ≤ 1 :=
    stageDelta_hcontract_of_ge_256 (icbrt x) hm256
  exact innerCbrt_upper_of_stage_icbrt x hx hm2 hstage h2d1 h2d2 hcontract

private theorem innerCbrt_upper_of_stage_icbrt_of_ge_two
    (x : Nat)
    (hx : 0 < x)
    (hm2 : 2 ≤ icbrt x)
    (hstage : run3From x (cbrtSeed x) ≤ icbrt x + stageDelta (icbrt x)) :
    innerCbrt x ≤ icbrt x + 1 := by
  have h2d1 : 2 * nextDelta (icbrt x) (stageDelta (icbrt x)) ≤ icbrt x :=
    stageDelta_h2d1_of_ge_two (icbrt x) hm2
  have h2d2 : 2 * nextDelta (icbrt x) (nextDelta (icbrt x) (stageDelta (icbrt x))) ≤ icbrt x :=
    stageDelta_h2d2_of_ge_two (icbrt x) hm2
  have hcontract : nextDelta3 (icbrt x) (stageDelta (icbrt x)) ≤ 1 :=
    stageDelta_hcontract_of_ge_two (icbrt x) hm2
  exact innerCbrt_upper_of_stage_icbrt x hx hm2 hstage h2d1 h2d2 hcontract

private theorem innerCbrt_upper_of_stage_icbrt_of_ge_2pow24
    (x : Nat)
    (hx : 0 < x)
    (hx24 : 16777216 ≤ x)
    (hstage : run3From x (cbrtSeed x) ≤ icbrt x + stageDelta (icbrt x)) :
    innerCbrt x ≤ icbrt x + 1 := by
  have hm256 : 256 ≤ icbrt x := icbrt_ge_256_of_ge_2pow24 x hx24
  exact innerCbrt_upper_of_stage_icbrt_of_ge_256 x hx hm256 hstage

set_option maxRecDepth 1000000 in
/-- Direct finite check for small inputs. -/
private theorem innerCbrt_upper_fin256 :
    ∀ i : Fin 256, innerCbrt i.val ≤ icbrt i.val + 1 := by
  decide

/-- Small-range corollary (used for base cases). -/
theorem innerCbrt_upper_of_lt_256 (x : Nat) (hx : x < 256) :
    innerCbrt x ≤ icbrt x + 1 := by
  simpa using innerCbrt_upper_fin256 ⟨x, hx⟩

private theorem innerCbrt_upper_of_stage_icbrt_all
    (x : Nat)
    (hx : 0 < x)
    (hstage : run3From x (cbrtSeed x) ≤ icbrt x + stageDelta (icbrt x)) :
    innerCbrt x ≤ icbrt x + 1 := by
  by_cases hm2 : 2 ≤ icbrt x
  · exact innerCbrt_upper_of_stage_icbrt_of_ge_two x hx hm2 hstage
  · have hic_lt2 : icbrt x < 2 := Nat.lt_of_not_ge hm2
    have hx8 : x < 8 := by
      have hlt : x < (icbrt x + 1) * (icbrt x + 1) * (icbrt x + 1) := icbrt_lt_succ_cube x
      have hsucc : icbrt x + 1 ≤ 2 := by omega
      have hmono :
          (icbrt x + 1) * (icbrt x + 1) * (icbrt x + 1) ≤
          2 * 2 * 2 := cube_monotone hsucc
      exact Nat.lt_of_lt_of_le hlt (by simpa using hmono)
    have hx256 : x < 256 := Nat.lt_of_lt_of_le hx8 (by decide : 8 ≤ 256)
    exact innerCbrt_upper_of_lt_256 x hx256

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
  PROOF STATUS:

  ✓ Cubic AM-GM: cubic_am_gm
  ✓ Floor Bound: cbrt_step_floor_bound
  ✓ Reference floor root: icbrt, icbrt_spec, icbrt_eq_of_bounds
  ✓ Computational Verification: cbrt_all_octaves_pass (decide, 256 cases)
  ✓ Seed Positivity: cbrt_all_seeds_pos (decide, 256 cases)
  ✓ Lower Bound Chain: innerCbrt_lower (6x cbrt_step_floor_bound)
  ✓ Floor Correction: cbrt_floor_correction (case split on x/(z²) < z)
  ✓ Named correctness statements:
      - innerCbrt_correct_of_upper
      - floorCbrt_correct_of_upper

  Remaining external link:
    proving the stage-1 bound
      `run3From x (cbrtSeed x) ≤ icbrt x + stageDelta (icbrt x)`
    from octave-level computation, after which `innerCbrt x ≤ icbrt x + 1`
    follows from the arithmetic bridge lemmas in this file.
-/
