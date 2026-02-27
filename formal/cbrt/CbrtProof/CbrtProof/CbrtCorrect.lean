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
-- Part 1c: Reference integer 8th root (for stage thresholds)
-- ============================================================================

/-- 8th power helper. -/
def pow8 (n : Nat) : Nat := n * n * n * n * n * n * n * n

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

/-- Integer polynomial identity used to upper-bound one cbrt Newton step. -/
private theorem int_poly_identity (m d q r : Int)
    (hd2 : d * d = m * q + r) :
    ((m - 2 * d + 3 * q + 6) * ((m + d) * (m + d)) - (m + 1) * (m + 1) * (m + 1))
      =
    q * (3 * m * q + 6 * m + 3 * r + 4 * d * m)
      + (-2 * d * r + 12 * d * m + 3 * m * m - 3 * m * r - 3 * m + 6 * r - 1) := by
  grind

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
    grind

  have h_rewrite0 :
      (12 * (d : Int) * (m : Int) + 3 * (m : Int) * (m : Int) - 3 * (m : Int) - 1)
        + ((m - 1 : Nat) : Int) * (-2 * (d : Int) - 3 * (m : Int) + 6)
      = 10 * (d : Int) * (m : Int) + 2 * (d : Int) + 6 * (m : Int) - 7 := by
    grind

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
private theorem cbrtStep_upper_of_le
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
