/-
  Correctness components for Sqrt.sol:_sqrt and sqrt.

  Theorem 1 (innerSqrt_correct):
    Lower-bound component: if m² ≤ x then m ≤ innerSqrt(x) (for x > 0).

  Theorem 2 (floorSqrt_correct):
    Given a 1-ULP bracket for innerSqrt(x), floorSqrt(x) satisfies
    r² ≤ x < (r+1)².
-/
import Init
import SqrtProof.FloorBound
import SqrtProof.StepMono
import SqrtProof.CertifiedChain

-- ============================================================================
-- Part 1: Definitions matching Sqrt.sol EVM semantics
-- ============================================================================

/-- One Babylonian step: ⌊(z + ⌊x/z⌋) / 2⌋. Same as StepMono.babylonStep. -/
def bstep (x z : Nat) : Nat := (z + x / z) / 2

/-- The seed: z₀ = 2^⌊(log2(x)+1)/2⌋. For x=0, returns 0.
    Matches EVM: shl(shr(1, sub(256, clz(x))), 1)
    Since 256 - clz(x) = bitLength(x) = log2(x) + 1 for x > 0. -/
def sqrtSeed (x : Nat) : Nat :=
  if x = 0 then 0
  else 1 <<< ((Nat.log2 x + 1) / 2)

/-- _sqrt: seed + 6 Babylonian steps. Returns z ∈ {isqrt(x), isqrt(x)+1}. -/
def innerSqrt (x : Nat) : Nat :=
  if x = 0 then 0
  else
    let z := sqrtSeed x
    let z := bstep x z
    let z := bstep x z
    let z := bstep x z
    let z := bstep x z
    let z := bstep x z
    let z := bstep x z
    z

/-- sqrt: _sqrt with floor correction. Returns exactly isqrt(x).
    Matches: z := sub(z, lt(div(x, z), z)) -/
def floorSqrt (x : Nat) : Nat :=
  let z := innerSqrt x
  if z = 0 then 0
  else if x / z < z then z - 1 else z

-- ============================================================================
-- Part 2: Computational verification of convergence (upper bound)
-- ============================================================================

/-- Compute the max-propagation upper bound for octave n.
    Z₀ = seed, Z_{i+1} = bstep(x_max, Z_i), return Z₆. -/
def maxProp (n : Nat) : Nat :=
  let x_max := 2 ^ (n + 1) - 1
  let z := 1 <<< ((n + 1) / 2)
  let z := bstep x_max z
  let z := bstep x_max z
  let z := bstep x_max z
  let z := bstep x_max z
  let z := bstep x_max z
  let z := bstep x_max z
  z

/-- Check that the max-propagation result Z₆ satisfies:
    Z₆² ≤ x_max AND (Z₆+1)² > x_max  (Z₆ = isqrt(x_max))
    OR Z₆² > x_max AND (Z₆-1)² ≤ x_max  (Z₆ = isqrt(x_max) + 1)
    In either case: Z₆ ≤ isqrt(x_max) + 1. -/
def checkOctave (n : Nat) : Bool :=
  let x_max := 2 ^ (n + 1) - 1
  let z := maxProp n
  -- Check: (z-1)² ≤ x_max (i.e., z ≤ isqrt(x_max) + 1)
  -- AND z*z ≤ x_max + z (equivalent to z ≤ isqrt(x_max) + 1 for the correction step)
  (z - 1) * (z - 1) ≤ x_max

/-- Also check that seed is positive (needed for the lower bound proof). -/
def checkSeedPos (n : Nat) : Bool :=
  1 <<< ((n + 1) / 2) > 0

/-- Also check that maxProp gives an overestimate or is in absorbing set.
    Specifically: maxProp(n)² > x_min OR maxProp(n) = isqrt(x_max) or isqrt(x_max)+1. -/
def checkUpperBound (n : Nat) : Bool :=
  let x_max := 2 ^ (n + 1) - 1
  let z := maxProp n
  -- (z-1)² ≤ x_max: z is at most isqrt(x_max) + 1
  (z - 1) * (z - 1) ≤ x_max &&
  -- z² ≤ x_max + z: ensures z ≤ isqrt(x_max) + 1 (slightly different formulation)
  -- Actually just check (z-1)*(z-1) ≤ x_max is sufficient.
  -- Also check z > 0 for division safety.
  z > 0

/-- The critical computational check: all 256 octaves pass. -/
theorem all_octaves_pass : ∀ i : Fin 256, checkUpperBound i.val = true := by
  native_decide

/-- Seeds are always positive. -/
theorem all_seeds_pos : ∀ i : Fin 256, checkSeedPos i.val = true := by
  native_decide

-- ============================================================================
-- Part 3: Lower bound (composing Lemma 1)
-- ============================================================================

/-- The seed is positive for x > 0. -/
theorem sqrtSeed_pos (x : Nat) (hx : 0 < x) :
    0 < sqrtSeed x := by
  unfold sqrtSeed
  simp [Nat.ne_of_gt hx]
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.lt_of_lt_of_le (by omega : 0 < 1) (Nat.one_le_pow _ 2 (by omega))

/-- bstep preserves positivity when x > 0 and z > 0. -/
theorem bstep_pos (x z : Nat) (hx : 0 < x) (hz : 0 < z) : 0 < bstep x z := by
  unfold bstep
  -- For x ≥ 1 and z ≥ 1: z + x/z ≥ 2 (since z ≥ 1 and x/z ≥ 1 when z = 1,
  -- or z ≥ 2 when x/z = 0). So (z + x/z)/2 ≥ 1.
  by_cases hle : x < z
  · -- x < z, so x/z = 0. But z ≥ 2 (since x ≥ 1 and x < z means z ≥ 2).
    have : x / z = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hle)
    omega
  · -- x ≥ z, so x/z ≥ 1
    have : 0 < x / z := Nat.div_pos (by omega) hz
    omega

/-- Canonical integer-square-root witness built by simple recursion.
    This avoids additional dependencies while giving `m² ≤ x < (m+1)²`. -/
def natSqrt : Nat → Nat
  | 0 => 0
  | n + 1 =>
      let m := natSqrt n
      if (m + 1) * (m + 1) ≤ n + 1 then m + 1 else m

/-- Correctness spec for `natSqrt`. -/
theorem natSqrt_spec (n : Nat) :
    natSqrt n * natSqrt n ≤ n ∧ n < (natSqrt n + 1) * (natSqrt n + 1) := by
  induction n with
  | zero =>
      simp [natSqrt]
  | succ n ih =>
      rcases ih with ⟨ihle, ihlt⟩
      let m := natSqrt n
      have ihle' : m * m ≤ n := by simpa [m] using ihle
      have ihlt' : n < (m + 1) * (m + 1) := by simpa [m] using ihlt
      by_cases hstep : (m + 1) * (m + 1) ≤ n + 1
      · have hn1eq : n + 1 = (m + 1) * (m + 1) := by omega
        have hm12 : m + 1 < m + 2 := by omega
        have hleft : (m + 1) * (m + 1) < (m + 1) * (m + 2) :=
          Nat.mul_lt_mul_of_pos_left hm12 (by omega : 0 < m + 1)
        have hright : (m + 2) * (m + 1) < (m + 2) * (m + 2) :=
          Nat.mul_lt_mul_of_pos_left hm12 (by omega : 0 < m + 2)
        have hsq_lt : (m + 1) * (m + 1) < (m + 2) * (m + 2) := by
          calc
            (m + 1) * (m + 1) < (m + 1) * (m + 2) := hleft
            _ = (m + 2) * (m + 1) := by rw [Nat.mul_comm]
            _ < (m + 2) * (m + 2) := hright
        constructor
        · simp [natSqrt, m, hstep]
        · have hlt2 : n + 1 < (m + 2) * (m + 2) := by simpa [hn1eq] using hsq_lt
          simpa [natSqrt, m, hstep, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt2
      · have hn1lt : n + 1 < (m + 1) * (m + 1) := Nat.lt_of_not_ge hstep
        constructor
        · have hmle : m * m ≤ n + 1 := Nat.le_trans ihle' (Nat.le_succ n)
          simpa [natSqrt, m, hstep] using hmle
        · simpa [natSqrt, m, hstep] using hn1lt

theorem natSqrt_sq_le (n : Nat) : natSqrt n * natSqrt n ≤ n :=
  (natSqrt_spec n).1

theorem natSqrt_lt_succ_sq (n : Nat) : n < (natSqrt n + 1) * (natSqrt n + 1) :=
  (natSqrt_spec n).2

-- ============================================================================
-- Part 4: Main theorems
-- ============================================================================

/-- innerSqrt gives a lower bound: for any m with m² ≤ x, m ≤ innerSqrt(x).
    This follows from 6 applications of babylon_step_floor_bound. -/
theorem innerSqrt_lower (x m : Nat) (hx : 0 < x)
    (hm : m * m ≤ x) : m ≤ innerSqrt x := by
  unfold innerSqrt
  simp [Nat.ne_of_gt hx]
  -- The seed is positive
  have hs := sqrtSeed_pos x hx
  -- Each bstep preserves positivity (x > 0)
  -- Chain: m ≤ bstep x (bstep x (... (bstep x (sqrtSeed x))))
  -- Each step: if m² ≤ x and z > 0, then m ≤ bstep x z
  -- bstep = babylonStep from FloorBound
  -- babylon_step_floor_bound : m*m ≤ x → 0 < z → m ≤ (z + x/z)/2
  have h1 := bstep_pos x _ hx hs
  have h2 := bstep_pos x _ hx h1
  have h3 := bstep_pos x _ hx h2
  have h4 := bstep_pos x _ hx h3
  have h5 := bstep_pos x _ hx h4
  -- Apply floor bound at the last step (z₅ is positive by h5)
  exact babylon_step_floor_bound x _ m h5 hm

/-- Unfolding identity: `innerSqrt` is six steps starting from `sqrtSeed`. -/
theorem innerSqrt_eq_run6From (x : Nat) (hx : 0 < x) :
    innerSqrt x = SqrtCertified.run6From x (sqrtSeed x) := by
  unfold innerSqrt SqrtCertified.run6From
  simp [Nat.ne_of_gt hx, bstep, SqrtBridge.bstep]

/-- Finite-certificate upper bound: if `m` is bracketed by the octave certificate,
    then six steps from the actual seed satisfy `innerSqrt x ≤ m + 1`. -/
theorem innerSqrt_upper_cert
    (i : Fin 256) (x m : Nat)
    (hx : 0 < x)
    (hm : 0 < m)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hseed : sqrtSeed x = SqrtCert.seedOf i)
    (hlo : SqrtCert.loOf i ≤ m)
    (hhi : m ≤ SqrtCert.hiOf i) :
    innerSqrt x ≤ m + 1 := by
  have hrun : SqrtCertified.run6From x (SqrtCert.seedOf i) ≤ m + 1 :=
    SqrtCertified.run6_le_m_plus_one i x m hm hmlo hmhi hlo hhi
  calc
    innerSqrt x = SqrtCertified.run6From x (sqrtSeed x) := innerSqrt_eq_run6From x hx
    _ = SqrtCertified.run6From x (SqrtCert.seedOf i) := by simp [hseed]
    _ ≤ m + 1 := hrun

/-- Certificate-backed 1-ULP bracket for `innerSqrt`. -/
theorem innerSqrt_bracket_cert
    (i : Fin 256) (x m : Nat)
    (hx : 0 < x)
    (hm : 0 < m)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hseed : sqrtSeed x = SqrtCert.seedOf i)
    (hlo : SqrtCert.loOf i ≤ m)
    (hhi : m ≤ SqrtCert.hiOf i) :
    m ≤ innerSqrt x ∧ innerSqrt x ≤ m + 1 := by
  exact ⟨innerSqrt_lower x m hx hmlo, innerSqrt_upper_cert i x m hx hm hmlo hmhi hseed hlo hhi⟩

/-- `sqrtSeed` agrees with the finite-certificate seed on octave `i`. -/
theorem sqrtSeed_eq_seedOf_of_octave
    (i : Fin 256) (x : Nat)
    (hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1)) :
    sqrtSeed x = SqrtCert.seedOf i := by
  have hx : 0 < x := Nat.lt_of_lt_of_le (Nat.two_pow_pos i.val) hOct.1
  have hx0 : x ≠ 0 := Nat.ne_of_gt hx
  have hlog : Nat.log2 x = i.val := (Nat.log2_eq_iff hx0).2 hOct
  unfold sqrtSeed SqrtCert.seedOf
  simp [Nat.ne_of_gt hx, hlog]

/-- From the certified octave endpoints and `m² ≤ x < (m+1)²`,
    derive `m ∈ [loOf i, hiOf i]`. -/
theorem m_within_cert_interval
    (i : Fin 256) (x m : Nat)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1)) :
    SqrtCert.loOf i ≤ m ∧ m ≤ SqrtCert.hiOf i := by
  have hloSq : SqrtCert.loOf i * SqrtCert.loOf i ≤ 2 ^ i.val := SqrtCert.lo_sq_le_pow2 i
  have hloSqX : SqrtCert.loOf i * SqrtCert.loOf i ≤ x := Nat.le_trans hloSq hOct.1
  have hlo : SqrtCert.loOf i ≤ m := by
    by_cases h : SqrtCert.loOf i ≤ m
    · exact h
    · have hlt : m < SqrtCert.loOf i := Nat.lt_of_not_ge h
      have hm1 : m + 1 ≤ SqrtCert.loOf i := Nat.succ_le_of_lt hlt
      have hm1sq : (m + 1) * (m + 1) ≤ SqrtCert.loOf i * SqrtCert.loOf i :=
        Nat.mul_le_mul hm1 hm1
      have hm1x : (m + 1) * (m + 1) ≤ x := Nat.le_trans hm1sq hloSqX
      exact False.elim ((Nat.not_lt_of_ge hm1x) hmhi)
  have hhiSq : 2 ^ (i.val + 1) ≤ (SqrtCert.hiOf i + 1) * (SqrtCert.hiOf i + 1) :=
    SqrtCert.pow2_succ_le_hi_succ_sq i
  have hXHi : x < (SqrtCert.hiOf i + 1) * (SqrtCert.hiOf i + 1) :=
    Nat.lt_of_lt_of_le hOct.2 hhiSq
  have hhi : m ≤ SqrtCert.hiOf i := by
    by_cases h : m ≤ SqrtCert.hiOf i
    · exact h
    · have hlt : SqrtCert.hiOf i < m := Nat.lt_of_not_ge h
      have hhi1 : SqrtCert.hiOf i + 1 ≤ m := Nat.succ_le_of_lt hlt
      have hhimsq : (SqrtCert.hiOf i + 1) * (SqrtCert.hiOf i + 1) ≤ m * m :=
        Nat.mul_le_mul hhi1 hhi1
      have hXmm : x < m * m := Nat.lt_of_lt_of_le hXHi hhimsq
      exact False.elim ((Nat.not_lt_of_ge hmlo) hXmm)
  exact ⟨hlo, hhi⟩

/-- Certificate-backed upper bound under octave membership. -/
theorem innerSqrt_upper_of_octave
    (i : Fin 256) (x m : Nat)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1)) :
    innerSqrt x ≤ m + 1 := by
  have hx : 0 < x := Nat.lt_of_lt_of_le (Nat.two_pow_pos i.val) hOct.1
  have hm : 0 < m := by
    by_cases hm0 : m = 0
    · subst hm0
      have hx1 : 1 ≤ x := Nat.succ_le_of_lt hx
      have hlt1 : x < 1 := by simpa using hmhi
      exact False.elim ((Nat.not_lt_of_ge hx1) hlt1)
    · exact Nat.pos_of_ne_zero hm0
  have hseed : sqrtSeed x = SqrtCert.seedOf i := sqrtSeed_eq_seedOf_of_octave i x hOct
  have hinterval : SqrtCert.loOf i ≤ m ∧ m ≤ SqrtCert.hiOf i :=
    m_within_cert_interval i x m hmlo hmhi hOct
  exact innerSqrt_upper_cert i x m hx hm hmlo hmhi hseed hinterval.1 hinterval.2

/-- Certificate-backed 1-ULP bracket under octave membership. -/
theorem innerSqrt_bracket_of_octave
    (i : Fin 256) (x m : Nat)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1)) :
    m ≤ innerSqrt x ∧ innerSqrt x ≤ m + 1 := by
  have hx : 0 < x := Nat.lt_of_lt_of_le (Nat.two_pow_pos i.val) hOct.1
  exact ⟨innerSqrt_lower x m hx hmlo, innerSqrt_upper_of_octave i x m hmlo hmhi hOct⟩

/-- The floor correction is correct.
    Given z > 0, (z-1)² ≤ x < (z+1)², the correction gives isqrt(x). -/
theorem floor_correction (x z : Nat) (hz : 0 < z)
    (hlo : (z - 1) * (z - 1) ≤ x)
    (hhi : x < (z + 1) * (z + 1)) :
    let r := if x / z < z then z - 1 else z
    r * r ≤ x ∧ x < (r + 1) * (r + 1) := by
  simp only
  by_cases h_lt : x / z < z
  · -- x/z < z means z² > x (since z * (x/z) ≤ x < z * z)
    simp [h_lt]
    have h_zsq : x < z * z := by
      have h_euc := Nat.div_add_mod x z
      have h_mod := Nat.mod_lt x hz
      -- x < z * (x/z + 1) and x/z + 1 ≤ z, so x < z * z
      have h1 : x < z * (x / z + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
      exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_left z (by omega))
    constructor
    · exact hlo
    · have : z - 1 + 1 = z := by omega
      rw [this]; exact h_zsq
  · -- x/z ≥ z means z² ≤ x
    simp [h_lt]
    simp only [Nat.not_lt] at h_lt
    have h_zsq : z * z ≤ x := by
      calc z * z ≤ z * (x / z) := Nat.mul_le_mul_left z h_lt
        _ ≤ x := Nat.mul_div_le x z
    exact ⟨h_zsq, hhi⟩

-- ============================================================================
-- Named wrappers for the advertised theorem entry points
-- ============================================================================

/-- `innerSqrt_correct`: established lower-bound component.
    For any witness `m` with `m² ≤ x` and `x > 0`, `innerSqrt x` is at least `m`. -/
theorem innerSqrt_correct (x m : Nat) (hx : 0 < x) (hm : m * m ≤ x) :
    m ≤ innerSqrt x :=
  innerSqrt_lower x m hx hm

/-- `floorSqrt_correct`: correction-step correctness under a 1-ULP bracket
    for the inner approximation. -/
theorem floorSqrt_correct (x : Nat) (hz : 0 < innerSqrt x)
    (hlo : (innerSqrt x - 1) * (innerSqrt x - 1) ≤ x)
    (hhi : x < (innerSqrt x + 1) * (innerSqrt x + 1)) :
    let r := floorSqrt x
    r * r ≤ x ∧ x < (r + 1) * (r + 1) := by
  unfold floorSqrt
  simpa [Nat.ne_of_gt hz] using floor_correction x (innerSqrt x) hz hlo hhi

/-- End-to-end correction theorem from the finite certificate assumptions. -/
theorem floorSqrt_correct_cert
    (i : Fin 256) (x m : Nat)
    (hx : 0 < x)
    (hm : 0 < m)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hseed : sqrtSeed x = SqrtCert.seedOf i)
    (hlo : SqrtCert.loOf i ≤ m)
    (hhi : m ≤ SqrtCert.hiOf i) :
    let r := floorSqrt x
    r * r ≤ x ∧ x < (r + 1) * (r + 1) := by
  have hlow : m ≤ innerSqrt x := innerSqrt_lower x m hx hmlo
  have hupp : innerSqrt x ≤ m + 1 := innerSqrt_upper_cert i x m hx hm hmlo hmhi hseed hlo hhi
  have hz : 0 < innerSqrt x := Nat.lt_of_lt_of_le hm hlow
  have hlo' : (innerSqrt x - 1) * (innerSqrt x - 1) ≤ x := by
    have hz1 : innerSqrt x - 1 ≤ m := by omega
    have hsq : (innerSqrt x - 1) * (innerSqrt x - 1) ≤ m * m := Nat.mul_le_mul hz1 hz1
    exact Nat.le_trans hsq hmlo
  have hhi' : x < (innerSqrt x + 1) * (innerSqrt x + 1) := by
    have hm1 : m + 1 ≤ innerSqrt x + 1 := by omega
    have hsq : (m + 1) * (m + 1) ≤ (innerSqrt x + 1) * (innerSqrt x + 1) :=
      Nat.mul_le_mul hm1 hm1
    exact Nat.lt_of_lt_of_le hmhi hsq
  exact floorSqrt_correct x hz hlo' hhi'

/-- End-to-end correctness under octave membership plus the witness
    `m² ≤ x < (m+1)²` (so `m` is the integer square root witness). -/
theorem floorSqrt_correct_of_octave
    (i : Fin 256) (x m : Nat)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1)) :
    let r := floorSqrt x
    r * r ≤ x ∧ x < (r + 1) * (r + 1) := by
  have hx : 0 < x := Nat.lt_of_lt_of_le (Nat.two_pow_pos i.val) hOct.1
  have hm : 0 < m := by
    by_cases hm0 : m = 0
    · subst hm0
      have hx1 : 1 ≤ x := Nat.succ_le_of_lt hx
      have hlt1 : x < 1 := by simpa using hmhi
      exact False.elim ((Nat.not_lt_of_ge hx1) hlt1)
    · exact Nat.pos_of_ne_zero hm0
  have hseed : sqrtSeed x = SqrtCert.seedOf i := sqrtSeed_eq_seedOf_of_octave i x hOct
  have hinterval : SqrtCert.loOf i ≤ m ∧ m ≤ SqrtCert.hiOf i :=
    m_within_cert_interval i x m hmlo hmhi hOct
  exact floorSqrt_correct_cert i x m hx hm hmlo hmhi hseed hinterval.1 hinterval.2

/-- Universal `_sqrt` bracket on uint256 domain:
    choose `m = natSqrt x` and derive `m ≤ innerSqrt x ≤ m+1`. -/
theorem innerSqrt_bracket_u256
    (x : Nat)
    (hx : 0 < x)
    (hx256 : x < 2 ^ 256) :
    let m := natSqrt x
    m ≤ innerSqrt x ∧ innerSqrt x ≤ m + 1 := by
  let i : Fin 256 := ⟨Nat.log2 x, (Nat.log2_lt (Nat.ne_of_gt hx)).2 hx256⟩
  let m := natSqrt x
  have hmlo : m * m ≤ x := by simpa [m] using natSqrt_sq_le x
  have hmhi : x < (m + 1) * (m + 1) := by simpa [m] using natSqrt_lt_succ_sq x
  have hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1) := by
    have hlog : 2 ^ Nat.log2 x ≤ x ∧ x < 2 ^ (Nat.log2 x + 1) :=
      (Nat.log2_eq_iff (Nat.ne_of_gt hx)).1 rfl
    simpa [i]
  exact innerSqrt_bracket_of_octave i x m hmlo hmhi hOct

/-- Universal `_sqrt` bracket on uint256 domain (including `x = 0`). -/
theorem innerSqrt_bracket_u256_all
    (x : Nat)
    (hx256 : x < 2 ^ 256) :
    let m := natSqrt x
    m ≤ innerSqrt x ∧ innerSqrt x ≤ m + 1 := by
  by_cases hx0 : x = 0
  · subst hx0
    simp [natSqrt, innerSqrt]
  · have hx : 0 < x := Nat.pos_of_ne_zero hx0
    simpa using innerSqrt_bracket_u256 x hx hx256

/-- Universal `sqrt` correctness on uint256 domain (Nat model):
    for every `x < 2^256`, `floorSqrt x` satisfies the integer-sqrt spec. -/
theorem floorSqrt_correct_u256
    (x : Nat)
    (hx256 : x < 2 ^ 256) :
    let r := floorSqrt x
    r * r ≤ x ∧ x < (r + 1) * (r + 1) := by
  by_cases hx0 : x = 0
  · subst hx0
    simp [floorSqrt, innerSqrt]
  · have hx : 0 < x := Nat.pos_of_ne_zero hx0
    let i : Fin 256 := ⟨Nat.log2 x, (Nat.log2_lt (Nat.ne_of_gt hx)).2 hx256⟩
    let m := natSqrt x
    have hmlo : m * m ≤ x := by simpa [m] using natSqrt_sq_le x
    have hmhi : x < (m + 1) * (m + 1) := by simpa [m] using natSqrt_lt_succ_sq x
    have hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1) := by
      have hlog : 2 ^ Nat.log2 x ≤ x ∧ x < 2 ^ (Nat.log2 x + 1) :=
        (Nat.log2_eq_iff (Nat.ne_of_gt hx)).1 rfl
      simpa [i]
    exact floorSqrt_correct_of_octave i x m hmlo hmhi hOct

/-- Canonical witness package for the advertised uint256 statement. -/
theorem sqrt_witness_correct_u256
    (x : Nat)
    (hx256 : x < 2 ^ 256) :
    ∃ m, m * m ≤ x ∧ x < (m + 1) * (m + 1) ∧
      m ≤ innerSqrt x ∧ innerSqrt x ≤ m + 1 := by
  refine ⟨natSqrt x, natSqrt_sq_le x, natSqrt_lt_succ_sq x, ?_⟩
  simpa using innerSqrt_bracket_u256_all x hx256

-- ============================================================================
-- Summary of proof status
-- ============================================================================

/-
  PROOF STATUS — ALL COMPLETE (0 sorry):

  ✓ Lemma 1 (Floor Bound): babylon_step_floor_bound
  ✓ Lemma 2 (Absorbing Set): babylon_from_ceil, babylon_from_floor
  ✓ Step Monotonicity: babylonStep_mono_x, babylonStep_mono_z
  ✓ Overestimate Contraction: babylonStep_lt_of_overestimate
  ✓ Computational Verification: all_octaves_pass (native_decide, 256 cases)
  ✓ Lower Bound Chain: innerSqrt_lower (6x babylon_step_floor_bound)
  ✓ Finite-Certificate Upper Bound: innerSqrt_upper_cert
  ✓ Floor Correction: floor_correction (case split on x/z < z)
  ✓ Octave Wiring: innerSqrt_upper_of_octave, floorSqrt_correct_of_octave
  ✓ Universal uint256 wrappers: innerSqrt_bracket_u256_all, floorSqrt_correct_u256
  ✓ Theorem wrappers: innerSqrt_correct, floorSqrt_correct, floorSqrt_correct_cert
-/
