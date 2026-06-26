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
import SqrtProof.LeanCompat

open SqrtCertified
open SqrtCert

-- Definitions matching the Sqrt.sol EVM arithmetic.

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

/-- Ceiling square root on the uint256 mathematical domain. -/
def sqrtUp256 (x : Nat) : Nat :=
  let r := floorSqrt x
  if r * r < x then r + 1 else r

-- Lower-bound composition.

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

-- Correctness theorems.

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
  -- bstep is defined in FloorBound
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
  simp [Nat.ne_of_gt hx, bstep]

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
  have hlog : Nat.log2 x = i.val := (SqrtCompat.log2_eq_iff hx0).2 hOct
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
-- Named wrapper theorems
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
      (SqrtCompat.log2_eq_iff (Nat.ne_of_gt hx)).1 rfl
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
        (SqrtCompat.log2_eq_iff (Nat.ne_of_gt hx)).1 rfl
      simpa [i]
    exact floorSqrt_correct_of_octave i x m hmlo hmhi hOct

private theorem step_error_bound_square
    (m d : Nat)
    (hm : 0 < m)
    (hmd : d ≤ m) :
    bstep (m * m) (m + d) - m ≤ d * d / (2 * m) := by
  unfold bstep
  have hpos : 0 < m + d := by omega
  have hsq : m * m = (m + d) * (m - d) + d * d := by
    have h := sq_identity_ge (m + d) m (by omega) (by omega)
    have hsub : 2 * m - (m + d) = m - d := by omega
    have hdm' : (m + d) - m = d := by rw [Nat.add_sub_cancel_left]
    simpa [hsub, hdm'] using h.symm
  have hdiv : m * m / (m + d) = (m - d) + d * d / (m + d) := by
    rw [hsq]
    rw [Nat.mul_add_div hpos]
  have hrewrite :
      (m + d + m * m / (m + d)) / 2 - m = (d * d / (m + d)) / 2 := by
    rw [hdiv]
    let q := d * d / (m + d)
    have htmp : (m + d + (m - d + q)) / 2 = m + q / 2 := by
      have hsum : m + d + (m - d + q) = 2 * m + q := by omega
      rw [hsum]
      have htmp2 : (2 * m + q) / 2 = m + q / 2 := by
        have hswap : 2 * m + q = q + m * 2 := by omega
        rw [hswap, Nat.add_mul_div_right q m (by decide : 0 < 2)]
        omega
      exact htmp2
    rw [htmp, Nat.add_sub_cancel_left]
  rw [hrewrite]
  have hden : m ≤ m + d := by omega
  have hdivLe : d * d / (m + d) ≤ d * d / m := Nat.div_le_div_left hden hm
  have hhalf : (d * d / (m + d)) / 2 ≤ (d * d / m) / 2 := Nat.div_le_div_right hdivLe
  have hmain : (d * d / m) / 2 = d * d / (2 * m) := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm m 2]
  exact Nat.le_trans hhalf (by simp [hmain])

private theorem step_from_bound_square
    (m lo z D : Nat)
    (hm : 0 < m)
    (hloPos : 0 < lo)
    (hlo : lo ≤ m)
    (hmz : m ≤ z)
    (hzD : z - m ≤ D)
    (hDlo : D ≤ lo) :
    bstep (m * m) z - m ≤ D * D / (2 * lo) := by
  let d := z - m
  have hdEq : z = m + d := by
    dsimp [d]
    omega
  have hdm : d ≤ m := by
    dsimp [d]
    omega
  have hstep : bstep (m * m) (m + d) - m ≤ d * d / (2 * m) :=
    step_error_bound_square m d hm hdm
  have hbase : bstep (m * m) z - m ≤ d * d / (2 * m) := by
    simpa [hdEq] using hstep
  have hdD : d ≤ D := by
    simpa [d] using hzD
  have hsq : d * d ≤ D * D := Nat.mul_le_mul hdD hdD
  have hdiv : d * d / (2 * m) ≤ D * D / (2 * m) := Nat.div_le_div_right hsq
  have hden : 2 * lo ≤ 2 * m := Nat.mul_le_mul_left 2 hlo
  have hdivDen : D * D / (2 * m) ≤ D * D / (2 * lo) :=
    Nat.div_le_div_left hden (by omega : 0 < 2 * lo)
  exact Nat.le_trans hbase (Nat.le_trans hdiv hdivDen)

private def sqNext (lo d : Nat) : Nat := d * d / (2 * lo)

private def sqD2 (i : Fin 256) : Nat := sqNext (loOf i) (d1 i)
private def sqD3 (i : Fin 256) : Nat := sqNext (loOf i) (sqD2 i)
private def sqD4 (i : Fin 256) : Nat := sqNext (loOf i) (sqD3 i)
private def sqD5 (i : Fin 256) : Nat := sqNext (loOf i) (sqD4 i)
private def sqD6 (i : Fin 256) : Nat := sqNext (loOf i) (sqD5 i)

private theorem sqNext_mono_right (lo a b : Nat) (hab : a ≤ b) :
    sqNext lo a ≤ sqNext lo b := by
  unfold sqNext
  exact Nat.div_le_div_right (Nat.mul_le_mul hab hab)

private theorem sqNext_le_lo
    (lo d : Nat)
    (hlo : 0 < lo)
    (hd : d ≤ lo) :
    sqNext lo d ≤ lo := by
  unfold sqNext
  have hsq : d * d ≤ lo * lo := Nat.mul_le_mul hd hd
  have hdiv : d * d / (2 * lo) ≤ lo * lo / (2 * lo) := Nat.div_le_div_right hsq
  have hden : lo ≤ 2 * lo := by omega
  have hdiv' : lo * lo / (2 * lo) ≤ lo * lo / lo := Nat.div_le_div_left hden hlo
  have hmul : lo * lo / lo = lo := by simpa [Nat.mul_comm] using Nat.mul_div_right lo hlo
  exact Nat.le_trans hdiv (by simpa [hmul] using hdiv')

private theorem sqD2_le_lo : ∀ i : Fin 256, sqD2 i ≤ loOf i := by
  intro i
  unfold sqD2
  exact sqNext_le_lo (loOf i) (d1 i) (lo_pos i) (d1_le_lo i)

private theorem sqD3_le_lo : ∀ i : Fin 256, sqD3 i ≤ loOf i := by
  intro i
  unfold sqD3
  exact sqNext_le_lo (loOf i) (sqD2 i) (lo_pos i) (sqD2_le_lo i)

private theorem sqD4_le_lo : ∀ i : Fin 256, sqD4 i ≤ loOf i := by
  intro i
  unfold sqD4
  exact sqNext_le_lo (loOf i) (sqD3 i) (lo_pos i) (sqD3_le_lo i)

private theorem sqD5_le_lo : ∀ i : Fin 256, sqD5 i ≤ loOf i := by
  intro i
  unfold sqD5
  exact sqNext_le_lo (loOf i) (sqD4 i) (lo_pos i) (sqD4_le_lo i)

private theorem sqD2_le_d2 : ∀ i : Fin 256, sqD2 i ≤ d2 i := by
  intro i
  simp [sqD2, d2, sqNext, nextD]

private theorem sqD3_le_d3 : ∀ i : Fin 256, sqD3 i ≤ d3 i := by
  intro i
  have hmono : sqNext (loOf i) (sqD2 i) ≤ sqNext (loOf i) (d2 i) :=
    sqNext_mono_right (loOf i) (sqD2 i) (d2 i) (sqD2_le_d2 i)
  unfold sqD3 d3 nextD
  exact Nat.le_trans hmono (Nat.le_succ _)

private theorem sqD4_le_d4 : ∀ i : Fin 256, sqD4 i ≤ d4 i := by
  intro i
  have hmono : sqNext (loOf i) (sqD3 i) ≤ sqNext (loOf i) (d3 i) :=
    sqNext_mono_right (loOf i) (sqD3 i) (d3 i) (sqD3_le_d3 i)
  unfold sqD4 d4 nextD
  exact Nat.le_trans hmono (Nat.le_succ _)

private theorem sqD5_le_d5 : ∀ i : Fin 256, sqD5 i ≤ d5 i := by
  intro i
  have hmono : sqNext (loOf i) (sqD4 i) ≤ sqNext (loOf i) (d4 i) :=
    sqNext_mono_right (loOf i) (sqD4 i) (d4 i) (sqD4_le_d4 i)
  unfold sqD5 d5 nextD
  exact Nat.le_trans hmono (Nat.le_succ _)

private theorem sqD6_eq_zero : ∀ i : Fin 256, sqD6 i = 0 := by
  intro i
  have hsqLe : sqD6 i ≤ sqNext (loOf i) (d5 i) := by
    unfold sqD6
    exact sqNext_mono_right (loOf i) (sqD5 i) (d5 i) (sqD5_le_d5 i)
  have hd6le : d6 i ≤ 1 := d6_le_one i
  have hd6ge : 1 ≤ d6 i := by
    unfold d6 nextD
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hd6eq : d6 i = 1 := Nat.le_antisymm hd6le hd6ge
  have hsq0 : sqNext (loOf i) (d5 i) = 0 := by
    have hq : sqNext (loOf i) (d5 i) + 1 = d6 i := by
      simp [sqNext, d6, nextD]
    omega
  have hsqD6le0 : sqD6 i ≤ 0 := Nat.le_trans hsqLe (by simp [hsq0])
  exact Nat.eq_zero_of_le_zero hsqD6le0

private theorem innerSqrt_eq_natSqrt_of_square
    (x : Nat)
    (hx256 : x < 2 ^ 256)
    (hsq : natSqrt x * natSqrt x = x) :
    innerSqrt x = natSqrt x := by
  by_cases hx0 : x = 0
  · subst hx0
    simp [innerSqrt, natSqrt]
  · have hx : 0 < x := Nat.pos_of_ne_zero hx0
    let m := natSqrt x
    have hmSq : m * m = x := by simpa [m] using hsq
    have hmlo : m * m ≤ x := by simp [m, hmSq]
    have hmhi : x < (m + 1) * (m + 1) := by simpa [m] using natSqrt_lt_succ_sq x
    have hm : 0 < m := by
      by_cases hm0 : m = 0
      · have hx0' : x = 0 := by simpa [m, hm0] using hmSq.symm
        exact False.elim (hx0 hx0')
      · exact Nat.pos_of_ne_zero hm0
    let i : Fin 256 := ⟨Nat.log2 x, (Nat.log2_lt (Nat.ne_of_gt hx)).2 hx256⟩
    have hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1) := by
      have hlog : 2 ^ Nat.log2 x ≤ x ∧ x < 2 ^ (Nat.log2 x + 1) :=
        (SqrtCompat.log2_eq_iff (Nat.ne_of_gt hx)).1 rfl
      simpa [i]
    have hseed : sqrtSeed x = seedOf i := sqrtSeed_eq_seedOf_of_octave i x hOct
    let z0 := seedOf i
    let z1 := bstep x z0
    let z2 := bstep x z1
    let z3 := bstep x z2
    let z4 := bstep x z3
    let z5 := bstep x z4
    let z6 := bstep x z5
    have hsPos : 0 < z0 := by
      dsimp [z0]
      have hpow : 0 < (2 : Nat) ^ ((i.val + 1) / 2) := Nat.pow_pos (by decide : 0 < (2 : Nat))
      rw [seedOf, Nat.shiftLeft_eq, Nat.one_mul]
      exact hpow
    have hmz1 : m ≤ z1 := by
      dsimp [z1, z0]
      exact babylon_step_floor_bound x (seedOf i) m hsPos hmlo
    have hz1Pos : 0 < z1 := Nat.lt_of_lt_of_le hm hmz1
    have hmz2 : m ≤ z2 := by
      dsimp [z2]
      exact babylon_step_floor_bound x z1 m hz1Pos hmlo
    have hz2Pos : 0 < z2 := Nat.lt_of_lt_of_le hm hmz2
    have hmz3 : m ≤ z3 := by
      dsimp [z3]
      exact babylon_step_floor_bound x z2 m hz2Pos hmlo
    have hz3Pos : 0 < z3 := Nat.lt_of_lt_of_le hm hmz3
    have hmz4 : m ≤ z4 := by
      dsimp [z4]
      exact babylon_step_floor_bound x z3 m hz3Pos hmlo
    have hz4Pos : 0 < z4 := Nat.lt_of_lt_of_le hm hmz4
    have hmz5 : m ≤ z5 := by
      dsimp [z5]
      exact babylon_step_floor_bound x z4 m hz4Pos hmlo
    have hz5Pos : 0 < z5 := Nat.lt_of_lt_of_le hm hmz5
    have hmz6 : m ≤ z6 := by
      dsimp [z6]
      exact babylon_step_floor_bound x z5 m hz5Pos hmlo
    have hinterval : loOf i ≤ m ∧ m ≤ hiOf i := m_within_cert_interval i x m hmlo hmhi hOct
    have hrun5 := run5_error_bounds i x m hm hmlo hmhi hinterval.1 hinterval.2
    have hd1 : z1 - m ≤ d1 i := by simpa [z1, z2, z3, z4, z5] using hrun5.1
    have hd2 : z2 - m ≤ sqD2 i := by
      have h := step_from_bound_square m (loOf i) z1 (d1 i) hm (lo_pos i) hinterval.1 hmz1 hd1 (d1_le_lo i)
      simpa [z2, hmSq, sqD2, sqNext] using h
    have hd3 : z3 - m ≤ sqD3 i := by
      have h := step_from_bound_square m (loOf i) z2 (sqD2 i) hm (lo_pos i) hinterval.1 hmz2 hd2 (sqD2_le_lo i)
      simpa [z3, hmSq, sqD3, sqNext] using h
    have hd4 : z4 - m ≤ sqD4 i := by
      have h := step_from_bound_square m (loOf i) z3 (sqD3 i) hm (lo_pos i) hinterval.1 hmz3 hd3 (sqD3_le_lo i)
      simpa [z4, hmSq, sqD4, sqNext] using h
    have hd5 : z5 - m ≤ sqD5 i := by
      have h := step_from_bound_square m (loOf i) z4 (sqD4 i) hm (lo_pos i) hinterval.1 hmz4 hd4 (sqD4_le_lo i)
      simpa [z5, hmSq, sqD5, sqNext] using h
    have hd6 : z6 - m ≤ sqD6 i := by
      have h := step_from_bound_square m (loOf i) z5 (sqD5 i) hm (lo_pos i) hinterval.1 hmz5 hd5 (sqD5_le_lo i)
      simpa [z6, hmSq, sqD6, sqNext] using h
    have hz6le : z6 ≤ m := by
      have h0 : z6 - m = 0 := by
        have h0le : z6 - m ≤ 0 := by simpa [sqD6_eq_zero i] using hd6
        exact Nat.eq_zero_of_le_zero h0le
      exact (Nat.sub_eq_zero_iff_le).1 h0
    have hz6eq : z6 = m := Nat.le_antisymm hz6le hmz6
    have hrun : innerSqrt x = run6From x (seedOf i) := by
      calc
        innerSqrt x = run6From x (sqrtSeed x) := innerSqrt_eq_run6From x hx
        _ = run6From x (seedOf i) := by simp [hseed]
    have hrun6 : run6From x (seedOf i) = z6 := by
      unfold run6From
      simp [z1, z2, z3, z4, z5, z6, z0, bstep]
    calc
      innerSqrt x = run6From x (seedOf i) := hrun
      _ = z6 := hrun6
      _ = m := hz6eq
      _ = natSqrt x := by rfl

theorem sqrt_spec_unique
    {x a b : Nat}
    (haLo : a * a ≤ x) (haHi : x < (a + 1) * (a + 1))
    (hbLo : b * b ≤ x) (hbHi : x < (b + 1) * (b + 1)) :
    a = b := by
  apply Nat.le_antisymm
  · by_cases hle : a ≤ b
    · exact hle
    have hlt : b < a := Nat.lt_of_not_ge hle
    have hsucc : b + 1 ≤ a := Nat.succ_le_of_lt hlt
    have hsq : (b + 1) * (b + 1) ≤ a * a := Nat.mul_le_mul hsucc hsucc
    have hn : (b + 1) * (b + 1) ≤ x := Nat.le_trans hsq haLo
    exact False.elim ((Nat.not_lt_of_ge hn) hbHi)
  · by_cases hle : b ≤ a
    · exact hle
    have hlt : a < b := Nat.lt_of_not_ge hle
    have hsucc : a + 1 ≤ b := Nat.succ_le_of_lt hlt
    have hsq : (a + 1) * (a + 1) ≤ b * b := Nat.mul_le_mul hsucc hsucc
    have hn : (a + 1) * (a + 1) ≤ x := Nat.le_trans hsq hbLo
    exact False.elim ((Nat.not_lt_of_ge hn) haHi)

theorem floorSqrt_eq_natSqrt_u256
    (x : Nat)
    (hx256 : x < 2 ^ 256) :
    floorSqrt x = natSqrt x := by
  have hfloor := floorSqrt_correct_u256 x hx256
  exact sqrt_spec_unique
    (a := floorSqrt x) (b := natSqrt x)
    (by simpa using hfloor.1)
    (by simpa using hfloor.2)
    (natSqrt_sq_le x)
    (natSqrt_lt_succ_sq x)

theorem sqrtUpInner_eq_sqrtUp256_u256
    (x : Nat)
    (hx256 : x < 2 ^ 256) :
    (let z := innerSqrt x
     if z * z < x then z + 1 else z) = sqrtUp256 x := by
  unfold sqrtUp256
  rw [floorSqrt_eq_natSqrt_u256 x hx256]
  let m := natSqrt x
  have hmlo : m * m ≤ x := by simpa [m] using natSqrt_sq_le x
  have hmhi : x < (m + 1) * (m + 1) := by simpa [m] using natSqrt_lt_succ_sq x
  have hbr : m ≤ innerSqrt x ∧ innerSqrt x ≤ m + 1 := by
    simpa [m] using innerSqrt_bracket_u256_all x hx256
  by_cases hsq : m * m < x
  · have hzCases : innerSqrt x = m ∨ innerSqrt x = m + 1 := by omega
    cases hzCases with
    | inl hz =>
        change
          (if innerSqrt x * innerSqrt x < x then innerSqrt x + 1 else innerSqrt x) =
            (if natSqrt x * natSqrt x < x then natSqrt x + 1 else natSqrt x)
        have hsqInner : innerSqrt x * innerSqrt x < x := by simpa [hz] using hsq
        have hsqNat : natSqrt x * natSqrt x < x := by simpa [m] using hsq
        rw [if_pos hsqInner, if_pos hsqNat]
        simp [m, hz]
    | inr hz =>
        have hnot : ¬ innerSqrt x * innerSqrt x < x := by
          have hle : x ≤ innerSqrt x * innerSqrt x := by
            rw [hz]
            exact Nat.le_of_lt hmhi
          exact Nat.not_lt_of_ge hle
        change
          (if innerSqrt x * innerSqrt x < x then innerSqrt x + 1 else innerSqrt x) =
            (if natSqrt x * natSqrt x < x then natSqrt x + 1 else natSqrt x)
        have hsqNat : natSqrt x * natSqrt x < x := by simpa [m] using hsq
        rw [if_neg hnot, if_pos hsqNat]
        simp [m, hz]
  · have hsqEq : m * m = x := Nat.le_antisymm hmlo (Nat.le_of_not_gt hsq)
    have hz : innerSqrt x = m := by
      have hsqNat : natSqrt x * natSqrt x = x := by simpa [m] using hsqEq
      simpa [m] using innerSqrt_eq_natSqrt_of_square x hx256 hsqNat
    have hnot : ¬ innerSqrt x * innerSqrt x < x := by
      simp [hz, hsq]
    change
      (if innerSqrt x * innerSqrt x < x then innerSqrt x + 1 else innerSqrt x) =
        (if natSqrt x * natSqrt x < x then natSqrt x + 1 else natSqrt x)
    have hsqNatNot : ¬ natSqrt x * natSqrt x < x := by simpa [m] using hsq
    rw [if_neg hnot, if_neg hsqNatNot]
    simp [m, hz]

/-- Canonical witness package for the uint256 correctness statement. -/
theorem sqrt_witness_correct_u256
    (x : Nat)
    (hx256 : x < 2 ^ 256) :
    ∃ m, m * m ≤ x ∧ x < (m + 1) * (m + 1) ∧
      m ≤ innerSqrt x ∧ innerSqrt x ≤ m + 1 := by
  refine ⟨natSqrt x, natSqrt_sq_le x, natSqrt_lt_succ_sq x, ?_⟩
  simpa using innerSqrt_bracket_u256_all x hx256
