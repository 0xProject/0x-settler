/-
  Wiring: connect the finite certificate chain to the unconditional
  upper bound `innerCbrt x ≤ icbrt x + 1` for all x < 2^256.

  Strategy:
    - For x < 256: use decide (innerCbrt_upper_of_lt_256)
    - For x ≥ 256: map x to certificate octave, verify seed/interval match,
      apply CbrtCertified.run6_le_m_plus_one
-/
import Init
import CbrtProof.CbrtCorrect
import CbrtProof.FiniteCert
import CbrtProof.CertifiedChain

namespace CbrtWiring

open CbrtCert
open CbrtCertified

-- ============================================================================
-- Octave membership: map x to its certificate octave
-- ============================================================================

/-- For x > 0, Nat.log2 gives the octave index. -/
private theorem log2_octave (x : Nat) (hx : x ≠ 0) :
    2 ^ Nat.log2 x ≤ x ∧ x < 2 ^ (Nat.log2 x + 1) :=
  (Nat.log2_eq_iff hx).1 rfl

/-- The seed depends only on log2(x), so it matches the certificate seed. -/
theorem cbrtSeed_eq_certSeed (i : Fin 248) (x : Nat)
    (hOct : 2 ^ (i.val + certOffset) ≤ x ∧ x < 2 ^ (i.val + certOffset + 1)) :
    cbrtSeed x = seedOf i := by
  have hx : 0 < x := Nat.lt_of_lt_of_le (Nat.two_pow_pos (i.val + certOffset)) hOct.1
  have hx0 : x ≠ 0 := Nat.ne_of_gt hx
  have hlog : Nat.log2 x = i.val + certOffset := (Nat.log2_eq_iff hx0).2 hOct
  unfold cbrtSeed
  simp [Nat.ne_of_gt hx, hlog]
  have hseed := seed_eq i
  simp [seedOf] at hseed ⊢
  rw [hseed]

/-- m = icbrt(x) lies within [loOf i, hiOf i] for x in octave i. -/
theorem m_within_cert_interval
    (i : Fin 248) (x m : Nat)
    (hmlo : m * m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1) * (m + 1))
    (hOct : 2 ^ (i.val + certOffset) ≤ x ∧ x < 2 ^ (i.val + certOffset + 1)) :
    loOf i ≤ m ∧ m ≤ hiOf i := by
  have hloSq : loOf i * loOf i * loOf i ≤ 2 ^ (i.val + certOffset) := lo_cube_le_pow2 i
  have hloSqX : loOf i * loOf i * loOf i ≤ x := Nat.le_trans hloSq hOct.1
  have hlo : loOf i ≤ m := by
    by_cases h : loOf i ≤ m
    · exact h
    · have hlt : m < loOf i := Nat.lt_of_not_ge h
      have hm1 : m + 1 ≤ loOf i := Nat.succ_le_of_lt hlt
      have hm1cube : (m + 1) * (m + 1) * (m + 1) ≤ loOf i * loOf i * loOf i :=
        cube_monotone hm1
      have hm1x : (m + 1) * (m + 1) * (m + 1) ≤ x := Nat.le_trans hm1cube hloSqX
      exact False.elim ((Nat.not_lt_of_ge hm1x) hmhi)
  have hhiSq : 2 ^ (i.val + certOffset + 1) ≤
      (hiOf i + 1) * (hiOf i + 1) * (hiOf i + 1) :=
    pow2_succ_le_hi_succ_cube i
  have hXHi : x < (hiOf i + 1) * (hiOf i + 1) * (hiOf i + 1) :=
    Nat.lt_of_lt_of_le hOct.2 hhiSq
  have hhi : m ≤ hiOf i := by
    by_cases h : m ≤ hiOf i
    · exact h
    · have hlt : hiOf i < m := Nat.lt_of_not_ge h
      have hhi1 : hiOf i + 1 ≤ m := Nat.succ_le_of_lt hlt
      have hhicube : (hiOf i + 1) * (hiOf i + 1) * (hiOf i + 1) ≤ m * m * m :=
        cube_monotone hhi1
      have hXmm : x < m * m * m := Nat.lt_of_lt_of_le hXHi hhicube
      exact False.elim ((Nat.not_lt_of_ge hmlo) hXmm)
  exact ⟨hlo, hhi⟩

-- ============================================================================
-- Certificate-backed upper bound
-- ============================================================================

/-- Certificate-backed upper bound for a single octave.
    If x is in certificate octave i with m = icbrt(x), then innerCbrt x ≤ m + 1. -/
theorem innerCbrt_upper_of_octave
    (i : Fin 248) (x m : Nat)
    (hmlo : m * m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1) * (m + 1))
    (hOct : 2 ^ (i.val + certOffset) ≤ x ∧ x < 2 ^ (i.val + certOffset + 1)) :
    innerCbrt x ≤ m + 1 := by
  have hx : 0 < x := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hOct.1
  have hinterval := m_within_cert_interval i x m hmlo hmhi hOct
  have hm2 : 2 ≤ m := Nat.le_trans (lo_ge_two i) hinterval.1
  have hseed : cbrtSeed x = seedOf i := cbrtSeed_eq_certSeed i x hOct
  -- innerCbrt x = run6From x (cbrtSeed x) = run6From x (seedOf i)
  have hrun : run6From x (seedOf i) ≤ m + 1 :=
    run6_le_m_plus_one i x m hm2 hmlo hmhi hinterval.1 hinterval.2
  -- Connect innerCbrt to run6From
  have hinnerEq : innerCbrt x = run6From x (cbrtSeed x) :=
    innerCbrt_eq_run6From_seed x hx
  calc innerCbrt x = run6From x (cbrtSeed x) := hinnerEq
    _ = run6From x (seedOf i) := by rw [hseed]
    _ ≤ m + 1 := hrun

/-- Universal upper bound on uint256 domain:
    for every x ∈ [1, 2^256-1], innerCbrt x ≤ icbrt x + 1. -/
theorem innerCbrt_upper_u256 (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    innerCbrt x ≤ icbrt x + 1 := by
  by_cases hx_small : x < 256
  · exact innerCbrt_upper_of_lt_256 x hx_small
  · -- x ≥ 256, use the finite certificate
    have hx256_le : 256 ≤ x := Nat.le_of_not_lt hx_small
    -- Map x to octave: log2(x) ∈ [8, 255]
    have hx0 : x ≠ 0 := Nat.ne_of_gt hx
    let n := Nat.log2 x
    have hn_bounds : 8 ≤ n := by
      dsimp [n]
      -- log2(x) ≥ 8 because x ≥ 256 = 2^8
      have hoctave := log2_octave x hx0
      -- log2(x) is the unique k with 2^k ≤ x < 2^(k+1)
      -- Since 2^8 = 256 ≤ x, we need 8 ≤ log2(x)
      -- Proof: if log2(x) < 8, then x < 2^(log2(x)+1) ≤ 2^8 = 256, contradiction
      by_cases h8 : 8 ≤ Nat.log2 x
      · exact h8
      · have hlt : Nat.log2 x + 1 ≤ 8 := by omega
        have hup : x < 2 ^ (Nat.log2 x + 1) := hoctave.2
        have hpow : 2 ^ (Nat.log2 x + 1) ≤ 2 ^ 8 :=
          Nat.pow_le_pow_right (by decide : 1 ≤ 2) hlt
        have : x < 256 := Nat.lt_of_lt_of_le hup (by simpa using hpow)
        omega
    have hn_lt : n < 256 := by
      dsimp [n]
      exact (Nat.log2_lt hx0).2 hx256
    -- Certificate index
    have hcert : certOffset = 8 := rfl
    let idx : Fin 248 := ⟨n - certOffset, by omega⟩
    have hidx_plus : idx.val + certOffset = n := by dsimp [idx]; omega
    -- Octave membership
    have hOct : 2 ^ (idx.val + certOffset) ≤ x ∧ x < 2 ^ (idx.val + certOffset + 1) := by
      rw [hidx_plus]
      exact log2_octave x hx0
    -- Apply the certificate
    let m := icbrt x
    have hmlo : m * m * m ≤ x := icbrt_cube_le x
    have hmhi : x < (m + 1) * (m + 1) * (m + 1) := icbrt_lt_succ_cube x
    exact innerCbrt_upper_of_octave idx x m hmlo hmhi hOct

/-- Universal floor correctness on uint256 domain:
    for every x ∈ [1, 2^256-1], floorCbrt x = icbrt x. -/
theorem floorCbrt_correct_u256 (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    floorCbrt x = icbrt x :=
  floorCbrt_correct_of_upper x hx (innerCbrt_upper_u256 x hx hx256)

/-- Universal floor correctness (including x = 0). -/
theorem floorCbrt_correct_u256_all (x : Nat) (hx256 : x < 2 ^ 256) :
    let r := floorCbrt x
    r * r * r ≤ x ∧ x < (r + 1) * (r + 1) * (r + 1) := by
  by_cases hx0 : x = 0
  · subst hx0; simp [floorCbrt, innerCbrt]
  · have hx : 0 < x := Nat.pos_of_ne_zero hx0
    have heq := floorCbrt_correct_u256 x hx hx256
    rw [heq]
    exact ⟨icbrt_cube_le x, icbrt_lt_succ_cube x⟩

-- ============================================================================
-- Perfect-cube exactness: innerCbrt(m³) = m
-- ============================================================================

/-- On a perfect cube, innerCbrt returns the exact cube root.
    For m < 256: verified computationally (innerCbrt_on_perfect_cube_small).
    For m ≥ 256: the certificate chain gives z₅ ≤ m + d5Of(i), and
    d5Of(i)² < loOf(i) ≤ m (from d5_sq_lt_lo), so
    cbrtStep_eq_on_perfect_cube_of_sq_lt gives z₆ = m. -/
theorem innerCbrt_on_perfect_cube
    (m : Nat) (hm : 0 < m) (hm256 : m * m * m < 2 ^ 256) :
    innerCbrt (m * m * m) = m := by
  by_cases hsmall : m < 256
  · exact innerCbrt_on_perfect_cube_small ⟨m, hsmall⟩
  · -- m ≥ 256
    have hm256_le : 256 ≤ m := Nat.le_of_not_lt hsmall
    -- Lower bound: m ≤ innerCbrt(m³)
    have hx_pos : 0 < m * m * m := Nat.mul_pos (Nat.mul_pos hm hm) hm
    have hlo_inner : m ≤ innerCbrt (m * m * m) :=
      innerCbrt_lower (m * m * m) m hx_pos (Nat.le_refl _)
    -- m³ < (m+1)³ (direct, not via icbrt)
    have hm1_cube : m * m * m < (m + 1) * (m + 1) * (m + 1) := by
      have h1 : m * m * m < m * m * (m + 1) :=
        Nat.mul_lt_mul_of_pos_left (by omega) (Nat.mul_pos hm hm)
      have h2 : m * m ≤ (m + 1) * (m + 1) := Nat.mul_le_mul (Nat.le_succ m) (Nat.le_succ m)
      exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ h2)
    -- icbrt(m³) = m
    have hicbrt : icbrt (m * m * m) = m :=
      (icbrt_eq_of_bounds (m * m * m) m (Nat.le_refl _) hm1_cube).symm
    -- Upper bound: innerCbrt(m³) ≤ m + 1
    have hhi_inner : innerCbrt (m * m * m) ≤ m + 1 := by
      have := innerCbrt_upper_u256 (m * m * m) hx_pos hm256
      rw [hicbrt] at this; exact this
    -- Rule out innerCbrt(m³) = m + 1 via certificate
    by_cases heq : innerCbrt (m * m * m) = m
    · exact heq
    · exfalso
      have heq1 : innerCbrt (m * m * m) = m + 1 := by omega
      -- Map m³ to certificate octave
      let x := m * m * m
      have hx0 : x ≠ 0 := Nat.ne_of_gt hx_pos
      let n := Nat.log2 x
      have hn_bounds : 8 ≤ n := by
        dsimp [n, x]
        have hoctave := log2_octave x hx0
        by_cases h8 : 8 ≤ Nat.log2 x
        · exact h8
        · have hlt : Nat.log2 x + 1 ≤ 8 := by omega
          have hup : x < 2 ^ (Nat.log2 x + 1) := hoctave.2
          have hpow : 2 ^ (Nat.log2 x + 1) ≤ 2 ^ 8 :=
            Nat.pow_le_pow_right (by decide : 1 ≤ 2) hlt
          have : x < 256 := Nat.lt_of_lt_of_le hup (by simpa using hpow)
          -- But m ≥ 256, m³ ≥ 256³ > 256
          have : 256 * 256 * 256 ≤ x :=
            Nat.mul_le_mul (Nat.mul_le_mul hm256_le hm256_le) hm256_le
          omega
      have hn_lt : n < 256 := by
        dsimp [n]
        exact (Nat.log2_lt hx0).2 hm256
      have hcert : certOffset = 8 := rfl
      let idx : Fin 248 := ⟨n - certOffset, by dsimp [n]; omega⟩
      have hidx_plus : idx.val + certOffset = n := by dsimp [idx, n]; omega
      have hOct : 2 ^ (idx.val + certOffset) ≤ x ∧ x < 2 ^ (idx.val + certOffset + 1) := by
        rw [hidx_plus]
        exact log2_octave x hx0
      -- m is in [loOf idx, hiOf idx]
      have hmlo_cube : m * m * m ≤ x := Nat.le_refl _
      have hmhi_cube : x < (m + 1) * (m + 1) * (m + 1) := hm1_cube
      have hinterval := m_within_cert_interval idx x m hmlo_cube hmhi_cube hOct
      have hm2 : 2 ≤ m := Nat.le_trans (by decide : 2 ≤ 256) hm256_le
      -- Use shared 5-step certified bounds
      have hseed : cbrtSeed x = seedOf idx := cbrtSeed_eq_certSeed idx x hOct
      have ⟨hmz5, hd5, h2d5⟩ := run5_certified_bounds idx x m hm2 hmlo_cube hmhi_cube
        hinterval.1 hinterval.2
      let z5 := run5From x (seedOf idx)
      -- innerCbrt(x) = cbrtStep(x, z5) via run5From expansion
      have hinner_run : innerCbrt x = cbrtStep x z5 := by
        rw [innerCbrt_eq_step_run5_seed x hx_pos, hseed]
      -- So cbrtStep(x, z5) = m + 1
      have hz6_eq : cbrtStep x z5 = m + 1 := by rw [← hinner_run]; exact heq1
      -- z₅ = m + e where e ≤ d5, e² < m, 2e ≤ m
      have hd5sq_m : d5Of idx * d5Of idx < m :=
        Nat.lt_of_lt_of_le (d5_sq_lt_lo idx) hinterval.1
      have he_sq : (z5 - m) * (z5 - m) < m :=
        Nat.lt_of_le_of_lt (Nat.mul_le_mul hd5 hd5) hd5sq_m
      have h2e : 2 * (z5 - m) ≤ m :=
        Nat.le_trans (Nat.mul_le_mul_left 2 hd5) h2d5
      -- cbrtStep(m³, z₅) = m via the perfect-cube lemma
      have hz5_eq : z5 = m + (z5 - m) := by omega
      have hz6_m : cbrtStep x z5 = m := by
        show cbrtStep (m * m * m) z5 = m
        rw [hz5_eq]
        exact cbrtStep_eq_on_perfect_cube_of_sq_lt m (z5 - m) hm2 h2e he_sq
      -- Contradiction: cbrtStep(x, z5) = m but also = m + 1
      omega

end CbrtWiring
