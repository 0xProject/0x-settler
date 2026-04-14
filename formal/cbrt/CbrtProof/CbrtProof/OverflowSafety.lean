/-
  Overflow safety proof for cbrtUp.

  Main theorem: `innerCbrt_cube_lt_word`
    For all x < 2^256, innerCbrt(x) * (innerCbrt(x) * innerCbrt(x)) < 2^256.
-/
import Init
import CbrtProof.CbrtCorrect
import CbrtProof.FiniteCert
import CbrtProof.CertifiedChain
import CbrtProof.Wiring

set_option exponentiation.threshold 300

namespace CbrtOverflow

open CbrtCert
open CbrtCertified
open CbrtWiring

-- ============================================================================
-- Constants
-- ============================================================================

private def R_MAX : Nat := 48740834812604276470692694

private def hiD1 : Nat := 5865868362315021153806969
private def hiD2 : Nat := hiD1 * hiD1 / R_MAX + 1
private def hiD3 : Nat := hiD2 * hiD2 / R_MAX + 1
private def hiD4 : Nat := hiD3 * hiD3 / R_MAX + 1
private def hiD5 : Nat := hiD4 * hiD4 / R_MAX + 1

-- ============================================================================
-- Verified constants (kernel-checked via decide, no native_decide)
-- ============================================================================

private theorem r_max_cube_lt_word : R_MAX * R_MAX * R_MAX < 2 ^ 256 := by decide
private theorem r_max_succ_cube_ge_word :
    2 ^ 256 ≤ (R_MAX + 1) * (R_MAX + 1) * (R_MAX + 1) := by decide
set_option maxRecDepth 1000000 in
private theorem hiD1_eq : hiD1 = d1Of ⟨247, by omega⟩ := by decide
private theorem hiD5_sq_lt_rmax : hiD5 * hiD5 < R_MAX := by decide
private theorem two_hiD1_le_rmax : 2 * hiD1 ≤ R_MAX := by decide
private theorem two_hiD2_le_rmax : 2 * hiD2 ≤ R_MAX := by decide
private theorem two_hiD3_le_rmax : 2 * hiD3 ≤ R_MAX := by decide
private theorem two_hiD4_le_rmax : 2 * hiD4 ≤ R_MAX := by decide
private theorem two_hiD5_le_rmax : 2 * hiD5 ≤ R_MAX := by decide
private theorem pow255_le_rmax_cube : 2 ^ 255 ≤ R_MAX * R_MAX * R_MAX := by decide
private theorem fBound_at_zero :
    (R_MAX + 3) * (R_MAX * R_MAX) ≥ 2 ^ 256 := by decide
private theorem fBound_at_hiD5 :
    (R_MAX + 3 - 2 * hiD5) * ((R_MAX + hiD5) * (R_MAX + hiD5)) ≥ 2 ^ 256 := by decide

-- d1 bound for octave 247 matches the analytic formula (decide)
set_option maxRecDepth 1000000 in
private theorem d1_bound_247 :
    (max (seedOf ⟨247, by omega⟩ - loOf ⟨247, by omega⟩) (hiOf ⟨247, by omega⟩ - seedOf ⟨247, by omega⟩) *
      max (seedOf ⟨247, by omega⟩ - loOf ⟨247, by omega⟩) (hiOf ⟨247, by omega⟩ - seedOf ⟨247, by omega⟩) *
      (hiOf ⟨247, by omega⟩ + 2 * seedOf ⟨247, by omega⟩) +
      3 * hiOf ⟨247, by omega⟩ * (hiOf ⟨247, by omega⟩ + 1)) /
    (3 * (seedOf ⟨247, by omega⟩ * seedOf ⟨247, by omega⟩)) = d1Of ⟨247, by omega⟩ := by decide

-- ============================================================================
-- Nat polynomial identity: (b-2)(2b+1) + 3b + 2 = 2b² for b ≥ 2
-- ============================================================================

private theorem poly_ident (b : Nat) (hb : 2 ≤ b) :
    (b - 2) * (2 * b + 1) + (3 * b + 2) = 2 * b * b := by
  generalize hc : b - 2 = c
  have hb_eq : b = c + 2 := by omega
  subst hb_eq
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]
  omega

-- ============================================================================
-- Discrete monotonicity of f(e) = (R+3-2e)(R+e)²
-- ============================================================================

/-- f(e) ≥ f(e+1) for e ≥ 1 with 2e ≤ R+1.
    Proof: (a+2)b² ≥ a(b+1)² where a = R+1-2e, b = R+e.
    Expand: suffices 2b² ≥ a(2b+1). Since a ≤ b-2 and (b-2)(2b+1) ≤ 2b². -/
private theorem fBound_step_le (e : Nat) (he : 1 ≤ e) (h2e : 2 * e ≤ R_MAX + 1) :
    (R_MAX + 3 - 2 * e) * ((R_MAX + e) * (R_MAX + e)) ≥
      (R_MAX + 3 - 2 * (e + 1)) * ((R_MAX + (e + 1)) * (R_MAX + (e + 1))) := by
  -- Let a = R+1-2e, b = R+e (avoid `set` which requires Mathlib)
  -- Rewrite goal in terms of a, b
  have h1 : R_MAX + 3 - 2 * e = (R_MAX + 1 - 2 * e) + 2 := by omega
  have h2 : R_MAX + 3 - 2 * (e + 1) = R_MAX + 1 - 2 * e := by omega
  have h3 : R_MAX + (e + 1) = (R_MAX + e) + 1 := by omega
  rw [h1, h2, h3]
  -- Goal: ((R+1-2e)+2) * ((R+e)*(R+e)) ≥ (R+1-2e) * (((R+e)+1)*((R+e)+1))
  -- Abbreviate: a = R+1-2e, b = R+e
  -- Goal: (a+2)*(b*b) ≥ a*((b+1)*(b+1))
  -- Suffices: 2*b*b ≥ a*(2*b+1).
  suffices hsuff : (R_MAX + 1 - 2 * e) * (2 * (R_MAX + e) + 1) ≤ 2 * (R_MAX + e) * (R_MAX + e) by
    -- (a+2)*b² = a*b² + 2*b²
    have hexp : ((R_MAX + 1 - 2 * e) + 2) * ((R_MAX + e) * (R_MAX + e)) =
        (R_MAX + 1 - 2 * e) * ((R_MAX + e) * (R_MAX + e)) + 2 * ((R_MAX + e) * (R_MAX + e)) := by
      simp only [Nat.add_mul]
    -- a*((b+1)*(b+1)) = a*(b*b) + a*(2*b+1)
    have hexp2 : (R_MAX + 1 - 2 * e) * (((R_MAX + e) + 1) * ((R_MAX + e) + 1)) =
        (R_MAX + 1 - 2 * e) * ((R_MAX + e) * (R_MAX + e)) +
        (R_MAX + 1 - 2 * e) * (2 * (R_MAX + e) + 1) := by
      have : ((R_MAX + e) + 1) * ((R_MAX + e) + 1) =
          (R_MAX + e) * (R_MAX + e) + (2 * (R_MAX + e) + 1) := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.add_assoc]; omega
      rw [this, Nat.mul_add]
    -- Goal: (a+2)*b² ≥ a*(b+1)², i.e., a*(b+1)² ≤ (a+2)*b²
    -- After rewriting both sides: a*b² + a*(2b+1) ≤ a*b² + 2*b²
    show (R_MAX + 1 - 2 * e) * (((R_MAX + e) + 1) * ((R_MAX + e) + 1)) ≤
         ((R_MAX + 1 - 2 * e) + 2) * ((R_MAX + e) * (R_MAX + e))
    rw [hexp, hexp2]
    have hassoc : 2 * (R_MAX + e) * (R_MAX + e) = 2 * ((R_MAX + e) * (R_MAX + e)) := by
      rw [Nat.mul_assoc]
    rw [hassoc] at hsuff
    exact Nat.add_le_add_left hsuff _
  -- Need: a*(2b+1) ≤ 2b².
  -- a ≤ b - 2 (since b - a = R+e - R - 1 + 2e = 3e - 1 ≥ 2)
  have hab : R_MAX + 1 - 2 * e ≤ (R_MAX + e) - 2 := by omega
  have hb2 : 2 ≤ R_MAX + e := by omega
  -- (b-2)*(2b+1) + (3b+2) = 2b² (from poly_ident)
  have hpoly := poly_ident (R_MAX + e) hb2
  -- So (b-2)*(2b+1) ≤ 2b².
  have hbd : ((R_MAX + e) - 2) * (2 * (R_MAX + e) + 1) ≤ 2 * (R_MAX + e) * (R_MAX + e) := by omega
  -- a*(2b+1) ≤ (b-2)*(2b+1) ≤ 2b².
  exact Nat.le_trans (Nat.mul_le_mul_right _ hab) hbd

/-- f is non-increasing on [1, hiD5]: for e in this range, f(e) ≥ f(hiD5). -/
private theorem fBound_ge_endpoint (e : Nat) (he1 : 1 ≤ e) (he2 : e ≤ hiD5) :
    (R_MAX + 3 - 2 * e) * ((R_MAX + e) * (R_MAX + e)) ≥
      (R_MAX + 3 - 2 * hiD5) * ((R_MAX + hiD5) * (R_MAX + hiD5)) := by
  -- Induction on n = hiD5 - e, generalizing e.
  have key : ∀ n, ∀ e', 1 ≤ e' → e' ≤ hiD5 → n = hiD5 - e' →
      (R_MAX + 3 - 2 * e') * ((R_MAX + e') * (R_MAX + e')) ≥
        (R_MAX + 3 - 2 * hiD5) * ((R_MAX + hiD5) * (R_MAX + hiD5)) := by
    intro n
    induction n with
    | zero =>
      intro e' he1' _ hk
      have : e' = hiD5 := by omega
      subst this
      exact Nat.le_refl _
    | succ k ih =>
      intro e' he1' he2' hk
      -- Apply the inductive hypothesis to e' + 1
      have h_ih := ih (e' + 1) (by omega) (by omega) (by omega)
      -- f(e') ≥ f(e'+1) by the step lemma
      have h_step := fBound_step_le e' he1' (by have := two_hiD5_le_rmax; omega)
      -- f(e') ≥ f(e'+1) ≥ f(hiD5)
      exact Nat.le_trans h_ih h_step
  exact key (hiD5 - e) e he1 he2 rfl

/-- For all e ∈ [0, hiD5], f(e) ≥ 2^256. -/
private theorem fBound_ge_word (e : Nat) (he : e ≤ hiD5) :
    (R_MAX + 3 - 2 * e) * ((R_MAX + e) * (R_MAX + e)) ≥ 2 ^ 256 := by
  by_cases he0 : e = 0
  · subst he0; simp; exact fBound_at_zero
  · exact Nat.le_trans fBound_at_hiD5 (fBound_ge_endpoint e (by omega) he)

-- ============================================================================
-- cbrtStep bounded by R_MAX when z is close to R_MAX
-- ============================================================================

/-- If z ∈ [R_MAX, R_MAX + hiD5] and x < 2^256, then cbrtStep x z ≤ R_MAX.
    Proof: x < f(d) = (R+3-2d)(R+d)² gives x/(R+d)² ≤ R+2-2d,
    so x/(R+d)² + 2(R+d) ≤ 3R+2, and step ≤ R. -/
private theorem cbrtStep_le_rmax
    (x z : Nat)
    (hx : x < 2 ^ 256)
    (hmz : R_MAX ≤ z)
    (hze : z ≤ R_MAX + hiD5) :
    cbrtStep x z ≤ R_MAX := by
  unfold cbrtStep
  have hd_def : z - R_MAX ≤ hiD5 := by omega
  have hzd : z = R_MAX + (z - R_MAX) := by omega
  have h2d : 2 * (z - R_MAX) ≤ R_MAX := by have := two_hiD5_le_rmax; omega
  -- f(d) ≥ 2^256 > x
  have hf := fBound_ge_word (z - R_MAX) hd_def
  have hf_gt_x : x < (R_MAX + 3 - 2 * (z - R_MAX)) * ((R_MAX + (z - R_MAX)) * (R_MAX + (z - R_MAX))) :=
    Nat.lt_of_lt_of_le hx (show 2 ^ 256 ≤ _ from hf)
  rw [hzd]
  -- x / (R+d)² < R+3-2d (by Nat.div_lt_iff_lt_mul)
  have hzz_pos : 0 < (R_MAX + (z - R_MAX)) * (R_MAX + (z - R_MAX)) :=
    Nat.mul_pos (by unfold R_MAX; omega) (by unfold R_MAX; omega)
  have hdiv_lt : x / ((R_MAX + (z - R_MAX)) * (R_MAX + (z - R_MAX))) < R_MAX + 3 - 2 * (z - R_MAX) :=
    (Nat.div_lt_iff_lt_mul hzz_pos).mpr hf_gt_x
  -- So x/(R+d)² ≤ R+2-2d
  have hdiv_bound : x / ((R_MAX + (z - R_MAX)) * (R_MAX + (z - R_MAX))) ≤ R_MAX + 2 - 2 * (z - R_MAX) := by omega
  -- sum ≤ R+2-2d + 2(R+d) = 3R+2
  have hsum : x / ((R_MAX + (z - R_MAX)) * (R_MAX + (z - R_MAX))) + 2 * (R_MAX + (z - R_MAX)) ≤ 3 * R_MAX + 2 := by omega
  -- step = sum/3 ≤ (3R+2)/3 = R
  exact Nat.le_trans (Nat.div_le_div_right hsum) (by omega)

-- ============================================================================
-- Tighter 5-step chain
-- ============================================================================

/-- When m = R_MAX, z₅ ∈ [R_MAX, R_MAX + hiD5]. -/
private theorem run5_hi_bound
    (x : Nat) (hx : x < 2 ^ 256) (_hx_pos : 0 < x)
    (hmlo : R_MAX * R_MAX * R_MAX ≤ x)
    (hmhi : x < (R_MAX + 1) * (R_MAX + 1) * (R_MAX + 1)) :
    R_MAX ≤ run5From x (seedOf ⟨247, by omega⟩) ∧
    run5From x (seedOf ⟨247, by omega⟩) ≤ R_MAX + hiD5 := by
  let idx : Fin 248 := ⟨247, by omega⟩
  have hOct : 2 ^ (idx.val + certOffset) ≤ x ∧ x < 2 ^ (idx.val + certOffset + 1) :=
    ⟨Nat.le_trans pow255_le_rmax_cube hmlo, hx⟩
  have hinterval := m_within_cert_interval idx x R_MAX hmlo hmhi hOct
  have hm2 : 2 ≤ R_MAX := by unfold R_MAX; omega
  have hsPos : 0 < seedOf idx := seed_pos idx
  -- Use run5_certified_bounds from CertifiedChain, but with R_MAX-specific d bounds.
  -- We need our own chain because we use R_MAX as the denominator (not loOf idx).
  -- The 5-step chain through run5From is definitionally:
  --   run5From x s = cbrtStep x (cbrtStep x (cbrtStep x (cbrtStep x (cbrtStep x s))))
  -- We prove bounds step by step.
  -- Step 1: floor bound
  have hmz1 : R_MAX ≤ cbrtStep x (seedOf idx) :=
    cbrt_step_floor_bound x (seedOf idx) R_MAX hsPos hmlo
  -- d1 bound from certificate
  have hd1 : cbrtStep x (seedOf idx) - R_MAX ≤ hiD1 := by
    rw [hiD1_eq]
    have h := cbrt_d1_bound x R_MAX (seedOf idx) (loOf idx) (hiOf idx) hsPos hmlo hmhi
      hinterval.1 hinterval.2
    simp only at h
    exact Nat.le_trans h (Nat.le_of_eq d1_bound_247)
  -- Steps 2-5 using step_from_bound with R_MAX as both m and lo
  have hloPos : 0 < R_MAX := by omega
  have hmz2 : R_MAX ≤ cbrtStep x (cbrtStep x (seedOf idx)) :=
    cbrt_step_floor_bound x _ R_MAX (by omega) hmlo
  have hd2 : cbrtStep x (cbrtStep x (seedOf idx)) - R_MAX ≤ hiD2 :=
    step_from_bound x R_MAX R_MAX _ hiD1 hm2 hloPos (Nat.le_refl _) hmhi hmz1 hd1 two_hiD1_le_rmax
  have hmz3 : R_MAX ≤ cbrtStep x (cbrtStep x (cbrtStep x (seedOf idx))) :=
    cbrt_step_floor_bound x _ R_MAX (by omega) hmlo
  have hd3 : cbrtStep x (cbrtStep x (cbrtStep x (seedOf idx))) - R_MAX ≤ hiD3 :=
    step_from_bound x R_MAX R_MAX _ hiD2 hm2 hloPos (Nat.le_refl _) hmhi hmz2 hd2 two_hiD2_le_rmax
  have hmz4 : R_MAX ≤ cbrtStep x (cbrtStep x (cbrtStep x (cbrtStep x (seedOf idx)))) :=
    cbrt_step_floor_bound x _ R_MAX (by omega) hmlo
  have hd4 : cbrtStep x (cbrtStep x (cbrtStep x (cbrtStep x (seedOf idx)))) - R_MAX ≤ hiD4 :=
    step_from_bound x R_MAX R_MAX _ hiD3 hm2 hloPos (Nat.le_refl _) hmhi hmz3 hd3 two_hiD3_le_rmax
  -- z5 = run5From x (seedOf idx)
  have hmz5 : R_MAX ≤ cbrtStep x (cbrtStep x (cbrtStep x (cbrtStep x (cbrtStep x (seedOf idx))))) :=
    cbrt_step_floor_bound x _ R_MAX (by omega) hmlo
  have hd5 : cbrtStep x (cbrtStep x (cbrtStep x (cbrtStep x (cbrtStep x (seedOf idx))))) - R_MAX ≤ hiD5 :=
    step_from_bound x R_MAX R_MAX _ hiD4 hm2 hloPos (Nat.le_refl _) hmhi hmz4 hd4 two_hiD4_le_rmax
  -- run5From x (seedOf idx) is definitionally equal to the 5-step chain
  have hrun5_def : run5From x (seedOf idx) =
      cbrtStep x (cbrtStep x (cbrtStep x (cbrtStep x (cbrtStep x (seedOf idx))))) := rfl
  rw [hrun5_def]
  exact ⟨hmz5, by omega⟩

-- ============================================================================
-- Main theorem
-- ============================================================================

/-- innerCbrt(x)³ < 2^256 for all x < 2^256 with x > 0. -/
theorem innerCbrt_cube_lt_word (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    innerCbrt x * (innerCbrt x * innerCbrt x) < 2 ^ 256 := by
  rw [← Nat.mul_assoc]
  let m := icbrt x
  have hmlo : m * m * m ≤ x := icbrt_cube_le x
  have hmhi : x < (m + 1) * (m + 1) * (m + 1) := icbrt_lt_succ_cube x
  have hbr := innerCbrt_upper_u256 x hx hx256
  rcases innerCbrt_correct_of_upper x hx hbr with heqm | heqm1
  · -- Case z = m: m³ ≤ x < 2^256
    rw [heqm]; exact Nat.lt_of_le_of_lt hmlo hx256
  · -- Case z = m + 1
    rw [heqm1]
    by_cases h_succ_lt : (m + 1) * (m + 1) * (m + 1) < 2 ^ 256
    · exact h_succ_lt
    · -- (m+1)³ ≥ 2^256 implies m = R_MAX. Derive contradiction.
      exfalso
      have h_ge : 2 ^ 256 ≤ (m + 1) * (m + 1) * (m + 1) := Nat.le_of_not_lt h_succ_lt
      -- m ≤ R_MAX (from m³ ≤ x < 2^256 and (R+1)³ ≥ 2^256)
      have hm_le : m ≤ R_MAX := by
        by_cases h : m ≤ R_MAX
        · exact h
        · exfalso
          have hR1m : R_MAX + 1 ≤ m := by omega
          have hcube : (R_MAX + 1) * (R_MAX + 1) * (R_MAX + 1) ≤ m * m * m := cube_monotone hR1m
          have : (R_MAX + 1) * (R_MAX + 1) * (R_MAX + 1) ≤ x := Nat.le_trans hcube hmlo
          have : 2 ^ 256 ≤ x := Nat.le_trans r_max_succ_cube_ge_word this
          omega
      -- m ≥ R_MAX (from (m+1)³ ≥ 2^256 and R_MAX³ < 2^256)
      have hm_ge : R_MAX ≤ m := by
        by_cases h : R_MAX ≤ m
        · exact h
        · exfalso
          have hm1R : m + 1 ≤ R_MAX := by omega
          have hcube : (m + 1) * (m + 1) * (m + 1) ≤ R_MAX * R_MAX * R_MAX := cube_monotone hm1R
          have : (m + 1) * (m + 1) * (m + 1) < 2 ^ 256 :=
            Nat.lt_of_le_of_lt hcube r_max_cube_lt_word
          omega
      have hm_eq : m = R_MAX := Nat.le_antisymm hm_le hm_ge
      -- Rewrite m = R_MAX everywhere
      rw [hm_eq] at hmlo hmhi
      -- z5 is in [R, R + hiD5]
      have ⟨hmz5, hz5⟩ := run5_hi_bound x hx256 hx hmlo hmhi
      -- innerCbrt = cbrtStep(x, z5)
      have hseed : cbrtSeed x = seedOf ⟨247, by omega⟩ :=
        cbrtSeed_eq_certSeed _ x ⟨Nat.le_trans pow255_le_rmax_cube hmlo, hx256⟩
      have hinner_eq : innerCbrt x = cbrtStep x (run5From x (seedOf ⟨247, by omega⟩)) := by
        rw [innerCbrt_eq_step_run5_seed, hseed]
      -- cbrtStep(x, z5) ≤ R_MAX
      have hz6 := cbrtStep_le_rmax x _ hx256 hmz5 hz5
      -- innerCbrt(x) ≤ R_MAX
      have hinner_le : innerCbrt x ≤ R_MAX := hinner_eq ▸ hz6
      -- But innerCbrt(x) = icbrt(x) + 1 and icbrt(x) = R_MAX
      rw [heqm1] at hinner_le
      -- hinner_le : icbrt x + 1 ≤ R_MAX, hm_eq : icbrt x = R_MAX (since m := icbrt x)
      have : icbrt x = R_MAX := hm_eq
      omega

end CbrtOverflow
