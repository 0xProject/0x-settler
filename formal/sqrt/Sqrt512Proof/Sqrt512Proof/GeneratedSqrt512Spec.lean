/-
  Bridge from model_sqrt512_evm to natSqrt: specification layer.

  Part 1 (fully proved): Fixed-seed convergence certificate.
  Part 2: EVM model bridge — model_sqrt512_evm = sqrt512.
  Part 3 (fully proved): Composition — sqrt512 = natSqrt.

  Architecture: model_sqrt512_evm →[evm bridge]→ model_sqrt512 →[norm bridge]→ sqrt512 →[proved]→ natSqrt
-/
import Sqrt512Proof.Sqrt512Correct
import Sqrt512Proof.GeneratedSqrt512Model

namespace Sqrt512Spec

open SqrtCert
open SqrtBridge
open SqrtCertified

-- ============================================================================
-- Section 1: Fixed-seed definitions
-- ============================================================================

/-- The fixed Newton seed used by 512-bit sqrt: floor(sqrt(2^255)).
    Equals hiOf(254) = loOf(255) in the finite certificate tables. -/
def FIXED_SEED : Nat := 240615969168004511545033772477625056927

theorem fixed_seed_pos : 0 < FIXED_SEED := by decide

/-- Run 6 Babylonian steps from the fixed seed. -/
def run6Fixed (x : Nat) : Nat :=
  let z := bstep x FIXED_SEED
  let z := bstep x z
  let z := bstep x z
  let z := bstep x z
  let z := bstep x z
  let z := bstep x z
  z

/-- Floor square root using the fixed seed: 6 Newton steps + correction. -/
def floorSqrt_fixed (x : Nat) : Nat :=
  let z := run6Fixed x
  if z = 0 then 0 else if x / z < z then z - 1 else z

-- ============================================================================
-- Section 2: Certificate for octave 254 (x ∈ [2^254, 2^255))
-- ============================================================================

private def lo254 : Nat := loOf ⟨254, by omega⟩
private def hi254 : Nat := hiOf ⟨254, by omega⟩
private def maxAbs254 : Nat := max (FIXED_SEED - lo254) (hi254 - FIXED_SEED)
private def fd1_254 : Nat := (maxAbs254 * maxAbs254 + 2 * hi254) / (2 * FIXED_SEED)
private def fd2_254 : Nat := nextD lo254 fd1_254
private def fd3_254 : Nat := nextD lo254 fd2_254
private def fd4_254 : Nat := nextD lo254 fd3_254
private def fd5_254 : Nat := nextD lo254 fd4_254
private def fd6_254 : Nat := nextD lo254 fd5_254

private theorem fd6_254_le_one : fd6_254 ≤ 1 := by native_decide
private theorem fd1_254_le_lo : fd1_254 ≤ lo254 := by native_decide
private theorem fd2_254_le_lo : fd2_254 ≤ lo254 := by native_decide
private theorem fd3_254_le_lo : fd3_254 ≤ lo254 := by native_decide
private theorem fd4_254_le_lo : fd4_254 ≤ lo254 := by native_decide
private theorem fd5_254_le_lo : fd5_254 ≤ lo254 := by native_decide
private theorem lo254_pos : 0 < lo254 := lo_pos ⟨254, by omega⟩

private theorem run6Fixed_error_254
    (x m : Nat) (hm : 0 < m) (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1)) (hlo : lo254 ≤ m) (hhi : m ≤ hi254) :
    run6Fixed x - m ≤ fd6_254 := by
  let z1 := bstep x FIXED_SEED; let z2 := bstep x z1; let z3 := bstep x z2
  let z4 := bstep x z3; let z5 := bstep x z4; let z6 := bstep x z5
  have hmz1 : m ≤ z1 := babylon_step_floor_bound x FIXED_SEED m fixed_seed_pos hmlo
  have hz1P : 0 < z1 := Nat.lt_of_lt_of_le hm hmz1
  have hmz2 : m ≤ z2 := babylon_step_floor_bound x z1 m hz1P hmlo
  have hz2P : 0 < z2 := Nat.lt_of_lt_of_le hm hmz2
  have hmz3 : m ≤ z3 := babylon_step_floor_bound x z2 m hz2P hmlo
  have hz3P : 0 < z3 := Nat.lt_of_lt_of_le hm hmz3
  have hmz4 : m ≤ z4 := babylon_step_floor_bound x z3 m hz3P hmlo
  have hz4P : 0 < z4 := Nat.lt_of_lt_of_le hm hmz4
  have hmz5 : m ≤ z5 := babylon_step_floor_bound x z4 m hz4P hmlo
  have hd1 : z1 - m ≤ fd1_254 := by
    simpa [z1, fd1_254, maxAbs254] using
      d1_bound x m FIXED_SEED lo254 hi254 fixed_seed_pos hmlo hmhi hlo hhi
  have hd1m : fd1_254 ≤ m := Nat.le_trans fd1_254_le_lo hlo
  have hd2 : z2 - m ≤ fd2_254 := by
    simpa [z2, fd2_254] using step_from_bound x m lo254 z1 fd1_254 hm lo254_pos hlo hmhi hmz1 hd1 hd1m
  have hd2m : fd2_254 ≤ m := Nat.le_trans fd2_254_le_lo hlo
  have hd3 : z3 - m ≤ fd3_254 := by
    simpa [z3, fd3_254] using step_from_bound x m lo254 z2 fd2_254 hm lo254_pos hlo hmhi hmz2 hd2 hd2m
  have hd3m : fd3_254 ≤ m := Nat.le_trans fd3_254_le_lo hlo
  have hd4 : z4 - m ≤ fd4_254 := by
    simpa [z4, fd4_254] using step_from_bound x m lo254 z3 fd3_254 hm lo254_pos hlo hmhi hmz3 hd3 hd3m
  have hd4m : fd4_254 ≤ m := Nat.le_trans fd4_254_le_lo hlo
  have hd5 : z5 - m ≤ fd5_254 := by
    simpa [z5, fd5_254] using step_from_bound x m lo254 z4 fd4_254 hm lo254_pos hlo hmhi hmz4 hd4 hd4m
  have hd5m : fd5_254 ≤ m := Nat.le_trans fd5_254_le_lo hlo
  have hd6 : z6 - m ≤ fd6_254 := by
    simpa [z6, fd6_254] using step_from_bound x m lo254 z5 fd5_254 hm lo254_pos hlo hmhi hmz5 hd5 hd5m
  simpa [run6Fixed, z1, z2, z3, z4, z5, z6] using hd6

-- ============================================================================
-- Section 3: Certificate for octave 255 (x ∈ [2^255, 2^256))
-- ============================================================================

private def lo255 : Nat := loOf ⟨255, by omega⟩
private def hi255 : Nat := hiOf ⟨255, by omega⟩
private def maxAbs255 : Nat := max (FIXED_SEED - lo255) (hi255 - FIXED_SEED)
private def fd1_255 : Nat := (maxAbs255 * maxAbs255 + 2 * hi255) / (2 * FIXED_SEED)
private def fd2_255 : Nat := nextD lo255 fd1_255
private def fd3_255 : Nat := nextD lo255 fd2_255
private def fd4_255 : Nat := nextD lo255 fd3_255
private def fd5_255 : Nat := nextD lo255 fd4_255
private def fd6_255 : Nat := nextD lo255 fd5_255

private theorem fd6_255_le_one : fd6_255 ≤ 1 := by native_decide
private theorem fd1_255_le_lo : fd1_255 ≤ lo255 := by native_decide
private theorem fd2_255_le_lo : fd2_255 ≤ lo255 := by native_decide
private theorem fd3_255_le_lo : fd3_255 ≤ lo255 := by native_decide
private theorem fd4_255_le_lo : fd4_255 ≤ lo255 := by native_decide
private theorem fd5_255_le_lo : fd5_255 ≤ lo255 := by native_decide
private theorem lo255_pos : 0 < lo255 := lo_pos ⟨255, by omega⟩

private theorem run6Fixed_error_255
    (x m : Nat) (hm : 0 < m) (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1)) (hlo : lo255 ≤ m) (hhi : m ≤ hi255) :
    run6Fixed x - m ≤ fd6_255 := by
  let z1 := bstep x FIXED_SEED; let z2 := bstep x z1; let z3 := bstep x z2
  let z4 := bstep x z3; let z5 := bstep x z4; let z6 := bstep x z5
  have hmz1 : m ≤ z1 := babylon_step_floor_bound x FIXED_SEED m fixed_seed_pos hmlo
  have hz1P : 0 < z1 := Nat.lt_of_lt_of_le hm hmz1
  have hmz2 : m ≤ z2 := babylon_step_floor_bound x z1 m hz1P hmlo
  have hz2P : 0 < z2 := Nat.lt_of_lt_of_le hm hmz2
  have hmz3 : m ≤ z3 := babylon_step_floor_bound x z2 m hz2P hmlo
  have hz3P : 0 < z3 := Nat.lt_of_lt_of_le hm hmz3
  have hmz4 : m ≤ z4 := babylon_step_floor_bound x z3 m hz3P hmlo
  have hz4P : 0 < z4 := Nat.lt_of_lt_of_le hm hmz4
  have hmz5 : m ≤ z5 := babylon_step_floor_bound x z4 m hz4P hmlo
  have hd1 : z1 - m ≤ fd1_255 := by
    simpa [z1, fd1_255, maxAbs255] using
      d1_bound x m FIXED_SEED lo255 hi255 fixed_seed_pos hmlo hmhi hlo hhi
  have hd1m : fd1_255 ≤ m := Nat.le_trans fd1_255_le_lo hlo
  have hd2 : z2 - m ≤ fd2_255 := by
    simpa [z2, fd2_255] using step_from_bound x m lo255 z1 fd1_255 hm lo255_pos hlo hmhi hmz1 hd1 hd1m
  have hd2m : fd2_255 ≤ m := Nat.le_trans fd2_255_le_lo hlo
  have hd3 : z3 - m ≤ fd3_255 := by
    simpa [z3, fd3_255] using step_from_bound x m lo255 z2 fd2_255 hm lo255_pos hlo hmhi hmz2 hd2 hd2m
  have hd3m : fd3_255 ≤ m := Nat.le_trans fd3_255_le_lo hlo
  have hd4 : z4 - m ≤ fd4_255 := by
    simpa [z4, fd4_255] using step_from_bound x m lo255 z3 fd3_255 hm lo255_pos hlo hmhi hmz3 hd3 hd3m
  have hd4m : fd4_255 ≤ m := Nat.le_trans fd4_255_le_lo hlo
  have hd5 : z5 - m ≤ fd5_255 := by
    simpa [z5, fd5_255] using step_from_bound x m lo255 z4 fd4_255 hm lo255_pos hlo hmhi hmz4 hd4 hd4m
  have hd5m : fd5_255 ≤ m := Nat.le_trans fd5_255_le_lo hlo
  have hd6 : z6 - m ≤ fd6_255 := by
    simpa [z6, fd6_255] using step_from_bound x m lo255 z5 fd5_255 hm lo255_pos hlo hmhi hmz5 hd5 hd5m
  simpa [run6Fixed, z1, z2, z3, z4, z5, z6] using hd6

-- ============================================================================
-- Section 4: Combined fixed-seed bracket + floor correction
-- ============================================================================

private theorem m_le_run6Fixed (x m : Nat) (hx : 0 < x) (hmlo : m * m ≤ x) :
    m ≤ run6Fixed x := by
  let z1 := bstep x FIXED_SEED; let z2 := bstep x z1; let z3 := bstep x z2
  let z4 := bstep x z3; let z5 := bstep x z4; let z6 := bstep x z5
  have hz1 : 0 < z1 := bstep_pos x FIXED_SEED hx fixed_seed_pos
  have hz2 : 0 < z2 := bstep_pos x z1 hx hz1
  have hz3 : 0 < z3 := bstep_pos x z2 hx hz2
  have hz4 : 0 < z4 := bstep_pos x z3 hx hz3
  have hz5 : 0 < z5 := bstep_pos x z4 hx hz4
  simpa [run6Fixed, z1, z2, z3, z4, z5, z6] using
    babylon_step_floor_bound x z5 m hz5 hmlo

theorem fixed_seed_bracket (x : Nat) (hlo : 2 ^ 254 ≤ x) (hhi : x < 2 ^ 256) :
    natSqrt x ≤ run6Fixed x ∧ run6Fixed x ≤ natSqrt x + 1 := by
  have hmlo := natSqrt_sq_le x
  have hmhi := natSqrt_lt_succ_sq x
  have hm : 0 < natSqrt x := by
    suffices natSqrt x ≠ 0 by omega
    intro h0; have := natSqrt_lt_succ_sq x; rw [h0] at this; omega
  constructor
  · exact m_le_run6Fixed x (natSqrt x) (by omega) hmlo
  · suffices run6Fixed x - natSqrt x ≤ 1 by omega
    by_cases hlt : x < 2 ^ 255
    · have hOct : 2 ^ (254 : Fin 256).val ≤ x ∧ x < 2 ^ ((254 : Fin 256).val + 1) := ⟨hlo, hlt⟩
      have hint := m_within_cert_interval ⟨254, by omega⟩ x (natSqrt x) hmlo hmhi hOct
      exact Nat.le_trans (run6Fixed_error_254 x (natSqrt x) hm hmlo hmhi hint.1 hint.2) fd6_254_le_one
    · have h255 : 2 ^ 255 ≤ x := Nat.le_of_not_lt hlt
      have hOct : 2 ^ (⟨255, by omega⟩ : Fin 256).val ≤ x ∧
          x < 2 ^ ((⟨255, by omega⟩ : Fin 256).val + 1) := ⟨h255, hhi⟩
      have hint := m_within_cert_interval ⟨255, by omega⟩ x (natSqrt x) hmlo hmhi hOct
      exact Nat.le_trans (run6Fixed_error_255 x (natSqrt x) hm hmlo hmhi hint.1 hint.2) fd6_255_le_one

theorem floorSqrt_fixed_eq_natSqrt (x : Nat) (hlo : 2 ^ 254 ≤ x) (hhi : x < 2 ^ 256) :
    floorSqrt_fixed x = natSqrt x := by
  have hbr := fixed_seed_bracket x hlo hhi
  have hz_pos : 0 < run6Fixed x := by
    have hm_pos : 0 < natSqrt x := by
      suffices natSqrt x ≠ 0 by omega
      intro h0; have := natSqrt_lt_succ_sq x; rw [h0] at this; omega
    exact Nat.lt_of_lt_of_le hm_pos hbr.1
  have hcorr := correction_correct x (run6Fixed x) hbr.1 hbr.2
  have h1 : floorSqrt_fixed x =
      (if x / run6Fixed x < run6Fixed x then run6Fixed x - 1 else run6Fixed x) := by
    unfold floorSqrt_fixed; dsimp only []; exact if_neg (Nat.ne_of_gt hz_pos)
  rw [h1]
  simp only [show (x / run6Fixed x < run6Fixed x) = (x < run6Fixed x * run6Fixed x) from
    propext (Nat.div_lt_iff_lt_mul hz_pos)]
  exact hcorr

-- ============================================================================
-- Section 5: Norm model helpers
-- ============================================================================

open Sqrt512GeneratedModel in
/-- normAdd (now unbounded) is just addition. -/
private theorem normAdd_eq (a b : Nat) : normAdd a b = a + b := rfl

open Sqrt512GeneratedModel in
/-- normShr is division by power of 2. -/
private theorem normShr_eq (s v : Nat) : normShr s v = v / 2 ^ s := rfl

open Sqrt512GeneratedModel in
/-- normDiv is Nat division. -/
private theorem normDiv_eq (a b : Nat) : normDiv a b = a / b := rfl

open Sqrt512GeneratedModel in
/-- normMod is Nat modulo. -/
private theorem normMod_eq (a b : Nat) : normMod a b = a % b := rfl

open Sqrt512GeneratedModel in
/-- normSub is Nat subtraction. -/
private theorem normSub_eq (a b : Nat) : normSub a b = a - b := rfl

open Sqrt512GeneratedModel in
/-- normMul is Nat multiplication. -/
private theorem normMul_eq (a b : Nat) : normMul a b = a * b := rfl

open Sqrt512GeneratedModel in
/-- normNot 0 = 2^256 - 1. -/
private theorem normNot_zero : normNot 0 = WORD_MOD - 1 := rfl

open Sqrt512GeneratedModel in
/-- normClz for positive x < 2^256 gives 255 - log2 x. -/
private theorem normClz_pos (x : Nat) (hx : 0 < x) :
    normClz x = 255 - Nat.log2 x := by
  unfold normClz; simp [Nat.ne_of_gt hx]

open Sqrt512GeneratedModel in
/-- normLt is a 0/1 indicator. -/
private theorem normLt_eq (a b : Nat) : normLt a b = if a < b then 1 else 0 := rfl

open Sqrt512GeneratedModel in
/-- One Babylonian step in the norm model equals bstep. -/
private theorem normStep_eq_bstep (x z : Nat) :
    normShr 1 (normAdd z (normDiv x z)) = bstep x z := by
  simp [normShr_eq, normAdd_eq, normDiv_eq, bstep]

open Sqrt512GeneratedModel in
/-- Floor correction: sub z (lt (div x z) z) gives the standard correction. -/
private theorem normFloor_correction (x z : Nat) (hz : 0 < z) :
    normSub z (normLt (normDiv x z) z) =
      (if x / z < z then z - 1 else z) := by
  simp only [normSub_eq, normLt_eq, normDiv_eq]
  split <;> omega

-- ============================================================================
-- Section 6: Norm model → sqrt512 bridge
-- ============================================================================

-- The bridge proves: model_sqrt512 x_hi x_lo = sqrt512 (x_hi * 2^256 + x_lo)
-- for 0 < x_hi < 2^256 and x_lo < 2^256.
--
-- Key correspondence:
--   let x := x_hi * 2^256 + x_lo
--   let k := (255 - Nat.log2 x_hi) / 2          -- half-shift
--   let x' := x * 4^k                            -- normalized 512-bit value
--   model_sqrt512 computes karatsubaFloor(x'/2^256, x'%2^256) / 2^k
--   which equals natSqrt(x) by karatsubaFloor_eq_natSqrt and natSqrt_shift_div.

open Sqrt512GeneratedModel in
/-- The 6 Babylonian steps in the norm model on x_hi_1 equal run6Fixed x_hi_1.
    Since normAdd is unbounded, normShr 1 (normAdd z (normDiv x z)) = bstep x z. -/
private theorem norm_6steps_eq_run6Fixed (x_hi_1 : Nat) :
    let r_hi_1 := FIXED_SEED
    let r_hi_2 := normShr 1 (normAdd r_hi_1 (normDiv x_hi_1 r_hi_1))
    let r_hi_3 := normShr 1 (normAdd r_hi_2 (normDiv x_hi_1 r_hi_2))
    let r_hi_4 := normShr 1 (normAdd r_hi_3 (normDiv x_hi_1 r_hi_3))
    let r_hi_5 := normShr 1 (normAdd r_hi_4 (normDiv x_hi_1 r_hi_4))
    let r_hi_6 := normShr 1 (normAdd r_hi_5 (normDiv x_hi_1 r_hi_5))
    let r_hi_7 := normShr 1 (normAdd r_hi_6 (normDiv x_hi_1 r_hi_6))
    r_hi_7 = run6Fixed x_hi_1 := by
  simp only [normStep_eq_bstep, run6Fixed, FIXED_SEED, bstep]

open Sqrt512GeneratedModel in
/-- The 6 steps + floor correction in the norm model = floorSqrt_fixed. -/
private theorem norm_inner_sqrt_eq_floorSqrt_fixed (x_hi_1 : Nat) (hx : 0 < x_hi_1) :
    let r_hi_1 := FIXED_SEED
    let r_hi_2 := normShr 1 (normAdd r_hi_1 (normDiv x_hi_1 r_hi_1))
    let r_hi_3 := normShr 1 (normAdd r_hi_2 (normDiv x_hi_1 r_hi_2))
    let r_hi_4 := normShr 1 (normAdd r_hi_3 (normDiv x_hi_1 r_hi_3))
    let r_hi_5 := normShr 1 (normAdd r_hi_4 (normDiv x_hi_1 r_hi_4))
    let r_hi_6 := normShr 1 (normAdd r_hi_5 (normDiv x_hi_1 r_hi_5))
    let r_hi_7 := normShr 1 (normAdd r_hi_6 (normDiv x_hi_1 r_hi_6))
    let r_hi_8 := normSub r_hi_7 (normLt (normDiv x_hi_1 r_hi_7) r_hi_7)
    r_hi_8 = floorSqrt_fixed x_hi_1 := by
  simp only
  have h7 := norm_6steps_eq_run6Fixed x_hi_1
  simp only at h7
  -- r_hi_7 = run6Fixed x_hi_1
  -- r_hi_8 = normSub r_hi_7 (normLt (normDiv x_hi_1 r_hi_7) r_hi_7)
  -- We need: r_hi_8 = floorSqrt_fixed x_hi_1
  -- floorSqrt_fixed x = if run6Fixed x = 0 then 0 else if x / run6Fixed x < run6Fixed x then run6Fixed x - 1 else run6Fixed x
  have hz_pos : 0 < run6Fixed x_hi_1 := by
    have hseed_pos : 0 < FIXED_SEED := fixed_seed_pos
    have hz1_pos := bstep_pos x_hi_1 FIXED_SEED hx hseed_pos
    have hz2_pos := bstep_pos x_hi_1 _ hx hz1_pos
    have hz3_pos := bstep_pos x_hi_1 _ hx hz2_pos
    have hz4_pos := bstep_pos x_hi_1 _ hx hz3_pos
    have hz5_pos := bstep_pos x_hi_1 _ hx hz4_pos
    have hz6_pos := bstep_pos x_hi_1 _ hx hz5_pos
    exact hz6_pos
  rw [h7, normFloor_correction x_hi_1 (run6Fixed x_hi_1) hz_pos]
  unfold floorSqrt_fixed
  simp [Nat.ne_of_gt hz_pos]

open Sqrt512GeneratedModel in
/-- The norm inner sqrt gives natSqrt on normalized inputs. -/
private theorem norm_inner_sqrt_eq_natSqrt (x_hi_1 : Nat)
    (hlo : 2 ^ 254 ≤ x_hi_1) (hhi : x_hi_1 < 2 ^ 256) :
    let r_hi_1 := FIXED_SEED
    let r_hi_2 := normShr 1 (normAdd r_hi_1 (normDiv x_hi_1 r_hi_1))
    let r_hi_3 := normShr 1 (normAdd r_hi_2 (normDiv x_hi_1 r_hi_2))
    let r_hi_4 := normShr 1 (normAdd r_hi_3 (normDiv x_hi_1 r_hi_3))
    let r_hi_5 := normShr 1 (normAdd r_hi_4 (normDiv x_hi_1 r_hi_4))
    let r_hi_6 := normShr 1 (normAdd r_hi_5 (normDiv x_hi_1 r_hi_5))
    let r_hi_7 := normShr 1 (normAdd r_hi_6 (normDiv x_hi_1 r_hi_6))
    let r_hi_8 := normSub r_hi_7 (normLt (normDiv x_hi_1 r_hi_7) r_hi_7)
    r_hi_8 = natSqrt x_hi_1 := by
  have hpos : 0 < x_hi_1 := by omega
  have h := norm_inner_sqrt_eq_floorSqrt_fixed x_hi_1 hpos
  simp only at h ⊢
  rw [h]
  exact floorSqrt_fixed_eq_natSqrt x_hi_1 hlo hhi

/-- The full Karatsuba computation in the norm model:
    normalization → inner sqrt → Karatsuba quotient → correction → un-normalization.
    This bridges the generated norm model to the algebraic sqrt512 definition. -/
private theorem model_sqrt512_norm_eq_sqrt512 (x_hi x_lo : Nat)
    (hxhi_pos : 0 < x_hi) (hxhi_lt : x_hi < 2 ^ 256) (hxlo_lt : x_lo < 2 ^ 256) :
    Sqrt512GeneratedModel.model_sqrt512 x_hi x_lo =
      sqrt512 (x_hi * 2 ^ 256 + x_lo) := by
  sorry

-- ============================================================================
-- Section 7: EVM model → norm model bridge
-- ============================================================================

-- The EVM model uses u256-wrapped operations. The norm model uses unbounded
-- Nat addition but truncating SHL. We show the final outputs match.
--
-- Key insight: all intermediate values except potentially the combine step
-- (r_hi_8 * 2^128 + r_lo) stay within [0, 2^256). At the combine step,
-- the value can be exactly 2^256, in which case:
--   EVM: wraps to 0, then evmSub(0, 1) = 2^256 - 1  (correct)
--   Norm: stays at 2^256, then normSub(2^256, 1) = 2^256 - 1  (correct)
-- So the final outputs agree.

section EvmNormBridge
open Sqrt512GeneratedModel

private theorem u256_id' (x : Nat) (hx : x < WORD_MOD) : u256 x = x :=
  Nat.mod_eq_of_lt hx

private theorem evmSub_eq_of_le (a b : Nat) (ha : a < WORD_MOD) (hb : b ≤ a) :
    evmSub a b = normSub a b := by
  have hb' : b < WORD_MOD := Nat.lt_of_le_of_lt hb ha
  have hab' : a - b < WORD_MOD := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
  unfold evmSub normSub u256
  simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb']
  have hsplit : a + WORD_MOD - b = WORD_MOD + (a - b) := by omega
  rw [hsplit, Nat.add_mod, Nat.mod_eq_zero_of_dvd (Nat.dvd_refl WORD_MOD), Nat.zero_add,
      Nat.mod_mod_of_dvd, Nat.mod_eq_of_lt hab']
  exact Nat.dvd_refl WORD_MOD

private theorem evmDiv_eq (a b : Nat) (ha : a < WORD_MOD) (hb : 0 < b) (hb' : b < WORD_MOD) :
    evmDiv a b = normDiv a b := by
  unfold evmDiv normDiv
  simp only [u256_id' a ha, u256_id' b hb']
  simp [Nat.ne_of_gt hb]

private theorem evmMod_eq (a b : Nat) (ha : a < WORD_MOD) (hb : 0 < b) (hb' : b < WORD_MOD) :
    evmMod a b = normMod a b := by
  unfold evmMod normMod
  simp only [u256_id' a ha, u256_id' b hb']
  simp [Nat.ne_of_gt hb]

private theorem evmNot_eq (a : Nat) (ha : a < WORD_MOD) :
    evmNot a = normNot a := by
  unfold evmNot normNot; simp [u256_id' a ha]

private theorem evmOr_eq (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmOr a b = normOr a b := by
  unfold evmOr normOr; simp [u256_id' a ha, u256_id' b hb]

private theorem evmAnd_eq (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmAnd a b = normAnd a b := by
  unfold evmAnd normAnd; simp [u256_id' a ha, u256_id' b hb]

private theorem evmEq_eq (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmEq a b = normEq a b := by
  unfold evmEq normEq; simp [u256_id' a ha, u256_id' b hb]

private theorem evmClz_eq (v : Nat) (hv : v < WORD_MOD) :
    evmClz v = normClz v := by
  unfold evmClz normClz; simp [u256_id' v hv]

private theorem evmLt_eq (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmLt a b = normLt a b := by
  unfold evmLt normLt; simp [u256_id' a ha, u256_id' b hb]

private theorem evmShr_eq_of_small (s v : Nat) (hs : s < 256) (hv : v < WORD_MOD) :
    evmShr s v = normShr s v := by
  have hs' : s < WORD_MOD := by unfold WORD_MOD; omega
  unfold evmShr normShr; simp [u256_id' s hs', u256_id' v hv, hs]

private theorem evmShl_eq_normShl (s v : Nat) (hs : s < 256) (hv : v < WORD_MOD)
    (hvs : v * 2 ^ s < WORD_MOD) :
    evmShl s v = normShl s v := by
  have hs' : s < WORD_MOD := by unfold WORD_MOD; omega
  unfold evmShl normShl u256
  simp [Nat.mod_eq_of_lt hs', Nat.mod_eq_of_lt hv, hs, Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt hvs]

/-- evmAdd on inputs whose sum < WORD_MOD equals normAdd (unbounded). -/
private theorem evmAdd_eq_of_bounded (a b : Nat)
    (ha : a < WORD_MOD) (hb : b < WORD_MOD) (hab : a + b < WORD_MOD) :
    evmAdd a b = normAdd a b := by
  unfold evmAdd normAdd u256
  simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hab]

/-- When a + b < WORD_MOD, evmSub (evmAdd a b) f = normSub (normAdd a b) f. -/
private theorem evmSub_evmAdd_eq_of_no_overflow (a b f : Nat)
    (ha : a < WORD_MOD) (hb : b < WORD_MOD)
    (hab : a + b < WORD_MOD) (hf : f < WORD_MOD) (habf : f ≤ a + b) :
    evmSub (evmAdd a b) f = normSub (normAdd a b) f := by
  unfold evmAdd evmSub normAdd normSub u256
  simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hab, Nat.mod_eq_of_lt hf]
  have hlt2 : a + b - f < WORD_MOD := by omega
  rw [show a + b + WORD_MOD - f = WORD_MOD + (a + b - f) from by omega]
  rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hlt2]

/-- When a + b = WORD_MOD and f = 1, the EVM overflow+underflow cancels:
    evmSub (evmAdd a b) 1 = WORD_MOD - 1 = normSub (a + b) 1. -/
private theorem evmSub_evmAdd_eq_of_overflow (a b : Nat)
    (ha : a < WORD_MOD) (hb : b < WORD_MOD)
    (hab : a + b = WORD_MOD) :
    evmSub (evmAdd a b) 1 = normSub (normAdd a b) 1 := by
  unfold evmAdd evmSub normAdd normSub u256
  simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hab, Nat.mod_self]
  have h1 : (1 : Nat) < WORD_MOD := by unfold WORD_MOD; omega
  simp [Nat.mod_eq_of_lt h1]

end EvmNormBridge

open Sqrt512GeneratedModel in
private theorem model_sqrt512_evm_eq_norm (x_hi x_lo : Nat)
    (hxhi_lt : x_hi < 2 ^ 256) (hxlo_lt : x_lo < 2 ^ 256) :
    Sqrt512GeneratedModel.model_sqrt512_evm x_hi x_lo =
      Sqrt512GeneratedModel.model_sqrt512 x_hi x_lo := by
  sorry

-- ============================================================================
-- Section 8: Main theorems
-- ============================================================================

/-- The EVM model computes the same as the algebraic sqrt512. -/
private theorem model_sqrt512_evm_eq_sqrt512 (x_hi x_lo : Nat)
    (hxhi_pos : 0 < x_hi) (hxhi_lt : x_hi < 2 ^ 256)
    (hxlo_lt : x_lo < 2 ^ 256) :
    Sqrt512GeneratedModel.model_sqrt512_evm x_hi x_lo =
      sqrt512 (x_hi * 2 ^ 256 + x_lo) := by
  rw [model_sqrt512_evm_eq_norm x_hi x_lo hxhi_lt hxlo_lt]
  exact model_sqrt512_norm_eq_sqrt512 x_hi x_lo hxhi_pos hxhi_lt hxlo_lt

set_option exponentiation.threshold 512 in
/-- The EVM model of 512-bit sqrt computes natSqrt. -/
theorem model_sqrt512_evm_correct (x_hi x_lo : Nat)
    (hxhi_pos : 0 < x_hi) (hxhi_lt : x_hi < 2 ^ 256)
    (hxlo_lt : x_lo < 2 ^ 256) :
    Sqrt512GeneratedModel.model_sqrt512_evm x_hi x_lo =
      natSqrt (x_hi * 2 ^ 256 + x_lo) := by
  rw [model_sqrt512_evm_eq_sqrt512 x_hi x_lo hxhi_pos hxhi_lt hxlo_lt]
  have hx_lt : x_hi * 2 ^ 256 + x_lo < 2 ^ 512 := by
    calc x_hi * 2 ^ 256 + x_lo
        < 2 ^ 256 * 2 ^ 256 := by
          have := Nat.mul_lt_mul_of_pos_right hxhi_lt (Nat.two_pow_pos 256)
          omega
      _ = 2 ^ 512 := by rw [← Nat.pow_add]
  exact sqrt512_correct (x_hi * 2 ^ 256 + x_lo) hx_lt

end Sqrt512Spec
