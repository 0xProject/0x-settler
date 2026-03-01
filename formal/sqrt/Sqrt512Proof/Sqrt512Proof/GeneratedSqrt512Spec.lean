/-
  Bridge from model_sqrt512_evm to natSqrt: specification layer.

  Part 1 (fully proved): Fixed-seed convergence certificate.
  Part 2: EVM model bridge — model_sqrt512_evm = sqrt512.
  Part 3 (fully proved): Composition — sqrt512 = natSqrt.

  Architecture: model_sqrt512_evm →[direct EVM bridge]→ sqrt512 →[proved]→ natSqrt

  Note: The auto-generated norm model (model_sqrt512) uses unbounded Nat operations
  (normShl, normMul) which do NOT match EVM uint256 semantics. Therefore we prove the
  EVM model correct directly, without factoring through the norm model.
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
-- Section 5: EVM operation simplification helpers
-- ============================================================================

open Sqrt512GeneratedModel in
/-- normAdd (unbounded) is just addition. -/
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
/-- The generated model_bstep equals bstep (definitional). -/
theorem model_bstep_eq_bstep (x z : Nat) : model_bstep x z = bstep x z := by
  simp [model_bstep, normShr_eq, normAdd_eq, normDiv_eq, bstep]

open Sqrt512GeneratedModel in
/-- Floor correction: sub z (lt (div x z) z) gives the standard correction. -/
private theorem normFloor_correction (x z : Nat) (hz : 0 < z) :
    normSub z (normLt (normDiv x z) z) =
      (if x / z < z then z - 1 else z) := by
  simp only [normSub_eq, normLt_eq, normDiv_eq]
  split <;> omega

-- ============================================================================
-- Section 5b: Constant-folding and bitwise helpers
-- ============================================================================

/-- For n < 256, n &&& 254 clears bit 0, giving 2*(n/2). -/
private theorem and_254_eq : ∀ n : Fin 256, (n.val &&& 254) = 2 * (n.val / 2) := by
  native_decide

private theorem normAnd_shift_254 (n : Nat) (hn : n < 256) :
    n &&& 254 = 2 * (n / 2) :=
  and_254_eq ⟨n, hn⟩

private theorem and_1_255 : (1 : Nat) &&& (255 : Nat) = 1 := by native_decide
private theorem and_128_255 : (128 : Nat) &&& (255 : Nat) = 128 := by native_decide

/-- Bitwise OR equals addition when bits don't overlap.
    Uses Nat.shiftLeft_add_eq_or_of_lt from Init. -/
private theorem or_eq_add_shl (a b s : Nat) (hb : b < 2 ^ s) :
    (a * 2 ^ s) ||| b = a * 2 ^ s + b := by
  rw [← Nat.shiftLeft_eq]
  exact (Nat.shiftLeft_add_eq_or_of_lt hb a).symm

-- ============================================================================
-- Section 6: Inner sqrt convergence (reusable for EVM bridge)
-- ============================================================================

-- The norm model's Babylonian steps (using unbounded normAdd) are identical to
-- bstep, and therefore converge to natSqrt on normalized inputs [2^254, 2^256).
-- For the EVM bridge, we reuse this by showing the EVM Babylonian steps produce
-- the same values (since the sums don't overflow 2^256).

open Sqrt512GeneratedModel in
/-- The 6 model_bstep calls equal run6Fixed. -/
private theorem norm_6steps_eq_run6Fixed (x_hi_1 : Nat) :
    let r_hi_1 := FIXED_SEED
    let r_hi_2 := model_bstep x_hi_1 r_hi_1
    let r_hi_3 := model_bstep x_hi_1 r_hi_2
    let r_hi_4 := model_bstep x_hi_1 r_hi_3
    let r_hi_5 := model_bstep x_hi_1 r_hi_4
    let r_hi_6 := model_bstep x_hi_1 r_hi_5
    let r_hi_7 := model_bstep x_hi_1 r_hi_6
    r_hi_7 = run6Fixed x_hi_1 := by
  simp only [model_bstep_eq_bstep, run6Fixed, FIXED_SEED, bstep]

open Sqrt512GeneratedModel in
/-- The 6 steps + floor correction in the norm model = floorSqrt_fixed. -/
private theorem norm_inner_sqrt_eq_floorSqrt_fixed (x_hi_1 : Nat) (hx : 0 < x_hi_1) :
    let r_hi_1 := FIXED_SEED
    let r_hi_2 := model_bstep x_hi_1 r_hi_1
    let r_hi_3 := model_bstep x_hi_1 r_hi_2
    let r_hi_4 := model_bstep x_hi_1 r_hi_3
    let r_hi_5 := model_bstep x_hi_1 r_hi_4
    let r_hi_6 := model_bstep x_hi_1 r_hi_5
    let r_hi_7 := model_bstep x_hi_1 r_hi_6
    let r_hi_8 := normSub r_hi_7 (normLt (normDiv x_hi_1 r_hi_7) r_hi_7)
    r_hi_8 = floorSqrt_fixed x_hi_1 := by
  simp only [model_bstep_eq_bstep]
  have h7 := norm_6steps_eq_run6Fixed x_hi_1
  simp only [model_bstep_eq_bstep] at h7
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
    let r_hi_2 := model_bstep x_hi_1 r_hi_1
    let r_hi_3 := model_bstep x_hi_1 r_hi_2
    let r_hi_4 := model_bstep x_hi_1 r_hi_3
    let r_hi_5 := model_bstep x_hi_1 r_hi_4
    let r_hi_6 := model_bstep x_hi_1 r_hi_5
    let r_hi_7 := model_bstep x_hi_1 r_hi_6
    let r_hi_8 := normSub r_hi_7 (normLt (normDiv x_hi_1 r_hi_7) r_hi_7)
    r_hi_8 = natSqrt x_hi_1 := by
  have hpos : 0 < x_hi_1 := by omega
  have h := norm_inner_sqrt_eq_floorSqrt_fixed x_hi_1 hpos
  simp only [model_bstep_eq_bstep] at h ⊢
  rw [h]
  exact floorSqrt_fixed_eq_natSqrt x_hi_1 hlo hhi

-- ============================================================================
-- Section 7: EVM operation bridge lemmas
-- ============================================================================

section EvmNormBridge
open Sqrt512GeneratedModel

private theorem u256_id' (x : Nat) (hx : x < WORD_MOD) : u256 x = x :=
  Nat.mod_eq_of_lt hx

private theorem evmSub_eq_of_le (a b : Nat) (ha : a < WORD_MOD) (hb : b ≤ a) :
    evmSub a b = a - b := by
  have hb' : b < WORD_MOD := Nat.lt_of_le_of_lt hb ha
  have hab' : a - b < WORD_MOD := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
  unfold evmSub u256
  simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb']
  have hsplit : a + WORD_MOD - b = WORD_MOD + (a - b) := by omega
  rw [hsplit, Nat.add_mod, Nat.mod_eq_zero_of_dvd (Nat.dvd_refl WORD_MOD), Nat.zero_add,
      Nat.mod_mod_of_dvd, Nat.mod_eq_of_lt hab']
  exact Nat.dvd_refl WORD_MOD

private theorem evmDiv_eq' (a b : Nat) (ha : a < WORD_MOD) (hb : 0 < b) (hb' : b < WORD_MOD) :
    evmDiv a b = a / b := by
  unfold evmDiv
  simp only [u256_id' a ha, u256_id' b hb']
  simp [Nat.ne_of_gt hb]

private theorem evmMod_eq' (a b : Nat) (ha : a < WORD_MOD) (hb : 0 < b) (hb' : b < WORD_MOD) :
    evmMod a b = a % b := by
  unfold evmMod
  simp only [u256_id' a ha, u256_id' b hb']
  simp [Nat.ne_of_gt hb]

private theorem evmOr_eq' (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmOr a b = a ||| b := by
  unfold evmOr; simp [u256_id' a ha, u256_id' b hb]

private theorem evmAnd_eq' (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmAnd a b = a &&& b := by
  unfold evmAnd; simp [u256_id' a ha, u256_id' b hb]

private theorem evmShr_eq' (s v : Nat) (hs : s < 256) (hv : v < WORD_MOD) :
    evmShr s v = v / 2 ^ s := by
  have hs' : s < WORD_MOD := by unfold WORD_MOD; omega
  unfold evmShr; simp [u256_id' s hs', u256_id' v hv, hs]

private theorem evmShl_eq' (s v : Nat) (hs : s < 256) (hv : v < WORD_MOD) :
    evmShl s v = (v * 2 ^ s) % WORD_MOD := by
  have hs' : s < WORD_MOD := by unfold WORD_MOD; omega
  unfold evmShl u256
  simp [Nat.mod_eq_of_lt hs', Nat.mod_eq_of_lt hv, hs]

private theorem evmAdd_eq' (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD)
    (hab : a + b < WORD_MOD) :
    evmAdd a b = a + b := by
  unfold evmAdd u256
  simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hab]

private theorem evmMul_eq' (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmMul a b = (a * b) % WORD_MOD := by
  unfold evmMul u256
  simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

private theorem evmClz_eq' (v : Nat) (hv : v < WORD_MOD) :
    evmClz v = if v = 0 then 256 else 255 - Nat.log2 v := by
  unfold evmClz; simp [u256_id' v hv]

private theorem evmLt_eq' (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmLt a b = if a < b then 1 else 0 := by
  unfold evmLt; simp [u256_id' a ha, u256_id' b hb]

private theorem evmEq_eq' (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmEq a b = if a = b then 1 else 0 := by
  unfold evmEq; simp [u256_id' a ha, u256_id' b hb]

private theorem evmNot_eq' (a : Nat) (ha : a < WORD_MOD) :
    evmNot a = WORD_MOD - 1 - a := by
  unfold evmNot; simp [u256_id' a ha]

/-- When a + b = WORD_MOD and f ∈ {0,1}, EVM overflow+underflow gives the right answer. -/
private theorem evmSub_evmAdd_eq_of_overflow (a b : Nat)
    (ha : a < WORD_MOD) (hb : b < WORD_MOD)
    (hab : a + b = WORD_MOD) :
    evmSub (evmAdd a b) 1 = WORD_MOD - 1 := by
  unfold evmAdd evmSub u256
  simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hab, Nat.mod_self]
  have h1 : (1 : Nat) < WORD_MOD := by unfold WORD_MOD; omega
  simp [Nat.mod_eq_of_lt h1]

/-- Generic: (a * n) % (n * n) = (a % n) * n -/
private theorem mul_mod_sq (a n : Nat) (hn : 0 < n) :
    (a * n) % (n * n) = (a % n) * n := by
  -- a = n * (a/n) + a%n, so a*n = n*n*(a/n) + (a%n)*n
  have h := Nat.div_add_mod a n  -- n * (a / n) + a % n = a
  have ha : a * n = n * n * (a / n) + a % n * n := by
    have h2 : a * n = (n * (a / n) + a % n) * n := by rw [h]
    rw [h2, Nat.add_mul]
    show n * (a / n) * n + a % n * n = n * n * (a / n) + a % n * n
    congr 1
    rw [Nat.mul_assoc, Nat.mul_comm (a / n) n, ← Nat.mul_assoc]
  rw [ha, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (Nat.mul_lt_mul_of_pos_right (Nat.mod_lt a hn) hn)

/-- Key: (a * 2^128) % 2^256 = (a % 2^128) * 2^128 -/
private theorem mul_pow128_mod_word (a : Nat) :
    (a * 2 ^ 128) % WORD_MOD = (a % 2 ^ 128) * 2 ^ 128 := by
  have : WORD_MOD = 2 ^ 128 * 2 ^ 128 := by unfold WORD_MOD; rw [← Nat.pow_add]
  rw [this]; exact mul_mod_sq a (2 ^ 128) (Nat.two_pow_pos 128)

/-- Euclidean division after recomposition: (d*q + r)/d = q + r/d -/
private theorem div_of_mul_add (d q r : Nat) (hd : 0 < d) :
    (d * q + r) / d = q + r / d := by
  rw [show d * q + r = r + q * d from by rw [Nat.mul_comm, Nat.add_comm],
      Nat.add_mul_div_right r q hd, Nat.add_comm]

/-- Euclidean mod after recomposition: (d*q + r) % d = r % d -/
private theorem mod_of_mul_add (d q r : Nat) (hd : 0 < d) :
    (d * q + r) % d = r % d := by
  rw [show d * q + r = r + q * d from by rw [Nat.mul_comm, Nat.add_comm]]
  exact Nat.add_mul_mod_self_right r q d

end EvmNormBridge

-- ============================================================================
-- Section 8: Sub-model bridge theorems
-- ============================================================================

-- With the refactored Solidity code, model_sqrt512_evm now calls three
-- sub-models: model_innerSqrt_evm, model_karatsubaQuotient_evm, and
-- model_sqrtCorrection_evm. Each sub-model is proved correct independently,
-- then chained in the top-level theorem.

section SubModelBridge
open Sqrt512GeneratedModel

/-- The norm model of _innerSqrt gives (floorSqrt_fixed x, x - floorSqrt_fixed(x)²).
    Follows from norm_inner_sqrt_eq_floorSqrt_fixed by unfolding model_innerSqrt. -/
private theorem model_innerSqrt_fst_eq_floorSqrt_fixed (x_hi_1 : Nat) (hx : 0 < x_hi_1) :
    (model_innerSqrt x_hi_1).1 = floorSqrt_fixed x_hi_1 := by
  unfold model_innerSqrt
  exact norm_inner_sqrt_eq_floorSqrt_fixed x_hi_1 hx

/-- The norm model of _innerSqrt gives natSqrt on normalized inputs. -/
private theorem model_innerSqrt_fst_eq_natSqrt (x_hi_1 : Nat)
    (hlo : 2 ^ 254 ≤ x_hi_1) (hhi : x_hi_1 < 2 ^ 256) :
    (model_innerSqrt x_hi_1).1 = natSqrt x_hi_1 := by
  have hpos : 0 < x_hi_1 := by omega
  rw [model_innerSqrt_fst_eq_floorSqrt_fixed x_hi_1 hpos]
  exact floorSqrt_fixed_eq_natSqrt x_hi_1 hlo hhi

end SubModelBridge

-- ============================================================================
-- Section 9: Direct EVM model → sqrt512 bridge
-- ============================================================================

-- We prove model_sqrt512_evm = sqrt512 DIRECTLY, without going through the
-- norm model (model_sqrt512). The norm model uses unbounded normShl/normMul
-- which don't match EVM uint256 semantics, making it unsuitable as an intermediate.
--
-- The EVM model uses u256-wrapped operations that correctly implement the
-- Solidity algorithm. We show its output equals sqrt512(x_hi * 2^256 + x_lo).
--
-- With the refactored model structure, the proof decomposes into sub-lemmas
-- that each unfold only ONE sub-model:
--   A. EVM normalization: x_hi_1 = x*4^k/2^256, x_lo_1 = x*4^k%2^256
--   B. model_innerSqrt_evm → (natSqrt(x_hi_1), x_hi_1 - natSqrt(x_hi_1)²)
--   C. model_karatsubaQuotient_evm → quotient/remainder with carry correction
--   D. model_sqrtCorrection_evm → combine + 257-bit correction = karatsubaFloor
--   E. Chain: karatsubaFloor(x_hi_1, x_lo_1) / 2^k = sqrt512(x)

section EvmBridge
open Sqrt512GeneratedModel

/-- Sub-lemma A: The EVM normalization phase computes the correct normalized words.
    Given x = x_hi * 2^256 + x_lo and k = (255 - log2 x_hi) / 2:
    - x_hi_1 = (x * 4^k) / 2^256
    - x_lo_1 = (x * 4^k) % 2^256
    - shift_1 = k -/
-- 512-bit left shift decomposition into high/low 256-bit words.
theorem shl512_hi (x_hi x_lo s : Nat) (hs : s ≤ 255) :
    (x_hi * 2 ^ 256 + x_lo) * 2 ^ s / 2 ^ 256 =
      x_hi * 2 ^ s + x_lo / 2 ^ (256 - s) := by
  have hrw : (x_hi * 2 ^ 256 + x_lo) * 2 ^ s =
      x_lo * 2 ^ s + x_hi * 2 ^ s * 2 ^ 256 := by
    rw [Nat.add_mul, Nat.mul_right_comm]; omega
  rw [hrw, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 256), Nat.add_comm]
  congr 1
  have h256_split : 2 ^ 256 = 2 ^ (256 - s) * 2 ^ s := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [h256_split]
  exact Nat.mul_div_mul_right _ _ (Nat.two_pow_pos s)

theorem shl512_lo' (x_hi x_lo s : Nat) (hs : s ≤ 255) :
    (x_hi * 2 ^ 256 + x_lo) * 2 ^ s % 2 ^ 256 =
      (x_lo * 2 ^ s) % 2 ^ 256 := by
  have hrw : (x_hi * 2 ^ 256 + x_lo) * 2 ^ s =
      x_lo * 2 ^ s + x_hi * 2 ^ s * 2 ^ 256 := by
    rw [Nat.add_mul, Nat.mul_right_comm]; omega
  rw [hrw, Nat.add_mul_mod_self_right]

-- x_hi * 2^s < 2^256 when x_hi * 2^s is exactly the product (no overflow)
-- and shift_range guarantees this.
private theorem shl_no_overflow (x_hi s : Nat) (h : x_hi * 2 ^ s < 2 ^ 256) :
    (x_hi * 2 ^ s) % (2 ^ 256) = x_hi * 2 ^ s :=
  Nat.mod_eq_of_lt h

-- The bottom s bits of (x_hi * 2^s) % 2^256 are zero, so OR = add with values < 2^s.
private theorem shl_or_shr (x_hi x_lo s : Nat) (hs : 0 < s) (hs' : s ≤ 255)
    (hxhi_shl : x_hi * 2 ^ s < 2 ^ 256) (hxlo : x_lo < 2 ^ 256) :
    (x_hi * 2 ^ s) ||| (x_lo / 2 ^ (256 - s)) =
      x_hi * 2 ^ s + x_lo / 2 ^ (256 - s) := by
  have hcarry : x_lo / 2 ^ (256 - s) < 2 ^ s := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    calc x_lo < 2 ^ 256 := hxlo
      _ = 2 ^ s * 2 ^ (256 - s) := by rw [← Nat.pow_add]; congr 1; omega
  -- x_hi * 2^s is a multiple of 2^s, carry < 2^s, so bits don't overlap
  exact or_eq_add_shl x_hi (x_lo / 2 ^ (256 - s)) s hcarry

-- Full high word computation: OR of SHL and SHR equals the high word of the 512-bit shift.
private theorem shl512_hi_or (x_hi x_lo s : Nat) (hs : 0 < s) (hs' : s ≤ 255)
    (hxhi_shl : x_hi * 2 ^ s < 2 ^ 256) (hxlo : x_lo < 2 ^ 256) :
    ((x_hi * 2 ^ s) % 2 ^ 256) ||| (x_lo / 2 ^ (256 - s)) =
      (x_hi * 2 ^ 256 + x_lo) * 2 ^ s / 2 ^ 256 := by
  rw [shl_no_overflow x_hi s hxhi_shl, shl_or_shr x_hi x_lo s hs hs' hxhi_shl hxlo,
      shl512_hi x_hi x_lo s hs']

private theorem evm_normalization_correct (x_hi x_lo : Nat)
    (hxhi_pos : 0 < x_hi) (hxhi_lt : x_hi < 2 ^ 256) (hxlo_lt : x_lo < 2 ^ 256) :
    let x := x_hi * 2 ^ 256 + x_lo
    let k := (255 - Nat.log2 x_hi) / 2
    let shift := evmClz (u256 x_hi)
    let dbl_k := evmAnd shift 254
    let x_lo_1 := evmShl dbl_k (u256 x_lo)
    let x_hi_1 := evmOr (evmShl dbl_k (u256 x_hi)) (evmShr (evmSub 256 dbl_k) (u256 x_lo))
    let shift_1 := evmShr (evmAnd (evmAnd 1 255) 255) shift
    x_hi_1 = x * 4 ^ k / 2 ^ 256 ∧
    x_lo_1 = x * 4 ^ k % 2 ^ 256 ∧
    shift_1 = k ∧
    2 ^ 254 ≤ x_hi_1 ∧
    x_hi_1 < 2 ^ 256 ∧
    x_lo_1 < 2 ^ 256 := by
  -- Inline all let-bindings upfront so rw/simp work on concrete expressions.
  -- dbl_k = evmAnd (evmClz (u256 x_hi)) 254
  -- shift = evmClz (u256 x_hi)
  -- x = x_hi * 2^256 + x_lo, k = (255 - log2 x_hi) / 2
  show let x := x_hi * 2 ^ 256 + x_lo; let k := (255 - Nat.log2 x_hi) / 2;
    let dbl_k := evmAnd (evmClz (u256 x_hi)) 254;
    evmOr (evmShl dbl_k (u256 x_hi)) (evmShr (evmSub 256 dbl_k) (u256 x_lo)) =
        x * 4 ^ k / 2 ^ 256 ∧
    evmShl dbl_k (u256 x_lo) = x * 4 ^ k % 2 ^ 256 ∧
    evmShr (evmAnd (evmAnd 1 255) 255) (evmClz (u256 x_hi)) = k ∧
    2 ^ 254 ≤ evmOr (evmShl dbl_k (u256 x_hi)) (evmShr (evmSub 256 dbl_k) (u256 x_lo)) ∧
    evmOr (evmShl dbl_k (u256 x_hi)) (evmShr (evmSub 256 dbl_k) (u256 x_lo)) < 2 ^ 256 ∧
    evmShl dbl_k (u256 x_lo) < 2 ^ 256
  intro x; intro k; intro dbl_k
  have hxhi_wm : x_hi < WORD_MOD := hxhi_lt
  have hxlo_wm : x_lo < WORD_MOD := hxlo_lt
  have hxhi_ne : x_hi ≠ 0 := Nat.ne_of_gt hxhi_pos
  have hlog_le : Nat.log2 x_hi ≤ 255 := by
    have := (Nat.log2_lt hxhi_ne).2 hxhi_lt; omega
  -- Step 1: evmClz (u256 x_hi) = 255 - log2(x_hi)
  have hshift_eq : evmClz (u256 x_hi) = 255 - Nat.log2 x_hi := by
    rw [u256_id' x_hi hxhi_wm, evmClz_eq' x_hi hxhi_wm]; simp [hxhi_ne]
  have hshift_wm : evmClz (u256 x_hi) < WORD_MOD := by rw [hshift_eq]; unfold WORD_MOD; omega
  -- Step 2: dbl_k = 2 * k
  have hdbl_k : dbl_k = 2 * k := by
    show evmAnd (evmClz (u256 x_hi)) 254 = _
    rw [evmAnd_eq' _ 254 hshift_wm (by unfold WORD_MOD; omega), hshift_eq]
    exact normAnd_shift_254 (255 - Nat.log2 x_hi) (by omega)
  have hdbl_k_lt : dbl_k < 256 := by omega
  have hdbl_k_le : dbl_k ≤ 254 := by omega
  -- Step 3: shift_1 = k
  have hshift_1_eq : evmShr (evmAnd (evmAnd 1 255) 255) (evmClz (u256 x_hi)) = k := by
    have h1 : (1 : Nat) < WORD_MOD := by unfold WORD_MOD; omega
    have h255 : (255 : Nat) < WORD_MOD := by unfold WORD_MOD; omega
    rw [evmAnd_eq' 1 255 h1 h255, and_1_255, evmAnd_eq' 1 255 h1 h255, and_1_255]
    rw [evmShr_eq' 1 _ (by omega) hshift_wm, hshift_eq, Nat.pow_one]
  -- Step 4: 4^k = 2^dbl_k
  have hfour_eq : 4 ^ k = 2 ^ dbl_k := by
    rw [hdbl_k, show (4 : Nat) = 2 ^ 2 from by decide, ← Nat.pow_mul]
  -- Step 5: x_hi * 2^dbl_k < 2^256
  have hsr := shift_range x_hi hxhi_pos hxhi_lt
  have hxhi_shl_lt : x_hi * 2 ^ dbl_k < 2 ^ 256 := by rw [← hfour_eq]; exact hsr.2
  -- Step 6: Simplify EVM operations
  have hsub_eq : evmSub 256 dbl_k = 256 - dbl_k :=
    evmSub_eq_of_le 256 dbl_k (by unfold WORD_MOD; omega) (by omega)
  have hshl_xhi : evmShl dbl_k (u256 x_hi) = (x_hi * 2 ^ dbl_k) % WORD_MOD := by
    rw [u256_id' x_hi hxhi_wm]; exact evmShl_eq' dbl_k x_hi hdbl_k_lt hxhi_wm
  -- Steps 6-10 use complex EVM-to-Nat rewrites. We case-split on dbl_k = 0
  -- (which is the only case where 256 - dbl_k = 256 makes evmShr behave differently).
  by_cases hdbl_k_zero : dbl_k = 0
  · -- CASE: dbl_k = 0, so k = 0, x already normalized
    have hk_zero : k = 0 := by omega
    -- With dbl_k = 0 and k = 0: 4^k = 1, x * 1 = x, x/2^256 = x_hi, x%2^256 = x_lo
    -- Since dbl_k is a let-binding, we can't rw it directly. Use simp + show.
    have hk_zero : k = 0 := by omega
    -- Simplify all EVM ops with dbl_k = 0
    have hu256_xhi : u256 x_hi = x_hi := u256_id' x_hi hxhi_wm
    have hu256_xlo : u256 x_lo = x_lo := u256_id' x_lo hxlo_wm
    have hxhi1_eq : evmOr (evmShl dbl_k (u256 x_hi)) (evmShr (evmSub 256 dbl_k) (u256 x_lo)) = x_hi := by
      rw [hdbl_k_zero, hu256_xhi, hu256_xlo]
      rw [evmShl_eq' 0 x_hi (by omega) hxhi_wm, Nat.pow_zero, Nat.mul_one]
      unfold WORD_MOD
      rw [Nat.mod_eq_of_lt hxhi_lt]
      -- evmShr (256 - 0) x_lo = evmShr 256 x_lo = 0 (since 256 is not < 256)
      rw [evmSub_eq_of_le 256 0 (by unfold WORD_MOD; omega) (by omega)]
      -- Goal: evmOr x_hi (evmShr 256 x_lo) = x_hi
      -- evmShr 256 x_lo: shift 256 ≥ 256 so result is 0
      have : evmShr 256 x_lo = 0 := by
        unfold evmShr u256 WORD_MOD; simp
      rw [this]
      rw [evmOr_eq' x_hi 0 hxhi_wm (by unfold WORD_MOD; omega)]
      simp
    have hxlo1_eq : evmShl dbl_k (u256 x_lo) = x_lo := by
      rw [hdbl_k_zero, hu256_xlo,
          evmShl_eq' 0 x_lo (by omega) hxlo_wm, Nat.pow_zero, Nat.mul_one]
      unfold WORD_MOD; exact Nat.mod_eq_of_lt hxlo_lt
    have hxdiv : x / 2 ^ 256 = x_hi := by
      show (x_hi * 2 ^ 256 + x_lo) / 2 ^ 256 = x_hi
      rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos 256), Nat.div_eq_of_lt hxlo_lt,
          Nat.add_zero]
    have hxmod : x % 2 ^ 256 = x_lo := by
      show (x_hi * 2 ^ 256 + x_lo) % 2 ^ 256 = x_lo
      rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hxlo_lt
    -- 4^k = 4^0 = 1 when k = 0
    have h4k_one : 4 ^ k = 1 := by simp [hk_zero]
    refine ⟨?_, ?_, hshift_1_eq, ?_, ?_, ?_⟩
    · rw [hxhi1_eq, h4k_one, Nat.mul_one, hxdiv]
    · rw [hxlo1_eq, h4k_one, Nat.mul_one, hxmod]
    · rw [hxhi1_eq]; have := hsr.1; rw [h4k_one, Nat.mul_one] at this; exact this
    · rw [hxhi1_eq]; exact hxhi_lt
    · rw [hxlo1_eq]; exact hxlo_lt
  · -- CASE: dbl_k > 0, so 256 - dbl_k < 256 and evmShr works normally
    have hdbl_k_pos : 0 < dbl_k := by omega
    have hshr_xlo : evmShr (evmSub 256 dbl_k) (u256 x_lo) = x_lo / 2 ^ (256 - dbl_k) := by
      rw [u256_id' x_lo hxlo_wm, hsub_eq]
      exact evmShr_eq' (256 - dbl_k) x_lo (by omega) hxlo_wm
    have hshl_xlo : evmShl dbl_k (u256 x_lo) = (x_lo * 2 ^ dbl_k) % WORD_MOD := by
      rw [u256_id' x_lo hxlo_wm]; exact evmShl_eq' dbl_k x_lo hdbl_k_lt hxlo_wm
    have hshl_xhi_wm : evmShl dbl_k (u256 x_hi) < WORD_MOD := by
      rw [hshl_xhi]; exact Nat.mod_lt _ (by unfold WORD_MOD; omega)
    have hshr_xlo_wm : evmShr (evmSub 256 dbl_k) (u256 x_lo) < WORD_MOD := by
      rw [hshr_xlo]; unfold WORD_MOD
      have : x_lo / 2 ^ (256 - dbl_k) < 2 ^ dbl_k := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
        calc x_lo < 2 ^ 256 := hxlo_lt
          _ = 2 ^ dbl_k * 2 ^ (256 - dbl_k) := by rw [← Nat.pow_add]; congr 1; omega
      exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) (by omega))
    have hxhi1_eq : evmOr (evmShl dbl_k (u256 x_hi)) (evmShr (evmSub 256 dbl_k) (u256 x_lo)) =
        x * 4 ^ k / 2 ^ 256 := by
      rw [evmOr_eq' _ _ hshl_xhi_wm hshr_xlo_wm, hshl_xhi, hshr_xlo]
      unfold WORD_MOD
      rw [shl512_hi_or x_hi x_lo dbl_k hdbl_k_pos (by omega) hxhi_shl_lt hxlo_lt]
      congr 1; rw [← hfour_eq]
    have hxlo1_eq : evmShl dbl_k (u256 x_lo) = x * 4 ^ k % 2 ^ 256 := by
      rw [hshl_xlo]; unfold WORD_MOD
      rw [show x * 4 ^ k = (x_hi * 2 ^ 256 + x_lo) * 2 ^ dbl_k from by rw [← hfour_eq]]
      exact (shl512_lo' x_hi x_lo dbl_k (by omega)).symm
    have hhi_eq : x * 4 ^ k / 2 ^ 256 = x_hi * 2 ^ dbl_k + x_lo / 2 ^ (256 - dbl_k) := by
      rw [show x * 4 ^ k = (x_hi * 2 ^ 256 + x_lo) * 2 ^ dbl_k from by rw [← hfour_eq]]
      exact shl512_hi x_hi x_lo dbl_k (by omega)
    have hhi_lo_bound : 2 ^ 254 ≤ x * 4 ^ k / 2 ^ 256 := by
      rw [hhi_eq]; have := hsr.1; rw [hfour_eq] at this; omega
    have hshr_xlo_val : x_lo / 2 ^ (256 - dbl_k) < 2 ^ dbl_k := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      calc x_lo < 2 ^ 256 := hxlo_lt
        _ = 2 ^ dbl_k * 2 ^ (256 - dbl_k) := by rw [← Nat.pow_add]; congr 1; omega
    have hhi_hi_bound : x * 4 ^ k / 2 ^ 256 < 2 ^ 256 := by
      rw [hhi_eq]
      have h2 : (x_hi + 1) * 2 ^ dbl_k ≤ 2 ^ 256 := by
        rw [Nat.succ_mul]
        have h256 : 2 ^ 256 = 2 ^ dbl_k * 2 ^ (256 - dbl_k) := by
          rw [← Nat.pow_add]; congr 1; omega
        -- hxhi_shl_lt : x_hi * 2^dbl_k < 2^256
        -- Goal: x_hi * 2^dbl_k + 2^dbl_k ≤ 2^256
        -- From x_hi * 2^dbl_k < 2^256 = 2^dbl_k * 2^(256-dbl_k)
        -- we get x_hi < 2^(256-dbl_k), so (x_hi+1) * 2^dbl_k ≤ 2^(256-dbl_k) * 2^dbl_k = 2^256
        rw [h256] at hxhi_shl_lt ⊢
        have hxhi_lt_pow : x_hi < 2 ^ (256 - dbl_k) := by
          rw [Nat.mul_comm] at hxhi_shl_lt
          exact Nat.lt_of_mul_lt_mul_left hxhi_shl_lt
        calc x_hi * 2 ^ dbl_k + 2 ^ dbl_k
            = (x_hi + 1) * 2 ^ dbl_k := by rw [Nat.succ_mul]
          _ ≤ 2 ^ (256 - dbl_k) * 2 ^ dbl_k :=
              Nat.mul_le_mul_right _ hxhi_lt_pow
          _ = 2 ^ dbl_k * 2 ^ (256 - dbl_k) := Nat.mul_comm _ _
      calc x_hi * 2 ^ dbl_k + x_lo / 2 ^ (256 - dbl_k)
          < x_hi * 2 ^ dbl_k + 2 ^ dbl_k := by omega
        _ = (x_hi + 1) * 2 ^ dbl_k := by rw [Nat.succ_mul]
        _ ≤ 2 ^ 256 := h2
    have hlo1_bound : evmShl dbl_k (u256 x_lo) < 2 ^ 256 := by
      rw [hxlo1_eq]; exact Nat.mod_lt _ (by omega)
    exact ⟨hxhi1_eq, hxlo1_eq, hshift_1_eq,
           hxhi1_eq ▸ hhi_lo_bound, hxhi1_eq ▸ hhi_hi_bound, hlo1_bound⟩

/-- One EVM Babylonian step equals bstep when z ≥ 2^127, z < 2^129, x ∈ [2^254, 2^256).
    The sum z + x/z < 2^129 + 2^129 = 2^130 < 2^256 so evmAdd doesn't overflow.
    Also preserves the bound: 2^127 ≤ bstep x z < 2^129. -/
private theorem evm_bstep_eq (x z : Nat)
    (hx_lo : 2 ^ 254 ≤ x) (hx_hi : x < WORD_MOD)
    (hz_lo : 2 ^ 127 ≤ z) (hz_hi : z < 2 ^ 129) :
    evmShr 1 (evmAdd z (evmDiv x z)) = bstep x z ∧
    2 ^ 127 ≤ bstep x z ∧ bstep x z < 2 ^ 129 := by
  have hz_pos : 0 < z := by omega
  have hz_wm : z < WORD_MOD := by unfold WORD_MOD; omega
  -- x / z < 2^129 since x < 2^256 and z ≥ 2^127
  have hxz_bound : x / z < 2 ^ 129 := by
    rw [Nat.div_lt_iff_lt_mul hz_pos]
    calc x < WORD_MOD := hx_hi
      _ = 2 ^ 256 := rfl
      _ = 2 ^ 129 * 2 ^ 127 := by rw [← Nat.pow_add]
      _ ≤ 2 ^ 129 * z := Nat.mul_le_mul_left _ hz_lo
  have hxz_lt : x / z < WORD_MOD := by unfold WORD_MOD; omega
  -- The sum z + x/z < 2^129 + 2^129 = 2^130 < WORD_MOD
  have hsum : z + x / z < WORD_MOD := by
    have h3 : (2 : Nat) ^ 129 + 2 ^ 129 ≤ WORD_MOD := by unfold WORD_MOD; omega
    omega
  -- Simplify evmDiv first, then evmAdd, then evmShr
  have hdiv_eq : evmDiv x z = x / z := evmDiv_eq' x z hx_hi hz_pos hz_wm
  have hadd_eq : evmAdd z (evmDiv x z) = z + x / z := by
    rw [hdiv_eq]; exact evmAdd_eq' z (x / z) hz_wm hxz_lt hsum
  have hadd_bound : evmAdd z (evmDiv x z) < WORD_MOD := by
    rw [hadd_eq]; exact hsum
  have hstep_val : evmShr 1 (evmAdd z (evmDiv x z)) = (z + x / z) / 2 := by
    have h := evmShr_eq' 1 _ (by omega : (1 : Nat) < 256) hadd_bound
    rw [h, hadd_eq, Nat.pow_one]
  have hbstep : bstep x z = (z + x / z) / 2 := rfl
  constructor
  · rw [hstep_val, hbstep]
  constructor
  -- Lower bound: bstep x z ≥ 2^127
  -- Uses babylon_step_floor_bound with m = 2^127: if m^2 ≤ x then m ≤ bstep x z
  · have hmsq : (2 : Nat) ^ 127 * 2 ^ 127 ≤ x := by
      have : (2 : Nat) ^ 127 * 2 ^ 127 = 2 ^ 254 := by rw [← Nat.pow_add]
      omega
    exact babylon_step_floor_bound x z (2 ^ 127) hz_pos hmsq
  -- Upper bound: bstep x z < 2^129
  · rw [hbstep]
    have hsum_bound : z + x / z < 2 ^ 129 + 2 ^ 129 := by omega
    -- (a / 2 < b) when (a < 2 * b)
    omega

/-- The generated model_bstep_evm = bstep when x ∈ [2^254, 2^256) and z ∈ [2^127, 2^129).
    Wraps evm_bstep_eq by stripping the u256 wrappers. Also preserves bounds. -/
private theorem model_bstep_evm_eq_bstep (x z : Nat)
    (hx_lo : 2 ^ 254 ≤ x) (hx_hi : x < WORD_MOD)
    (hz_lo : 2 ^ 127 ≤ z) (hz_hi : z < 2 ^ 129) :
    model_bstep_evm x z = bstep x z ∧
    2 ^ 127 ≤ bstep x z ∧ bstep x z < 2 ^ 129 := by
  have hx_wm : x < WORD_MOD := hx_hi
  have hz_wm : z < WORD_MOD := by unfold WORD_MOD; omega
  unfold model_bstep_evm
  simp only [u256_id' x hx_wm, u256_id' z hz_wm]
  exact evm_bstep_eq x z hx_lo hx_hi hz_lo hz_hi

/-- FIXED_SEED < 2^128 < 2^129. -/
private theorem fixed_seed_lt_2_129 : FIXED_SEED < 2 ^ 129 := by
  unfold FIXED_SEED; omega

/-- FIXED_SEED ≥ 2^127. -/
private theorem fixed_seed_ge_2_127 : 2 ^ 127 ≤ FIXED_SEED := by
  unfold FIXED_SEED; omega

/-- Sub-lemma B: model_innerSqrt_evm gives (natSqrt(x_hi_1), x_hi_1 - natSqrt(x_hi_1)²).
    Unfolds only model_innerSqrt_evm (~10 let-bindings). Each EVM Babylonian step
    equals bstep (proved by evm_bstep_eq), and the floor correction matches on
    bounded inputs. Together: EVM inner sqrt = floorSqrt_fixed = natSqrt. -/
private theorem natSqrt_lt_2_128 (x : Nat) (hx : x < 2 ^ 256) :
    natSqrt x < 2 ^ 128 := by
  suffices h : ¬(2 ^ 128 ≤ natSqrt x) by omega
  intro h
  have hsq := natSqrt_sq_le x
  have hpow : (2 : Nat) ^ 128 * 2 ^ 128 = 2 ^ 256 := by rw [← Nat.pow_add]
  have := Nat.mul_le_mul h h
  omega

private theorem natSqrt_ge_2_127 (x : Nat) (hx : 2 ^ 254 ≤ x) :
    2 ^ 127 ≤ natSqrt x := by
  suffices h : ¬(natSqrt x < 2 ^ 127) by omega
  intro h
  have h1 : natSqrt x + 1 ≤ 2 ^ 127 := h
  have h2 := Nat.mul_le_mul h1 h1
  have h3 := natSqrt_lt_succ_sq x
  have h4 : (2 : Nat) ^ 127 * 2 ^ 127 = 2 ^ 254 := by rw [← Nat.pow_add]
  omega

/-- The norm model's second component is x - fst^2 (definitional). -/
theorem model_innerSqrt_snd_def (x : Nat) :
    (model_innerSqrt x).2 = x - (model_innerSqrt x).1 * (model_innerSqrt x).1 := by
  rfl

/-- The norm model's second component gives the residue x - natSqrt(x)^2. -/
theorem model_innerSqrt_snd_eq_residue (x : Nat)
    (hlo : 2 ^ 254 ≤ x) (hhi : x < 2 ^ 256) :
    (model_innerSqrt x).2 = x - natSqrt x * natSqrt x := by
  rw [model_innerSqrt_snd_def, model_innerSqrt_fst_eq_natSqrt x hlo hhi]

/-- EVM inner sqrt equals norm inner sqrt on in-range inputs.
    Since all intermediate sums z + x/z < 2^130 < 2^256, the EVM
    operations (evmAdd, evmDiv, evmShr, etc.) match their norm
    counterparts exactly. Each step stays in [2^127, 2^129).
    Proof: chain evm_bstep_eq 6 times + show correction/residue match. -/
theorem model_innerSqrt_evm_eq_norm (x_hi_1 : Nat)
    (hlo : 2 ^ 254 ≤ x_hi_1) (hhi : x_hi_1 < 2 ^ 256) :
    model_innerSqrt_evm x_hi_1 = model_innerSqrt x_hi_1 := by
  have hx_wm : x_hi_1 < WORD_MOD := hhi
  -- Both models return (r_hi_8, res_1). Show each component is equal.
  -- Strategy: EVM bstep chain = bstep chain = norm bstep chain,
  -- then correction + residue EVM ops match norm ops under bounds.
  ext
  -- ===== Component 1: .1 (the corrected sqrt) =====
  -- Both .1 equal natSqrt x_hi_1, so they're equal to each other.
  · rw [show (model_innerSqrt x_hi_1).1 = natSqrt x_hi_1 from
      model_innerSqrt_fst_eq_natSqrt x_hi_1 hlo hhi]
    -- Prove (model_innerSqrt_evm x_hi_1).1 = natSqrt x_hi_1
    -- Unfold to expose 6 model_bstep_evm calls + correction
    unfold model_innerSqrt_evm
    -- After unfolding, FIXED_SEED appears as its literal value. Fold it back.
    simp only [u256_id' x_hi_1 hx_wm,
      show (240615969168004511545033772477625056927 : Nat) = FIXED_SEED from rfl]
    -- Chain: each model_bstep_evm step equals bstep (and preserves [2^127, 2^129) bounds)
    have h1 := model_bstep_evm_eq_bstep x_hi_1 FIXED_SEED hlo hx_wm
      fixed_seed_ge_2_127 fixed_seed_lt_2_129
    have h2 := model_bstep_evm_eq_bstep x_hi_1 _ hlo hx_wm h1.2.1 h1.2.2
    have h3 := model_bstep_evm_eq_bstep x_hi_1 _ hlo hx_wm h2.2.1 h2.2.2
    have h4 := model_bstep_evm_eq_bstep x_hi_1 _ hlo hx_wm h3.2.1 h3.2.2
    have h5 := model_bstep_evm_eq_bstep x_hi_1 _ hlo hx_wm h4.2.1 h4.2.2
    have h6 := model_bstep_evm_eq_bstep x_hi_1 _ hlo hx_wm h5.2.1 h5.2.2
    -- Rewrite all 6 EVM bstep calls to bstep
    simp only [h1.1, h2.1, h3.1, h4.1, h5.1, h6.1]
    -- Now .1 = evmSub z6 (evmLt (evmDiv x z6) z6) where z6 = run6Fixed x
    -- Fold the 6-step bstep chain to run6Fixed
    have hz6_def : bstep x_hi_1 (bstep x_hi_1 (bstep x_hi_1 (bstep x_hi_1
      (bstep x_hi_1 (bstep x_hi_1 FIXED_SEED))))) = run6Fixed x_hi_1 := by
      simp only [run6Fixed, FIXED_SEED, bstep]
    rw [hz6_def]
    -- Bounds on z6 := run6Fixed x_hi_1
    have hz6_lo : 2 ^ 127 ≤ run6Fixed x_hi_1 := h6.2.1
    have hz6_hi : run6Fixed x_hi_1 < 2 ^ 129 := h6.2.2
    have hz6_wm : run6Fixed x_hi_1 < WORD_MOD := by unfold WORD_MOD; omega
    have hz6_pos : 0 < run6Fixed x_hi_1 := by omega
    -- Simplify EVM correction ops to Nat (z6 = run6Fixed x_hi_1 after rw)
    have hdiv_eq : evmDiv x_hi_1 (run6Fixed x_hi_1) = x_hi_1 / (run6Fixed x_hi_1) :=
      evmDiv_eq' x_hi_1 _ hx_wm hz6_pos hz6_wm
    have hdiv_wm : x_hi_1 / (run6Fixed x_hi_1) < WORD_MOD := by
      unfold WORD_MOD; exact Nat.lt_of_lt_of_le (by
        rw [Nat.div_lt_iff_lt_mul hz6_pos]
        calc x_hi_1 < 2 ^ 256 := hhi
          _ = 2 ^ 129 * 2 ^ 127 := by rw [← Nat.pow_add]
          _ ≤ 2 ^ 129 * run6Fixed x_hi_1 := Nat.mul_le_mul_left _ hz6_lo)
        (by omega)
    have hlt_eq : evmLt (evmDiv x_hi_1 (run6Fixed x_hi_1)) (run6Fixed x_hi_1) =
        if x_hi_1 / (run6Fixed x_hi_1) < (run6Fixed x_hi_1) then 1 else 0 := by
      rw [hdiv_eq]; exact evmLt_eq' _ _ hdiv_wm hz6_wm
    have hlt_le : (if x_hi_1 / (run6Fixed x_hi_1) < (run6Fixed x_hi_1) then 1
        else (0 : Nat)) ≤ run6Fixed x_hi_1 := by split <;> omega
    have hsub_corr : evmSub (run6Fixed x_hi_1) (evmLt (evmDiv x_hi_1 (run6Fixed x_hi_1))
        (run6Fixed x_hi_1)) =
        (run6Fixed x_hi_1) - (if x_hi_1 / (run6Fixed x_hi_1) < (run6Fixed x_hi_1)
          then 1 else 0) := by
      rw [hlt_eq]; exact evmSub_eq_of_le _ _ hz6_wm hlt_le
    rw [hsub_corr]
    -- Show: run6Fixed - correction = natSqrt x_hi_1
    have hbracket := fixed_seed_bracket x_hi_1 hlo hhi
    simp only [Nat.div_lt_iff_lt_mul hz6_pos]
    -- correction_correct gives: (if x < r*r then r-1 else r) = natSqrt
    -- We need: r - (if x < r*r then 1 else 0) = natSqrt
    have hcc := correction_correct x_hi_1 (run6Fixed x_hi_1) hbracket.1 hbracket.2
    by_cases hlt : x_hi_1 < run6Fixed x_hi_1 * run6Fixed x_hi_1
    · simp [hlt] at hcc ⊢; omega
    · simp [hlt] at hcc ⊢; omega
  -- ===== Component 2: .2 (the residue) =====
  -- Both .2 = x - (.1)^2 = x - natSqrt(x)^2, so they're equal.
  · rw [show (model_innerSqrt x_hi_1).2 = x_hi_1 - natSqrt x_hi_1 * natSqrt x_hi_1 from
      model_innerSqrt_snd_eq_residue x_hi_1 hlo hhi]
    -- Show (model_innerSqrt_evm x_hi_1).2 = x_hi_1 - natSqrt(x_hi_1)^2
    -- Since we just proved .1 = natSqrt, we know the correction value r8.
    -- .2 = evmSub x (evmMul r8 r8) where r8 = .1 = natSqrt x_hi_1
    -- Using the model definition: .2 depends on .1 in the same let-chain.
    -- The cleanest approach: .2 = x - .1 * .1 (the EVM model computes this)
    -- and .1 = natSqrt, so .2 = x - natSqrt^2 (if no overflow).
    -- We need natSqrt(x)^2 < WORD_MOD and natSqrt(x)^2 ≤ x.
    have hr8 := natSqrt_lt_2_128 x_hi_1 hhi
    have hr8_sq_lt : natSqrt x_hi_1 * natSqrt x_hi_1 < WORD_MOD := by
      calc natSqrt x_hi_1 * natSqrt x_hi_1
          < 2 ^ 128 * 2 ^ 128 := Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hr8) hr8 (by omega)
        _ = WORD_MOD := by unfold WORD_MOD; rw [← Nat.pow_add]
    have hr8_sq_le : natSqrt x_hi_1 * natSqrt x_hi_1 ≤ x_hi_1 := natSqrt_sq_le x_hi_1
    -- Now we need to show (model_innerSqrt_evm x_hi_1).2 equals x - natSqrt(x)^2
    -- Unfold and trace through the same chain as for .1
    unfold model_innerSqrt_evm
    simp only [u256_id' x_hi_1 hx_wm,
      show (240615969168004511545033772477625056927 : Nat) = FIXED_SEED from rfl]
    -- Same 6 bstep rewrites
    have h1 := model_bstep_evm_eq_bstep x_hi_1 FIXED_SEED hlo hx_wm
      fixed_seed_ge_2_127 fixed_seed_lt_2_129
    have h2 := model_bstep_evm_eq_bstep x_hi_1 _ hlo hx_wm h1.2.1 h1.2.2
    have h3 := model_bstep_evm_eq_bstep x_hi_1 _ hlo hx_wm h2.2.1 h2.2.2
    have h4 := model_bstep_evm_eq_bstep x_hi_1 _ hlo hx_wm h3.2.1 h3.2.2
    have h5 := model_bstep_evm_eq_bstep x_hi_1 _ hlo hx_wm h4.2.1 h4.2.2
    have h6 := model_bstep_evm_eq_bstep x_hi_1 _ hlo hx_wm h5.2.1 h5.2.2
    simp only [h1.1, h2.1, h3.1, h4.1, h5.1, h6.1]
    -- Abbreviate the 6-step bstep chain as z6
    have hz6_def : bstep x_hi_1 (bstep x_hi_1 (bstep x_hi_1 (bstep x_hi_1
      (bstep x_hi_1 (bstep x_hi_1 FIXED_SEED))))) = run6Fixed x_hi_1 := by
      simp only [run6Fixed, FIXED_SEED, bstep]
    rw [hz6_def]
    -- Bounds on run6Fixed x_hi_1
    have hz6_lo : 2 ^ 127 ≤ run6Fixed x_hi_1 := h6.2.1
    have hz6_wm : run6Fixed x_hi_1 < WORD_MOD := by unfold WORD_MOD; omega
    have hz6_pos : 0 < run6Fixed x_hi_1 := by omega
    -- Correction: same steps as .1 proof
    have hdiv_eq : evmDiv x_hi_1 (run6Fixed x_hi_1) = x_hi_1 / (run6Fixed x_hi_1) :=
      evmDiv_eq' x_hi_1 _ hx_wm hz6_pos hz6_wm
    have hdiv_wm : x_hi_1 / (run6Fixed x_hi_1) < WORD_MOD := by
      unfold WORD_MOD; exact Nat.lt_of_lt_of_le (by
        rw [Nat.div_lt_iff_lt_mul hz6_pos]
        calc x_hi_1 < 2 ^ 256 := hhi
          _ = 2 ^ 129 * 2 ^ 127 := by rw [← Nat.pow_add]
          _ ≤ 2 ^ 129 * run6Fixed x_hi_1 := Nat.mul_le_mul_left _ hz6_lo)
        (by omega)
    have hlt_eq : evmLt (evmDiv x_hi_1 (run6Fixed x_hi_1)) (run6Fixed x_hi_1) =
        if x_hi_1 / (run6Fixed x_hi_1) < (run6Fixed x_hi_1) then 1 else 0 := by
      rw [hdiv_eq]; exact evmLt_eq' _ _ hdiv_wm hz6_wm
    have hlt_le : (if x_hi_1 / (run6Fixed x_hi_1) < (run6Fixed x_hi_1) then 1
        else (0 : Nat)) ≤ run6Fixed x_hi_1 := by split <;> omega
    have hsub_corr : evmSub (run6Fixed x_hi_1) (evmLt (evmDiv x_hi_1 (run6Fixed x_hi_1))
        (run6Fixed x_hi_1)) =
        (run6Fixed x_hi_1) - (if x_hi_1 / (run6Fixed x_hi_1) < (run6Fixed x_hi_1)
          then 1 else 0) := by
      rw [hlt_eq]; exact evmSub_eq_of_le _ _ hz6_wm hlt_le
    rw [hsub_corr]
    -- r8 = natSqrt x_hi_1
    have hbracket := fixed_seed_bracket x_hi_1 hlo hhi
    have hcorr_eq : (run6Fixed x_hi_1) - (if x_hi_1 / (run6Fixed x_hi_1) < (run6Fixed x_hi_1)
        then 1 else 0) = natSqrt x_hi_1 := by
      simp only [Nat.div_lt_iff_lt_mul hz6_pos]
      have hcc := correction_correct x_hi_1 (run6Fixed x_hi_1) hbracket.1 hbracket.2
      by_cases hlt : x_hi_1 < run6Fixed x_hi_1 * run6Fixed x_hi_1
      · simp [hlt] at hcc ⊢; omega
      · simp [hlt] at hcc ⊢; omega
    rw [hcorr_eq]
    -- evmMul (natSqrt x_hi_1) (natSqrt x_hi_1) = natSqrt(x)^2 (no overflow)
    have hr8_wm : natSqrt x_hi_1 < WORD_MOD := by unfold WORD_MOD; omega
    rw [evmMul_eq' (natSqrt x_hi_1) (natSqrt x_hi_1) hr8_wm hr8_wm,
        Nat.mod_eq_of_lt hr8_sq_lt]
    -- evmSub x (natSqrt(x)^2) = x - natSqrt(x)^2 (since natSqrt(x)^2 ≤ x)
    exact evmSub_eq_of_le x_hi_1 _ hx_wm hr8_sq_le

theorem model_innerSqrt_evm_correct (x_hi_1 : Nat)
    (hlo : 2 ^ 254 ≤ x_hi_1) (hhi : x_hi_1 < 2 ^ 256) :
    (model_innerSqrt_evm x_hi_1).1 = natSqrt x_hi_1 ∧
    (model_innerSqrt_evm x_hi_1).2 = x_hi_1 - natSqrt x_hi_1 * natSqrt x_hi_1 := by
  rw [model_innerSqrt_evm_eq_norm x_hi_1 hlo hhi]
  exact ⟨model_innerSqrt_fst_eq_natSqrt x_hi_1 hlo hhi,
         model_innerSqrt_snd_eq_residue x_hi_1 hlo hhi⟩

/-- Sub-lemma C: model_karatsubaQuotient_evm computes the Karatsuba quotient and
    remainder, including carry correction for the 257-bit overflow case.
    Unfolds only model_karatsubaQuotient_evm (~6 let-bindings + if-block). -/
private theorem model_karatsubaQuotient_evm_correct
    (res x_lo r_hi : Nat)
    (hres : res ≤ 2 * r_hi)
    (hxlo : x_lo < 2 ^ 256) (hrhi_lo : 2 ^ 127 ≤ r_hi) (hrhi_hi : r_hi < 2 ^ 128)
    (hres_lt : res < 2 ^ 256) :
    let n_full := res * 2 ^ 128 + x_lo / 2 ^ 128
    let d := 2 * r_hi
    (model_karatsubaQuotient_evm res x_lo r_hi).1 = n_full / d % 2 ^ 256 ∧
    (model_karatsubaQuotient_evm res x_lo r_hi).2 = n_full % d % 2 ^ 256 := by
  intro n_full d
  -- === Key bounds ===
  have hres_wm : res < WORD_MOD := hres_lt
  have hxlo_wm : x_lo < WORD_MOD := hxlo
  have hrhi_wm : r_hi < WORD_MOD := by unfold WORD_MOD; omega
  have hd_pos : (0 : Nat) < d := by show 0 < 2 * r_hi; omega
  have hd_ge : (2 : Nat) ^ 128 ≤ d := by show 2 ^ 128 ≤ 2 * r_hi; omega
  have hd_wm : d < WORD_MOD := by unfold WORD_MOD; omega
  have h_wm_sq : WORD_MOD = 2 ^ 128 * 2 ^ 128 := by unfold WORD_MOD; rw [← Nat.pow_add]
  have hxlo_hi : x_lo / 2 ^ 128 < 2 ^ 128 :=
    Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hxlo)
  have hn_evm_lt : (res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128 < WORD_MOD := by
    have := Nat.mod_lt res (Nat.two_pow_pos 128); rw [h_wm_sq]; omega
  -- === EVM simplification lemmas ===
  have hd_eq : evmShl 1 r_hi = d := by
    rw [evmShl_eq' 1 r_hi (by omega) hrhi_wm, Nat.pow_one, Nat.mul_comm]
    exact Nat.mod_eq_of_lt (by unfold WORD_MOD; omega)
  have hshl_res : evmShl 128 res = (res % 2 ^ 128) * 2 ^ 128 := by
    rw [evmShl_eq' 128 res (by omega) hres_wm]; exact mul_pow128_mod_word res
  have hshr_xlo : evmShr 128 x_lo = x_lo / 2 ^ 128 :=
    evmShr_eq' 128 x_lo (by omega) hxlo_wm
  have hshl_wm : (res % 2 ^ 128) * 2 ^ 128 < WORD_MOD := by
    have := Nat.mod_lt res (Nat.two_pow_pos 128); rw [h_wm_sq]
    exact Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos 128)
  have hshr_wm : x_lo / 2 ^ 128 < WORD_MOD := by unfold WORD_MOD; omega
  have hn_eq : evmOr (evmShl 128 res) (evmShr 128 x_lo) =
      (res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128 := by
    rw [hshl_res, hshr_xlo, evmOr_eq' _ _ hshl_wm hshr_wm]
    exact or_eq_add_shl (res % 2 ^ 128) (x_lo / 2 ^ 128) 128 hxlo_hi
  have hc_eq : evmShr 128 res = res / 2 ^ 128 :=
    evmShr_eq' 128 res (by omega) hres_wm
  -- === Unfold model, inline let-bindings, then simplify EVM ops ===
  unfold model_karatsubaQuotient_evm
  -- Step 1: Inline all let-bindings to make the goal flat
  dsimp only
  -- Step 2: Remove u256 wrappers and simplify EVM operations
  simp only [u256_id' res hres_wm, u256_id' x_lo hxlo_wm, u256_id' r_hi hrhi_wm,
             hshl_res, hshr_xlo, hd_eq, hn_eq, hc_eq]
  -- The goal is now flat with an if on (res / 2^128 ≠ 0)
  split
  · -- CARRY case: res / 2^128 ≠ 0
    next hc_ne =>
    -- Simplify Prod projections
    simp only [Prod.fst, Prod.snd]
    -- Simplify evmOr to n_evm (the EVM-computed n, missing one WORD_MOD from n_full)
    have hn_or : evmOr (res % 2 ^ 128 * 2 ^ 128) (x_lo / 2 ^ 128) =
        (res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128 := by
      rw [evmOr_eq' _ _ hshl_wm hshr_wm,
          or_eq_add_shl (res % 2 ^ 128) (x_lo / 2 ^ 128) 128 hxlo_hi]
    simp only [hn_or]
    -- Abbreviate n_evm for clarity
    -- n_evm := (res % 2^128) * 2^128 + x_lo / 2^128
    -- Simplify evmDiv/evmMod on n_evm
    have hn_div : evmDiv ((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) d =
        ((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) / d :=
      evmDiv_eq' _ d hn_evm_lt hd_pos hd_wm
    have hn_mod : evmMod ((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) d =
        ((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d :=
      evmMod_eq' _ d hn_evm_lt hd_pos hd_wm
    -- Simplify evmNot 0 = WORD_MOD - 1
    have hnot_eq : evmNot 0 = WORD_MOD - 1 :=
      evmNot_eq' 0 (by unfold WORD_MOD; omega)
    have hnot_wm : WORD_MOD - 1 < WORD_MOD := by omega
    have hwm_div : evmDiv (WORD_MOD - 1) d = (WORD_MOD - 1) / d :=
      evmDiv_eq' _ d hnot_wm hd_pos hd_wm
    have hwm_mod : evmMod (WORD_MOD - 1) d = (WORD_MOD - 1) % d :=
      evmMod_eq' _ d hnot_wm hd_pos hd_wm
    simp only [hn_div, hn_mod, hnot_eq, hwm_div, hwm_mod]
    -- Now: evmAdd 1 ((WORD_MOD-1) % d) = 1 + (WORD_MOD-1) % d
    have hrw_lt : (WORD_MOD - 1) % d < d := Nat.mod_lt _ hd_pos
    have hrw_wm : (WORD_MOD - 1) % d < WORD_MOD :=
      Nat.lt_of_lt_of_le hrw_lt (by unfold WORD_MOD; omega)
    have h1_wm : (1 : Nat) < WORD_MOD := by unfold WORD_MOD; omega
    have h1rw_sum : 1 + (WORD_MOD - 1) % d < WORD_MOD :=
      Nat.lt_of_le_of_lt (by omega : 1 + (WORD_MOD - 1) % d ≤ d) (by unfold WORD_MOD; omega)
    have hadd_1_rw : evmAdd 1 ((WORD_MOD - 1) % d) = 1 + (WORD_MOD - 1) % d :=
      evmAdd_eq' 1 _ h1_wm hrw_wm h1rw_sum
    simp only [hadd_1_rw]
    -- evmAdd (n_evm%d) (1 + (WORD_MOD-1)%d) = R where R = n_evm%d + 1 + (WORD_MOD-1)%d
    have hr0_lt : ((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d < d :=
      Nat.mod_lt _ hd_pos
    have hr0_wm : ((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d < WORD_MOD :=
      Nat.lt_of_lt_of_le hr0_lt (by unfold WORD_MOD; omega)
    have hR_sum : ((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d +
        (1 + (WORD_MOD - 1) % d) < WORD_MOD :=
      -- r0 < d and 1 + rw < d + 1, so R < 2*d < 2^130 < WORD_MOD
      Nat.lt_of_lt_of_le (by omega : _ < 2 * d) (by unfold WORD_MOD; omega)
    have hstep2 : evmAdd (((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d)
        (1 + (WORD_MOD - 1) % d) =
        ((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d + (1 + (WORD_MOD - 1) % d) :=
      evmAdd_eq' _ _ hr0_wm h1rw_sum hR_sum
    simp only [hstep2]
    -- Abbreviate R = n_evm%d + 1 + (WORD_MOD-1)%d
    -- evmDiv R d = R / d, evmMod R d = R % d
    have hR_lt2d : ((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d +
        (1 + (WORD_MOD - 1) % d) < 2 * d := by omega
    have hR_wm : ((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d +
        (1 + (WORD_MOD - 1) % d) < WORD_MOD := hR_sum
    have hdiv_R : evmDiv (((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d +
        (1 + (WORD_MOD - 1) % d)) d =
        (((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d +
        (1 + (WORD_MOD - 1) % d)) / d :=
      evmDiv_eq' _ d hR_wm hd_pos hd_wm
    have hmod_R : evmMod (((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d +
        (1 + (WORD_MOD - 1) % d)) d =
        (((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d +
        (1 + (WORD_MOD - 1) % d)) % d :=
      evmMod_eq' _ d hR_wm hd_pos hd_wm
    simp only [hdiv_R, hmod_R]
    -- evmAdd (n_evm/d) ((WORD_MOD-1)/d) = n_evm/d + (WORD_MOD-1)/d
    have hq0_wm : ((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) / d < WORD_MOD := by
      unfold WORD_MOD; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn_evm_lt
    have hqw_wm : (WORD_MOD - 1) / d < WORD_MOD := by
      unfold WORD_MOD; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hnot_wm
    -- Tighter bounds: q0 < 2^128 and qw < 2^128 (from n < 2^256 and d ≥ 2^128)
    have hq0_128 : ((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) / d < 2 ^ 128 :=
      (Nat.div_lt_iff_lt_mul hd_pos).mpr (Nat.lt_of_lt_of_le hn_evm_lt
        (by rw [h_wm_sq]; exact Nat.mul_le_mul_left _ hd_ge))
    have hqw_128 : (WORD_MOD - 1) / d < 2 ^ 128 :=
      (Nat.div_lt_iff_lt_mul hd_pos).mpr (Nat.lt_of_lt_of_le hnot_wm
        (by rw [h_wm_sq]; exact Nat.mul_le_mul_left _ hd_ge))
    have h129_le_wm : (2 : Nat) ^ 129 ≤ WORD_MOD := by
      unfold WORD_MOD; exact Nat.pow_le_pow_right (by omega) (by omega)
    have hq0qw_sum : ((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) / d +
        (WORD_MOD - 1) / d < WORD_MOD :=
      Nat.lt_of_lt_of_le (by omega : _ < 2 ^ 129) h129_le_wm
    have hstep1 : evmAdd (((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) / d)
        ((WORD_MOD - 1) / d) =
        ((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) / d + (WORD_MOD - 1) / d :=
      evmAdd_eq' _ _ hq0_wm hqw_wm hq0qw_sum
    simp only [hstep1]
    -- evmAdd (q0+qw) (R/d) = q0+qw+R/d
    have hR_div_le1 : (((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d +
        (1 + (WORD_MOD - 1) % d)) / d ≤ 1 :=
      Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hd_pos).mpr hR_lt2d)
    have hR_div_wm : (((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d +
        (1 + (WORD_MOD - 1) % d)) / d < WORD_MOD :=
      Nat.lt_of_le_of_lt hR_div_le1 (by unfold WORD_MOD; omega)
    have hfinal_sum : ((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) / d +
        (WORD_MOD - 1) / d + (((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d +
        (1 + (WORD_MOD - 1) % d)) / d < WORD_MOD :=
      Nat.lt_of_lt_of_le (by omega : _ < 2 ^ 129 + 1) (by omega : 2 ^ 129 + 1 ≤ WORD_MOD)
    have hstep3 : evmAdd (((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) / d +
        (WORD_MOD - 1) / d)
        ((((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d +
        (1 + (WORD_MOD - 1) % d)) / d) =
        ((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) / d + (WORD_MOD - 1) / d +
        (((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d +
        (1 + (WORD_MOD - 1) % d)) / d :=
      evmAdd_eq' _ _ hq0qw_sum hR_div_wm hfinal_sum
    simp only [hstep3]
    -- === Now the goal is pure Nat ===
    -- Show these equal n_full/d and n_full%d via the carry correction identity
    -- n_full = n_evm + WORD_MOD where n_evm = (res%2^128)*2^128 + x_lo/2^128
    have hc_one : res / 2 ^ 128 = 1 := by
      have hc_pos : 0 < res / 2 ^ 128 := Nat.pos_of_ne_zero hc_ne
      have hc_le : res / 2 ^ 128 ≤ 1 := by
        have : res / 2 ^ 128 < 2 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 128)).mpr (by omega)
        omega
      omega
    have hn_full_eq : n_full =
        (res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128 + WORD_MOD := by
      show res * 2 ^ 128 + x_lo / 2 ^ 128 =
        (res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128 + WORD_MOD
      have h := Nat.div_add_mod res (2 ^ 128); rw [hc_one] at h; rw [h_wm_sq]; omega
    -- n_full = d * (q0 + qw) + R
    -- where q0 = n_evm/d, qw = (WORD_MOD-1)/d, R = n_evm%d + 1 + (WORD_MOD-1)%d
    have hn_full_decomp : n_full =
        d * (((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) / d + (WORD_MOD - 1) / d) +
        (((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d + (1 + (WORD_MOD - 1) % d)) := by
      rw [hn_full_eq]
      have h1 := (Nat.div_add_mod ((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) d).symm
      have h2 := (Nat.div_add_mod (WORD_MOD - 1) d).symm
      rw [Nat.mul_add]; omega
    -- Apply div_of_mul_add and mod_of_mul_add
    rw [show (2 : Nat) ^ 256 = WORD_MOD from rfl]
    have hn_div : n_full / d =
        ((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) / d + (WORD_MOD - 1) / d +
        (((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d + (1 + (WORD_MOD - 1) % d)) / d := by
      rw [hn_full_decomp]; exact div_of_mul_add d _ _ hd_pos
    have hn_mod : n_full % d =
        (((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d + (1 + (WORD_MOD - 1) % d)) % d := by
      rw [hn_full_decomp]; exact mod_of_mul_add d _ _ hd_pos
    have hn_full_mod_wm : n_full % d < WORD_MOD :=
      Nat.lt_of_lt_of_le (Nat.mod_lt n_full hd_pos) (by unfold WORD_MOD; omega)
    refine ⟨?_, ?_⟩
    · rw [hn_div]; exact (Nat.mod_eq_of_lt hfinal_sum).symm
    · rw [hn_mod]
      have : (((res % 2 ^ 128) * 2 ^ 128 + x_lo / 2 ^ 128) % d +
          (1 + (WORD_MOD - 1) % d)) % d < WORD_MOD :=
        Nat.lt_of_lt_of_le (Nat.mod_lt _ hd_pos) (by unfold WORD_MOD; omega)
      exact (Nat.mod_eq_of_lt this).symm
  · -- NO CARRY case
    next hc_not =>
    have hc_zero : res / 2 ^ 128 = 0 := Decidable.byContradiction hc_not
    have hres_128 : res < 2 ^ 128 := by
      suffices ¬(2 ^ 128 ≤ res) by omega
      intro h; exact absurd hc_zero (Nat.ne_of_gt (Nat.div_pos h (Nat.two_pow_pos 128)))
    have hmod_res : res % 2 ^ 128 = res := Nat.mod_eq_of_lt hres_128
    -- Simplify evmOr to Nat addition = n_full
    have hn_or : evmOr (res % 2 ^ 128 * 2 ^ 128) (x_lo / 2 ^ 128) = n_full := by
      rw [evmOr_eq' _ _ hshl_wm hshr_wm,
          or_eq_add_shl (res % 2 ^ 128) (x_lo / 2 ^ 128) 128 hxlo_hi, hmod_res]
    -- n_full < WORD_MOD (n_full = res*2^128 + x_lo/2^128, and res%2^128 = res)
    have hn_full_wm : n_full < WORD_MOD := by
      show res * 2 ^ 128 + x_lo / 2 ^ 128 < WORD_MOD
      rw [← hmod_res]; exact hn_evm_lt
    -- Reduce .fst/.snd, rewrite evmOr, simplify evmDiv/evmMod
    simp only [Prod.fst, Prod.snd, hn_or]
    rw [evmDiv_eq' n_full d hn_full_wm hd_pos hd_wm,
        evmMod_eq' n_full d hn_full_wm hd_pos hd_wm,
        show (2 : Nat) ^ 256 = WORD_MOD from rfl]
    exact ⟨(Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn_full_wm)).symm,
           (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt n_full hd_pos) (by unfold WORD_MOD; omega))).symm⟩

/-- Sub-lemma D: model_sqrtCorrection_evm computes the raw correction step.
    Given r_hi (high sqrt), r_lo (Karatsuba quotient), rem (Karatsuba remainder), x_lo:
    result = r_hi * 2^128 + r_lo - (if rem * 2^128 + x_lo % 2^128 < r_lo * r_lo then 1 else 0)
    The 257-bit split comparison correctly evaluates rem*2^128 + x_lo_lo < r_lo^2. -/
private theorem model_sqrtCorrection_evm_correct
    (r_hi r_lo rem x_lo : Nat)
    (hrhi_lo : 2 ^ 127 ≤ r_hi) (hrhi_hi : r_hi < 2 ^ 128)
    (hrlo_le : r_lo ≤ 2 ^ 128) (hrem : rem < 2 * r_hi)
    (hxlo : x_lo < 2 ^ 256)
    (hedge : r_lo = 2 ^ 128 → rem < 2 ^ 128) :
    model_sqrtCorrection_evm r_hi r_lo rem x_lo =
      r_hi * 2 ^ 128 + r_lo -
        (if rem * 2 ^ 128 + x_lo % 2 ^ 128 < r_lo * r_lo then 1 else 0) := by
  have hrhi_wm : r_hi < WORD_MOD := by unfold WORD_MOD; omega
  have hrlo_wm : r_lo < WORD_MOD := by unfold WORD_MOD; omega
  have hrem_wm : rem < WORD_MOD := by unfold WORD_MOD; omega
  have hxlo_wm : x_lo < WORD_MOD := hxlo
  have hrem_129 : rem < 2 ^ 129 := by omega
  have h_wm_sq : WORD_MOD = 2 ^ 128 * 2 ^ 128 := by unfold WORD_MOD; rw [← Nat.pow_add]
  -- Constant-fold: evmAnd(evmAnd(128, 255), 255) = 128
  have hcf128 : evmAnd (evmAnd 128 255) 255 = 128 := by native_decide
  -- 340282366920938463463374607431768211455 = 2^128 - 1
  have hmask : (340282366920938463463374607431768211455 : Nat) = 2 ^ 128 - 1 := by native_decide
  -- Unfold and inline let-bindings
  unfold model_sqrtCorrection_evm
  dsimp only
  simp only [u256_id' r_hi hrhi_wm, u256_id' r_lo hrlo_wm, u256_id' rem hrem_wm,
             u256_id' x_lo hxlo_wm, hcf128, hmask]
  -- === Simplify each EVM operation ===
  -- evmShl 128 r_hi, evmShr 128 rem, evmShr 128 r_lo
  have hshl_rhi : evmShl 128 r_hi = r_hi * 2 ^ 128 := by
    rw [evmShl_eq' 128 r_hi (by omega) hrhi_wm]
    exact Nat.mod_eq_of_lt (by rw [h_wm_sq]; exact Nat.mul_lt_mul_of_pos_right hrhi_hi (Nat.two_pow_pos 128))
  have hshr_rem : evmShr 128 rem = rem / 2 ^ 128 := evmShr_eq' 128 rem (by omega) hrem_wm
  have hshr_rlo : evmShr 128 r_lo = r_lo / 2 ^ 128 := evmShr_eq' 128 r_lo (by omega) hrlo_wm
  -- evmShl 128 rem = (rem % 2^128) * 2^128
  have hshl_rem : evmShl 128 rem = (rem % 2 ^ 128) * 2 ^ 128 := by
    rw [evmShl_eq' 128 rem (by omega) hrem_wm]; exact mul_pow128_mod_word rem
  -- evmAnd x_lo (2^128-1) = x_lo % 2^128
  have hand_mask : evmAnd x_lo (2 ^ 128 - 1) = x_lo % (2 ^ 128) := by
    rw [evmAnd_eq' x_lo (2 ^ 128 - 1) hxlo_wm (by unfold WORD_MOD; omega)]
    exact Nat.and_two_pow_sub_one_eq_mod x_lo 128
  -- evmOr for res_lo_concat: (rem%2^128)*2^128 + x_lo%2^128
  have hshl_rem_wm : (rem % 2 ^ 128) * 2 ^ 128 < WORD_MOD := by
    rw [h_wm_sq]; exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt rem (Nat.two_pow_pos 128)) (Nat.two_pow_pos 128)
  have hxlo_mod_lt : x_lo % 2 ^ 128 < 2 ^ 128 := Nat.mod_lt x_lo (Nat.two_pow_pos 128)
  have hxlo_mod_wm : x_lo % 2 ^ 128 < WORD_MOD := by unfold WORD_MOD; omega
  have hor_concat : evmOr (evmShl 128 rem) (evmAnd x_lo (2 ^ 128 - 1)) =
      (rem % 2 ^ 128) * 2 ^ 128 + x_lo % 2 ^ 128 := by
    rw [hshl_rem, hand_mask, evmOr_eq' _ _ hshl_rem_wm hxlo_mod_wm,
        or_eq_add_shl (rem % 2 ^ 128) (x_lo % 2 ^ 128) 128 hxlo_mod_lt]
  -- evmMul r_lo r_lo = (r_lo * r_lo) % WORD_MOD
  have hmul_rlo : evmMul r_lo r_lo = (r_lo * r_lo) % WORD_MOD :=
    evmMul_eq' r_lo r_lo hrlo_wm hrlo_wm
  -- evmLt, evmEq simplifications
  have hrem_hi_wm : rem / 2 ^ 128 < WORD_MOD := by unfold WORD_MOD; omega
  have hrlo_hi_wm : r_lo / 2 ^ 128 < WORD_MOD := by unfold WORD_MOD; omega
  have hconcat_wm : (rem % 2 ^ 128) * 2 ^ 128 + x_lo % 2 ^ 128 < WORD_MOD := by
    rw [h_wm_sq]; omega
  have hmul_wm : (r_lo * r_lo) % WORD_MOD < WORD_MOD := Nat.mod_lt _ (by unfold WORD_MOD; omega)
  have hlt_hi : evmLt (evmShr 128 rem) (evmShr 128 r_lo) =
      if rem / 2 ^ 128 < r_lo / 2 ^ 128 then 1 else 0 := by
    rw [hshr_rem, hshr_rlo]; exact evmLt_eq' _ _ hrem_hi_wm hrlo_hi_wm
  have heq_hi : evmEq (evmShr 128 rem) (evmShr 128 r_lo) =
      if rem / 2 ^ 128 = r_lo / 2 ^ 128 then 1 else 0 := by
    rw [hshr_rem, hshr_rlo]; exact evmEq_eq' _ _ hrem_hi_wm hrlo_hi_wm
  have hlt_lo : evmLt (evmOr (evmShl 128 rem) (evmAnd x_lo (2 ^ 128 - 1))) (evmMul r_lo r_lo) =
      if (rem % 2 ^ 128) * 2 ^ 128 + x_lo % 2 ^ 128 < (r_lo * r_lo) % WORD_MOD then 1 else 0 := by
    rw [hor_concat, hmul_rlo]; exact evmLt_eq' _ _ hconcat_wm hmul_wm
  -- Combine the comparison: cmp = evmOr(lt_hi, evmAnd(eq_hi, lt_lo))
  simp only [hlt_hi, heq_hi, hlt_lo, hshl_rhi]
  -- Now simplify evmAnd/evmOr on {0,1} comparison results, and evmAdd/evmSub
  -- The goal has the form:
  -- evmSub (evmAdd (r_hi*2^128) r_lo)
  --   (evmOr (if rem_hi < rlo_hi then 1 else 0)
  --     (evmAnd (if rem_hi = rlo_hi then 1 else 0)
  --       (if res_lo_concat < rlo_sq_mod then 1 else 0)))
  -- = r_hi*2^128 + r_lo - (if rem*2^128 + x_lo%2^128 < r_lo*r_lo then 1 else 0)
  --
  -- Key: the 257-bit comparison via (hi_lt || (hi_eq && lo_lt)) correctly evaluates
  -- rem * 2^128 + x_lo % 2^128 < r_lo * r_lo
  -- where:
  --   rem_hi = rem / 2^128, rlo_hi = r_lo / 2^128
  --   LHS_lo = (rem % 2^128) * 2^128 + x_lo % 2^128
  --   RHS_lo = (r_lo * r_lo) % WORD_MOD
  -- LHS = rem_hi * WORD_MOD + LHS_lo, RHS = rlo_hi * WORD_MOD + RHS_lo (conceptually)
  -- Since rem < 2*r_hi < 2^129, rem_hi ∈ {0,1}
  -- Since r_lo ≤ 2^128, rlo_hi ∈ {0,1}
  -- rem / 2^128 ≤ 1
  have hrem_hi_le : rem / 2 ^ 128 ≤ 1 :=
    Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 128)).mpr (by omega))
  -- r_lo / 2^128 ≤ 1
  have hrlo_hi_le : r_lo / 2 ^ 128 ≤ 1 := by
    have : r_lo / 2 ^ 128 < 2 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 128)).mpr (by omega)
    omega
  -- === Simplify evmAnd/evmOr on {0,1} values ===
  -- evmAnd (if a then 1 else 0) (if b then 1 else 0) =
  --   if a ∧ b then 1 else 0
  -- evmOr (if a then 1 else 0) (if b then 1 else 0) =
  --   if a ∨ b then 1 else 0
  -- These follow because the values are 0 or 1, which are < WORD_MOD
  -- After expanding: the cmp value is (if (rem_hi < rlo_hi) ∨ (rem_hi = rlo_hi ∧ lo_lt) then 1 else 0)
  -- where lo_lt = ((rem%2^128)*2^128 + x_lo%2^128 < (r_lo*r_lo)%WORD_MOD)
  --
  -- Need: this equals (if rem*2^128 + x_lo%2^128 < r_lo*r_lo then 1 else 0)
  -- This is the 257-bit comparison correctness.
  --
  -- And then: evmSub(evmAdd(r_hi*2^128, r_lo), cmp) = r_hi*2^128 + r_lo - cmp
  -- Case split on rem / 2^128 and r_lo / 2^128
  have hrem_hi_cases : rem / 2 ^ 128 = 0 ∨ rem / 2 ^ 128 = 1 := by omega
  have hrlo_hi_cases : r_lo / 2 ^ 128 = 0 ∨ r_lo / 2 ^ 128 = 1 := by omega
  rcases hrem_hi_cases with hremh | hremh <;> rcases hrlo_hi_cases with hrloh | hrloh <;>
    simp only [hremh, hrloh]
  · -- Case (0,0): rem < 2^128, r_lo < 2^128
    -- Reduce: if 0 < 0 → 0, if True → 1
    have h00 : (if (0 : Nat) < 0 then 1 else 0) = 0 := by decide
    simp only [h00, ite_true]
    -- evmOr 0 (evmAnd 1 x) where x = if P then 1 else 0
    -- evmAnd 1 (if P then 1 else 0) = if P then 1 else 0
    have hand1 : ∀ (n : Nat), n ≤ 1 →
        evmAnd 1 n = n := by
      intro n hn; rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl <;> native_decide
    -- evmOr 0 n = n for n ≤ 1
    have hor0 : ∀ (n : Nat), n ≤ 1 → evmOr 0 n = n := by
      intro n hn; rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl <;> native_decide
    -- Simplify: rem < 2^128 → rem % 2^128 = rem
    have hrem_lt : rem < 2 ^ 128 := by omega
    have hrem_mod : rem % 2 ^ 128 = rem := Nat.mod_eq_of_lt hrem_lt
    -- r_lo < 2^128 → r_lo * r_lo < WORD_MOD → r_lo*r_lo % WORD_MOD = r_lo*r_lo
    have hrlo_lt : r_lo < 2 ^ 128 := by omega
    have hrlo_sq_lt : r_lo * r_lo < WORD_MOD := by
      have := Nat.mul_le_mul_left r_lo (show r_lo ≤ 2 ^ 128 from by omega)
      have := Nat.mul_lt_mul_of_pos_right hrlo_lt (Nat.two_pow_pos 128)
      rw [h_wm_sq]; omega
    have hmod_sq : r_lo * r_lo % WORD_MOD = r_lo * r_lo := Nat.mod_eq_of_lt hrlo_sq_lt
    rw [hrem_mod, hmod_sq]
    -- Now both comparisons match, simplify evmAnd/evmOr
    have hcmp_le : (if rem * 2 ^ 128 + x_lo % 2 ^ 128 < r_lo * r_lo then 1 else (0 : Nat)) ≤ 1 := by
      split <;> omega
    rw [hand1 _ hcmp_le, hor0 _ hcmp_le]
    -- Simplify evmAdd/evmSub
    have hrhi_mul_lt : r_hi * 2 ^ 128 < WORD_MOD := by
      rw [h_wm_sq]; exact Nat.mul_lt_mul_of_pos_right hrhi_hi (Nat.two_pow_pos 128)
    have hadd_lt : r_hi * 2 ^ 128 + r_lo < WORD_MOD := by omega
    have hcmp_le_sum : (if rem * 2 ^ 128 + x_lo % 2 ^ 128 < r_lo * r_lo then 1 else 0) ≤
        r_hi * 2 ^ 128 + r_lo := by
      split <;> omega
    rw [evmAdd_eq' _ _ hrhi_mul_lt hrlo_wm hadd_lt,
        evmSub_eq_of_le _ _ hadd_lt hcmp_le_sum]
  · -- Case (0,1): rem < 2^128, r_lo / 2^128 = 1 → r_lo = 2^128
    have hrlo_eq : r_lo = 2 ^ 128 := by omega
    -- Reduce ifs
    have h01a : (if (0 : Nat) < 1 then 1 else 0) = 1 := by decide
    have h01b : (if (0 : Nat) = 1 then 1 else 0) = 0 := by decide
    simp only [h01a, h01b]
    -- evmAnd 0 _ = 0
    have hand0 : ∀ x, evmAnd 0 x = 0 := by
      intro x; unfold evmAnd u256; simp
    simp only [hand0]
    -- evmOr 1 0 = 1
    have : evmOr 1 0 = 1 := by native_decide
    simp only [this]
    -- RHS comparison is true: rem*2^128 + x_lo%2^128 < 2^128*2^128 = 2^256
    have hrem_lt : rem < 2 ^ 128 := by omega
    have hcmp_true : rem * 2 ^ 128 + x_lo % 2 ^ 128 < r_lo * r_lo := by
      rw [hrlo_eq, show (2 : Nat) ^ 128 * 2 ^ 128 = 2 ^ 256 from by rw [← Nat.pow_add]]
      have := Nat.mod_lt x_lo (Nat.two_pow_pos 128); omega
    simp only [hcmp_true, ↓reduceIte]
    rw [hrlo_eq]
    -- Now: evmSub (evmAdd (r_hi * 2^128) (2^128)) 1 = r_hi * 2^128 + 2^128 - 1
    -- Two subcases: overflow or not
    by_cases hoverflow : r_hi * 2 ^ 128 + 2 ^ 128 < WORD_MOD
    · -- No overflow
      rw [evmAdd_eq' _ _ (by omega) (by unfold WORD_MOD; omega) hoverflow,
          evmSub_eq_of_le _ 1 hoverflow (by omega)]
    · -- Overflow: r_hi * 2^128 + 2^128 = WORD_MOD
      have hsum_eq : r_hi * 2 ^ 128 + 2 ^ 128 = WORD_MOD := by
        have : r_hi * 2 ^ 128 + 2 ^ 128 ≤ WORD_MOD := by
          rw [h_wm_sq, ← Nat.succ_mul]
          exact Nat.mul_le_mul_right _ hrhi_hi
        omega
      rw [evmSub_evmAdd_eq_of_overflow _ _ (by omega) (by unfold WORD_MOD; omega) hsum_eq]
      omega
  · -- Case (1,0): rem / 2^128 = 1, r_lo < 2^128
    -- Reduce if 1 < 0 → 0, if 1 = 0 → 0
    have h10a : (if (1 : Nat) < 0 then 1 else 0) = 0 := by decide
    have h10b : (if (1 : Nat) = 0 then 1 else 0) = 0 := by decide
    simp only [h10a, h10b]
    -- evmAnd 0 _ = 0
    have hand0 : ∀ x, evmAnd 0 x = 0 := by
      intro x; unfold evmAnd u256; simp
    simp only [hand0]
    -- evmOr 0 0 = 0
    have hor00 : evmOr 0 0 = 0 := by native_decide
    simp only [hor00]
    -- RHS comparison: rem ≥ 2^128, r_lo < 2^128 → comparison false
    have hrlo_lt : r_lo < 2 ^ 128 := by omega
    have hrlo_sq_lt : r_lo * r_lo < WORD_MOD := by
      have h1 := Nat.mul_le_mul_left r_lo (show r_lo ≤ 2 ^ 128 from by omega)
      have h2 := Nat.mul_lt_mul_of_pos_right (show r_lo < 2 ^ 128 from by omega) (Nat.two_pow_pos 128)
      rw [h_wm_sq]; omega
    have hcmp_false : ¬(rem * 2 ^ 128 + x_lo % 2 ^ 128 < r_lo * r_lo) := by omega
    simp only [hcmp_false, ↓reduceIte, Nat.sub_zero]
    -- Simplify evmSub (evmAdd ...) 0
    have hrhi_mul_lt : r_hi * 2 ^ 128 < WORD_MOD := by
      rw [h_wm_sq]; exact Nat.mul_lt_mul_of_pos_right hrhi_hi (Nat.two_pow_pos 128)
    have hadd_lt : r_hi * 2 ^ 128 + r_lo < WORD_MOD := by omega
    rw [evmAdd_eq' _ _ hrhi_mul_lt hrlo_wm hadd_lt,
        evmSub_eq_of_le _ 0 hadd_lt (Nat.zero_le _)]
    omega
  · -- Case (1,1): contradiction (hedge + rem ≥ 2^128 + r_lo = 2^128)
    -- r_lo / 2^128 = 1, r_lo ≤ 2^128 → r_lo = 2^128
    have hrlo_eq : r_lo = 2 ^ 128 := by omega
    -- hedge: r_lo = 2^128 → rem < 2^128
    have hrem_lt : rem < 2 ^ 128 := hedge hrlo_eq
    -- But rem / 2^128 = 1 → rem ≥ 2^128
    exfalso; omega

end EvmBridge

/-- The EVM model computes the same as the algebraic sqrt512.
    With the refactored model, model_sqrt512_evm is just normalization +
    3 sub-model calls + un-normalization (~10 let-bindings), so this proof
    chains sub-results through karatsubaFloor_eq_natSqrt and natSqrt_shift_div. -/
private theorem model_sqrt512_evm_eq_sqrt512 (x_hi x_lo : Nat)
    (hxhi_pos : 0 < x_hi) (hxhi_lt : x_hi < 2 ^ 256)
    (hxlo_lt : x_lo < 2 ^ 256) :
    Sqrt512GeneratedModel.model_sqrt512_evm x_hi x_lo =
      sqrt512 (x_hi * 2 ^ 256 + x_lo) := by
  open Sqrt512GeneratedModel in
  -- Step 0: sqrt512 takes else branch since x_hi > 0 → x ≥ 2^256
  have hx_ge : ¬(x_hi * 2 ^ 256 + x_lo < 2 ^ 256) := by omega
  unfold sqrt512; simp only [hx_ge, ↓reduceIte]
  -- Simplify: (x_hi*2^256+x_lo)/2^256 = x_hi
  have hx_div : (x_hi * 2 ^ 256 + x_lo) / 2 ^ 256 = x_hi := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos 256),
        Nat.div_eq_of_lt hxlo_lt, Nat.add_zero]
  rw [hx_div]
  -- Now both sides use k = (255 - Nat.log2 x_hi) / 2
  -- LHS = model_sqrt512_evm x_hi x_lo
  -- RHS = karatsubaFloor (x * 4^k / 2^256) (x * 4^k % 2^256) / 2^k

  -- Unfold model_sqrt512_evm to see its structure
  sorry

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
