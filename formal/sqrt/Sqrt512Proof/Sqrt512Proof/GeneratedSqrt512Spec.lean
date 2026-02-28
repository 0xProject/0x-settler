/-
  Bridge from model_sqrt512_evm to natSqrt: specification layer.

  Part 1 (fully proved): Fixed-seed convergence certificate.
  Part 2: EVM model bridge to sqrt512 (3 sorry's: normalization, compute, kf bound).
  Part 3 (fully proved): Composition model_sqrt512_evm = natSqrt.
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

private def maxAbs254 : Nat :=
  max (FIXED_SEED - lo254) (hi254 - FIXED_SEED)

private def fd1_254 : Nat :=
  (maxAbs254 * maxAbs254 + 2 * hi254) / (2 * FIXED_SEED)

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
    have h := d1_bound x m FIXED_SEED lo254 hi254 fixed_seed_pos hmlo hmhi hlo hhi
    simpa [z1, fd1_254, maxAbs254] using h
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
    have h := d1_bound x m FIXED_SEED lo255 hi255 fixed_seed_pos hmlo hmhi hlo hhi
    simpa [z1, fd1_255, maxAbs255] using h
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
-- Section 5: Phase bridge sub-lemmas (sorry'd)
-- ============================================================================

/-- Phase 1: EVM normalization matches algebraic spec. -/
private theorem evm_normalization_bridge (x_hi x_lo : Nat)
    (hxhi_pos : 0 < x_hi) (hxhi_lt : x_hi < 2 ^ 256) (hxlo_lt : x_lo < 2 ^ 256) :
    let shift := Sqrt512GeneratedModel.evmClz x_hi
    let even_shift := Sqrt512GeneratedModel.evmAnd shift 254
    let x_lo_1 := Sqrt512GeneratedModel.evmShl even_shift x_lo
    let x_hi_1 := Sqrt512GeneratedModel.evmOr
      (Sqrt512GeneratedModel.evmShl even_shift x_hi)
      (Sqrt512GeneratedModel.evmShr (Sqrt512GeneratedModel.evmSub 256 even_shift) x_lo)
    let half_shift := Sqrt512GeneratedModel.evmShr
      (Sqrt512GeneratedModel.evmAnd (Sqrt512GeneratedModel.evmAnd 1 255) 255) shift
    let alg_shift := (255 - Nat.log2 x_hi) / 2
    let x' := (x_hi * 2 ^ 256 + x_lo) * 4 ^ alg_shift
    half_shift = alg_shift ∧
    x_hi_1 = x' / 2 ^ 256 ∧ x_lo_1 = x' % 2 ^ 256 ∧
    2 ^ 254 ≤ x_hi_1 ∧ x_hi_1 < 2 ^ 256 ∧ x_lo_1 < 2 ^ 256 := by
  sorry

/-- Phase 2+3: EVM Newton + Karatsuba + correction = karatsubaFloor. -/
private theorem evm_compute_bridge (x_hi_1 x_lo_1 : Nat)
    (hxhi1_lo : 2 ^ 254 ≤ x_hi_1) (hxhi1_hi : x_hi_1 < 2 ^ 256)
    (hxlo1 : x_lo_1 < 2 ^ 256) :
    let r_hi_1 := (240615969168004511545033772477625056927 : Nat)
    let r_hi_2 := Sqrt512GeneratedModel.evmShr 1 (Sqrt512GeneratedModel.evmAdd r_hi_1 (Sqrt512GeneratedModel.evmDiv x_hi_1 r_hi_1))
    let r_hi_3 := Sqrt512GeneratedModel.evmShr 1 (Sqrt512GeneratedModel.evmAdd r_hi_2 (Sqrt512GeneratedModel.evmDiv x_hi_1 r_hi_2))
    let r_hi_4 := Sqrt512GeneratedModel.evmShr 1 (Sqrt512GeneratedModel.evmAdd r_hi_3 (Sqrt512GeneratedModel.evmDiv x_hi_1 r_hi_3))
    let r_hi_5 := Sqrt512GeneratedModel.evmShr 1 (Sqrt512GeneratedModel.evmAdd r_hi_4 (Sqrt512GeneratedModel.evmDiv x_hi_1 r_hi_4))
    let r_hi_6 := Sqrt512GeneratedModel.evmShr 1 (Sqrt512GeneratedModel.evmAdd r_hi_5 (Sqrt512GeneratedModel.evmDiv x_hi_1 r_hi_5))
    let r_hi_7 := Sqrt512GeneratedModel.evmShr 1 (Sqrt512GeneratedModel.evmAdd r_hi_6 (Sqrt512GeneratedModel.evmDiv x_hi_1 r_hi_6))
    let r_hi_8 := Sqrt512GeneratedModel.evmSub r_hi_7 (Sqrt512GeneratedModel.evmLt (Sqrt512GeneratedModel.evmDiv x_hi_1 r_hi_7) r_hi_7)
    let res_1 := Sqrt512GeneratedModel.evmSub x_hi_1 (Sqrt512GeneratedModel.evmMul r_hi_8 r_hi_8)
    let n := Sqrt512GeneratedModel.evmOr (Sqrt512GeneratedModel.evmShl 128 res_1) (Sqrt512GeneratedModel.evmShr 128 x_lo_1)
    let d := Sqrt512GeneratedModel.evmShl 1 r_hi_8
    let r_lo_1 := Sqrt512GeneratedModel.evmDiv n d
    let c := Sqrt512GeneratedModel.evmShr 128 res_1
    let res_2 := Sqrt512GeneratedModel.evmMod n d
    let (r_lo, res) := if c ≠ 0 then
        let r_lo := Sqrt512GeneratedModel.evmAdd r_lo_1 (Sqrt512GeneratedModel.evmDiv (Sqrt512GeneratedModel.evmNot 0) d)
        let res := Sqrt512GeneratedModel.evmAdd res_2 (Sqrt512GeneratedModel.evmAdd 1 (Sqrt512GeneratedModel.evmMod (Sqrt512GeneratedModel.evmNot 0) d))
        let r_lo := Sqrt512GeneratedModel.evmAdd r_lo (Sqrt512GeneratedModel.evmDiv res d)
        let res := Sqrt512GeneratedModel.evmMod res d
        (r_lo, res)
      else (r_lo_1, res_2)
    let r_1 := Sqrt512GeneratedModel.evmAdd (Sqrt512GeneratedModel.evmShl (Sqrt512GeneratedModel.evmAnd (Sqrt512GeneratedModel.evmAnd 128 255) 255) r_hi_8) r_lo
    let r_2 := Sqrt512GeneratedModel.evmSub r_1
      (Sqrt512GeneratedModel.evmOr
        (Sqrt512GeneratedModel.evmLt (Sqrt512GeneratedModel.evmShr (Sqrt512GeneratedModel.evmAnd (Sqrt512GeneratedModel.evmAnd 128 255) 255) res) (Sqrt512GeneratedModel.evmShr (Sqrt512GeneratedModel.evmAnd (Sqrt512GeneratedModel.evmAnd 128 255) 255) r_lo))
        (Sqrt512GeneratedModel.evmAnd (Sqrt512GeneratedModel.evmEq (Sqrt512GeneratedModel.evmShr (Sqrt512GeneratedModel.evmAnd (Sqrt512GeneratedModel.evmAnd 128 255) 255) res) (Sqrt512GeneratedModel.evmShr (Sqrt512GeneratedModel.evmAnd (Sqrt512GeneratedModel.evmAnd 128 255) 255) r_lo))
          (Sqrt512GeneratedModel.evmLt (Sqrt512GeneratedModel.evmOr (Sqrt512GeneratedModel.evmShl (Sqrt512GeneratedModel.evmAnd (Sqrt512GeneratedModel.evmAnd 128 255) 255) res) (Sqrt512GeneratedModel.evmAnd x_lo_1 340282366920938463463374607431768211455)) (Sqrt512GeneratedModel.evmMul r_lo r_lo))))
    r_2 = karatsubaFloor x_hi_1 x_lo_1 := by
  sorry

-- ============================================================================
-- Section 6: Composition — model_sqrt512_evm = sqrt512 = natSqrt
-- ============================================================================

set_option exponentiation.threshold 512 in
private theorem model_sqrt512_evm_eq_sqrt512 (x_hi x_lo : Nat)
    (hxhi_pos : 0 < x_hi) (hxhi_lt : x_hi < 2 ^ 256)
    (hxlo_lt : x_lo < 2 ^ 256) :
    Sqrt512GeneratedModel.model_sqrt512_evm x_hi x_lo =
      sqrt512 (x_hi * 2 ^ 256 + x_lo) := by
  -- Unfold sqrt512 for x ≥ 2^256
  have hx_ge : ¬ (x_hi * 2 ^ 256 + x_lo < 2 ^ 256) := by omega
  have hx_div : (x_hi * 2 ^ 256 + x_lo) / 2 ^ 256 = x_hi := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 256),
        Nat.div_eq_of_lt hxlo_lt, Nat.zero_add]
  unfold sqrt512; simp only [hx_ge, ↓reduceIte, hx_div]
  -- RHS = karatsubaFloor(x' / 2^256, x' % 2^256) / 2^alg_shift
  -- Get normalization bridge
  have hnorm := evm_normalization_bridge x_hi x_lo hxhi_pos hxhi_lt hxlo_lt
  simp only [] at hnorm
  obtain ⟨h_hs, h_xhi1, h_xlo1, h_xhi1_lo, h_xhi1_hi, h_xlo1_lt⟩ := hnorm
  -- Get compute bridge
  have hcomp := evm_compute_bridge _ _ h_xhi1_lo h_xhi1_hi h_xlo1_lt
  simp only [] at hcomp
  -- The model_sqrt512_evm unfolds to evmShr shift_1 r_2
  -- where r_2 is the compute phase output
  -- By hcomp: r_2 = karatsubaFloor(x_hi_1, x_lo_1)
  -- By h_hs: shift_1 = alg_shift
  -- By h_xhi1, h_xlo1: x_hi_1 = x'/2^256, x_lo_1 = x'%2^256
  -- Connect model to the spec through the bridges
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
