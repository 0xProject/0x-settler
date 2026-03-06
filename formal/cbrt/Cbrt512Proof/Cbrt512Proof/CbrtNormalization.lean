/-
  Normalization: EVM shift = clz(x_hi)/3, left-shift x by 3*shift.

  For x_hi > 0:
    shift = evmDiv(evmClz(x_hi), 3)
    x_hi_1 = evmOr(evmShl(shift*3, x_hi), evmShr(256 - shift*3, x_lo))
    x_lo_1 = evmShl(shift*3, x_lo)

  Properties:
    (1) x_hi_1 * 2^256 + x_lo_1 = (x_hi * 2^256 + x_lo) * 2^(3*shift)
    (2) 2^253 ≤ x_hi_1 < 2^256
    (3) x_lo_1 < 2^256
    (4) shift < 86 (so 3*shift < 256)
-/
import Cbrt512Proof.GeneratedCbrt512Model

namespace Cbrt512Spec

open Cbrt512GeneratedModel

-- ============================================================================
-- CLZ / shift properties
-- ============================================================================

/-- For x_hi > 0 and x_hi < 2^256, evmClz(x_hi) = 255 - Nat.log2(x_hi). -/
theorem evmClz_of_pos (x_hi : Nat) (hpos : 0 < x_hi) (hlt : x_hi < WORD_MOD) :
    evmClz x_hi = 255 - Nat.log2 x_hi := by
  unfold evmClz u256
  simp [Nat.mod_eq_of_lt hlt, Nat.ne_of_gt hpos]

/-- clz(x_hi) < 256 for x_hi < 2^256. -/
theorem clz_lt_256 (x_hi : Nat) (hpos : 0 < x_hi) (hlt : x_hi < WORD_MOD) :
    evmClz x_hi < 256 := by
  rw [evmClz_of_pos x_hi hpos hlt]
  have hlog : Nat.log2 x_hi < 256 := by
    exact (Nat.log2_lt (Nat.ne_of_gt hpos)).2 (by unfold WORD_MOD at hlt; exact hlt)
  omega

/-- shift = clz(x_hi) / 3 < 86. -/
theorem shift_lt_86 (x_hi : Nat) (hpos : 0 < x_hi) (hlt : x_hi < WORD_MOD) :
    evmClz x_hi / 3 < 86 := by
  have h := clz_lt_256 x_hi hpos hlt
  omega

/-- 3 * shift < 256. -/
theorem three_shift_lt_256 (x_hi : Nat) (hpos : 0 < x_hi) (hlt : x_hi < WORD_MOD) :
    3 * (evmClz x_hi / 3) < 256 := by
  have h := shift_lt_86 x_hi hpos hlt; omega

/-- After normalization, x_hi_1 ≥ 2^253.
    Since clz(x_hi) = 255 - log2(x_hi), shift = (255 - log2(x_hi))/3,
    and 3*shift ≤ 255 - log2(x_hi), the top bit of x after shifting is at least
    log2(x_hi) + 3*shift ≥ log2(x_hi) + 255 - log2(x_hi) - 2 = 253. -/
theorem normalized_x_hi_ge_253 (x_hi x_lo : Nat)
    (hxhi_pos : 0 < x_hi) (hxhi : x_hi < 2 ^ 256) (hxlo : x_lo < 2 ^ 256) :
    let shift := evmClz x_hi / 3
    let s3 := 3 * shift
    let x_hi_1 := (x_hi * 2 ^ s3 + x_lo * 2 ^ s3 / 2 ^ 256) % 2 ^ 256
    2 ^ 253 ≤ x_hi_1 := by
  simp only
  have hne : x_hi ≠ 0 := Nat.ne_of_gt hxhi_pos
  have hxhi_wm : x_hi < WORD_MOD := by unfold WORD_MOD; exact hxhi
  -- Rewrite evmClz using log2
  rw [evmClz_of_pos x_hi hxhi_pos hxhi_wm]
  -- Name log2 x_hi as L and 3*((255-L)/3) as s3
  generalize hL_def : Nat.log2 x_hi = L
  generalize hs3_def : 3 * ((255 - L) / 3) = s3
  -- log2 properties: 2^L ≤ x_hi < 2^(L+1)
  have hL_lt : L < 256 := by rw [← hL_def]; exact (Nat.log2_lt hne).mpr hxhi
  have hL_lo : 2 ^ L ≤ x_hi := by
    suffices ¬(x_hi < 2 ^ L) by omega
    intro hlt
    have := (Nat.log2_lt hne).mpr hlt
    omega -- Nat.log2 x_hi < L contradicts hL_def : Nat.log2 x_hi = L
  have hL_hi : x_hi < 2 ^ (L + 1) := by
    have : Nat.log2 x_hi < L + 1 := by omega
    exact (Nat.log2_lt hne).mp this
  -- s3 bounds: L + s3 ≥ 253 (from floor division losing at most 2)
  have hdivmod := Nat.div_add_mod (255 - L) 3
  have hmod_lt := Nat.mod_lt (255 - L) (by omega : (0 : Nat) < 3)
  have hLs3 : 253 ≤ L + s3 := by omega
  -- Lower bound: 2^253 ≤ x_hi * 2^s3
  have hprod_lo : 2 ^ 253 ≤ x_hi * 2 ^ s3 :=
    calc 2 ^ 253 ≤ 2 ^ (L + s3) := Nat.pow_le_pow_right (by omega) hLs3
      _ = 2 ^ L * 2 ^ s3 := Nat.pow_add 2 L s3
      _ ≤ x_hi * 2 ^ s3 := Nat.mul_le_mul_right _ hL_lo
  -- Upper bound: x_lo * 2^s3 / 2^256 < 2^s3
  have hdiv_bound : x_lo * 2 ^ s3 / 2 ^ 256 < 2 ^ s3 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 256)]
    calc x_lo * 2 ^ s3
        < 2 ^ 256 * 2 ^ s3 := Nat.mul_lt_mul_of_pos_right hxlo (Nat.two_pow_pos s3)
      _ = 2 ^ s3 * 2 ^ 256 := Nat.mul_comm _ _
  -- Upper bound: sum < 2^256 so mod is identity
  have hsum_lt : x_hi * 2 ^ s3 + x_lo * 2 ^ s3 / 2 ^ 256 < 2 ^ 256 := by
    have hLs3_up : L + 1 + s3 ≤ 256 := by omega
    calc x_hi * 2 ^ s3 + x_lo * 2 ^ s3 / 2 ^ 256
        < x_hi * 2 ^ s3 + 2 ^ s3 := by omega
      _ = (x_hi + 1) * 2 ^ s3 := (Nat.succ_mul x_hi (2 ^ s3)).symm
      _ ≤ 2 ^ (L + 1) * 2 ^ s3 := Nat.mul_le_mul_right _ hL_hi
      _ = 2 ^ (L + 1 + s3) := (Nat.pow_add 2 (L + 1) s3).symm
      _ ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) hLs3_up
  -- Combine: mod is identity, then lower bound + monotonicity
  rw [Nat.mod_eq_of_lt hsum_lt]
  exact Nat.le_trans hprod_lo (Nat.le_add_right _ _)

/-- After normalization, x_hi_1 < 2^256. -/
theorem normalized_x_hi_lt (x_hi x_lo : Nat)
    (_hxhi_pos : 0 < x_hi) (_hxhi : x_hi < 2 ^ 256) (_hxlo : x_lo < 2 ^ 256) :
    let shift := evmClz x_hi / 3
    let s3 := 3 * shift
    let x_hi_1 := (x_hi * 2 ^ s3 + x_lo * 2 ^ s3 / 2 ^ 256) % 2 ^ 256
    x_hi_1 < 2 ^ 256 := by
  simp only; exact Nat.mod_lt _ (Nat.two_pow_pos 256)

-- ============================================================================
-- 512-bit shift decomposition helpers
-- ============================================================================

/-- High word of 512-bit left shift: (x_hi * 2^256 + x_lo) * 2^s / 2^256. -/
private theorem shl512_hi (x_hi x_lo s : Nat) (hs : s ≤ 255) :
    (x_hi * 2 ^ 256 + x_lo) * 2 ^ s / 2 ^ 256 =
      x_hi * 2 ^ s + x_lo / 2 ^ (256 - s) := by
  have hrw : (x_hi * 2 ^ 256 + x_lo) * 2 ^ s =
      x_lo * 2 ^ s + x_hi * 2 ^ s * 2 ^ 256 := by
    rw [Nat.add_mul, Nat.mul_right_comm]; omega
  rw [hrw, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 256), Nat.add_comm]
  congr 1
  rw [show 2 ^ 256 = 2 ^ (256 - s) * 2 ^ s from by rw [← Nat.pow_add]; congr 1; omega]
  exact Nat.mul_div_mul_right _ _ (Nat.two_pow_pos s)

/-- Low word of 512-bit left shift: (x_hi * 2^256 + x_lo) * 2^s % 2^256. -/
private theorem shl512_lo (x_hi x_lo s : Nat) :
    (x_hi * 2 ^ 256 + x_lo) * 2 ^ s % 2 ^ 256 =
      (x_lo * 2 ^ s) % 2 ^ 256 := by
  have hrw : (x_hi * 2 ^ 256 + x_lo) * 2 ^ s =
      x_lo * 2 ^ s + x_hi * 2 ^ s * 2 ^ 256 := by
    rw [Nat.add_mul, Nat.mul_right_comm]; omega
  rw [hrw, Nat.add_mul_mod_self_right]

/-- Bitwise OR equals addition when bits don't overlap. -/
private theorem or_eq_add_shl (a b s : Nat) (hb : b < 2 ^ s) :
    (a * 2 ^ s) ||| b = a * 2 ^ s + b := by
  rw [← Nat.shiftLeft_eq]
  exact (Nat.shiftLeft_add_eq_or_of_lt hb a).symm

/-- OR of SHL and SHR equals high word of 512-bit shift (s > 0 case). -/
private theorem shl_or_shr (x_hi x_lo s : Nat) (hs_pos : 0 < s) (hs : s ≤ 255)
    (hxhi_shl : x_hi * 2 ^ s < 2 ^ 256) (hxlo : x_lo < 2 ^ 256) :
    ((x_hi * 2 ^ s) % 2 ^ 256) ||| (x_lo / 2 ^ (256 - s)) =
      (x_hi * 2 ^ 256 + x_lo) * 2 ^ s / 2 ^ 256 := by
  rw [Nat.mod_eq_of_lt hxhi_shl]
  have hcarry : x_lo / 2 ^ (256 - s) < 2 ^ s := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    calc x_lo < 2 ^ 256 := hxlo
      _ = 2 ^ s * 2 ^ (256 - s) := by rw [← Nat.pow_add]; congr 1; omega
  rw [or_eq_add_shl x_hi (x_lo / 2 ^ (256 - s)) s hcarry,
      shl512_hi x_hi x_lo s hs]

-- ============================================================================
-- EVM normalization bridge
-- ============================================================================

set_option exponentiation.threshold 1024 in
/-- The EVM normalization computes the same values as Nat arithmetic. -/
theorem evm_normalization_correct (x_hi x_lo : Nat)
    (hxhi_pos : 0 < x_hi) (hxhi : x_hi < 2 ^ 256) (hxlo : x_lo < 2 ^ 256) :
    let _hxhi_wm : x_hi < WORD_MOD := by unfold WORD_MOD; exact hxhi
    let _hxlo_wm : x_lo < WORD_MOD := by unfold WORD_MOD; exact hxlo
    let shift := evmDiv (evmClz x_hi) 3
    let s3 := evmMul shift 3
    let x_lo_1 := evmShl s3 x_lo
    let x_hi_1 := evmOr (evmShl s3 x_hi) (evmShr (evmSub 256 s3) x_lo)
    -- shift is the floor division
    shift = evmClz x_hi / 3 ∧
    -- s3 = 3 * shift (no overflow)
    s3 = 3 * shift ∧
    -- The normalized values reconstruct x * 2^(3*shift) mod 2^512
    x_hi_1 * 2 ^ 256 + x_lo_1 = (x_hi * 2 ^ 256 + x_lo) * 2 ^ (3 * (evmClz x_hi / 3)) % (2 ^ 512) ∧
    -- x_hi_1 ≥ 2^253
    2 ^ 253 ≤ x_hi_1 ∧
    -- EVM bounds
    x_hi_1 < WORD_MOD ∧
    x_lo_1 < WORD_MOD := by
  simp only
  -- Basic bounds
  have hxhi_wm : x_hi < WORD_MOD := by unfold WORD_MOD; exact hxhi
  have hxlo_wm : x_lo < WORD_MOD := by unfold WORD_MOD; exact hxlo
  have hclz_wm : evmClz x_hi < WORD_MOD := by
    unfold WORD_MOD; exact Nat.lt_of_lt_of_le (clz_lt_256 x_hi hxhi_pos hxhi_wm) (by omega)
  have h3_wm : (3 : Nat) < WORD_MOD := by unfold WORD_MOD; omega
  have h256_wm : (256 : Nat) < WORD_MOD := by unfold WORD_MOD; omega
  have hshift_lt := shift_lt_86 x_hi hxhi_pos hxhi_wm
  have hs3_lt := three_shift_lt_256 x_hi hxhi_pos hxhi_wm
  -- Name the Nat-level shift values via let (definitionally transparent)
  let shift := evmClz x_hi / 3
  let s3 := 3 * shift
  have hshift_wm : shift < WORD_MOD := by unfold WORD_MOD; omega
  have hs3_wm : s3 < WORD_MOD := by unfold WORD_MOD; omega
  have hs3_lt_256 : s3 < 256 := hs3_lt
  -- ========== Part 1: evmDiv (evmClz x_hi) 3 = shift ==========
  have hshift_eq : evmDiv (evmClz x_hi) 3 = shift := by
    unfold evmDiv u256
    rw [Nat.mod_eq_of_lt hclz_wm, Nat.mod_eq_of_lt h3_wm,
        if_neg (show ¬(3 : Nat) = 0 from by omega)]
  -- ========== Part 2: evmMul shift 3 = s3 ==========
  have hs3_eq : evmMul shift 3 = s3 := by
    unfold evmMul u256
    rw [Nat.mod_eq_of_lt hshift_wm, Nat.mod_eq_of_lt h3_wm,
        Nat.mod_eq_of_lt (show shift * 3 < WORD_MOD from by unfold WORD_MOD; omega),
        Nat.mul_comm]
  -- Rewrite the EVM shift/s3 in the goal
  -- After simp only, the goal uses evmDiv/evmMul directly; we use rw to simplify
  rw [hshift_eq, hs3_eq]
  -- ========== Simplify EVM sub/shl/shr to Nat ==========
  have hsub_eq : evmSub 256 s3 = 256 - s3 := by
    unfold evmSub u256
    simp [Nat.mod_eq_of_lt h256_wm, Nat.mod_eq_of_lt hs3_wm]
    show (256 + WORD_MOD - s3) % WORD_MOD = 256 - s3
    rw [show 256 + WORD_MOD - s3 = (256 - s3) + WORD_MOD from by omega]
    simp [Nat.add_mod_right, Nat.mod_eq_of_lt (by unfold WORD_MOD; omega : 256 - s3 < WORD_MOD)]
  have hshl_xhi : evmShl s3 x_hi = (x_hi * 2 ^ s3) % WORD_MOD := by
    unfold evmShl u256
    simp [Nat.mod_eq_of_lt hs3_wm, Nat.mod_eq_of_lt hxhi_wm, hs3_lt_256]
  have hshl_xlo : evmShl s3 x_lo = (x_lo * 2 ^ s3) % WORD_MOD := by
    unfold evmShl u256
    simp [Nat.mod_eq_of_lt hs3_wm, Nat.mod_eq_of_lt hxlo_wm, hs3_lt_256]
  -- ========== x_hi * 2^s3 < 2^256 (shift range) ==========
  have hne : x_hi ≠ 0 := Nat.ne_of_gt hxhi_pos
  have hlog_le : Nat.log2 x_hi ≤ 255 := by
    have := (Nat.log2_lt hne).2 (by unfold WORD_MOD at hxhi_wm; exact hxhi_wm); omega
  have hL_hi : x_hi < 2 ^ (Nat.log2 x_hi + 1) := (Nat.log2_lt hne).mp (by omega)
  have hLs3_up : Nat.log2 x_hi + 1 + s3 ≤ 256 := by
    show Nat.log2 x_hi + 1 + 3 * (evmClz x_hi / 3) ≤ 256
    rw [evmClz_of_pos x_hi hxhi_pos hxhi_wm]
    omega
  have hxhi_shl_lt : x_hi * 2 ^ s3 < 2 ^ 256 :=
    calc x_hi * 2 ^ s3
        < 2 ^ (Nat.log2 x_hi + 1) * 2 ^ s3 := Nat.mul_lt_mul_of_pos_right hL_hi (Nat.two_pow_pos s3)
      _ = 2 ^ (Nat.log2 x_hi + 1 + s3) := (Nat.pow_add 2 _ s3).symm
      _ ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) hLs3_up
  -- ========== Case split: s3 = 0 vs s3 > 0 ==========
  by_cases hs3_zero : s3 = 0
  · -- CASE s3 = 0: x is already normalized enough
    have hshift_zero : shift = 0 := by omega
    -- evmShr (256 - 0) x_lo: shift ≥ 256 so result is 0
    have hshr_eq : evmShr (evmSub 256 s3) x_lo = 0 := by
      rw [hsub_eq, hs3_zero]
      unfold evmShr u256
      simp [Nat.mod_eq_of_lt h256_wm]
    -- evmShl 0 x_hi = x_hi
    have hshl_xhi_0 : evmShl s3 x_hi = x_hi := by
      rw [hshl_xhi, hs3_zero, Nat.pow_zero, Nat.mul_one]
      exact Nat.mod_eq_of_lt hxhi_wm
    -- evmShl 0 x_lo = x_lo
    have hshl_xlo_0 : evmShl s3 x_lo = x_lo := by
      rw [hshl_xlo, hs3_zero, Nat.pow_zero, Nat.mul_one]
      exact Nat.mod_eq_of_lt hxlo_wm
    -- x_hi_1 = evmOr x_hi 0 = x_hi
    have hshl_xhi_wm : evmShl s3 x_hi < WORD_MOD := by rw [hshl_xhi_0]; exact hxhi_wm
    have hshr_wm : evmShr (evmSub 256 s3) x_lo < WORD_MOD := by
      rw [hshr_eq]; unfold WORD_MOD; omega
    have hxhi1_eq : evmOr (evmShl s3 x_hi) (evmShr (evmSub 256 s3) x_lo) = x_hi := by
      unfold evmOr u256
      rw [Nat.mod_eq_of_lt hshl_xhi_wm, Nat.mod_eq_of_lt hshr_wm,
          hshl_xhi_0, hshr_eq]; simp
    -- Reconstruction: x_hi * 2^256 + x_lo = (x_hi * 2^256 + x_lo) * 2^0 % 2^512
    have hrecon : x_hi * 2 ^ 256 + x_lo =
        (x_hi * 2 ^ 256 + x_lo) * 2 ^ s3 % 2 ^ 512 := by
      rw [hs3_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt]
      rw [show (2 : Nat) ^ 512 = 2 ^ 256 * 2 ^ 256 from by rw [← Nat.pow_add]]
      calc x_hi * 2 ^ 256 + x_lo
          < x_hi * 2 ^ 256 + 2 ^ 256 := Nat.add_lt_add_left hxlo _
        _ = (x_hi + 1) * 2 ^ 256 := (Nat.succ_mul _ _).symm
        _ ≤ 2 ^ 256 * 2 ^ 256 := Nat.mul_le_mul_right _ hxhi
    -- Lower bound from normalized_x_hi_ge_253
    have hge_253 : 2 ^ 253 ≤ x_hi := by
      have h := normalized_x_hi_ge_253 x_hi x_lo hxhi_pos hxhi hxlo
      simp only at h
      -- s3 = 3 * (evmClz x_hi / 3) = 0
      rw [show 3 * (evmClz x_hi / 3) = 0 from hs3_zero] at h
      rw [Nat.pow_zero, Nat.mul_one, Nat.mul_one, Nat.div_eq_of_lt hxlo, Nat.add_zero,
          Nat.mod_eq_of_lt hxhi] at h
      exact h
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rw [hxhi1_eq, hshl_xlo_0]; exact hrecon
    · rw [hxhi1_eq]; exact hge_253
    · rw [hxhi1_eq]; exact hxhi_wm
    · rw [hshl_xlo_0]; exact hxlo_wm
  · -- CASE s3 > 0: standard normalization
    have hs3_pos : 0 < s3 := by omega
    -- evmShr (256 - s3) x_lo = x_lo / 2^(256-s3)
    have hshr_eq2 : evmShr (evmSub 256 s3) x_lo = x_lo / 2 ^ (256 - s3) := by
      rw [hsub_eq]; unfold evmShr u256
      have h256s3_wm : (256 - s3 : Nat) < WORD_MOD := by unfold WORD_MOD; omega
      simp [Nat.mod_eq_of_lt h256s3_wm, Nat.mod_eq_of_lt hxlo_wm,
            show 256 - s3 < 256 from by omega]
    -- Bounds for OR operands
    have hshl_xhi_wm : evmShl s3 x_hi < WORD_MOD := by
      rw [hshl_xhi]; exact Nat.mod_lt _ (by unfold WORD_MOD; omega)
    have hdiv_lt_s3 : x_lo / 2 ^ (256 - s3) < 2 ^ s3 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      calc x_lo < 2 ^ 256 := hxlo
        _ = 2 ^ s3 * 2 ^ (256 - s3) := by rw [← Nat.pow_add]; congr 1; omega
    have hshr_wm : evmShr (evmSub 256 s3) x_lo < WORD_MOD := by
      rw [hshr_eq2]; unfold WORD_MOD
      exact Nat.lt_of_lt_of_le hdiv_lt_s3 (Nat.pow_le_pow_right (by omega) (by omega))
    -- x_hi_1 = (x_hi * 2^256 + x_lo) * 2^s3 / 2^256 via shl_or_shr
    have hxhi1_eq : evmOr (evmShl s3 x_hi) (evmShr (evmSub 256 s3) x_lo) =
        (x_hi * 2 ^ 256 + x_lo) * 2 ^ s3 / 2 ^ 256 := by
      unfold evmOr u256
      rw [Nat.mod_eq_of_lt hshl_xhi_wm, Nat.mod_eq_of_lt hshr_wm,
          hshl_xhi, hshr_eq2]
      exact shl_or_shr x_hi x_lo s3 hs3_pos (by omega) hxhi_shl_lt hxlo
    -- x_lo_1 = (x_hi * 2^256 + x_lo) * 2^s3 % 2^256 via shl512_lo
    have hxlo1_eq : evmShl s3 x_lo = (x_hi * 2 ^ 256 + x_lo) * 2 ^ s3 % 2 ^ 256 := by
      rw [hshl_xlo]; unfold WORD_MOD; exact (shl512_lo x_hi x_lo s3).symm
    -- Reconstruction: x_hi_1 * 2^256 + x_lo_1 = (x * 2^s3) % 2^512
    -- Since x_hi_1 < 2^256 and x_lo_1 < 2^256, the sum < 2^512
    have hhi_val := shl512_hi x_hi x_lo s3 (by omega : s3 ≤ 255)
    have hhi_lt : (x_hi * 2 ^ 256 + x_lo) * 2 ^ s3 / 2 ^ 256 < 2 ^ 256 := by
      rw [hhi_val]
      calc x_hi * 2 ^ s3 + x_lo / 2 ^ (256 - s3)
          < x_hi * 2 ^ s3 + 2 ^ s3 := by omega
        _ = (x_hi + 1) * 2 ^ s3 := (Nat.succ_mul x_hi (2 ^ s3)).symm
        _ ≤ 2 ^ (Nat.log2 x_hi + 1) * 2 ^ s3 := Nat.mul_le_mul_right _ hL_hi
        _ = 2 ^ (Nat.log2 x_hi + 1 + s3) := (Nat.pow_add 2 _ s3).symm
        _ ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) hLs3_up
    have hlo_lt : (x_hi * 2 ^ 256 + x_lo) * 2 ^ s3 % 2 ^ 256 < 2 ^ 256 :=
      Nat.mod_lt _ (Nat.two_pow_pos 256)
    -- x * 2^s3 < 2^512, so mod 2^512 is identity
    have hprod_lt_512 : (x_hi * 2 ^ 256 + x_lo) * 2 ^ s3 < 2 ^ 512 := by
      -- Nat.div_add_mod: 2^256 * q + r = prod; q < 2^256, r < 2^256 ⟹ prod < 2^512
      have hdm := Nat.div_add_mod ((x_hi * 2 ^ 256 + x_lo) * 2 ^ s3) (2 ^ 256)
      rw [← hdm, show (2 : Nat) ^ 512 = 2 ^ 256 * 2 ^ 256 from by rw [← Nat.pow_add]]
      calc 2 ^ 256 * ((x_hi * 2 ^ 256 + x_lo) * 2 ^ s3 / 2 ^ 256) +
              (x_hi * 2 ^ 256 + x_lo) * 2 ^ s3 % 2 ^ 256
          < 2 ^ 256 * ((x_hi * 2 ^ 256 + x_lo) * 2 ^ s3 / 2 ^ 256 + 1) := by
            rw [Nat.mul_add, Nat.mul_one]; exact Nat.add_lt_add_left hlo_lt _
        _ ≤ 2 ^ 256 * 2 ^ 256 := Nat.mul_le_mul_left _ (by omega)
    have hrecon : (x_hi * 2 ^ 256 + x_lo) * 2 ^ s3 / 2 ^ 256 * 2 ^ 256 +
        (x_hi * 2 ^ 256 + x_lo) * 2 ^ s3 % 2 ^ 256 =
        (x_hi * 2 ^ 256 + x_lo) * 2 ^ s3 % 2 ^ 512 := by
      -- q * M + r = M * q + r = prod = prod % 2^512
      rw [Nat.mul_comm ((x_hi * 2 ^ 256 + x_lo) * 2 ^ s3 / 2 ^ 256) (2 ^ 256),
          Nat.div_add_mod, Nat.mod_eq_of_lt hprod_lt_512]
    -- Lower bound: 2^253 ≤ x_hi_1
    have hge_253 : 2 ^ 253 ≤ (x_hi * 2 ^ 256 + x_lo) * 2 ^ s3 / 2 ^ 256 := by
      rw [hhi_val]
      -- x_lo / 2^(256-s3) = x_lo * 2^s3 / 2^256
      have hdiv_rw : x_lo / 2 ^ (256 - s3) = x_lo * 2 ^ s3 / 2 ^ 256 := by
        rw [show 2 ^ 256 = 2 ^ (256 - s3) * 2 ^ s3
            from by rw [← Nat.pow_add]; congr 1; omega]
        exact (Nat.mul_div_mul_right _ _ (Nat.two_pow_pos s3)).symm
      rw [hdiv_rw]
      -- Now goal matches normalized_x_hi_ge_253's Nat form (before the mod)
      have hsum_lt := (normalized_x_hi_ge_253 x_hi x_lo hxhi_pos hxhi hxlo)
      simp only at hsum_lt
      -- The existing theorem uses (... ) % 2^256, but we showed sum < 2^256 so mod = id
      have hmod_id : (x_hi * 2 ^ s3 + x_lo * 2 ^ s3 / 2 ^ 256) % 2 ^ 256 =
          x_hi * 2 ^ s3 + x_lo * 2 ^ s3 / 2 ^ 256 := by
        rw [Nat.mod_eq_of_lt]; rw [hhi_val] at hhi_lt; omega
      rw [hmod_id] at hsum_lt; exact hsum_lt
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rw [hxhi1_eq, hxlo1_eq]; exact hrecon
    · rw [hxhi1_eq]; exact hge_253
    · rw [hxhi1_eq]; unfold WORD_MOD; exact hhi_lt
    · rw [hxlo1_eq]; unfold WORD_MOD; exact hlo_lt

end Cbrt512Spec
