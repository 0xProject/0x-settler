/-
  Bridge from model_cbrt512_evm to icbrt: specification layer.

  Part 1: EVM simplification lemmas (shared with wrapper/up specs).
  Part 2: Core algorithm bridge — model_cbrt512_evm within 1ulp of icbrt.
  Part 3: Composition with icbrt.

  Architecture: model_cbrt512_evm →[direct EVM bridge]→ icbrt ± 1

  Note: The auto-generated norm model (model_cbrt512) uses unbounded Nat operations
  which do NOT match EVM uint256 semantics. Therefore we prove the EVM model correct
  directly, without factoring through the norm model.
-/
import Cbrt512Proof.Cbrt512Correct
import Cbrt512Proof.GeneratedCbrt512Model
import Cbrt512Proof.CbrtDenormalization
import Cbrt512Proof.CbrtNormalization
import Cbrt512Proof.CbrtBaseCase
import Cbrt512Proof.CbrtKaratsubaQuotient
import Cbrt512Proof.CbrtComposition
import Cbrt512Proof.EvmBridge

namespace Cbrt512Spec

-- ============================================================================
-- Section 2: Core algorithm correctness
-- model_cbrt512_evm returns a value within 1ulp of icbrt for x_hi > 0.
-- ============================================================================

open Cbrt512GeneratedModel

-- ============================================================================
-- Helper 1: Normalization does not overflow 512 bits
-- ============================================================================

set_option exponentiation.threshold 1024 in
/-- The 512-bit normalization shift does not overflow: x * 2^(3*shift) < 2^512. -/
private theorem norm_no_overflow (x_hi x_lo : Nat)
    (hxhi_pos : 0 < x_hi) (hxhi : x_hi < 2 ^ 256) (hxlo : x_lo < 2 ^ 256) :
    (x_hi * 2 ^ 256 + x_lo) * 2 ^ (3 * (evmClz x_hi / 3)) < 2 ^ 512 := by
  have hxhi_wm : x_hi < WORD_MOD := by unfold WORD_MOD; exact hxhi
  have hne : x_hi ≠ 0 := Nat.ne_of_gt hxhi_pos
  have hL_hi : x_hi < 2 ^ (Nat.log2 x_hi + 1) := (Nat.log2_lt hne).mp (by omega)
  have hlog_le : Nat.log2 x_hi ≤ 255 := by
    have := (Nat.log2_lt hne).2 (by unfold WORD_MOD at hxhi_wm; exact hxhi_wm); omega
  have hLs3 : Nat.log2 x_hi + 1 + 3 * (evmClz x_hi / 3) ≤ 256 := by
    rw [evmClz_of_pos x_hi hxhi_pos hxhi_wm]; omega
  -- x < 2^(L+1+256)
  have hx_lt : x_hi * 2 ^ 256 + x_lo < 2 ^ (Nat.log2 x_hi + 1 + 256) := by
    calc x_hi * 2 ^ 256 + x_lo
        < (x_hi + 1) * 2 ^ 256 := by omega
      _ ≤ 2 ^ (Nat.log2 x_hi + 1) * 2 ^ 256 :=
          Nat.mul_le_mul_right _ hL_hi
      _ = 2 ^ (Nat.log2 x_hi + 1 + 256) := (Nat.pow_add 2 _ 256).symm
  -- x * 2^(3*shift) < 2^(L+1+256+3*shift) ≤ 2^512
  calc (x_hi * 2 ^ 256 + x_lo) * 2 ^ (3 * (evmClz x_hi / 3))
      < 2 ^ (Nat.log2 x_hi + 1 + 256) * 2 ^ (3 * (evmClz x_hi / 3)) :=
        Nat.mul_lt_mul_of_pos_right hx_lt (Nat.two_pow_pos _)
    _ = 2 ^ (Nat.log2 x_hi + 1 + 256 + 3 * (evmClz x_hi / 3)) :=
        (Nat.pow_add 2 _ _).symm
    _ ≤ 2 ^ 512 := Nat.pow_le_pow_right (by omega) (by omega)

-- ============================================================================
-- Helper 2: 3m² + 3m < 2^171 when m³ < 2^254
-- ============================================================================

set_option exponentiation.threshold 1024 in
/-- For icbrt of values < 2^254, the residue fits in 171 bits. -/
private theorem three_msq_plus_3m_lt (m : Nat)
    (hm_cube : m * m * m < 2 ^ 254) :
    3 * (m * m) + 3 * m < 2 ^ 171 := by
  -- Certificate: K³ ≥ 2^254, so m < K by cube_monotone
  have hK : 2 ^ 254 ≤ 30704801884924481767496090 * 30704801884924481767496090 *
      30704801884924481767496090 := by native_decide
  have hm_lt : m < 30704801884924481767496090 := by
    cases Nat.lt_or_ge m 30704801884924481767496090 with
    | inl h => exact h
    | inr hge =>
      exfalso
      exact Nat.lt_irrefl _
        (Nat.lt_of_lt_of_le hm_cube (Nat.le_trans hK (cube_monotone hge)))
  -- Certificate: 3*(K-1)²+3*(K-1) < 2^171
  have hm_le : m ≤ 30704801884924481767496089 := by omega
  have hcert : 3 * (30704801884924481767496089 * 30704801884924481767496089) +
      3 * 30704801884924481767496089 < 2 ^ 171 := by native_decide
  -- Monotonicity of 3x²+3x
  have h_mm : m * m ≤ 30704801884924481767496089 * 30704801884924481767496089 :=
    Nat.mul_le_mul hm_le hm_le
  calc 3 * (m * m) + 3 * m
      ≤ 3 * (30704801884924481767496089 * 30704801884924481767496089) +
        3 * 30704801884924481767496089 := by
        have := Nat.mul_le_mul_left 3 h_mm
        have := Nat.mul_le_mul_left 3 hm_le
        omega
    _ < 2 ^ 171 := hcert

-- ============================================================================
-- Helper 3: EVM pipeline on normalized inputs = Nat r_qc
-- ============================================================================

set_option exponentiation.threshold 1024 in
/-- The EVM pipeline (base case → Karatsuba → QC) on normalized inputs produces
    the same result as the Nat-level composition, hence satisfies within-1-ulp. -/
private theorem evm_pipeline_within_1ulp (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD) :
    let x_norm := x_hi_1 * 2 ^ 256 + x_lo_1
    let bc := model_cbrtBaseCase_evm x_hi_1
    let limb_hi := evmOr (evmShl 84 (evmAnd 3 x_hi_1)) (evmShr 172 x_lo_1)
    let r_lo_evm := model_cbrtKaratsubaQuotient_evm bc.2.1 limb_hi bc.2.2
    let r_1 := model_cbrtQuadraticCorrection_evm bc.1 r_lo_evm
    icbrt x_norm ≤ r_1 ∧ r_1 ≤ icbrt x_norm + 1 ∧
    r_1 < WORD_MOD ∧ r_1 * r_1 * r_1 < WORD_MOD * WORD_MOD ∧
    r_1 + 1 < WORD_MOD ∧
    (r_1 * r_1 * r_1 > x_norm →
      icbrt x_norm * icbrt x_norm * icbrt x_norm < x_norm) := by
  simp only
  -- ======== Step 1: Base case bridge ========
  have hbc := model_cbrtBaseCase_evm_correct x_hi_1 hxhi_lo hxhi_hi
  simp only at hbc
  -- Name the Nat values
  let w := x_hi_1 / 4
  let m := icbrt w
  -- Extract key equalities and bounds
  have hbc_m : (model_cbrtBaseCase_evm x_hi_1).1 = m := hbc.1
  have hbc_res : (model_cbrtBaseCase_evm x_hi_1).2.1 = w - m * m * m := hbc.2.1
  have hbc_d : (model_cbrtBaseCase_evm x_hi_1).2.2 = 3 * (m * m) := hbc.2.2.1
  have hm_lo : 2 ^ 83 ≤ m := hbc.2.2.2.1
  have hm_hi : m < 2 ^ 85 := hbc.2.2.2.2.1
  have hcube_le_w : m * m * m ≤ w := hbc.2.2.2.2.2.1
  have hres_bound : w - m * m * m ≤ 3 * (m * m) + 3 * m := hbc.2.2.2.2.2.2.1
  have hm_wm : m < WORD_MOD := hbc.2.2.2.2.2.2.2.1
  have hd_wm : 3 * (m * m) < WORD_MOD := hbc.2.2.2.2.2.2.2.2.2.1
  have hd_pos : 3 * (m * m) > 0 := hbc.2.2.2.2.2.2.2.2.2.2
  -- ======== Step 2: Limb_hi bridge ========
  have hlimb := limb_hi_correct x_hi_1 x_lo_1 hxhi_hi hxlo
  simp only at hlimb
  have hlimb_eq : evmOr (evmShl 84 (evmAnd 3 x_hi_1)) (evmShr 172 x_lo_1) =
      (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 := hlimb.1
  have hlimb_86 : (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86 := hlimb_eq ▸ hlimb.2.1
  have hlimb_wm : (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < WORD_MOD := hlimb_eq ▸ hlimb.2.2
  -- ======== Step 3: Karatsuba preconditions ========
  -- res < WORD_MOD
  have hw_lt : w < 2 ^ 254 := by unfold WORD_MOD at hxhi_hi; omega
  have hres_wm : w - m * m * m < WORD_MOD := by unfold WORD_MOD; omega
  -- m*m bounds
  have hmm_lo : 2 ^ 166 ≤ m * m := by
    calc 2 ^ 166 = 2 ^ 83 * 2 ^ 83 := by rw [← Nat.pow_add]
      _ ≤ m * m := Nat.mul_le_mul hm_lo hm_lo
  have hmm_hi : m * m < 2 ^ 170 :=
    calc m * m
        < m * 2 ^ 85 := Nat.mul_lt_mul_of_pos_left hm_hi (by omega)
      _ ≤ 2 ^ 85 * 2 ^ 85 := Nat.mul_le_mul_right _ (Nat.le_of_lt hm_hi)
      _ = 2 ^ 170 := by rw [← Nat.pow_add]
  -- d = 3m² ≥ 2^86 (since m² ≥ 2^166 >> 2^86)
  have hd_ge : 2 ^ 86 ≤ 3 * (m * m) := by
    have : 2 ^ 86 ≤ m * m :=
      Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega : 86 ≤ 166)) hmm_lo
    omega
  -- d = 3m² < 2^172 (since m² < 2^170, 3*2^170 < 4*2^170 = 2^172)
  have hd_hi : 3 * (m * m) < 2 ^ 172 := by
    have h172 : (2 : Nat) ^ 172 = 4 * 2 ^ 170 := by
      rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
    rw [h172]; omega
  -- res < 2^171 (from three_msq_plus_3m_lt)
  have hm_cube_lt : m * m * m < 2 ^ 254 :=
    Nat.lt_of_le_of_lt hcube_le_w hw_lt
  have h3m_lt := three_msq_plus_3m_lt m hm_cube_lt
  have hres_171 : w - m * m * m < 2 ^ 171 := by omega
  -- ======== Step 4: Apply Karatsuba bridge ========
  have hkq : model_cbrtKaratsubaQuotient_evm
      (model_cbrtBaseCase_evm x_hi_1).2.1
      (evmOr (evmShl 84 (evmAnd 3 x_hi_1)) (evmShr 172 x_lo_1))
      (model_cbrtBaseCase_evm x_hi_1).2.2 =
      ((w - m * m * m) * 2 ^ 86 + ((x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172)) /
        (3 * (m * m)) := by
    rw [hbc_res, hlimb_eq, hbc_d]
    exact model_cbrtKaratsubaQuotient_evm_correct
      (w - m * m * m) ((x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172) (3 * (m * m))
      hres_wm hlimb_wm hd_ge hd_hi hres_171 hlimb_86
  -- ======== Step 5: r_lo bound (< 2^87) ========
  -- From r_qc_lt_pow172 proof: res ≤ 2*(3m²) - 1, so (res*2^86+limb)/d < 2^87
  let nat_r_lo := ((w - m * m * m) * 2 ^ 86 +
      ((x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172)) / (3 * (m * m))
  have hr_lo_bound : nat_r_lo < 2 ^ 87 := by
    show ((w - m * m * m) * 2 ^ 86 +
        ((x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172)) / (3 * (m * m)) < 2 ^ 87
    rw [Nat.div_lt_iff_lt_mul hd_pos]
    have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    calc (w - m * m * m) * 2 ^ 86 +
            ((x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172)
        < ((w - m * m * m) + 1) * 2 ^ 86 := by omega
      _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by
          apply Nat.mul_le_mul_right; omega
      _ ≤ (2 * (3 * (m * m))) * 2 ^ 86 := by
          apply Nat.mul_le_mul_right; omega
      _ = 2 ^ 87 * (3 * (m * m)) := by
          rw [show (2 : Nat) ^ 87 = 2 * 2 ^ 86 from by
            rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]]; omega
  have hr_lo_wm : nat_r_lo < WORD_MOD := by unfold WORD_MOD; omega
  -- ======== Step 6: QC bridge ========
  have hqc := model_cbrtQuadraticCorrection_evm_correct m nat_r_lo
      hm_wm hr_lo_wm (by omega : 2 ≤ m) hm_hi hr_lo_bound
  have hqc_eq : model_cbrtQuadraticCorrection_evm
      (model_cbrtBaseCase_evm x_hi_1).1
      (model_cbrtKaratsubaQuotient_evm
        (model_cbrtBaseCase_evm x_hi_1).2.1
        (evmOr (evmShl 84 (evmAnd 3 x_hi_1)) (evmShr 172 x_lo_1))
        (model_cbrtBaseCase_evm x_hi_1).2.2) =
      m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86) := by
    rw [hbc_m, hkq]; exact hqc.1
  -- ======== Step 7: Composition ========
  have hcomp := composition_within_1ulp x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  simp only at hcomp
  -- After simp only, hcomp talks about the same Nat expression
  -- Rewrite EVM pipeline to Nat in goal
  rw [hqc_eq]
  exact hcomp

/-- The 512-bit _cbrt EVM model returns a value within 1ulp of icbrt.
    For x_hi > 0 and both x_hi, x_lo < 2^256:
      icbrt(x_hi * 2^256 + x_lo) ≤ r ≤ icbrt(x_hi * 2^256 + x_lo) + 1
    and r < WORD_MOD, r³ < WORD_MOD² (so cube512_correct applies).
    Additionally, when r overshoots (r³ > x), x is not a perfect cube.
    This ensures the cbrtUp wrapper's cube-and-compare correction is sound. -/
theorem model_cbrt512_evm_within_1ulp (x_hi x_lo : Nat)
    (hxhi_pos : 0 < x_hi) (hxhi : x_hi < 2 ^ 256) (hxlo : x_lo < 2 ^ 256) :
    let x := x_hi * 2 ^ 256 + x_lo
    let r := model_cbrt512_evm x_hi x_lo
    icbrt x ≤ r ∧ r ≤ icbrt x + 1 ∧ r < WORD_MOD ∧ r * r * r < WORD_MOD * WORD_MOD
    ∧ r + 1 < WORD_MOD
    ∧ (r * r * r > x → icbrt x * icbrt x * icbrt x < x) := by
  simp only
  -- ======== WM bounds and u256 stripping ========
  have hxhi_wm : x_hi < WORD_MOD := by unfold WORD_MOD; exact hxhi
  have hxlo_wm : x_lo < WORD_MOD := by unfold WORD_MOD; exact hxlo
  have hu_xhi : u256 x_hi = x_hi := u256_id' x_hi hxhi_wm
  have hu_xlo : u256 x_lo = x_lo := u256_id' x_lo hxlo_wm
  -- ======== Normalization ========
  have h_norm := evm_normalization_correct x_hi x_lo hxhi_pos hxhi hxlo
  simp only at h_norm
  obtain ⟨h_shift_eq, h_s3_eq, h_recon, h_ge253, h_xhi1_wm, h_xlo1_wm⟩ := h_norm
  -- Name EVM normalization values (definitionally transparent)
  let shift := evmDiv (evmClz x_hi) 3
  let s3 := evmMul shift 3
  let x_hi_1 := evmOr (evmShl s3 x_hi) (evmShr (evmSub 256 s3) x_lo)
  let x_lo_1 := evmShl s3 x_lo
  -- shift = evmClz x_hi / 3 < 86
  have hshift_lt := shift_lt_86 x_hi hxhi_pos hxhi_wm
  -- No overflow → reconstruction is exact
  have h_no_ovf := norm_no_overflow x_hi x_lo hxhi_pos hxhi hxlo
  have h_recon_exact : x_hi_1 * 2 ^ 256 + x_lo_1 =
      (x_hi * 2 ^ 256 + x_lo) * 2 ^ (3 * (evmClz x_hi / 3)) := by
    show x_hi_1 * 2 ^ 256 + x_lo_1 =
        (x_hi * 2 ^ 256 + x_lo) * 2 ^ (3 * (evmClz x_hi / 3))
    rw [h_recon, Nat.mod_eq_of_lt h_no_ovf]
  -- ======== EVM pipeline on normalized inputs ========
  have h_pipe := evm_pipeline_within_1ulp x_hi_1 x_lo_1 h_ge253 h_xhi1_wm h_xlo1_wm
  simp only at h_pipe
  obtain ⟨h_lo, h_hi, h_r1_wm, h_r1_cube, h_r1_succ, h_r1_overshoot⟩ := h_pipe
  -- Name the pipeline result
  let r_1 := model_cbrtQuadraticCorrection_evm
      (model_cbrtBaseCase_evm x_hi_1).1
      (model_cbrtKaratsubaQuotient_evm
        (model_cbrtBaseCase_evm x_hi_1).2.1
        (evmOr (evmShl 84 (evmAnd 3 x_hi_1)) (evmShr 172 x_lo_1))
        (model_cbrtBaseCase_evm x_hi_1).2.2)
  -- ======== Connect model to pipeline ========
  -- model_cbrt512_evm x_hi x_lo = evmShr shift r_1 (by definitional unfolding)
  have h_model_eq : model_cbrt512_evm x_hi x_lo = evmShr shift r_1 := by
    unfold model_cbrt512_evm
    rw [hu_xhi, hu_xlo]
  -- evmShr shift r_1 = r_1 / 2^(evmClz x_hi / 3)
  have hshift_lt_256 : (evmClz x_hi / 3 : Nat) < 256 := by omega
  have h_shr_eq : evmShr shift r_1 = r_1 / 2 ^ (evmClz x_hi / 3) := by
    show evmShr (evmDiv (evmClz x_hi) 3) r_1 = r_1 / 2 ^ (evmClz x_hi / 3)
    rw [h_shift_eq]; exact evmShr_eq' _ r_1 hshift_lt_256 h_r1_wm
  -- Combined: model = r_1 / 2^shift_nat
  let shift_nat := evmClz x_hi / 3
  have h_model_div : model_cbrt512_evm x_hi x_lo = r_1 / 2 ^ shift_nat := by
    rw [h_model_eq, h_shr_eq]
  -- ======== Rewrite x_norm = x * 2^(3*shift_nat) ========
  -- h_recon_exact says x_hi_1 * 2^256 + x_lo_1 = x * 2^(3*shift_nat)
  -- Rewrite pipeline results to use x instead of x_hi_1 * 2^256 + x_lo_1
  rw [h_recon_exact] at h_lo h_hi h_r1_overshoot
  -- Now h_lo: icbrt(x * 2^(3*shift_nat)) ≤ r_1
  -- And h_hi: r_1 ≤ icbrt(x * 2^(3*shift_nat)) + 1
  -- ======== Denormalization ========
  let x := x_hi * 2 ^ 256 + x_lo
  -- within_1ulp_denorm gives icbrt(x) ≤ r_1/2^k ≤ icbrt(x)+1
  have h_denorm := within_1ulp_denorm x shift_nat r_1 h_lo h_hi
  -- r = r_1 / 2^shift_nat
  rw [h_model_div]
  refine ⟨h_denorm.1, h_denorm.2, ?_, ?_, ?_, ?_⟩
  · -- r < WORD_MOD: r ≤ r_1 (division reduces) and r_1 < WORD_MOD
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h_r1_wm
  · -- r³ < WORD_MOD²: r ≤ r_1, so r³ ≤ r_1³ < WORD_MOD²
    have hr_le : r_1 / 2 ^ shift_nat ≤ r_1 := Nat.div_le_self _ _
    exact Nat.lt_of_le_of_lt (cube_monotone hr_le) h_r1_cube
  · -- r + 1 < WORD_MOD: r ≤ r_1 and r_1 + 1 < WORD_MOD
    have hr_le : r_1 / 2 ^ shift_nat ≤ r_1 := Nat.div_le_self _ _
    omega
  · -- Overshoot: r³ > x → icbrt(x)³ < x
    intro h_over
    -- Need: r_1³ > x_norm, then pipeline gives icbrt(x_norm)³ < x_norm,
    -- then overshoot_denorm gives icbrt(x)³ < x
    -- Step 1: (r * 2^k)³ = r³ * 2^(3k) (cube_mul_pow reproved inline)
    have h_div_mul : r_1 / 2 ^ shift_nat * 2 ^ shift_nat ≤ r_1 :=
      Nat.div_mul_le_self r_1 (2 ^ shift_nat)
    -- Step 2: (r*2^k)³ ≤ r_1³
    have h_cube_le := cube_monotone h_div_mul
    -- Step 3: r³ * 2^(3*k) > x * 2^(3*k) (from r³ > x)
    have h_scaled : x * 2 ^ (3 * shift_nat) <
        (r_1 / 2 ^ shift_nat) * (r_1 / 2 ^ shift_nat) * (r_1 / 2 ^ shift_nat) *
        2 ^ (3 * shift_nat) := by
      exact Nat.mul_lt_mul_of_pos_right h_over (Nat.two_pow_pos _)
    -- Step 4: (a*b)*(a*b)*(a*b) = a*a*a * (b*b*b)
    have h_cube_factor : ∀ a b : Nat,
        (a * b) * (a * b) * (a * b) = a * a * a * (b * b * b) := by
      intro a b
      suffices hi : (↑((a * b) * (a * b) * (a * b)) : Int) =
          ↑(a * a * a * (b * b * b)) by exact_mod_cast hi
      push_cast; simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have h_pow_cube : 2 ^ shift_nat * 2 ^ shift_nat * 2 ^ shift_nat =
        2 ^ (3 * shift_nat) := by
      rw [show 3 * shift_nat = shift_nat + shift_nat + shift_nat from by omega,
          Nat.pow_add, Nat.pow_add]
    -- Step 5: Combine: (r*2^k)³ = r³ * 2^(3k) > x * 2^(3k) = x_norm
    -- and (r*2^k)³ ≤ r_1³, so r_1³ > x_norm
    rw [h_cube_factor] at h_cube_le
    rw [h_pow_cube] at h_cube_le
    -- h_cube_le : r_1/2^k * r_1/2^k * r_1/2^k * 2^(3k) ≤ r_1 * r_1 * r_1
    -- h_scaled : x * 2^(3k) < r/2^k * r/2^k * r/2^k * 2^(3k)
    -- Therefore: x * 2^(3k) < r_1 * r_1 * r_1
    have h_r1_over : x * 2 ^ (3 * shift_nat) < r_1 * r_1 * r_1 :=
      Nat.lt_of_lt_of_le h_scaled h_cube_le
    -- Apply pipeline overshoot
    have h_norm_over := h_r1_overshoot h_r1_over
    -- Apply overshoot_denorm
    exact overshoot_denorm x shift_nat h_norm_over

end Cbrt512Spec
