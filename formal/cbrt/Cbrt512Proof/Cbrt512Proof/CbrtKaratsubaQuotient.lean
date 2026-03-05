/-
  Karatsuba quotient: model_cbrtKaratsubaQuotient_evm(res, limb_hi, d) computes
  both floor((res * 2^86 + limb_hi) / d) and (res * 2^86 + limb_hi) % d,
  even when res * 2^86 + limb_hi overflows 256 bits.

  The carry branch handles overflow: when res >> 170 ≠ 0, the dividend n has
  257+ bits. The three-part decomposition computes floor((WORD_MOD + n_evm) / d).

  Also proves limb_hi extraction: the next 86 bits of x_norm after the base case.
-/
import Cbrt512Proof.GeneratedCbrt512Model
import Cbrt512Proof.EvmBridge

namespace Cbrt512Spec

open Cbrt512GeneratedModel

-- ============================================================================
-- limb_hi extraction
-- ============================================================================

/-- The limb_hi extraction correctly picks out 86 bits:
    limb_hi = evmOr(evmShl(84, evmAnd(3, x_hi_1)), evmShr(172, x_lo_1))
    equals (x_hi_1 % 4) * 2^84 + x_lo_1 / 2^172. -/
theorem limb_hi_correct (x_hi_1 x_lo_1 : Nat)
    (hxhi : x_hi_1 < WORD_MOD) (hxlo : x_lo_1 < WORD_MOD) :
    let limb_hi := evmOr (evmShl 84 (evmAnd 3 x_hi_1)) (evmShr 172 x_lo_1)
    limb_hi = (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 ∧
    limb_hi < 2 ^ 86 ∧
    limb_hi < WORD_MOD := by
  simp only
  -- Step 1: evmAnd 3 x_hi_1 = x_hi_1 % 4
  have h3_wm : (3 : Nat) < WORD_MOD := by unfold WORD_MOD; omega
  have hand : evmAnd 3 x_hi_1 = x_hi_1 % 4 := by
    unfold evmAnd u256
    simp [Nat.mod_eq_of_lt h3_wm, Nat.mod_eq_of_lt hxhi]
    rw [Nat.and_comm]
    exact Nat.and_two_pow_sub_one_eq_mod x_hi_1 2
  have hmod4 : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
  have hmod4_wm : x_hi_1 % 4 < WORD_MOD := by unfold WORD_MOD; omega
  -- Step 2: evmShl 84 (evmAnd 3 x_hi_1) = (x_hi_1 % 4) * 2^84
  have hprod_lt : (x_hi_1 % 4) * 2 ^ 84 < 2 ^ 86 :=
    calc (x_hi_1 % 4) * 2 ^ 84
        < 4 * 2 ^ 84 := Nat.mul_lt_mul_of_pos_right hmod4 (Nat.two_pow_pos 84)
      _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
  have hprod_wm : (x_hi_1 % 4) * 2 ^ 84 < WORD_MOD :=
    Nat.lt_of_lt_of_le hprod_lt
      (by unfold WORD_MOD; exact Nat.pow_le_pow_right (by omega) (by omega))
  have hshl : evmShl 84 (evmAnd 3 x_hi_1) = (x_hi_1 % 4) * 2 ^ 84 := by
    rw [hand]; unfold evmShl u256
    simp [Nat.mod_eq_of_lt (show (84 : Nat) < WORD_MOD from by unfold WORD_MOD; omega),
          Nat.mod_eq_of_lt hmod4_wm, show (84 : Nat) < 256 from by omega]
    exact Nat.mod_eq_of_lt hprod_wm
  -- Step 3: evmShr 172 x_lo_1 = x_lo_1 / 2^172
  have hshr : evmShr 172 x_lo_1 = x_lo_1 / 2 ^ 172 := by
    unfold evmShr u256
    simp [Nat.mod_eq_of_lt (show (172 : Nat) < WORD_MOD from by unfold WORD_MOD; omega),
          Nat.mod_eq_of_lt hxlo, show (172 : Nat) < 256 from by omega]
  have hdiv_lt : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 172)]
    calc x_lo_1 < WORD_MOD := hxlo
      _ = 2 ^ 84 * 2 ^ 172 := by unfold WORD_MOD; rw [← Nat.pow_add]
  have hdiv_wm : x_lo_1 / 2 ^ 172 < WORD_MOD :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hxlo
  -- Step 4: evmOr with disjoint bits = addition
  have hor : evmOr (evmShl 84 (evmAnd 3 x_hi_1)) (evmShr 172 x_lo_1) =
      (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 := by
    rw [hshl, hshr]; unfold evmOr u256
    simp [Nat.mod_eq_of_lt hprod_wm, Nat.mod_eq_of_lt hdiv_wm]
    rw [show (x_hi_1 % 4) * 2 ^ 84 = (x_hi_1 % 4) <<< 84 from (Nat.shiftLeft_eq _ _).symm]
    exact (Nat.shiftLeft_add_eq_or_of_lt hdiv_lt (x_hi_1 % 4)).symm
  -- Step 5: bounds
  have hsum_lt : (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86 :=
    calc (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
        < (x_hi_1 % 4) * 2 ^ 84 + 2 ^ 84 := Nat.add_lt_add_left hdiv_lt _
      _ = ((x_hi_1 % 4) + 1) * 2 ^ 84 := (Nat.succ_mul _ _).symm
      _ ≤ 4 * 2 ^ 84 := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
  have hsum_wm : (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < WORD_MOD :=
    Nat.lt_of_lt_of_le hsum_lt
      (by unfold WORD_MOD; exact Nat.pow_le_pow_right (by omega) (by omega))
  rw [hor]; exact ⟨rfl, hsum_lt, hsum_wm⟩

-- ============================================================================
-- Helper lemmas
-- ============================================================================

/-- Euclidean division after recomposition: (d*q + r)/d = q + r/d -/
private theorem div_of_mul_add (d q r : Nat) (hd : 0 < d) :
    (d * q + r) / d = q + r / d := by
  rw [show d * q + r = r + q * d from by rw [Nat.mul_comm, Nat.add_comm],
      Nat.add_mul_div_right r q hd, Nat.add_comm]

/-- Euclidean mod after recomposition: (d*q + r) % d = r % d -/
private theorem mod_of_mul_add (d q r : Nat) (hd : 0 < d) :
    (d * q + r) % d = r % d := by
  rw [show d * q + r = r + q * d from by rw [Nat.mul_comm, Nat.add_comm],
      Nat.add_mul_mod_self_right]

/-- (a * k) % (n * k) = (a % n) * k -/
private theorem mul_mod_mul_right (a n k : Nat) (hk : 0 < k) (hn : 0 < n) :
    (a * k) % (n * k) = (a % n) * k := by
  -- Rewrite a * k = (a%n)*k + (a/n)*(n*k)  via Euclidean decomposition of a
  have hrw : a * k = (a % n) * k + (a / n) * (n * k) := by
    have h := Nat.div_add_mod a n  -- n * (a/n) + a%n = a
    calc a * k
        = (n * (a / n) + a % n) * k := by rw [h]
      _ = n * (a / n) * k + a % n * k := Nat.add_mul _ _ _
      _ = (a / n) * (n * k) + a % n * k := by
            rw [Nat.mul_comm n (a / n), Nat.mul_assoc]
      _ = a % n * k + (a / n) * (n * k) := Nat.add_comm _ _
  rw [hrw, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (Nat.mul_lt_mul_of_pos_right (Nat.mod_lt a hn) hk)]

/-- (a * 2^86) % WORD_MOD = (a % 2^170) * 2^86, since WORD_MOD = 2^170 * 2^86 -/
private theorem mul_pow86_mod_word (a : Nat) :
    (a * 2 ^ 86) % WORD_MOD = (a % 2 ^ 170) * 2 ^ 86 := by
  have h_wm : WORD_MOD = 2 ^ 170 * 2 ^ 86 := by unfold WORD_MOD; rw [← Nat.pow_add]
  rw [h_wm]; exact mul_mod_mul_right a (2 ^ 170) (2 ^ 86) (Nat.two_pow_pos 86) (Nat.two_pow_pos 170)

-- ============================================================================
-- Shared setup for both carry and no-carry proofs
-- ============================================================================

/-- Shared derived bounds and EVM simplifications for the Karatsuba quotient proof. -/
private structure KQContext (res limb_hi d : Nat) where
  hd_pos : 0 < d
  hd_wm : d < WORD_MOD
  h_wm_sq : WORD_MOD = 2 ^ 170 * 2 ^ 86
  hn_evm_lt : (res % 2 ^ 170) * 2 ^ 86 + limb_hi < WORD_MOD

-- ============================================================================
-- Karatsuba quotient correctness (.1 = quotient)
-- ============================================================================

/-- The first component of the Karatsuba quotient computes floor((res * 2^86 + limb_hi) / d). -/
private theorem kq_fst_correct
    (res limb_hi d : Nat)
    (hres : res < WORD_MOD) (hlimb : limb_hi < WORD_MOD)
    (hd_ge : 2 ^ 86 ≤ d) (hd_bound : d < 2 ^ 172)
    (hres_bound : res < 2 ^ 171)
    (hlimb_bound : limb_hi < 2 ^ 86) :
    (model_cbrtKaratsubaQuotient_evm res limb_hi d).1 =
      (res * 2 ^ 86 + limb_hi) / d := by
  -- Derived bounds
  have hd_pos : 0 < d := by omega
  have hd_wm : d < WORD_MOD := by unfold WORD_MOD; omega
  have h2d_wm : 2 * d < WORD_MOD := by unfold WORD_MOD; omega
  have h_wm_sq : WORD_MOD = 2 ^ 170 * 2 ^ 86 := by unfold WORD_MOD; rw [← Nat.pow_add]
  -- n_evm components
  have hres_mod_lt : res % 2 ^ 170 < 2 ^ 170 := Nat.mod_lt _ (Nat.two_pow_pos 170)
  have hn_hi_lt : (res % 2 ^ 170) * 2 ^ 86 < WORD_MOD := by
    rw [h_wm_sq]; exact Nat.mul_lt_mul_of_pos_right hres_mod_lt (Nat.two_pow_pos 86)
  have hlimb_wm : limb_hi < WORD_MOD := by unfold WORD_MOD; omega
  have hn_evm_lt : (res % 2 ^ 170) * 2 ^ 86 + limb_hi < WORD_MOD := by
    calc (res % 2 ^ 170) * 2 ^ 86 + limb_hi
        < (res % 2 ^ 170) * 2 ^ 86 + 2 ^ 86 := by omega
      _ = ((res % 2 ^ 170) + 1) * 2 ^ 86 := (Nat.succ_mul _ _).symm
      _ ≤ 2 ^ 170 * 2 ^ 86 := Nat.mul_le_mul_right _ (by omega)
      _ = WORD_MOD := h_wm_sq.symm
  -- EVM simplifications
  have hres_u : u256 res = res := u256_id' res hres
  have hlimb_u : u256 limb_hi = limb_hi := u256_id' limb_hi hlimb
  have hd_u : u256 d = d := u256_id' d hd_wm
  have hshl_res : evmShl 86 res = (res % 2 ^ 170) * 2 ^ 86 := by
    rw [evmShl_eq' 86 res (by omega) hres]; exact mul_pow86_mod_word res
  -- OR = addition (bits disjoint)
  have hor_eq : evmOr ((res % 2 ^ 170) * 2 ^ 86) limb_hi =
      (res % 2 ^ 170) * 2 ^ 86 + limb_hi := by
    rw [evmOr_eq' _ _ hn_hi_lt hlimb_wm]
    rw [show (res % 2 ^ 170) * 2 ^ 86 = (res % 2 ^ 170) <<< 86 from (Nat.shiftLeft_eq _ _).symm]
    exact (Nat.shiftLeft_add_eq_or_of_lt hlimb_bound (res % 2 ^ 170)).symm
  -- Carry condition
  have hc_eq : evmShr 170 res = res / 2 ^ 170 := evmShr_eq' 170 res (by omega) hres
  -- The .1 projection: after resolving (r_lo, rem), .1 picks out r_lo
  -- In the carry case, r_lo is the quotient chain; in no-carry, r_lo_1 = evmDiv n d
  unfold model_cbrtKaratsubaQuotient_evm
  simp only [hres_u, hlimb_u, hd_u, hshl_res, hc_eq, hor_eq]
  split
  · -- === CARRY CASE: res / 2^170 ≠ 0 ===
    next hc_ne =>
    -- res / 2^170 = 1 (from 2^170 ≤ res < 2^171)
    have hres_ge : 2 ^ 170 ≤ res := by
      have h := Nat.pos_of_ne_zero hc_ne
      have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos 170)).mp h
      omega
    have hc_one : res / 2 ^ 170 = 1 := by
      have hc_le : res / 2 ^ 170 ≤ 1 :=
        Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 170)).mpr (by omega))
      omega
    -- n_full = WORD_MOD + n_evm
    have hn_full_eq : res * 2 ^ 86 + limb_hi =
        (res % 2 ^ 170) * 2 ^ 86 + limb_hi + WORD_MOD := by
      have hdm := Nat.div_add_mod res (2 ^ 170)
      rw [hc_one] at hdm; rw [h_wm_sq]; omega
    -- Simplify EVM div/mod on n_evm
    have hn_div : evmDiv ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) d =
        ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d :=
      evmDiv_eq' _ d hn_evm_lt hd_pos hd_wm
    have hn_mod : evmMod ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) d =
        ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d :=
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
    -- evmAdd 1 ((WORD_MOD-1) % d) = 1 + (WORD_MOD-1) % d
    have hrw_lt : (WORD_MOD - 1) % d < d := Nat.mod_lt _ hd_pos
    have hrw_wm : (WORD_MOD - 1) % d < WORD_MOD := Nat.lt_of_lt_of_le hrw_lt (by omega)
    have h1_wm : (1 : Nat) < WORD_MOD := by unfold WORD_MOD; omega
    have h1rw_sum : 1 + (WORD_MOD - 1) % d < WORD_MOD :=
      Nat.lt_of_le_of_lt (by omega : 1 + (WORD_MOD - 1) % d ≤ d) hd_wm
    have hadd_1_rw : evmAdd 1 ((WORD_MOD - 1) % d) = 1 + (WORD_MOD - 1) % d :=
      evmAdd_eq' 1 _ h1_wm hrw_wm h1rw_sum
    simp only [hadd_1_rw]
    -- evmAdd (n_evm%d) (1 + (WORD_MOD-1)%d) = remainder_sum
    have hr0_lt : ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d < d := Nat.mod_lt _ hd_pos
    have hr0_wm : ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d < WORD_MOD :=
      Nat.lt_of_lt_of_le hr0_lt (by omega)
    have hR_sum : ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d) < WORD_MOD :=
      Nat.lt_of_lt_of_le (by omega : _ < 2 * d) (by omega)
    have hstep2 : evmAdd (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d) (1 + (WORD_MOD - 1) % d) =
        ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d) :=
      evmAdd_eq' _ _ hr0_wm h1rw_sum hR_sum
    simp only [hstep2]
    -- evmDiv remainder_sum d
    have hR_lt2d : ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d) < 2 * d := by omega
    have hR_wm := hR_sum
    have hdiv_R : evmDiv (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d)) d =
        (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d)) / d :=
      evmDiv_eq' _ d hR_wm hd_pos hd_wm
    simp only [hdiv_R]
    -- evmAdd (n_evm/d) ((WORD_MOD-1)/d) = quotient_sum
    have hq0_wm : ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d < WORD_MOD :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn_evm_lt
    have hqw_wm : (WORD_MOD - 1) / d < WORD_MOD :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hnot_wm
    have hq0_170 : ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d < 2 ^ 170 :=
      (Nat.div_lt_iff_lt_mul hd_pos).mpr (Nat.lt_of_lt_of_le hn_evm_lt
        (by rw [h_wm_sq]; exact Nat.mul_le_mul_left _ hd_ge))
    have hqw_170 : (WORD_MOD - 1) / d < 2 ^ 170 :=
      (Nat.div_lt_iff_lt_mul hd_pos).mpr (Nat.lt_of_lt_of_le hnot_wm
        (by rw [h_wm_sq]; exact Nat.mul_le_mul_left _ hd_ge))
    have h171_le_wm : (2 : Nat) ^ 171 ≤ WORD_MOD := by
      unfold WORD_MOD; exact Nat.pow_le_pow_right (by omega) (by omega)
    have hq0qw_sum : ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d + (WORD_MOD - 1) / d < WORD_MOD :=
      Nat.lt_of_lt_of_le (by omega : _ < 2 ^ 171) h171_le_wm
    have hstep1 : evmAdd (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d) ((WORD_MOD - 1) / d) =
        ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d + (WORD_MOD - 1) / d :=
      evmAdd_eq' _ _ hq0_wm hqw_wm hq0qw_sum
    simp only [hstep1]
    -- evmAdd quotient_sum (remainder_sum / d) = final result
    have hR_div_le1 : (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d)) / d ≤ 1 :=
      Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hd_pos).mpr hR_lt2d)
    have hR_div_wm : (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d)) / d < WORD_MOD :=
      Nat.lt_of_le_of_lt hR_div_le1 (by unfold WORD_MOD; omega)
    have hfinal_sum : ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d + (WORD_MOD - 1) / d +
        (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d)) / d < WORD_MOD :=
      Nat.lt_of_lt_of_le (by omega : _ < 2 ^ 171 + 1) (by omega : 2 ^ 171 + 1 ≤ WORD_MOD)
    have hstep3 : evmAdd (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d + (WORD_MOD - 1) / d)
        ((((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d)) / d) =
        ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d + (WORD_MOD - 1) / d +
        (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d)) / d :=
      evmAdd_eq' _ _ hq0qw_sum hR_div_wm hfinal_sum
    simp only [hstep3]
    -- === Now the goal is pure Nat: show these equal n_full / d ===
    have hn_full_decomp : res * 2 ^ 86 + limb_hi =
        d * (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d + (WORD_MOD - 1) / d) +
        (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d)) := by
      rw [hn_full_eq]
      have h1 := (Nat.div_add_mod ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) d).symm
      have h2 := (Nat.div_add_mod (WORD_MOD - 1) d).symm
      rw [Nat.mul_add]; omega
    rw [hn_full_decomp]
    exact (div_of_mul_add d _ _ hd_pos).symm
  · -- === NO-CARRY CASE: res / 2^170 = 0 ===
    next hc_not =>
    have hc_zero : res / 2 ^ 170 = 0 := Decidable.byContradiction hc_not
    have hres_small : res < 2 ^ 170 := by
      cases Nat.lt_or_ge res (2 ^ 170) with
      | inl h => exact h
      | inr h =>
        have : 0 < res / 2 ^ 170 := Nat.div_pos h (Nat.two_pow_pos 170)
        omega
    have hmod_res : res % 2 ^ 170 = res := Nat.mod_eq_of_lt hres_small
    have hn_eq : (res % 2 ^ 170) * 2 ^ 86 + limb_hi = res * 2 ^ 86 + limb_hi := by
      rw [hmod_res]
    rw [hn_eq, evmDiv_eq' _ d (by rw [← hn_eq]; exact hn_evm_lt) hd_pos hd_wm]

-- ============================================================================
-- Karatsuba quotient correctness (.2 = remainder)
-- ============================================================================

/-- The second component of the Karatsuba quotient computes (res * 2^86 + limb_hi) % d. -/
private theorem kq_snd_correct
    (res limb_hi d : Nat)
    (hres : res < WORD_MOD) (hlimb : limb_hi < WORD_MOD)
    (hd_ge : 2 ^ 86 ≤ d) (hd_bound : d < 2 ^ 172)
    (hres_bound : res < 2 ^ 171)
    (hlimb_bound : limb_hi < 2 ^ 86) :
    (model_cbrtKaratsubaQuotient_evm res limb_hi d).2 =
      (res * 2 ^ 86 + limb_hi) % d := by
  -- Derived bounds
  have hd_pos : 0 < d := by omega
  have hd_wm : d < WORD_MOD := by unfold WORD_MOD; omega
  have h2d_wm : 2 * d < WORD_MOD := by unfold WORD_MOD; omega
  have h_wm_sq : WORD_MOD = 2 ^ 170 * 2 ^ 86 := by unfold WORD_MOD; rw [← Nat.pow_add]
  -- n_evm components
  have hres_mod_lt : res % 2 ^ 170 < 2 ^ 170 := Nat.mod_lt _ (Nat.two_pow_pos 170)
  have hn_hi_lt : (res % 2 ^ 170) * 2 ^ 86 < WORD_MOD := by
    rw [h_wm_sq]; exact Nat.mul_lt_mul_of_pos_right hres_mod_lt (Nat.two_pow_pos 86)
  have hlimb_wm : limb_hi < WORD_MOD := by unfold WORD_MOD; omega
  have hn_evm_lt : (res % 2 ^ 170) * 2 ^ 86 + limb_hi < WORD_MOD := by
    calc (res % 2 ^ 170) * 2 ^ 86 + limb_hi
        < (res % 2 ^ 170) * 2 ^ 86 + 2 ^ 86 := by omega
      _ = ((res % 2 ^ 170) + 1) * 2 ^ 86 := (Nat.succ_mul _ _).symm
      _ ≤ 2 ^ 170 * 2 ^ 86 := Nat.mul_le_mul_right _ (by omega)
      _ = WORD_MOD := h_wm_sq.symm
  -- EVM simplifications
  have hres_u : u256 res = res := u256_id' res hres
  have hlimb_u : u256 limb_hi = limb_hi := u256_id' limb_hi hlimb
  have hd_u : u256 d = d := u256_id' d hd_wm
  have hshl_res : evmShl 86 res = (res % 2 ^ 170) * 2 ^ 86 := by
    rw [evmShl_eq' 86 res (by omega) hres]; exact mul_pow86_mod_word res
  have hor_eq : evmOr ((res % 2 ^ 170) * 2 ^ 86) limb_hi =
      (res % 2 ^ 170) * 2 ^ 86 + limb_hi := by
    rw [evmOr_eq' _ _ hn_hi_lt hlimb_wm]
    rw [show (res % 2 ^ 170) * 2 ^ 86 = (res % 2 ^ 170) <<< 86 from (Nat.shiftLeft_eq _ _).symm]
    exact (Nat.shiftLeft_add_eq_or_of_lt hlimb_bound (res % 2 ^ 170)).symm
  have hc_eq : evmShr 170 res = res / 2 ^ 170 := evmShr_eq' 170 res (by omega) hres
  unfold model_cbrtKaratsubaQuotient_evm
  simp only [hres_u, hlimb_u, hd_u, hshl_res, hc_eq, hor_eq]
  split
  · -- === CARRY CASE ===
    next hc_ne =>
    have hres_ge : 2 ^ 170 ≤ res := by
      have h := Nat.pos_of_ne_zero hc_ne
      have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos 170)).mp h
      omega
    have hc_one : res / 2 ^ 170 = 1 := by
      have hc_le : res / 2 ^ 170 ≤ 1 :=
        Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 170)).mpr (by omega))
      omega
    have hn_full_eq : res * 2 ^ 86 + limb_hi =
        (res % 2 ^ 170) * 2 ^ 86 + limb_hi + WORD_MOD := by
      have hdm := Nat.div_add_mod res (2 ^ 170)
      rw [hc_one] at hdm; rw [h_wm_sq]; omega
    -- Simplify EVM ops
    have hn_mod : evmMod ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) d =
        ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d :=
      evmMod_eq' _ d hn_evm_lt hd_pos hd_wm
    have hnot_eq : evmNot 0 = WORD_MOD - 1 :=
      evmNot_eq' 0 (by unfold WORD_MOD; omega)
    have hnot_wm : WORD_MOD - 1 < WORD_MOD := by omega
    have hwm_mod : evmMod (WORD_MOD - 1) d = (WORD_MOD - 1) % d :=
      evmMod_eq' _ d hnot_wm hd_pos hd_wm
    -- Also need div simplifications for the r_lo lets (they affect control flow)
    have hn_div : evmDiv ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) d =
        ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d :=
      evmDiv_eq' _ d hn_evm_lt hd_pos hd_wm
    have hwm_div : evmDiv (WORD_MOD - 1) d = (WORD_MOD - 1) / d :=
      evmDiv_eq' _ d hnot_wm hd_pos hd_wm
    simp only [hn_div, hn_mod, hnot_eq, hwm_div, hwm_mod]
    -- Simplify evmAdd chains
    have hrw_lt : (WORD_MOD - 1) % d < d := Nat.mod_lt _ hd_pos
    have hrw_wm : (WORD_MOD - 1) % d < WORD_MOD := Nat.lt_of_lt_of_le hrw_lt (by omega)
    have h1_wm : (1 : Nat) < WORD_MOD := by unfold WORD_MOD; omega
    have h1rw_sum : 1 + (WORD_MOD - 1) % d < WORD_MOD :=
      Nat.lt_of_le_of_lt (by omega : 1 + (WORD_MOD - 1) % d ≤ d) hd_wm
    have hadd_1_rw : evmAdd 1 ((WORD_MOD - 1) % d) = 1 + (WORD_MOD - 1) % d :=
      evmAdd_eq' 1 _ h1_wm hrw_wm h1rw_sum
    simp only [hadd_1_rw]
    have hr0_lt : ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d < d := Nat.mod_lt _ hd_pos
    have hr0_wm : ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d < WORD_MOD :=
      Nat.lt_of_lt_of_le hr0_lt (by omega)
    have hR_sum : ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d) < WORD_MOD :=
      Nat.lt_of_lt_of_le (by omega : _ < 2 * d) (by omega)
    have hstep2 : evmAdd (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d) (1 + (WORD_MOD - 1) % d) =
        ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d) :=
      evmAdd_eq' _ _ hr0_wm h1rw_sum hR_sum
    simp only [hstep2]
    -- Simplify remaining EVM ops for r_lo (div) and rem (mod)
    have hR_lt2d : ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d) < 2 * d := by omega
    have hR_wm := hR_sum
    have hdiv_R : evmDiv (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d)) d =
        (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d)) / d :=
      evmDiv_eq' _ d hR_wm hd_pos hd_wm
    have hmod_R : evmMod (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d)) d =
        (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d)) % d :=
      evmMod_eq' _ d hR_wm hd_pos hd_wm
    -- Also need evmAdd for quotient chain (affects let r_lo)
    have hq0_wm : ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d < WORD_MOD :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn_evm_lt
    have hqw_wm : (WORD_MOD - 1) / d < WORD_MOD :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hnot_wm
    have hq0_170 : ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d < 2 ^ 170 :=
      (Nat.div_lt_iff_lt_mul hd_pos).mpr (Nat.lt_of_lt_of_le hn_evm_lt
        (by rw [h_wm_sq]; exact Nat.mul_le_mul_left _ hd_ge))
    have hqw_170 : (WORD_MOD - 1) / d < 2 ^ 170 :=
      (Nat.div_lt_iff_lt_mul hd_pos).mpr (Nat.lt_of_lt_of_le hnot_wm
        (by rw [h_wm_sq]; exact Nat.mul_le_mul_left _ hd_ge))
    have h171_le_wm : (2 : Nat) ^ 171 ≤ WORD_MOD := by
      unfold WORD_MOD; exact Nat.pow_le_pow_right (by omega) (by omega)
    have hq0qw_sum : ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d + (WORD_MOD - 1) / d < WORD_MOD :=
      Nat.lt_of_lt_of_le (by omega : _ < 2 ^ 171) h171_le_wm
    have hstep1 : evmAdd (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d) ((WORD_MOD - 1) / d) =
        ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d + (WORD_MOD - 1) / d :=
      evmAdd_eq' _ _ hq0_wm hqw_wm hq0qw_sum
    have hR_div_le1 : (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d)) / d ≤ 1 :=
      Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hd_pos).mpr hR_lt2d)
    have hR_div_wm : (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d)) / d < WORD_MOD :=
      Nat.lt_of_le_of_lt hR_div_le1 (by unfold WORD_MOD; omega)
    have hfinal_sum : ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d + (WORD_MOD - 1) / d +
        (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d)) / d < WORD_MOD :=
      Nat.lt_of_lt_of_le (by omega : _ < 2 ^ 171 + 1) (by omega : 2 ^ 171 + 1 ≤ WORD_MOD)
    have hstep3 : evmAdd (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d + (WORD_MOD - 1) / d)
        ((((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d)) / d) =
        ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d + (WORD_MOD - 1) / d +
        (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d)) / d :=
      evmAdd_eq' _ _ hq0qw_sum hR_div_wm hfinal_sum
    simp only [hdiv_R, hmod_R, hstep1, hstep3]
    -- Now the goal is pure Nat: remainder_sum % d = n_full % d
    have hn_full_decomp : res * 2 ^ 86 + limb_hi =
        d * (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) / d + (WORD_MOD - 1) / d) +
        (((res % 2 ^ 170) * 2 ^ 86 + limb_hi) % d + (1 + (WORD_MOD - 1) % d)) := by
      rw [hn_full_eq]
      have h1 := (Nat.div_add_mod ((res % 2 ^ 170) * 2 ^ 86 + limb_hi) d).symm
      have h2 := (Nat.div_add_mod (WORD_MOD - 1) d).symm
      rw [Nat.mul_add]; omega
    rw [hn_full_decomp]
    exact (mod_of_mul_add d _ _ hd_pos).symm
  · -- === NO-CARRY CASE ===
    next hc_not =>
    have hc_zero : res / 2 ^ 170 = 0 := Decidable.byContradiction hc_not
    have hres_small : res < 2 ^ 170 := by
      cases Nat.lt_or_ge res (2 ^ 170) with
      | inl h => exact h
      | inr h =>
        have : 0 < res / 2 ^ 170 := Nat.div_pos h (Nat.two_pow_pos 170)
        omega
    have hmod_res : res % 2 ^ 170 = res := Nat.mod_eq_of_lt hres_small
    have hn_eq : (res % 2 ^ 170) * 2 ^ 86 + limb_hi = res * 2 ^ 86 + limb_hi := by
      rw [hmod_res]
    have hn_lt : res * 2 ^ 86 + limb_hi < WORD_MOD := by rw [← hn_eq]; exact hn_evm_lt
    rw [hn_eq, evmMod_eq' _ d hn_lt hd_pos hd_wm]

-- ============================================================================
-- Combined Karatsuba quotient correctness
-- ============================================================================

/-- The Karatsuba quotient computes both floor((res * 2^86 + limb_hi) / d)
    and (res * 2^86 + limb_hi) % d.
    This handles both the normal case (no overflow) and the carry case.

    Preconditions tightened from the original 0 < d and d < WORD_MOD:
    - d ≥ 2^86 ensures quotients fit in 170 bits (their sum < WORD_MOD)
    - d < 2^172 ensures 2*d < WORD_MOD (remainder sum doesn't overflow)
    Both hold at call site: d = 3*m² with 2^83 ≤ m < 2^85. -/
theorem model_cbrtKaratsubaQuotient_evm_correct
    (res limb_hi d : Nat)
    (hres : res < WORD_MOD) (hlimb : limb_hi < WORD_MOD)
    (hd_ge : 2 ^ 86 ≤ d) (hd_bound : d < 2 ^ 172)
    (hres_bound : res < 2 ^ 171)
    (hlimb_bound : limb_hi < 2 ^ 86) :
    (model_cbrtKaratsubaQuotient_evm res limb_hi d).1 =
      (res * 2 ^ 86 + limb_hi) / d ∧
    (model_cbrtKaratsubaQuotient_evm res limb_hi d).2 =
      (res * 2 ^ 86 + limb_hi) % d :=
  ⟨kq_fst_correct res limb_hi d hres hlimb hd_ge hd_bound hres_bound hlimb_bound,
   kq_snd_correct res limb_hi d hres hlimb hd_ge hd_bound hres_bound hlimb_bound⟩

end Cbrt512Spec
