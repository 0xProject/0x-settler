/-
  Sub-lemma B: (r_qc - 1)³ ≤ x_norm, giving r_qc ≤ icbrt + 1.
-/
import Cbrt512Proof.GeneratedCbrt512Model
import Cbrt512Proof.CbrtBaseCase
import Cbrt512Proof.CbrtAlgebraic
import Cbrt512Proof.EvmBridge
import CbrtProof.CbrtCorrect

namespace Cbrt512Spec

open Cbrt512GeneratedModel

-- ============================================================================
-- Sub-lemma B: Upper bound — (r_qc - 1)³ ≤ x_norm
-- ============================================================================

/-- The cube of (r_qc - 1) does not exceed x_norm.
    Combined with icbrt_lt_succ_cube, this gives r_qc ≤ icbrt(x_norm) + 1.
    Note: r_qc ≥ 1 since r_qc ≥ R = m·2^86 ≥ 2^169.
    Proof sketch: x_norm - (r_qc-1)³ = 3R²(c+1) + S - 3R(q-1)² - (q-1)³
    where S = rem·2^172 + c_tail ≥ 0. Since 3R²(c+1) > 3R·r_lo² ≥ 3R(q-1)²
    and the surplus 3R[R(c+1) - (q-1)²] grows quadratically in r_lo while
    (q-1)³ grows cubically but with r_lo/R ≪ 1, the surplus dominates. -/
theorem r_qc_pred_cube_le (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD) :
    let w := x_hi_1 / 4
    let m := icbrt w
    let res := w - m * m * m
    let d := 3 * (m * m)
    let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
    let r_lo := (res * 2 ^ 86 + limb_hi) / d
    let R := m * 2 ^ 86
    let correction := r_lo * r_lo / R
    let r_qc := R + r_lo - correction
    let x_norm := x_hi_1 * 2 ^ 256 + x_lo_1
    (r_qc - 1) * (r_qc - 1) * (r_qc - 1) ≤ x_norm := by
  simp only
  -- ======== Step 1: Extract base case properties ========
  have hbc := model_cbrtBaseCase_evm_correct x_hi_1 hxhi_lo hxhi_hi
  have hm_lo : 2 ^ 83 ≤ icbrt (x_hi_1 / 4) := hbc.2.2.2.1
  have hm_hi : icbrt (x_hi_1 / 4) < 2 ^ 85 := hbc.2.2.2.2.1
  have hcube_le_w : icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ x_hi_1 / 4 := hbc.2.2.2.2.2.1
  have hres_bound : x_hi_1 / 4 - icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) + 3 * icbrt (x_hi_1 / 4) :=
    hbc.2.2.2.2.2.2.1
  have hd_pos : 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) > 0 :=
    hbc.2.2.2.2.2.2.2.2.2.2
  -- Abbreviate
  let m := icbrt (x_hi_1 / 4)
  let w := x_hi_1 / 4
  let res := w - m * m * m
  let d := 3 * (m * m)
  let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
  let r_lo := (res * 2 ^ 86 + limb_hi) / d
  let R := m * 2 ^ 86
  let c := r_lo * r_lo / R
  let rem_kq := (res * 2 ^ 86 + limb_hi) % d
  let c_tail := x_lo_1 % 2 ^ 172
  -- ======== Step 2: Key bounds ========
  have hR_pos : 0 < R := by omega
  have hlimb_bound : limb_hi < 2 ^ 86 := by
    show (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86
    have hmod4 : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
    have hdiv : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 172)]
      calc x_lo_1 < WORD_MOD := hxlo
        _ = 2 ^ 84 * 2 ^ 172 := by unfold WORD_MOD; rw [← Nat.pow_add]
    have : (x_hi_1 % 4) * 2 ^ 84 < 2 ^ 86 :=
      calc (x_hi_1 % 4) * 2 ^ 84 < 4 * 2 ^ 84 :=
              Nat.mul_lt_mul_of_pos_right hmod4 (Nat.two_pow_pos 84)
        _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
    omega
  have hr_lo_bound : r_lo < 2 ^ 87 := by
    show (res * 2 ^ 86 + limb_hi) / d < 2 ^ 87
    rw [Nat.div_lt_iff_lt_mul hd_pos]
    have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    calc res * 2 ^ 86 + limb_hi
        < (res + 1) * 2 ^ 86 := by omega
      _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by
          apply Nat.mul_le_mul_right; exact Nat.succ_le_succ hres_bound
      _ ≤ (2 * (3 * (m * m))) * 2 ^ 86 := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ 87 * (3 * (m * m)) := by
          rw [show (2 : Nat) ^ 87 = 2 * 2 ^ 86 from by
            rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]]; omega
  -- Floor division bound: r_lo² < (c+1)R
  have hcR_lt : r_lo * r_lo < (c + 1) * R := by
    show r_lo * r_lo < (r_lo * r_lo / R + 1) * R
    have hdm := Nat.div_add_mod (r_lo * r_lo) R
    -- hdm : R * (r_lo * r_lo / R) + r_lo * r_lo % R = r_lo * r_lo
    have hmod_lt := Nat.mod_lt (r_lo * r_lo) hR_pos
    -- (c + 1) * R = c * R + R = R * c + R
    calc r_lo * r_lo
        = R * (r_lo * r_lo / R) + r_lo * r_lo % R := hdm.symm
      _ < R * (r_lo * r_lo / R) + R := by omega
      _ = R * (r_lo * r_lo / R + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = (r_lo * r_lo / R + 1) * R := Nat.mul_comm _ _
  -- ======== Step 3: x_norm lower bound ========
  -- x_norm = R³ + n_full·2^172 + c_tail where n_full = d·r_lo + rem_kq
  -- x_norm ≥ R³ + d·r_lo·2^172 = R³ + 3R²·r_lo
  have hx_decomp := x_norm_decomp x_hi_1 x_lo_1 (m * m * m) hcube_le_w
  have hn_full := Nat.div_add_mod (res * 2 ^ 86 + limb_hi) d
  have h_num_eq : (res * 2 ^ 86 + limb_hi) = d * r_lo + rem_kq := hn_full.symm
  have h_num_mul : (d * r_lo + rem_kq) * 2 ^ 172 = d * r_lo * 2 ^ 172 + rem_kq * 2 ^ 172 :=
    Nat.add_mul _ _ _
  have hx_lb : m * m * m * 2 ^ 258 + d * r_lo * 2 ^ 172 ≤
      x_hi_1 * 2 ^ 256 + x_lo_1 := by
    rw [hx_decomp]
    rw [show ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) = d * r_lo + rem_kq from h_num_eq]
    rw [h_num_mul]
    omega
  -- Rewrite using R³ = m³·2^258 and 3R² = d·2^172
  have hR3 := R_cube_factor m
  have hd_eq_3R2 := d_pow172_eq_3R_sq m
  -- x_norm ≥ R³ + 3R²·r_lo
  have hx_lb2 : R * R * R + 3 * (R * R) * r_lo ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := by
    calc R * R * R + 3 * (R * R) * r_lo
        = m * m * m * 2 ^ 258 + 3 * (m * m) * r_lo * 2 ^ 172 := by
          rw [← hR3]
          show R * R * R + 3 * (R * R) * r_lo =
            R * R * R + 3 * (m * m) * r_lo * 2 ^ 172
          rw [← hd_eq_3R2]
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = m * m * m * 2 ^ 258 + d * r_lo * 2 ^ 172 := by rfl
      _ ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := hx_lb
  -- ======== Step 4: Case split ========
  -- r_qc - 1 = R + r_lo - c - 1
  -- Need to show (R + r_lo - c - 1)³ ≤ x_norm
  by_cases hrloc : r_lo ≤ c
  · -- Trivial case: r_lo ≤ c → r_qc - 1 ≤ R - 1, and (R-1)³ ≤ R³ ≤ x_norm
    have hrqc1_le : R + r_lo - c - 1 ≤ R - 1 := by omega
    have hR1_le : R - 1 ≤ R := Nat.sub_le _ _
    calc (R + r_lo - c - 1) * (R + r_lo - c - 1) * (R + r_lo - c - 1)
        ≤ (R - 1) * (R - 1) * (R - 1) := cube_monotone hrqc1_le
      _ ≤ R * R * R :=
          Nat.mul_le_mul (Nat.mul_le_mul hR1_le hR1_le) hR1_le
      _ ≤ R * R * R + 3 * (R * R) * r_lo := Nat.le_add_right _ _
      _ ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := hx_lb2
  · -- Main case: r_lo ≥ c + 1
    -- Let t = r_lo - c - 1 (≥ 0). Then r_qc - 1 = R + t.
    -- Need: (R + t)³ ≤ x_norm where t = r_lo - c - 1.
    -- Expand: (R + t)³ = R³ + 3R²t + 3Rt² + t³
    -- From x_norm ≥ R³ + 3R²·r_lo, suffices: 3R²t + 3Rt² + t³ ≤ 3R²·r_lo
    -- i.e., 3R²(r_lo - t) ≥ 3Rt² + t³, i.e., 3R²(c+1) ≥ 3Rt² + t³
    have hrqc1_eq : R + r_lo - c - 1 = R + (r_lo - c - 1) := by omega
    rw [hrqc1_eq, cube_sum_expand R (r_lo - c - 1)]
    -- Goal: R³ + 3R²·t + 3R·t² + t³ ≤ x_norm
    -- Suffices: 3R²·t + 3R·t² + t³ ≤ 3R²·r_lo (since R³ + 3R²·r_lo ≤ x_norm)
    suffices h_suff : 3 * (R * R) * (r_lo - c - 1) +
        3 * R * ((r_lo - c - 1) * (r_lo - c - 1)) +
        (r_lo - c - 1) * (r_lo - c - 1) * (r_lo - c - 1) ≤
        3 * (R * R) * r_lo from
      calc R * R * R + 3 * (R * R) * (r_lo - c - 1) +
            3 * R * ((r_lo - c - 1) * (r_lo - c - 1)) +
            (r_lo - c - 1) * (r_lo - c - 1) * (r_lo - c - 1)
          ≤ R * R * R + 3 * (R * R) * r_lo := by omega
        _ ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := hx_lb2
    -- Reduce: 3R²·t + 3Rt² + t³ ≤ 3R²·r_lo
    -- ↔ 3Rt² + t³ ≤ 3R²(r_lo - t) = 3R²(c + 1)
    -- Since r_lo - t = r_lo - (r_lo - c - 1) = c + 1
    -- Rewrite 3R²·r_lo = 3R²·t + 3R²·(c+1)
    have hrlo_split : 3 * (R * R) * r_lo =
        3 * (R * R) * (r_lo - c - 1) + 3 * (R * R) * (c + 1) := by
      rw [← Nat.mul_add]; congr 1; omega
    rw [hrlo_split]
    -- Cancel 3R²·t from both sides. Need: 3Rt² + t³ ≤ 3R²(c+1)
    -- Suffices to prove this
    suffices h_core : 3 * R * ((r_lo - c - 1) * (r_lo - c - 1)) +
        (r_lo - c - 1) * (r_lo - c - 1) * (r_lo - c - 1) ≤
        3 * (R * R) * (c + 1) by omega
    -- t² ≤ r_lo² < (c+1)R; t < 2^87; t³ < 2^87·(c+1)R ≤ 3R·(c+1)R = 3R²(c+1)
    have ht_le_rlo : r_lo - c - 1 ≤ r_lo := Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)
    have ht_sq_lt_cR : (r_lo - c - 1) * (r_lo - c - 1) < (c + 1) * R :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul ht_le_rlo ht_le_rlo) hcR_lt
    -- Use sq_sum_expand: r_lo = t + (c+1), so r_lo² = t² + 2t(c+1) + (c+1)².
    -- From (c+1)R > r_lo²: (c+1)R - t² > 2t(c+1).
    -- Then: 3R((c+1)R - t²) > 6Rt(c+1) ≥ t(c+1)R > t·t² = t³.
    -- So 3Rt² + t³ < 3Rt² + 3R((c+1)R - t²) = 3R(c+1)R = 3R²(c+1).
    have hrlo_eq : r_lo = (r_lo - c - 1) + (c + 1) := by omega
    have hrlo_sq := sq_sum_expand (r_lo - c - 1) (c + 1)
    have h_gap : (r_lo - c - 1) * (r_lo - c - 1) + 2 * (r_lo - c - 1) * (c + 1) <
        (c + 1) * R := by
      have : (r_lo - c - 1 + (c + 1)) * (r_lo - c - 1 + (c + 1)) =
          (r_lo - c - 1) * (r_lo - c - 1) + 2 * (r_lo - c - 1) * (c + 1) +
          (c + 1) * (c + 1) := hrlo_sq
      rw [← hrlo_eq] at this; omega
    cases Nat.eq_or_lt_of_le (Nat.zero_le (r_lo - c - 1)) with
    | inl ht0 =>
      -- t = 0: everything is 0 ≤ 3R²(c+1)
      rw [← ht0]; simp
    | inr ht_pos =>
      -- t ≥ 1, where t = r_lo - c - 1. Strategy: show t³ < 3R·((c+1)R - t²),
      -- then 3Rt² + t³ < 3Rt² + 3R·((c+1)R - t²) = 3R·(c+1)R = 3R²·(c+1).
      -- Rewrite t*t*t = t*(t*t) for associativity
      rw [show (r_lo - c - 1) * (r_lo - c - 1) * (r_lo - c - 1) =
          (r_lo - c - 1) * ((r_lo - c - 1) * (r_lo - c - 1)) from Nat.mul_assoc _ _ _]
      -- t·t² < t·(c+1)R (from ht_sq_lt_cR)
      have ht_cube_bound : (r_lo - c - 1) * ((r_lo - c - 1) * (r_lo - c - 1)) <
          (r_lo - c - 1) * ((c + 1) * R) :=
        Nat.mul_lt_mul_of_pos_left ht_sq_lt_cR ht_pos
      -- Key: t·(c+1)·R ≤ 2t(c+1)·R  (trivially: a ≤ 2a)
      -- Then: 2t(c+1)·R < ((c+1)R - t²)·R  (from h_gap, mul by R)
      -- Then: ((c+1)R-t²)·R ≤ R·((c+1)R-t²) = 1·R·((c+1)R-t²) ≤ 3R·((c+1)R-t²)
      -- So: t·(c+1)R < 3R·((c+1)R - t²), hence t³ < t·(c+1)R < 3R·((c+1)R - t²).
      -- We prove: (r_lo-c-1) * ((c+1)*R) < 3 * R * ((c+1)*R - t²)
      -- by showing: a*b*c < (a*b - d) * c ≤ 3c * (a*b - d) where appropriate.
      -- Actually let's just show t³ < 3R * ((c+1)R - t²) directly.
      -- From h_gap: 2*t*(c+1) < (c+1)*R - t², so (c+1)*R - t² > 2*t*(c+1) ≥ 2*t
      -- Since 3R ≥ 3*2^169 and t < 2^87, we have 3R*((c+1)R - t²) > 3R*2t > 6R*t > t*(c+1)R > t³
      -- But these chains involve nonlinear reasoning that omega can't do.
      -- Simplest working approach: show it all as one calc chain using Nat mul lemmas.
      -- t³ = t*t² < t*(c+1)R  [from ht_cube_bound]
      --    ≤ (c+1)*R*t  [comm]  -- actually same thing
      -- We need (r_lo-c-1)*((c+1)*R) < 3*R*((c+1)*R - (r_lo-c-1)*(r_lo-c-1))
      -- i.e., t*(c+1)*R < 3R*((c+1)*R - t²)
      -- i.e., t*(c+1) < 3*((c+1)*R - t²)  [div by R, but careful with Nat]
      -- From h_gap: (c+1)*R - t² > 2*t*(c+1) ≥ t*(c+1)
      -- So 3*((c+1)*R - t²) > 3*t*(c+1) > t*(c+1). Not quite what we need.
      -- Actually: t*(c+1)*R = t*(c+1) * R. And 3R * ((c+1)R - t²) = 3 * R * ((c+1)*R - t²).
      -- Need: t*(c+1)*R < 3*R*((c+1)*R - t²)
      -- ↔ t*(c+1) < 3*((c+1)*R - t²)  [cancel R; safe since R > 0]
      -- From h_gap: (c+1)*R - t² > t² + 2t(c+1) - t² + something... wait:
      -- h_gap says t² + 2t(c+1) < (c+1)*R, so (c+1)*R - t² > 2t(c+1).
      -- 3*((c+1)*R - t²) > 3*2*t*(c+1) = 6t(c+1) > t(c+1).
      -- So the inequality holds. Let's formalize with Nat.div.
      -- Actually, just prove it directly without dividing:
      -- t*(c+1)*R ≤ 2*t*(c+1)*R  [x ≤ 2x for Nat]
      --          < ((c+1)*R - t²)*R  [h_gap * R]
      --          ≤ 3*R*((c+1)*R - t²)  [a*R ≤ 3R*a, i.e., R ≤ 3R]
      -- Chain using Nat.mul_lt_mul_of_pos_right and omega.
      -- For step 1: t*(c+1)*R = Nat.mul_assoc: (r_lo-c-1) * ((c+1) * R) = ((r_lo-c-1)*(c+1)) * R
      have hassoc1 : (r_lo - c - 1) * ((c + 1) * R) = (r_lo - c - 1) * (c + 1) * R :=
        (Nat.mul_assoc _ _ _).symm
      -- For step 2 lhs: 2*t*(c+1)*R = (2*(r_lo-c-1)*(c+1)) * R
      -- h_gap : (r_lo-c-1)*(r_lo-c-1) + 2*(r_lo-c-1)*(c+1) < (c+1)*R
      -- Multiply by R: (2*(r_lo-c-1)*(c+1)) * R < ((c+1)*R - (r_lo-c-1)*(r_lo-c-1)) * R
      have h_gap2 : 2 * (r_lo - c - 1) * (c + 1) <
          (c + 1) * R - (r_lo - c - 1) * (r_lo - c - 1) := by omega
      have hstep2 : 2 * (r_lo - c - 1) * (c + 1) * R <
          ((c + 1) * R - (r_lo - c - 1) * (r_lo - c - 1)) * R :=
        Nat.mul_lt_mul_of_pos_right h_gap2 (by omega)
      -- Now combine:
      -- t*(c+1)*R = (t*(c+1))*R ≤ (2*t*(c+1))*R < ((c+1)*R - t²)*R ≤ 3R*((c+1)*R - t²)
      have hchain : (r_lo - c - 1) * ((c + 1) * R) <
          3 * R * ((c + 1) * R - (r_lo - c - 1) * (r_lo - c - 1)) := by
        rw [hassoc1]
        calc (r_lo - c - 1) * (c + 1) * R
            ≤ 2 * (r_lo - c - 1) * (c + 1) * R :=
              Nat.mul_le_mul_right R
                (Nat.mul_le_mul_right (c + 1) (Nat.le_mul_of_pos_left _ (by omega)))
          _ < ((c + 1) * R - (r_lo - c - 1) * (r_lo - c - 1)) * R := hstep2
          _ = R * ((c + 1) * R - (r_lo - c - 1) * (r_lo - c - 1)) := Nat.mul_comm _ _
          _ ≤ 3 * R * ((c + 1) * R - (r_lo - c - 1) * (r_lo - c - 1)) :=
              Nat.mul_le_mul_right _
                (Nat.le_mul_of_pos_left R (by omega))
      -- Split 3R(c+1)R = 3Rt² + 3R((c+1)R - t²)
      have h_sum : 3 * R * ((r_lo - c - 1) * (r_lo - c - 1)) +
          3 * R * ((c + 1) * R - (r_lo - c - 1) * (r_lo - c - 1)) =
          3 * R * ((c + 1) * R) := by
        rw [← Nat.mul_add]; congr 1; omega
      -- 3R(c+1)R = 3(R*R)(c+1)
      have h_assoc : 3 * R * ((c + 1) * R) = 3 * (R * R) * (c + 1) := by
        -- 3*R*((c+1)*R) = 3*(R*((c+1)*R)) = 3*((c+1)*(R*R)) = 3*(c+1)*(R*R) = (3*(R*R))*(c+1)
        suffices h : (↑(3 * R * ((c + 1) * R)) : Int) = ↑(3 * (R * R) * (c + 1)) by
          exact_mod_cast h
        push_cast
        simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      -- Final: use Nat.le_of_lt on the strict chain
      exact Nat.le_of_lt (calc
        3 * R * ((r_lo - c - 1) * (r_lo - c - 1)) +
            (r_lo - c - 1) * ((r_lo - c - 1) * (r_lo - c - 1))
          < 3 * R * ((r_lo - c - 1) * (r_lo - c - 1)) +
            3 * R * ((c + 1) * R - (r_lo - c - 1) * (r_lo - c - 1)) := by omega
        _ = 3 * R * ((c + 1) * R) := h_sum
        _ = 3 * (R * R) * (c + 1) := h_assoc)


end Cbrt512Spec
