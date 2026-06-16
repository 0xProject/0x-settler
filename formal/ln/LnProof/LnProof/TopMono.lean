import LnProof.OctaveMono
import LnProof.LnMono

/-!
# Monotonicity of the generated `lnWad` model over its whole domain

The three legs are stitched together here:

* within an octave (`evmClz` fixed), `tail_mono` carries the analytic
  certificates through the model tail;
* each adjacent pair crossing a `clz` seam is decided in `LnMono`;
* the `x = 10^18` corrected point and its neighbors are decided in `LnMono`.

`model_ln_wad_mono` chains the unit step over the domain, and
`model_ln_wad_to_wad_mono` pushes the result through the wad helper's
floor division.
-/

set_option maxRecDepth 4096

namespace LnGeneratedModel

/-! ## `sle` / `toInt` glue -/

theorem sle_eq_sleInt (a b : Nat) : sle a b = sleInt a b := rfl

theorem sle_of_toInt {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : toInt a ≤ toInt b) : sle a b = true := by
  rw [sle_eq_sleInt]
  exact (sleInt_iff ha hb).mpr h

theorem toInt_of_sle {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : sle a b = true) : toInt a ≤ toInt b := by
  rw [sle_eq_sleInt] at h
  exact (sleInt_iff ha hb).mp h

theorem model_lt {x : Nat} (h : x < 2 ^ 256) : model_ln_wad_evm x < 2 ^ 256 := by
  rw [model_eq_tail h]
  unfold lnTail
  exact evmAdd_lt _ _

/-! ## Small opcode facts -/

theorem evmClz_eq {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 256) :
    evmClz x = 255 - Nat.log2 x := by
  unfold evmClz
  rw [u256_of_lt h2, if_neg (by omega)]

/-! ## The mantissa for a fixed `clz` -/

theorem mant_facts {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) :
    evmShr 160 (evmShl (evmClz x) x) = x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 ∧
      MLO ≤ x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 ∧
      x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 < MHI := by
  have hx0 : x ≠ 0 := by omega
  have ha1 : Nat.log2 x < 255 := (Nat.log2_lt hx0).mpr (by omega)
  have h2a : 2 ^ Nat.log2 x ≤ x := (Nat.le_log2 hx0).mp (Nat.le_refl _)
  have hx2a : x < 2 ^ (Nat.log2 x + 1) := (Nat.log2_lt hx0).mp (Nat.lt_succ_self _)
  have hclz : evmClz x = 255 - Nat.log2 x := evmClz_eq h1 (by omega)
  have hpow : 2 ^ (Nat.log2 x + 1) * 2 ^ (255 - Nat.log2 x) = 2 ^ 256 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hov : x * 2 ^ (255 - Nat.log2 x) < 2 ^ 256 := by
    have h := (Nat.mul_lt_mul_right (Nat.two_pow_pos (255 - Nat.log2 x))).mpr hx2a
    rw [hpow] at h
    exact h
  have hlo : 2 ^ 255 ≤ x * 2 ^ (255 - Nat.log2 x) := by
    have h := Nat.mul_le_mul_right (2 ^ (255 - Nat.log2 x)) h2a
    have he : 2 ^ Nat.log2 x * 2 ^ (255 - Nat.log2 x) = 2 ^ 255 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [he] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · rw [hclz, evmShl_eq (by omega) hov, evmShr_eq_div_160 hov]
  · have h := Nat.div_le_div_right (c := 2 ^ 160) hlo
    have he : (2 : Nat) ^ 255 / 2 ^ 160 = 2 ^ 95 := by decide
    rw [he] at h
    simp only [MLO]
    exact h
  · have h := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 160)).mpr
      (by rw [show (2 : Nat) ^ 96 * 2 ^ 160 = 2 ^ 256 by decide]; exact hov)
    simp only [MHI]
    exact h

/-! ## The decided legs, extracted -/

theorem seam_extract {t : Nat} (ht1 : 1 ≤ t) (ht2 : t ≤ 254) :
    sle (model_ln_wad_evm (2 ^ t - 1)) (model_ln_wad_evm (2 ^ t)) = true := by
  have h := model_ln_wad_seam_mono
  rw [seamMono, List.all_eq_true] at h
  have hm := h (t - 1) (List.mem_range.mpr (by omega))
  rw [show t - 1 + 1 = t by omega] at hm
  exact hm

/-! ## The unit step -/

theorem model_unit_step {x : Nat} (h1 : 1 ≤ x) (h2 : x + 1 < 2 ^ 255) :
    toInt (model_ln_wad_evm x) ≤ toInt (model_ln_wad_evm (x + 1)) := by
  have hx256 : x < 2 ^ 256 := by omega
  have hx1256 : x + 1 < 2 ^ 256 := by omega
  have hd := model_ln_wad_one_wad_mono
  rw [Bool.and_eq_true] at hd
  rcases Decidable.em (x = 999999999999999999) with hsp | hne1
  · -- x = 10^18 - 1: decided
    subst hsp
    have h := toInt_of_sle (model_lt (by omega)) (model_lt (by omega)) hd.1
    rw [show (10 : Nat) ^ 18 - 1 = 999999999999999999 by decide,
      show (10 : Nat) ^ 18 = 999999999999999999 + 1 by decide] at h
    exact h
  · rcases Decidable.em (x = 1000000000000000000) with hsp | hne2
    · -- x = 10^18: decided
      subst hsp
      have h := toInt_of_sle (model_lt (by omega)) (model_lt (by omega)) hd.2
      rw [show (10 : Nat) ^ 18 = 1000000000000000000 by decide,
        show (10 : Nat) ^ 18 + 1 = 1000000000000000000 + 1 by decide] at h
      exact h
    · rcases Decidable.em (evmClz (x + 1) = evmClz x) with hclz | hclz
      · -- same octave: the analytic leg
        have e1 := evmClz_eq h1 hx256
        have e2 := evmClz_eq (by omega) hx1256
        have hl1 : Nat.log2 x < 255 := (Nat.log2_lt (by omega)).mpr (by omega)
        have hl2 : Nat.log2 (x + 1) < 255 := (Nat.log2_lt (by omega)).mpr (by omega)
        have hlog : Nat.log2 (x + 1) = Nat.log2 x := by omega
        obtain ⟨me, mlo, mhi⟩ := mant_facts h1 (by omega)
        obtain ⟨me', mlo', mhi'⟩ := mant_facts (x := x + 1) (by omega) h2
        have hmm : x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 ≤
            (x + 1) * 2 ^ (255 - Nat.log2 (x + 1)) / 2 ^ 160 := by
          rw [hlog]
          exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_succ x))
        have hc : evmClz x < 256 := by omega
        rw [model_eq_tail hx256, model_eq_tail hx1256, me, me', hclz]
        exact tail_mono mlo hmm mhi' (ln2k_bound hc).1 (ln2k_bound hc).2
      · -- clz seam: x + 1 is a power of two; decided
        have e1 := evmClz_eq h1 hx256
        have e2 := evmClz_eq (by omega) hx1256
        have hl1 : Nat.log2 x < 255 := (Nat.log2_lt (by omega)).mpr (by omega)
        have hl2 : Nat.log2 (x + 1) < 255 := (Nat.log2_lt (by omega)).mpr (by omega)
        have hlog : Nat.log2 (x + 1) ≠ Nat.log2 x := by omega
        have h2a : 2 ^ Nat.log2 x ≤ x := (Nat.le_log2 (by omega)).mp (Nat.le_refl _)
        have hx2a : x < 2 ^ (Nat.log2 x + 1) :=
          (Nat.log2_lt (by omega)).mp (Nat.lt_succ_self _)
        have h2b : 2 ^ Nat.log2 (x + 1) ≤ x + 1 :=
          (Nat.le_log2 (by omega)).mp (Nat.le_refl _)
        have hab : Nat.log2 x ≤ Nat.log2 (x + 1) :=
          (Nat.le_log2 (by omega)).mpr (by omega)
        have hstep : 2 ^ (Nat.log2 x + 1) ≤ 2 ^ Nat.log2 (x + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hxe : x + 1 = 2 ^ Nat.log2 (x + 1) := by omega
        have hb1 : 1 ≤ Nat.log2 (x + 1) := by
          rcases Nat.eq_zero_or_pos (Nat.log2 (x + 1)) with h0 | hpos
          · exfalso
            rw [h0] at hxe
            omega
          · exact hpos
        have hs := seam_extract hb1 (by omega)
        have h := toInt_of_sle (model_lt (by omega)) (model_lt (by omega)) hs
        rw [show 2 ^ Nat.log2 (x + 1) - 1 = x by omega, ← hxe] at h
        exact h

/-! ## The full domain -/

/-- `lnWad` is monotone nondecreasing over its entire domain
`0 < x ≤ y < 2^255` (signed comparison of the output words). -/
theorem model_ln_wad_mono {x y : Nat} (hx : 0 < x) (hxy : x ≤ y)
    (hy : y < 2 ^ 255) : sle (model_ln_wad_evm x) (model_ln_wad_evm y) = true := by
  have key : ∀ n : Nat, x + n < 2 ^ 255 →
      toInt (model_ln_wad_evm x) ≤ toInt (model_ln_wad_evm (x + n)) := by
    intro n
    induction n with
    | zero => intro _; exact Int.le_refl _
    | succ k ih =>
      intro hk
      have hs := model_unit_step (x := x + k) (by omega) (by omega)
      have he : x + (k + 1) = x + k + 1 := by omega
      rw [he]
      exact Int.le_trans (ih (by omega)) hs
  have hkey := key (y - x) (by omega)
  rw [show x + (y - x) = y by omega] at hkey
  exact sle_of_toInt (model_lt (by omega)) (model_lt (by omega)) hkey

/-! ## The wad helper -/

theorem evmSub_zero {a : Nat} (h : a < 2 ^ 256) : evmSub a 0 = a := by
  unfold evmSub u256
  simp only [word_mod_eq]
  omega

theorem evmSlt_zero {r : Nat} (h : r < 2 ^ 256) :
    evmSlt r 0 = if toInt r < 0 then 1 else 0 := by
  unfold evmSlt u256 toInt
  simp only [word_mod_eq]
  repeat' split
  all_goals omega

theorem evmSgt_zero_eq_slt_zero (r : Nat) : evmSgt 0 r = evmSlt r 0 := by
  unfold evmSgt evmSlt
  rfl

theorem to_wad_eq {x : Nat} (h : x < 2 ^ 256) :
    model_ln_wad_to_wad_evm x =
      evmSdiv
        (evmSub (model_ln_wad_evm x)
          (evmMul (evmSlt (model_ln_wad_evm x) 0) 999999999))
        1000000000 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256_of_lt h]
  rw [evmSgt_zero_eq_slt_zero, evmMul_comm 999999999]

theorem to_wad_numerator_eq {r : Nat} (hr : r < 2 ^ 256)
    (hb1 : -(12259964326927110866866776217202473468949912977468817408 : Int) ≤ toInt r)
    (hb2 : toInt r ≤ (12259964326927110866866776217202473468949912977468817409 : Int)) :
    toInt (evmSub r (evmMul (evmSlt r 0) 999999999)) =
      toInt r - (if toInt r < 0 then (999999999 : Int) else 0) := by
  have hm1 : evmMul 1 999999999 = 999999999 := by decide
  have hm0 : evmMul 0 999999999 = 0 := by decide
  have h999 : toInt 999999999 = (999999999 : Int) := by decide
  rw [evmSlt_zero hr]
  rcases Int.lt_or_le (toInt r) 0 with hneg | hpos
  · rw [if_pos hneg, if_pos hneg, hm1]
    rw [evmSub_transport hr (by omega)
      (by rw [h999]; simp only [ipow255]; omega)
      (by rw [h999]; simp only [ipow255]; omega), h999]
  · rw [if_neg (by omega), if_neg (by omega), hm0, evmSub_zero hr]
    omega

theorem floor_div_pos_window {a : Int} (ha : 0 ≤ a) :
    (((a.toNat / 1000000000 : Nat) : Int) * 1000000000 ≤ a) ∧
      (a < (((a.toNat / 1000000000 : Nat) : Int) + 1) * 1000000000) := by
  have hsplit := Nat.div_add_mod a.toNat 1000000000
  have hmod := Nat.mod_lt a.toNat (by decide : 0 < 1000000000)
  have ha' : ((a.toNat : Nat) : Int) = a := Int.toNat_of_nonneg ha
  constructor <;> omega

theorem floor_div_neg_window {a : Int} (ha : a < 0) :
    (-(((((-a).toNat + 999999999) / 1000000000 : Nat) : Int)) * 1000000000 ≤ a) ∧
      (a < (-(((((-a).toNat + 999999999) / 1000000000 : Nat) : Int)) + 1) *
        1000000000) := by
  let A := (-a).toNat
  let q := (A + 999999999) / 1000000000
  have hapos : 0 < A := by
    unfold A
    rcases Nat.eq_zero_or_pos (-a).toNat with hz | hp
    · have hcast : (((-a).toNat : Nat) : Int) = -a := Int.toNat_of_nonneg (by omega)
      rw [hz] at hcast
      omega
    · exact hp
  have ha' : ((A : Nat) : Int) = -a := by
    unfold A
    exact Int.toNat_of_nonneg (by omega)
  have hsplit := Nat.div_add_mod (A + 999999999) 1000000000
  have hmod := Nat.mod_lt (A + 999999999) (by decide : 0 < 1000000000)
  constructor <;> unfold q at * <;> omega

/-- The model's output sits inside `[-2^183, 2^183 + 1]`: the post-shift value is
a 184-bit signed quantity, and the `s + (s == -1)` self-correction keeps it there
(it only sends `-1` to `0`). -/
theorem lnTail_bound (kw m : Nat) :
    -(12259964326927110866866776217202473468949912977468817408 : Int) ≤
        toInt (lnTail kw m) ∧
      toInt (lnTail kw m) ≤
        (12259964326927110866866776217202473468949912977468817409 : Int) := by
  unfold lnTail
  obtain ⟨wlt, s1, s2⟩ := evmSar_sandwich_72 (evmAdd_lt
    (evmAdd (evmMul (x1W (zWord m)) Kc) (evmMul LN2c kw)) BIASc)
  have hwl := toInt_lt (evmAdd_lt
    (evmAdd (evmMul (x1W (zWord m)) Kc) (evmMul LN2c kw)) BIASc)
  have hwg := toInt_ge (evmAdd_lt
    (evmAdd (evmMul (x1W (zWord m)) Kc) (evmMul LN2c kw)) BIASc)
  rw [corr_toInt wlt]
  generalize toInt (evmAdd (evmAdd (evmMul (x1W (zWord m)) Kc) (evmMul LN2c kw)) BIASc) =
    t at s1 s2 hwl hwg
  generalize toInt (evmSar 72 (evmAdd (evmAdd (evmMul (x1W (zWord m)) Kc) (evmMul LN2c kw)) BIASc)) =
    s at s1 s2 ⊢
  simp only [ipow255] at hwl hwg
  split <;> omega

theorem model_bound {x : Nat} (h : x < 2 ^ 256) :
    -(12259964326927110866866776217202473468949912977468817408 : Int) ≤
        toInt (model_ln_wad_evm x) ∧
      toInt (model_ln_wad_evm x) ≤
        (12259964326927110866866776217202473468949912977468817409 : Int) := by
  rw [model_eq_tail h]
  exact lnTail_bound _ _

theorem to_wad_floor_window {x : Nat} (h : x < 2 ^ 256) :
    toInt (model_ln_wad_to_wad_evm x) * 1000000000 ≤ toInt (model_ln_wad_evm x) ∧
      toInt (model_ln_wad_evm x) < (toInt (model_ln_wad_to_wad_evm x) + 1) *
        1000000000 := by
  have hr := model_lt h
  obtain ⟨hb1, hb2⟩ := model_bound h
  have hn := to_wad_numerator_eq hr hb1 hb2
  have hnlt : evmSub (model_ln_wad_evm x) (evmMul (evmSlt (model_ln_wad_evm x) 0) 999999999) <
      2 ^ 256 := evmSub_lt _ _
  have hdlt : (1000000000 : Nat) < 2 ^ 256 := by omega
  have hden : toInt 1000000000 = (1000000000 : Int) := by decide
  have hdenN : ((1000000000 : Int)).toNat = 1000000000 := by decide
  rw [to_wad_eq h]
  generalize hw : evmSub (model_ln_wad_evm x) (evmMul (evmSlt (model_ln_wad_evm x) 0) 999999999) = nw at hn hnlt ⊢
  rcases Int.lt_or_le (toInt (model_ln_wad_evm x)) 0 with hneg | hpos
  · rw [if_pos hneg] at hn
    have hnum : toInt nw < 0 := by omega
    rw [evmSdiv_neg_pos hnlt hdlt hnum (by simp only [ipow255]; omega)
      (by rw [hden]; omega), hden, hdenN]
    have hwnd := floor_div_neg_window (a := toInt (model_ln_wad_evm x)) hneg
    have hmag : (-toInt nw).toNat = (-toInt (model_ln_wad_evm x)).toNat + 999999999 := by
      apply Int.ofNat.inj
      change ((-toInt nw).toNat : Int) =
        (((-toInt (model_ln_wad_evm x)).toNat + 999999999 : Nat) : Int)
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -toInt nw), Int.natCast_add,
        Int.toNat_of_nonneg (by omega : 0 ≤ -toInt (model_ln_wad_evm x))]
      omega
    rw [hmag]
    exact hwnd
  · rw [if_neg (by omega)] at hn
    have hnum : 0 ≤ toInt nw := by omega
    rw [evmSdiv_pos_pos hnlt hdlt hnum (by rw [hden]; omega), hden, hdenN]
    have hwnd := floor_div_pos_window (a := toInt (model_ln_wad_evm x)) hpos
    have hn0 : toInt nw = toInt (model_ln_wad_evm x) := by omega
    rw [hn0]
    exact hwnd

/-- Signed floor division by `10^9` (as the helper computes it) is monotone. -/
theorem floordiv_mono {r r' : Nat} (hr : r < 2 ^ 256) (hr' : r' < 2 ^ 256)
    (hb1 : -(12259964326927110866866776217202473468949912977468817408 : Int) ≤ toInt r)
    (hb2 : toInt r ≤ (12259964326927110866866776217202473468949912977468817409 : Int))
    (hb1' : -(12259964326927110866866776217202473468949912977468817408 : Int) ≤ toInt r')
    (hb2' : toInt r' ≤ (12259964326927110866866776217202473468949912977468817409 : Int))
    (hle : toInt r ≤ toInt r') :
    toInt (evmSdiv (evmSub r (evmMul (evmSlt r 0) 999999999)) 1000000000) ≤
      toInt (evmSdiv (evmSub r' (evmMul (evmSlt r' 0) 999999999)) 1000000000) := by
  have hden : toInt 1000000000 = (1000000000 : Int) := by decide
  have hdenN : ((1000000000 : Int)).toNat = 1000000000 := by decide
  have hdlt : (1000000000 : Nat) < 2 ^ 256 := by omega
  have e1 := to_wad_numerator_eq hr hb1 hb2
  have e1' := to_wad_numerator_eq hr' hb1' hb2'
  have hnlt : evmSub r (evmMul (evmSlt r 0) 999999999) < 2 ^ 256 := evmSub_lt _ _
  have hnlt' : evmSub r' (evmMul (evmSlt r' 0) 999999999) < 2 ^ 256 := evmSub_lt _ _
  have hdpos : (0 : Int) < toInt 1000000000 := by rw [hden]; omega
  generalize evmSub r (evmMul (evmSlt r 0) 999999999) = nw at e1 hnlt ⊢
  generalize evmSub r' (evmMul (evmSlt r' 0) 999999999) = nw' at e1' hnlt' ⊢
  rcases Int.lt_or_le (toInt r) 0 with hneg | hpos
  · rw [if_pos hneg] at e1
    have hnum : toInt nw < 0 := by omega
    rw [evmSdiv_neg_pos hnlt hdlt hnum (by simp only [ipow255]; omega) hdpos, e1, hden,
      hdenN]
    rcases Int.lt_or_le (toInt r') 0 with hneg' | hpos'
    · rw [if_pos hneg'] at e1'
      have hnum' : toInt nw' < 0 := by omega
      rw [evmSdiv_neg_pos hnlt' hdlt hnum' (by simp only [ipow255]; omega) hdpos, e1',
        hden, hdenN]
      omega
    · rw [if_neg (by omega)] at e1'
      have hnum' : (0 : Int) ≤ toInt nw' := by omega
      rw [evmSdiv_pos_pos hnlt' hdlt hnum' hdpos, e1', hden, hdenN]
      omega
  · rw [if_neg (by omega)] at e1
    rw [if_neg (by omega)] at e1'
    have hnum : (0 : Int) ≤ toInt nw := by omega
    have hnum' : (0 : Int) ≤ toInt nw' := by omega
    rw [evmSdiv_pos_pos hnlt hdlt hnum hdpos,
      evmSdiv_pos_pos hnlt' hdlt hnum' hdpos, e1, e1', hden, hdenN]
    omega

theorem to_wad_lt {x : Nat} (h : x < 2 ^ 256) :
    model_ln_wad_to_wad_evm x < 2 ^ 256 := by
  rw [to_wad_eq h]
  exact evmSdiv_lt _ _

/-- `lnWadToWad` is monotone nondecreasing over the entire domain
`0 < x ≤ y < 2^255`. -/
theorem model_ln_wad_to_wad_mono {x y : Nat} (hx : 0 < x) (hxy : x ≤ y)
    (hy : y < 2 ^ 255) :
    sle (model_ln_wad_to_wad_evm x) (model_ln_wad_to_wad_evm y) = true := by
  have hx256 : x < 2 ^ 256 := by omega
  have hy256 : y < 2 ^ 256 := by omega
  have hr := model_ln_wad_mono hx hxy hy
  have hri := toInt_of_sle (model_lt hx256) (model_lt hy256) hr
  obtain ⟨hb1, hb2⟩ := model_bound hx256
  obtain ⟨hb1', hb2'⟩ := model_bound hy256
  have hdd := floordiv_mono (model_lt hx256) (model_lt hy256) hb1 hb2 hb1' hb2' hri
  rw [to_wad_eq hx256, to_wad_eq hy256]
  exact sle_of_toInt (evmSdiv_lt _ _) (evmSdiv_lt _ _) hdd

end LnGeneratedModel
