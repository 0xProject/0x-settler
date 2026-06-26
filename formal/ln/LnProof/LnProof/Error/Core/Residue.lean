import LnProof.Floor.CutEquiv
import LnProof.Error.Cert
import LnProof.Error.Core.CutDefs

/-!
# Error bound — Residue

`posAccI` / `posResidueGap` / `lnTail` residue algebra and the modular bucket-index helpers.
-/

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

namespace LnFloorCert

open LnYul LnFloor LnExp LnPoly

attribute [local irreducible] lnWadToRayBody


def posPhaseI (m c : Nat) : Int :=
  int256 (x1W (zWord m)) * lnPhaseScaleI +
    ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
      lnBiasI * twoPow27I

def posAccI (m c : Nat) : Int :=
  int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c + lnBiasI

def posResidueGap (m c : Nat) (r : Int) : Int :=
  (r + 1) * twoPow72I - posAccI m c

def posResidueGapThreshold : Int := 86144214621787901969

def firstCongruentGE (q r lo : Nat) : Nat :=
  if lo ≤ r then
    r
  else
    r + ((lo - r + q - 1) / q) * q

theorem firstCongruentGE_le_of_mod {q r lo h : Nat}
    (hq : 0 < q) (hmod : h % q = r) (hlo : lo ≤ h) :
    firstCongruentGE q r lo ≤ h := by
  unfold firstCongruentGE
  let k := h / q
  have hdecomp : h = k * q + r := by
    have hdm := Nat.div_add_mod h q
    rw [hmod] at hdm
    simpa [k, Nat.add_comm, Nat.mul_comm] using hdm.symm
  by_cases hlr : lo ≤ r
  · simp [hlr]
    rw [hdecomp]
    omega
  · simp [hlr]
    have hlo' : lo ≤ k * q + r := by
      rw [← hdecomp]
      exact hlo
    have hsub : lo - r ≤ k * q := by omega
    have hceil : (lo - r + q - 1) / q ≤ k := by
      rw [Nat.div_le_iff_le_mul_add_pred hq]
      calc
        lo - r + q - 1 = (lo - r) + (q - 1) := by omega
        _ ≤ k * q + (q - 1) := Nat.add_le_add_right hsub _
        _ = q * k + (q - 1) := by rw [Nat.mul_comm]
    have hmul : ((lo - r + q - 1) / q) * q ≤ k * q :=
      Nat.mul_le_mul_right q hceil
    rw [hdecomp]
    omega

theorem no_congruent_of_first_gt {q r lo hi h : Nat}
    (hq : 0 < q) (hfirst : hi < firstCongruentGE q r lo)
    (hlo : lo ≤ h) (hhi : h ≤ hi) :
    h % q ≠ r := by
  intro hmod
  have hle := firstCongruentGE_le_of_mod hq hmod hlo
  omega

theorem bucket_index_eq_of_mod_bracket {r : Int} {d rem q : Nat}
    (hq : 0 < q) (hrem : rem < q)
    (hlo : r * (q : Int) ≤ (d : Int) * (q : Int) + (rem : Int))
    (hhi : (d : Int) * (q : Int) + (rem : Int) < (r + 1) * (q : Int)) :
    r = (d : Int) := by
  have hq_nonneg : (0 : Int) ≤ (q : Int) := by omega
  have hd_le_r : (d : Int) ≤ r := by
    by_cases hle : (d : Int) ≤ r
    · exact hle
    · have hsucc : r + 1 ≤ (d : Int) := by omega
      have hmul : (r + 1) * (q : Int) ≤ (d : Int) * (q : Int) :=
        Int.mul_le_mul_of_nonneg_right hsucc hq_nonneg
      omega
  have hr_le_d : r ≤ (d : Int) := by
    by_cases hle : r ≤ (d : Int)
    · exact hle
    · have hsucc : (d : Int) + 1 ≤ r := by omega
      have hmul : ((d : Int) + 1) * (q : Int) ≤ r * (q : Int) :=
        Int.mul_le_mul_of_nonneg_right hsucc hq_nonneg
      rw [Int.add_mul, Int.one_mul] at hmul
      omega
  omega

theorem posAccI_nonneg {m c : Nat}
    (hmlo : MLO ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    0 ≤ posAccI m c := by
  have hb := (LnYul.r1_bound hmlo hmhi).1
  have hx1 :
      -(240000000000000000000000000000 : Int) * 7450580596923828125 ≤
        int256 (x1W (zWord m)) * 7450580596923828125 :=
    Int.mul_le_mul_of_nonneg_right hb (by decide)
  have hln2 : (LN2c : Int) ≤ ln2kInt c := by
    unfold ln2kInt
    rw [if_pos (by omega : c ≤ 160)]
    have hk : (1 : Int) ≤ ((160 - c : Nat) : Int) := by
      omega
    have hmul : (LN2c : Int) * 1 ≤ (LN2c : Int) * ((160 - c : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left hk (by unfold LN2c; decide)
    simpa [Int.mul_one] using hmul
  have hfloor :
      0 ≤
        (-(240000000000000000000000000000 : Int)) *
          7450580596923828125 + (LN2c : Int) + lnBiasI := by
    unfold LN2c lnBiasI
    decide
  unfold posAccI
  omega

theorem lnTail_floor_bracket_pos {m c : Nat}
    (hmlo : MLO ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    let r := int256 (lnTail (evmSub 160 c) m)
    r * twoPow72I ≤ posAccI m c ∧ posAccI m c < (r + 1) * twoPow72I := by
  have hc256 : c < 256 := by omega
  have hacc := r4_value hmlo hmhi hc256
  let s := evmSar 72
    (evmAdd (evmAdd (evmMul (x1W (zWord m)) Kc) (evmMul LN2c (evmSub 160 c))) BIASc)
  have hs := evmSar_sandwich_72 (evmAdd_lt
    (evmAdd (evmMul (x1W (zWord m)) Kc) (evmMul LN2c (evmSub 160 c))) BIASc)
  have hslt : s < 2 ^ 256 := by
    unfold s
    exact hs.1
  have hnon := posAccI_nonneg hmlo hmhi hc
  have hcorr : int256 (lnTail (evmSub 160 c) m) = int256 s := by
    unfold lnTail
    change int256 (evmAdd (evmIszero (evmNot s)) s) = int256 s
    rw [corr_toInt hslt]
    rw [if_neg]
    intro hsneg
    have hhi := hs.2.2
    rw [hacc] at hhi
    change posAccI m c < int256 s * 4722366482869645213696 +
      4722366482869645213696 at hhi
    rw [hsneg] at hhi
    omega
  rw [hcorr]
  have hlo := hs.2.1
  have hhi := hs.2.2
  rw [hacc] at hlo hhi
  change int256 s * 4722366482869645213696 ≤ posAccI m c at hlo
  change posAccI m c < int256 s * 4722366482869645213696 +
    4722366482869645213696 at hhi
  have hpow : twoPow72I = (4722366482869645213696 : Int) := by
    unfold twoPow72I
    decide
  rw [hpow]
  have heq : (int256 s + 1) * (4722366482869645213696 : Int) =
      int256 s * 4722366482869645213696 + 4722366482869645213696 := by
    rw [Int.add_mul, Int.one_mul]
  change int256 s * (4722366482869645213696 : Int) ≤ posAccI m c ∧
    posAccI m c < (int256 s + 1) * (4722366482869645213696 : Int)
  rw [heq]
  exact ⟨hlo, hhi⟩

theorem lnTail_nonneg_pos {m c : Nat}
    (hmlo : MLO ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    0 ≤ int256 (lnTail (evmSub 160 c) m) := by
  have hbr := lnTail_floor_bracket_pos hmlo hmhi hc
  have hnon := posAccI_nonneg hmlo hmhi hc
  unfold twoPow72I at hbr
  omega

theorem posResidueGap_bounds {m c : Nat}
    (hmlo : MLO ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    let r := int256 (lnTail (evmSub 160 c) m)
    1 ≤ posResidueGap m c r ∧ posResidueGap m c r ≤ twoPow72I := by
  have hbr := lnTail_floor_bracket_pos hmlo hmhi hc
  unfold posResidueGap
  have hpow : twoPow72I = (4722366482869645213696 : Int) := by
    unfold twoPow72I
    decide
  rw [hpow] at hbr ⊢
  omega

theorem posResidueGap_eq_twoPow72_sub_mod {m c : Nat}
    (hmlo : MLO ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    let r := int256 (lnTail (evmSub 160 c) m)
    posResidueGap m c r =
      ((twoPow72N - (posAccI m c).toNat % twoPow72N : Nat) : Int) := by
  intro r
  let q : Nat := twoPow72N
  let A : Nat := (posAccI m c).toNat
  let d : Nat := A / q
  let rem : Nat := A % q
  change posResidueGap m c r = ((q - rem : Nat) : Int)
  have hq : 0 < q := by
    unfold q twoPow72N
    decide
  have hqI : ((q : Nat) : Int) = twoPow72I := by
    unfold q twoPow72N twoPow72I
    decide
  have hnon : 0 ≤ posAccI m c := posAccI_nonneg hmlo hmhi hc
  have hAcast : ((A : Nat) : Int) = posAccI m c := by
    unfold A
    exact Int.toNat_of_nonneg hnon
  have hdm := Nat.div_add_mod A q
  have hdm' : A / q * q + A % q = A := by
    simpa [Nat.mul_comm] using hdm
  have hAeq : (d : Int) * (q : Int) + (rem : Int) = posAccI m c := by
    unfold d rem
    rw [← Int.natCast_mul, ← Int.natCast_add, hdm', hAcast]
  have hrem_lt : rem < q := by
    unfold rem
    exact Nat.mod_lt A hq
  have hbr := lnTail_floor_bracket_pos (m := m) (c := c) hmlo hmhi hc
  change r * twoPow72I ≤ posAccI m c ∧
    posAccI m c < (r + 1) * twoPow72I at hbr
  have hlo : r * (q : Int) ≤ (d : Int) * (q : Int) + (rem : Int) := by
    rw [hAeq, hqI]
    exact hbr.1
  have hhi : (d : Int) * (q : Int) + (rem : Int) < (r + 1) * (q : Int) := by
    rw [hAeq, hqI]
    exact hbr.2
  have hr : r = (d : Int) :=
    bucket_index_eq_of_mod_bracket (r := r) (d := d) (rem := rem) (q := q)
      hq hrem_lt hlo hhi
  unfold posResidueGap
  rw [hr, ← hqI, ← hAeq]
  have hremle : rem ≤ q := Nat.le_of_lt hrem_lt
  have hsubcast : ((q - rem : Nat) : Int) = (q : Int) - (rem : Int) := by
    omega
  rw [hsubcast]
  rw [Int.add_mul, Int.one_mul]
  omega

theorem lnTail_eq_of_posAcc_window {lo m c : Nat}
    (hlo1 : MLO ≤ lo) (hlom : lo ≤ m) (hmhi : m < MHI) (hc : c < 160)
    (hdiff :
      posAccI m c - posAccI lo c +
          posResidueGap m c (int256 (lnTail (evmSub 160 c) m)) ≤ twoPow72I) :
    int256 (lnTail (evmSub 160 c) lo) =
      int256 (lnTail (evmSub 160 c) m) := by
  have hlohi : lo < MHI := by omega
  have hbrLo := lnTail_floor_bracket_pos hlo1 hlohi hc
  have hbrM := lnTail_floor_bracket_pos (by omega : MLO ≤ m) hmhi hc
  let rlo := int256 (lnTail (evmSub 160 c) lo)
  let rm := int256 (lnTail (evmSub 160 c) m)
  have hrloLo := hbrLo.1
  have hrloHi := hbrLo.2
  have hrmLo := hbrM.1
  have hrmHi := hbrM.2
  have hx := LnYul.r1_mono hlo1 hlom hmhi
  have hacc_mono : posAccI lo c ≤ posAccI m c := by
    have hmul := Int.mul_le_mul_of_nonneg_right hx
      (by change (0 : Int) ≤ 7450580596923828125; decide)
    have h1 := Int.add_le_add_right hmul (ln2kInt c)
    have h2 := Int.add_le_add_right h1 lnBiasI
    simpa [posAccI, Int.add_assoc] using h2
  have hpow : twoPow72I = (4722366482869645213696 : Int) := by
    unfold twoPow72I
    decide
  rw [hpow] at hdiff hrloLo hrloHi hrmLo hrmHi
  unfold posResidueGap at hdiff
  change posAccI m c - posAccI lo c +
      ((rm + 1) * 4722366482869645213696 - posAccI m c) ≤
        4722366482869645213696 at hdiff
  change rlo * 4722366482869645213696 ≤ posAccI lo c at hrloLo
  change posAccI lo c < (rlo + 1) * 4722366482869645213696 at hrloHi
  change rm * 4722366482869645213696 ≤ posAccI m c at hrmLo
  change posAccI m c < (rm + 1) * 4722366482869645213696 at hrmHi
  generalize hQ : (4722366482869645213696 : Int) = Q at hdiff hrloLo hrloHi hrmLo hrmHi
  change posAccI m c - posAccI lo c + ((rm + 1) * Q - posAccI m c) ≤ Q at hdiff
  change rlo * Q ≤ posAccI lo c at hrloLo
  change posAccI lo c < (rlo + 1) * Q at hrloHi
  change rm * Q ≤ posAccI m c at hrmLo
  change posAccI m c < (rm + 1) * Q at hrmHi
  have hdiffQ :
      posAccI m c - posAccI lo c + ((rm + 1) * Q - posAccI m c) ≤ Q := by
    simpa [hQ] using hdiff
  have hQpos : (0 : Int) < Q := by
    rw [← hQ]
    decide
  have hQnonneg : (0 : Int) ≤ Q := by omega
  have sub_swap (A B C : Int) : C - B = A - B + (C - A) := by omega
  have cancel_bucket {A B Q' : Int} (h : A + Q' - B ≤ Q') : A ≤ B := by omega
  have lt_of_le_lt {A B C : Int} (hAB : A ≤ B) (hBC : B < C) : A < C := by omega
  have le_lt_false {A B : Int} (hBA : B ≤ A) (hAB : A < B) : False := by omega
  have succ_le_of_not_le {A B : Int} (h : ¬ A ≤ B) : B + 1 ≤ A := by omega
  have hmlo_for_rm : rm * Q ≤ posAccI lo c := by
    have hcollapse :
        (rm + 1) * Q - posAccI lo c ≤ Q := by
      calc
        (rm + 1) * Q - posAccI lo c =
            posAccI m c - posAccI lo c + ((rm + 1) * Q - posAccI m c) := by
              exact sub_swap (posAccI m c) (posAccI lo c) ((rm + 1) * Q)
        _ ≤ Q := hdiffQ
    have hsplit : (rm + 1) * Q = rm * Q + Q := by
      rw [Int.add_mul, Int.one_mul]
    rw [hsplit] at hcollapse
    exact cancel_bucket hcollapse
  have hmhi_for_rm : posAccI lo c < (rm + 1) * Q :=
    lt_of_le_lt hacc_mono hrmHi
  have hle1 : rlo ≤ rm := by
    by_cases hle : rlo ≤ rm
    · exact hle
    · have hge : rm + 1 ≤ rlo := succ_le_of_not_le hle
      have hmul := Int.mul_le_mul_of_nonneg_right hge hQnonneg
      have hcontr : (rm + 1) * Q ≤ posAccI lo c :=
        Int.le_trans hmul hrloLo
      exact False.elim (le_lt_false hcontr hmhi_for_rm)
  have hle2 : rm ≤ rlo := by
    by_cases hle : rm ≤ rlo
    · exact hle
    · have hge : rlo + 1 ≤ rm := succ_le_of_not_le hle
      have hmul := Int.mul_le_mul_of_nonneg_right hge hQnonneg
      have hcontr : (rlo + 1) * Q ≤ posAccI lo c :=
        Int.le_trans hmul hmlo_for_rm
      exact False.elim (le_lt_false hcontr hrloHi)
  change rlo = rm
  exact Int.le_antisymm hle1 hle2

theorem posAccI_mono_m {lo m c : Nat}
    (hlo : MLO ≤ lo) (hlom : lo ≤ m) (hmhi : m < MHI) :
    posAccI lo c ≤ posAccI m c := by
  have hx := LnYul.r1_mono hlo hlom hmhi
  have hmul := Int.mul_le_mul_of_nonneg_right hx
    (by change (0 : Int) ≤ 7450580596923828125; decide)
  unfold posAccI
  omega

theorem lnTail_eq_of_same_posAcc_endpoints {lo hi m c : Nat}
    (hlo : MLO ≤ lo) (hlom : lo ≤ m) (hmhi : m ≤ hi) (hhi : hi < MHI)
    (hc : c < 160)
    (heq : int256 (lnTail (evmSub 160 c) lo) =
      int256 (lnTail (evmSub 160 c) hi)) :
    int256 (lnTail (evmSub 160 c) m) =
      int256 (lnTail (evmSub 160 c) hi) := by
  have hmlo : MLO ≤ m := by omega
  have hmhi' : m < MHI := by omega
  have hlohi : lo < MHI := by omega
  have hbrLo := lnTail_floor_bracket_pos hlo hlohi hc
  have hbrM := lnTail_floor_bracket_pos hmlo hmhi' hc
  have hbrHi := lnTail_floor_bracket_pos (by omega : MLO ≤ hi) hhi hc
  have haccLoM : posAccI lo c ≤ posAccI m c :=
    posAccI_mono_m hlo hlom hmhi'
  have haccMHi : posAccI m c ≤ posAccI hi c :=
    posAccI_mono_m hmlo hmhi hhi
  have hpow : twoPow72I = (4722366482869645213696 : Int) := by
    unfold twoPow72I
    decide
  rw [hpow] at hbrLo hbrM hbrHi
  generalize hQ : (4722366482869645213696 : Int) = Q at hbrLo hbrM hbrHi
  change int256 (lnTail (evmSub 160 c) lo) * Q ≤ posAccI lo c ∧
    posAccI lo c < (int256 (lnTail (evmSub 160 c) lo) + 1) * Q at hbrLo
  change int256 (lnTail (evmSub 160 c) m) * Q ≤ posAccI m c ∧
    posAccI m c < (int256 (lnTail (evmSub 160 c) m) + 1) * Q at hbrM
  change int256 (lnTail (evmSub 160 c) hi) * Q ≤ posAccI hi c ∧
    posAccI hi c < (int256 (lnTail (evmSub 160 c) hi) + 1) * Q at hbrHi
  rw [← heq] at hbrHi
  have hQnonneg : (0 : Int) ≤ Q := by rw [← hQ]; decide
  have succ_le_of_not_le {A B : Int} (h : ¬ A ≤ B) : B + 1 ≤ A := by omega
  have le_lt_false {A B : Int} (hBA : B ≤ A) (hAB : A < B) : False := by omega
  have hm_eq_lo :
      int256 (lnTail (evmSub 160 c) m) =
        int256 (lnTail (evmSub 160 c) lo) := by
    have hm_le_lo : int256 (lnTail (evmSub 160 c) m) ≤
        int256 (lnTail (evmSub 160 c) lo) := by
      by_cases hle : int256 (lnTail (evmSub 160 c) m) ≤
          int256 (lnTail (evmSub 160 c) lo)
      · exact hle
      · have hsucc : int256 (lnTail (evmSub 160 c) lo) + 1 ≤
            int256 (lnTail (evmSub 160 c) m) := succ_le_of_not_le hle
        have hmul := Int.mul_le_mul_of_nonneg_right hsucc hQnonneg
        have hcontr : (int256 (lnTail (evmSub 160 c) lo) + 1) * Q ≤
            posAccI hi c :=
          Int.le_trans (Int.le_trans hmul hbrM.1) haccMHi
        exact False.elim (le_lt_false hcontr hbrHi.2)
    have hlo_le_m : int256 (lnTail (evmSub 160 c) lo) ≤
        int256 (lnTail (evmSub 160 c) m) := by
      by_cases hle : int256 (lnTail (evmSub 160 c) lo) ≤
          int256 (lnTail (evmSub 160 c) m)
      · exact hle
      · have hsucc : int256 (lnTail (evmSub 160 c) m) + 1 ≤
            int256 (lnTail (evmSub 160 c) lo) := succ_le_of_not_le hle
        have hmul := Int.mul_le_mul_of_nonneg_right hsucc hQnonneg
        have hcontr : (int256 (lnTail (evmSub 160 c) m) + 1) * Q ≤
            posAccI m c :=
          Int.le_trans (Int.le_trans hmul hbrLo.1) haccLoM
        exact False.elim (le_lt_false hcontr hbrM.2)
    exact Int.le_antisymm hm_le_lo hlo_le_m
  exact Eq.trans hm_eq_lo heq

theorem posResidueGap_ge_of_same_posAcc_endpoints {lo hi m c : Nat}
    (hlo : MLO ≤ lo) (hlom : lo ≤ m) (hmhi : m ≤ hi) (hhi : hi < MHI)
    (hc : c < 160)
    (heq : int256 (lnTail (evmSub 160 c) lo) =
      int256 (lnTail (evmSub 160 c) hi)) :
    posResidueGap hi c (int256 (lnTail (evmSub 160 c) hi)) ≤
      posResidueGap m c (int256 (lnTail (evmSub 160 c) m)) := by
  have hmlo : MLO ≤ m := by omega
  have htail :=
    lnTail_eq_of_same_posAcc_endpoints hlo hlom hmhi hhi hc heq
  have hacc : posAccI m c ≤ posAccI hi c :=
    posAccI_mono_m hmlo hmhi hhi
  unfold posResidueGap
  rw [htail]
  have sub_left_antitone {A B C : Int} (h : A ≤ B) : C - B ≤ C - A := by omega
  exact sub_left_antitone hacc

theorem lnErrArg_eq_posPhase_gap {m c : Nat}
    (hmlo : MLO ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    let r := int256 (lnTail (evmSub 160 c) m)
    ((lnErrArg r : Nat) : Int) =
      posPhaseI m c * (lnErrorBoundDen : Int) +
        (lnErrorExtraNum : Int) * twoPow99I +
          posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) := by
  intro r
  have hr0 : 0 ≤ r := lnTail_nonneg_pos hmlo hmhi hc
  have harg : 0 ≤ r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
    unfold lnErrorBoundDen lnErrorBoundNum
    omega
  have hVs := v_scale_pos (int256 (x1W (zWord m))) c (by omega : c ≤ 160)
  have hVs' : posAccI m c * twoPow27I = posPhaseI m c := by
    unfold posAccI posPhaseI
    simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  have hnum : ((lnErrorBoundNum : Nat) : Int) = (1698600000 : Int) := by
    unfold lnErrorBoundNum
    rfl
  have hextra : ((lnErrorExtraNum : Nat) : Int) = (698600000 : Int) := by
    unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen
    decide +kernel
  unfold lnErrArg posResidueGap
  rw [Int.natCast_mul, Int.toNat_of_nonneg harg]
  rw [hden, hnum, hextra]
  unfold twoPow99I twoPow27I at hVs' ⊢
  unfold twoPow72I
  rw [← hVs']
  change (r * 1000000000 + 1698600000) * 633825300114114700748351602688 =
    posAccI m c * 134217728 * 1000000000 +
      698600000 * 633825300114114700748351602688 +
        ((r + 1) * 4722366482869645213696 - posAccI m c) * 134217728 *
          1000000000
  have hP : (4722366482869645213696 : Int) * 134217728 =
      633825300114114700748351602688 := by
    decide
  have hN : (1698600000 : Int) = 1000000000 + 698600000 := by
    decide
  rw [hN, ← hP]
  simp only [Int.add_mul, Int.mul_add, Int.add_assoc, Int.sub_eq_add_neg,
    Int.neg_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  generalize r * (134217728 * (1000000000 * 4722366482869645213696)) = X
  generalize 134217728 * (1000000000 * 4722366482869645213696) = Y
  generalize 134217728 * (698600000 * 4722366482869645213696) = Z
  generalize posAccI m c * (134217728 * 1000000000) = W
  omega

end LnFloorCert
