import LnProof.Floor.CarryIndependent.Normalization
import LnProof.Floor.CarryIndependent.StageErrors

open FormalYul FormalYul.Preservation

namespace LnFloorCarry

open LnYul Common.Poly

set_option maxRecDepth 8192

noncomputable section

private theorem int_mul_le_mul_of_bounds {a b c d : Int}
    (hac : a ≤ c) (hbd : b ≤ d) (hb0 : 0 ≤ b) (ha0 : 0 ≤ a) :
    a * b ≤ c * d :=
  Int.mul_le_mul hac hbd hb0 (ha0.trans hac)

private theorem int_toNat_pos_of_pos {x : Int} (hx : 0 < x) : 0 < x.toNat :=
  Int.pos_iff_toNat_pos.mp hx

private theorem real_int_natCast (n : Nat) : (((n : Int) : Real)) = (n : Real) := by
  norm_cast

theorem x1_floor_eq {m : Nat} (hmlo : 2 ^ 95 ≤ m) (hmsc : m < Sc) :
    let z := int256 (zWord m)
    let u := uWord (zWord m)
    let p := int256 (pS4 u)
    let d := -int256 (qS5 u)
    int256 (x1W (zWord m)) = -((p.toNat * z.toNat / d.toNat : Nat) : Int) := by
  dsimp
  have hz := low_z_facts hmlo hmsc
  have hu := low_u_facts hmlo hmsc
  obtain ⟨hpw, hp0, hp1, _, _⟩ := pS4_facts hu.1
  obtain ⟨hqw, _, hq1, _, _⟩ := qS5_facts hu.1
  have hpnonneg : 0 ≤ int256 (pS4 (uWord (zWord m))) :=
    (by norm_num : (0 : Int) ≤ 13131151825116561693704478250792).trans hp0
  have hzw : zWord m < 2 ^ 256 := evmSdiv_lt _ _
  have hprod0 : 0 ≤ int256 (pS4 (uWord (zWord m))) * int256 (zWord m) :=
    Int.mul_nonneg hpnonneg hz.1
  have hprodHi : int256 (pS4 (uWord (zWord m))) * int256 (zWord m) < 2 ^ 255 := by
    calc
      int256 (pS4 (uWord (zWord m))) * int256 (zWord m) ≤
          (13972178604861559108982341686387 : Int) * Zc :=
        int_mul_le_mul_of_bounds hp1 hz.2 hz.1 hpnonneg
      _ < 2 ^ 255 := by norm_num [Zc]
  have hmul : int256 (evmMul (pS4 (uWord (zWord m))) (zWord m)) =
      int256 (pS4 (uWord (zWord m))) * int256 (zWord m) := by
    apply evmMul_transport hpw hzw
    · exact (by norm_num : -(2 ^ 255 : Int) ≤ 0).trans hprod0
    · exact hprodHi
  have hmul0 : 0 ≤ int256 (evmMul (pS4 (uWord (zWord m))) (zWord m)) := by
    rw [hmul]
    exact hprod0
  have hqneg : int256 (qS5 (uWord (zWord m))) < 0 :=
    hq1.trans_lt (by norm_num)
  unfold x1W
  rw [evmSdiv_pos_neg (evmMul_lt _ _) hqw hmul0 hqneg, hmul]
  exact congrArg
    (fun n : Nat =>
      -((n / (-int256 (qS5 (uWord (zWord m)))).toNat : Nat) : Int))
    (Int.toNat_mul hpnonneg hz.1)

theorem final_stage_sandwich_of_u {u : Nat} (hu : u ≤ Uc) :
    let p := (int256 (pS4 u) : Real)
    let d := (-int256 (qS5 u) : Int)
    exactP u - pError u ≤ p ∧ p ≤ exactP u ∧
      exactD u ≤ (d : Real) ∧ (d : Real) ≤ exactD u + dError u ∧
      0 < exactD u ∧ 0 < d := by
  dsimp
  obtain ⟨_, _, _, _, hpHi⟩ := pS4_facts hu
  obtain ⟨_, _, hq1, _, hqHi⟩ := qS5_facts hu
  have huI : (u : Int) ≤ UcI := by
    simp only [UcI]
    exact_mod_cast hu
  have hcertQ := certQ_all (Int.ofNat_zero_le u) huI
  have hpError := pS4_error_bound hu
  have hqError := qS5_error hu
  have hpLoI :
      evalPoly PPc (u : Int) - pErrorNum u * 2 ^ 84 ≤
        int256 (pS4 u) * pScale := by
    linarith
  have hpLoR :
      ((evalPoly PPc (u : Int) - pErrorNum u * 2 ^ 84 : Int) : Real) ≤
      (int256 (pS4 u) : Real) * pScale := by
    exact_mod_cast hpLoI
  have hpHiR : (int256 (pS4 u) : Real) * pScale ≤
      (evalPoly PPc (u : Int) : Real) := by
    exact_mod_cast hpHi
  have hqHiR : (int256 (qS5 u) : Real) * qScale ≤
      (evalPoly QQc (u : Int) : Real) := by
    exact_mod_cast hqHi
  have hdHiI :
      (-int256 (qS5 u)) * qScale ≤
        -evalPoly QQc (u : Int) + dErrorNum u * 2 ^ 113 := by
    linarith
  have hdHiR :
      ((-int256 (qS5 u) : Int) : Real) * qScale ≤
        ((-evalPoly QQc (u : Int) : Int) : Real) +
          ((dErrorNum u * 2 ^ 113 : Int) : Real) := by
    exact_mod_cast hdHiI
  have hpScalePos : (0 : Real) < pScale := by norm_num [pScale]
  have hqScalePos : (0 : Real) < qScale := by norm_num [qScale]
  constructor
  · rw [exactP, pError_eq_scaled, ← sub_div]
    rw [div_le_iff₀ hpScalePos]
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using hpLoR
  constructor
  · simp only [exactP]
    rw [le_div_iff₀ hpScalePos]
    exact hpHiR
  constructor
  · simp only [exactD]
    rw [div_le_iff₀ hqScalePos]
    calc
      ((-evalPoly QQc (u : Int) : Int) : Real) =
          -(evalPoly QQc (u : Int) : Real) := by rw [Int.cast_neg]
      _ ≤ -((int256 (qS5 u) : Real) * qScale) := neg_le_neg hqHiR
      _ = ((-int256 (qS5 u) : Int) : Real) * qScale := by
        rw [Int.cast_neg]
        ring
  constructor
  · rw [exactD, dError_eq_scaled, ← add_div, le_div_iff₀ hqScalePos]
    simpa only [Int.cast_add, Int.cast_neg] using hdHiR
  constructor
  · simp only [exactD]
    apply div_pos
    · have : (0 : Int) < -evalPoly QQc (u : Int) :=
        (by norm_num [SLOPQc] : (0 : Int) < SLOPQc).trans_le hcertQ
      exact_mod_cast this
    · exact hqScalePos
  · have hdPos : (0 : Int) < -int256 (qS5 u) :=
      neg_pos.mpr (hq1.trans_lt (by norm_num))
    exact_mod_cast hdPos

theorem runtimeRatio_ge_shadow_of_u {u : Nat} (hu : u ≤ Uc) :
    shadowRatio u ≤
      (int256 (pS4 u) : Real) / (-int256 (qS5 u) : Int) := by
  obtain ⟨hpLo, _, _, hdHi, hD0, hd0⟩ := final_stage_sandwich_of_u hu
  have hden0 : 0 < exactD u + dError u :=
    add_pos_of_pos_of_nonneg hD0 (dError_nonneg u)
  have hd0R : (0 : Real) < (-int256 (qS5 u) : Int) := by
    exact_mod_cast hd0
  have hp0R : (0 : Real) ≤ int256 (pS4 u) := by
    have hp0 := (pS4_facts hu).2.1
    have hp0I : (0 : Int) ≤ int256 (pS4 u) :=
      (by norm_num : (0 : Int) ≤ 13131151825116561693704478250792).trans hp0
    exact_mod_cast hp0I
  unfold shadowRatio
  rw [div_le_div_iff₀ hden0 hd0R]
  exact mul_le_mul hpLo hdHi hd0R.le hp0R

theorem runtimeRatio_ge_shadow {m : Nat} (hmlo : 2 ^ 95 ≤ m) (hmsc : m < Sc) :
    shadowRatio (uWord (zWord m)) ≤
      (int256 (pS4 (uWord (zWord m))) : Real) /
        (-int256 (qS5 (uWord (zWord m))) : Int) := by
  exact runtimeRatio_ge_shadow_of_u (low_u_facts hmlo hmsc).1

theorem runtimeRatio_le_exact_of_u {u : Nat} (hu : u ≤ Uc) :
    (int256 (pS4 u) : Real) / (-int256 (qS5 u) : Int) ≤ exactRatio u := by
  obtain ⟨_, hpHi, hdLo, _, hD0, hd0⟩ := final_stage_sandwich_of_u hu
  have hp0 : (0 : Real) ≤ int256 (pS4 u) := by
    have hpFacts := (pS4_facts hu).2.1
    have hp0I : (0 : Int) ≤ int256 (pS4 u) :=
      (by norm_num : (0 : Int) ≤ 13131151825116561693704478250792).trans hpFacts
    exact_mod_cast hp0I
  have hd0R : (0 : Real) < (-int256 (qS5 u) : Int) := by exact_mod_cast hd0
  have hP0 : (0 : Real) ≤ exactP u := hp0.trans hpHi
  unfold exactRatio
  rw [div_le_div_iff₀ hd0R hD0]
  exact mul_le_mul hpHi hdLo hD0.le hP0

theorem nat_div_real_lt_add_one {n d : Nat} (hd : 0 < d) :
    (n : Real) / d < (n / d : Nat) + 1 := by
  have hmod := Nat.mod_lt n hd
  have hNat : n < (n / d + 1) * d := by
    calc
      n = (n / d) * d + n % d := by
        rw [mul_comm (n / d)]
        exact (Nat.div_add_mod _ _).symm
      _ < (n / d) * d + d := Nat.add_lt_add_left hmod _
      _ = (n / d + 1) * d := by rw [Nat.add_mul, one_mul]
  rw [div_lt_iff₀ (by exact_mod_cast hd : (0 : Real) < d)]
  exact_mod_cast hNat

theorem nat_div_real_le {n d : Nat} (hd : 0 < d) :
    ((n / d : Nat) : Real) ≤ (n : Real) / d := by
  rw [le_div_iff₀ (by exact_mod_cast hd : (0 : Real) < d)]
  exact_mod_cast Nat.div_mul_le_self n d

theorem high_x1_floor_eq {m : Nat} (hscm : Sc ≤ m) (hmhi : m < 2 ^ 96) :
    let z := int256 (zWord m)
    let u := uWord (zWord m)
    let p := int256 (pS4 u)
    let d := -int256 (qS5 u)
    int256 (x1W (zWord m)) = (((-(p * z)).toNat / d.toNat : Nat) : Int) := by
  dsimp
  have hz := high_z_facts hscm hmhi
  have hu := high_u_facts hscm hmhi
  obtain ⟨hpw, hp0, hp1, _, _⟩ := pS4_facts hu.1
  obtain ⟨hqw, _, hq1, _, _⟩ := qS5_facts hu.1
  have hpPos : 0 < int256 (pS4 (uWord (zWord m))) :=
    (by norm_num : (0 : Int) < 13131151825116561693704478250792).trans_le hp0
  have hzw : zWord m < 2 ^ 256 := evmSdiv_lt _ _
  have hpz := pz_bound hp0 hp1 hz.1
    (hz.2.trans (by norm_num))
  have hmul : int256 (evmMul (pS4 (uWord (zWord m))) (zWord m)) =
      int256 (pS4 (uWord (zWord m))) * int256 (zWord m) :=
    evmMul_transport hpw hzw hpz.1.le hpz.2
  have hqneg : int256 (qS5 (uWord (zWord m))) < 0 :=
    hq1.trans_lt (by norm_num)
  unfold x1W
  rcases eq_or_lt_of_le hz.2 with hzEq | hzNeg
  · have hmul0 : 0 ≤
        int256 (evmMul (pS4 (uWord (zWord m))) (zWord m)) := by
      rw [hmul, hzEq, mul_zero]
    calc
      int256 (evmSdiv (evmMul (pS4 (uWord (zWord m))) (zWord m))
          (qS5 (uWord (zWord m)))) =
          -(((int256 (evmMul (pS4 (uWord (zWord m))) (zWord m))).toNat /
            (-int256 (qS5 (uWord (zWord m)))).toNat : Nat) : Int) :=
        evmSdiv_pos_neg (evmMul_lt _ _) hqw hmul0 hqneg
      _ = 0 := by
        rw [hmul, hzEq, mul_zero, Int.toNat_zero, Nat.zero_div]
        simp only [Int.ofNat_zero, neg_zero]
      _ = (((-(int256 (pS4 (uWord (zWord m))) * int256 (zWord m))).toNat /
          (-int256 (qS5 (uWord (zWord m)))).toNat : Nat) : Int) := by
        rw [hzEq, mul_zero, neg_zero, Int.toNat_zero, Nat.zero_div]
        simp only [Int.ofNat_zero]
  · have hmulNeg : int256 (evmMul (pS4 (uWord (zWord m))) (zWord m)) < 0 := by
      rw [hmul]
      exact Int.mul_neg_of_pos_of_neg hpPos hzNeg
    have hmulMin : -(2 ^ 255) <
        int256 (evmMul (pS4 (uWord (zWord m))) (zWord m)) := by
      rw [hmul]
      exact hpz.1
    calc
      int256 (evmSdiv (evmMul (pS4 (uWord (zWord m))) (zWord m))
          (qS5 (uWord (zWord m)))) =
          (((-int256 (evmMul (pS4 (uWord (zWord m))) (zWord m))).toNat /
            (-int256 (qS5 (uWord (zWord m)))).toNat : Nat) : Int) :=
        evmSdiv_neg_neg (evmMul_lt _ _) hqw hmulNeg hmulMin hqneg
      _ = (((-(int256 (pS4 (uWord (zWord m))) * int256 (zWord m))).toNat /
          (-int256 (qS5 (uWord (zWord m)))).toNat : Nat) : Int) := by
        exact congrArg
          (fun n : Nat =>
            ((n / (-int256 (qS5 (uWord (zWord m)))).toNat : Nat) : Int))
          (congrArg (fun x : Int => (-x).toNat) hmul)

theorem highClosingDivision_le {m : Nat} (hscm : Sc ≤ m) (hmhi : m < 2 ^ 96) :
    (int256 (x1W (zWord m)) : Real) / 2 ^ 99 ≤
      2 * highNormalizedZ m *
        ((int256 (pS4 (uWord (zWord m))) : Real) /
          (-int256 (qS5 (uWord (zWord m))) : Int)) := by
  have hz := high_z_facts hscm hmhi
  have hu := high_u_facts hscm hmhi
  have hp0 := (pS4_facts hu.1).2.1
  have hq1 := (qS5_facts hu.1).2.2.1
  let p := int256 (pS4 (uWord (zWord m)))
  let z := int256 (zWord m)
  let d := -int256 (qS5 (uWord (zWord m)))
  have hp : 0 ≤ p := by
    dsimp [p]
    exact (by norm_num : (0 : Int) ≤ 13131151825116561693704478250792).trans hp0
  have hz0 : z ≤ 0 := by exact hz.2
  have hn : 0 ≤ -(p * z) := by
    rw [neg_nonneg]
    exact Int.mul_nonpos_of_nonneg_of_nonpos hp hz0
  have hd : 0 < d := by
    dsimp [d]
    exact neg_pos.mpr (hq1.trans_lt (by norm_num))
  have hdNat : 0 < d.toNat := @int_toNat_pos_of_pos d hd
  have hfloor := nat_div_real_le
    (n := (-(p * z)).toNat) (d := d.toNat) hdNat
  rw [real_cast_toNat hn, real_cast_toNat hd.le] at hfloor
  have hnegMulCast : ((-(p * z) : Int) : Real) = -(p : Real) * (z : Real) := by
    rw [Int.cast_neg, Int.cast_mul]
    ring
  rw [hnegMulCast] at hfloor
  have hx : int256 (x1W (zWord m)) =
      (((-(p * z)).toNat / d.toNat : Nat) : Int) := by
    simpa only [p, z, d] using high_x1_floor_eq hscm hmhi
  have hxR : (int256 (x1W (zWord m)) : Real) =
      (((-(p * z)).toNat / d.toNat : Nat) : Real) :=
    Eq.trans (congrArg (fun x : Int => (x : Real)) hx) (real_int_natCast _)
  rw [hxR]
  calc
    (((-(p * z)).toNat / d.toNat : Nat) : Real) / 2 ^ 99 ≤
        (-(p : Real) * z / d) / 2 ^ 99 :=
      div_le_div_of_nonneg_right hfloor (by positivity)
    _ = 2 * highNormalizedZ m *
          ((int256 (pS4 (uWord (zWord m))) : Real) /
            (-int256 (qS5 (uWord (zWord m))) : Int)) := by
      unfold highNormalizedZ p z d
      norm_num [wordQ100]
      ring

theorem neg_floor_div_le {p z d : Int} (hp : 0 ≤ p) (hz : 0 ≤ z) (hd : 0 < d) :
    -(((p.toNat * z.toNat / d.toNat : Nat) : Real)) ≤
      -(p : Real) * (z : Real) / (d : Real) + 1 := by
  have hdNat : 0 < d.toNat := @int_toNat_pos_of_pos d hd
  have hfloor := nat_div_real_lt_add_one (n := p.toNat * z.toNat) (d := d.toNat) hdNat
  simp only [Nat.cast_mul] at hfloor
  rw [real_cast_toNat hp, real_cast_toNat hz, real_cast_toNat hd.le] at hfloor
  have hsub : (p : Real) * z / d - 1 <
      ((p.toNat * z.toNat / d.toNat : Nat) : Real) :=
    (sub_lt_iff_lt_add).2 hfloor
  have hneg := neg_lt_neg hsub
  exact le_of_lt (by
    calc
      -(((p.toNat * z.toNat / d.toNat : Nat) : Real)) <
          -((p : Real) * z / d - 1) := hneg
      _ = -(p : Real) * z / d + 1 := by ring)

theorem closingDivision_le {m : Nat} (hmlo : 2 ^ 95 ≤ m) (hmsc : m < Sc) :
    (int256 (x1W (zWord m)) : Real) / 2 ^ 99 ≤
      -2 * normalizedZ m *
          ((int256 (pS4 (uWord (zWord m))) : Real) /
            (-int256 (qS5 (uWord (zWord m))) : Int)) +
        2 / wordQ100 := by
  have hz := low_z_facts hmlo hmsc
  have hu := low_u_facts hmlo hmsc
  have hp0 := (pS4_facts hu.1).2.1
  have hq1 := (qS5_facts hu.1).2.2.1
  let p := int256 (pS4 (uWord (zWord m)))
  let z := int256 (zWord m)
  let d := -int256 (qS5 (uWord (zWord m)))
  have hp : 0 ≤ p := by
    dsimp [p]
    exact (by norm_num : (0 : Int) ≤ 13131151825116561693704478250792).trans hp0
  have hz0 : 0 ≤ z := by exact hz.1
  have hd : 0 < d := by
    dsimp [d]
    exact neg_pos.mpr (hq1.trans_lt (by norm_num))
  have hfloor := neg_floor_div_le hp hz0 hd
  have hx : int256 (x1W (zWord m)) =
      -((p.toNat * z.toNat / d.toNat : Nat) : Int) := by
    simpa only [p, z, d] using x1_floor_eq hmlo hmsc
  have hxR : (int256 (x1W (zWord m)) : Real) =
      -(((p.toNat * z.toNat / d.toNat : Nat) : Real)) := by exact_mod_cast hx
  rw [hxR]
  calc
    -(((p.toNat * z.toNat / d.toNat : Nat) : Real)) / 2 ^ 99 ≤
        (-(p : Real) * z / d + 1) / 2 ^ 99 :=
      div_le_div_of_nonneg_right hfloor (by positivity)
    _ = -2 * normalizedZ m *
          ((int256 (pS4 (uWord (zWord m))) : Real) /
            (-int256 (qS5 (uWord (zWord m))) : Int)) +
        2 / wordQ100 := by
      unfold normalizedZ p z d
      norm_num [wordQ100]
      ring

theorem runtime_le_lowShadow {m : Nat} (hmlo : 2 ^ 95 ≤ m) (hmsc : m < Sc) :
    (int256 (x1W (zWord m)) : Real) / 2 ^ 99 ≤ lowShadow m := by
  have hclose := closingDivision_le hmlo hmsc
  have hratio := runtimeRatio_ge_shadow hmlo hmsc
  have ha0 := (low_endpoint_bounds hmlo hmsc).1
  have hscaledNonpos : (0 : Real) ≥ -2 * normalizedZ m :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num) ha0
  have hscaled :
      -2 * normalizedZ m *
          ((int256 (pS4 (uWord (zWord m))) : Real) /
            (-int256 (qS5 (uWord (zWord m))) : Int)) ≤
        -2 * normalizedZ m * shadowRatio (uWord (zWord m)) :=
    mul_le_mul_of_nonpos_left hratio hscaledNonpos
  unfold lowShadow
  exact hclose.trans (add_le_add_right hscaled _)

theorem runtime_le_highShadow {m : Nat} (hscm : Sc ≤ m) (hmhi : m < 2 ^ 96) :
    (int256 (x1W (zWord m)) : Real) / 2 ^ 99 ≤ highShadow m := by
  have hclose := highClosingDivision_le hscm hmhi
  have hratio := runtimeRatio_le_exact_of_u (high_u_facts hscm hmhi).1
  have hb0 := (high_endpoint_bounds hscm hmhi).1
  have hscaledNonneg : (0 : Real) ≤ 2 * highNormalizedZ m :=
    mul_nonneg (by norm_num) hb0
  have hscaled :
      2 * highNormalizedZ m *
          ((int256 (pS4 (uWord (zWord m))) : Real) /
            (-int256 (qS5 (uWord (zWord m))) : Int)) ≤
        2 * highNormalizedZ m * exactRatio (uWord (zWord m)) :=
    mul_le_mul_of_nonneg_left hratio hscaledNonneg
  unfold highShadow
  exact hclose.trans hscaled

end

end LnFloorCarry
