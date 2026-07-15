import LnProof.Mono.ZOctave
import LnProof.Floor.CarryIndependent.Bounds

open FormalYul FormalYul.Preservation

namespace LnFloorCarry

open LnYul

set_option maxRecDepth 8192

noncomputable section

theorem real_cast_toNat {x : Int} (hx : 0 ≤ x) :
    (((x.toNat : Nat) : Real)) = (x : Real) := by
  norm_cast
  exact Int.toNat_of_nonneg hx

theorem z_at_low_endpoint : int256 (zWord (2 ^ 95)) = (Zc : Int) := by
  decide +kernel

theorem low_z_facts {m : Nat} (hmlo : 2 ^ 95 ≤ m) (hmsc : m < Sc) :
    0 ≤ int256 (zWord m) ∧ int256 (zWord m) ≤ (Zc : Int) := by
  have hr := zWord_range hmlo (by simp only [MHI, Sc] at *; omega)
  have hz := zWord_antitone (m := 2 ^ 95) (m' := m)
    (by simp only [MLO]; exact le_refl _) hmlo
    (by simp only [MHI, Sc] at *; omega)
  rw [z_at_low_endpoint] at hz
  constructor
  · obtain ⟨e2, e3⟩ := zWord_transport hmlo
      (by simp only [MHI, Sc] at *; omega)
    have hden : 0 < int256 (evmAdd m Sc) := by
      rw [e3]
      exact Int.add_pos_of_nonneg_of_pos (Int.ofNat_zero_le m) (by norm_num [Sc])
    have hnum : 0 ≤ int256 (evmShl 100 (evmSub Sc m)) := by
      rw [e2]
      exact Int.mul_nonneg
        (sub_nonneg.mpr (Int.ofNat_le.mpr (Nat.le_of_lt hmsc))) (by norm_num)
    unfold zWord
    rw [evmSdiv_pos_pos (evmShl_lt _ _) (evmAdd_lt _ _) hnum hden]
    exact Int.natCast_nonneg _
  · exact hz

theorem low_u_eq {m : Nat} (hmlo : 2 ^ 95 ≤ m) (hmsc : m < Sc) :
    uWord (zWord m) = uVal (int256 (zWord m)) := by
  have hr := zWord_range hmlo (by simp only [MHI, Sc] at *; omega)
  have hword := uint256OfInt_int256 (w := zWord m) (evmSdiv_lt _ _)
  calc
    uWord (zWord m) = uWord (uint256OfInt (int256 (zWord m))) :=
      congrArg uWord hword.symm
    _ = uVal (int256 (zWord m)) := uWord_eq _ hr.1 hr.2

theorem uVal_floor {z : Int} :
    (uVal z : Int) * 2 ^ 104 ≤ z ^ 2 ∧
      z ^ 2 < ((uVal z : Int) + 1) * 2 ^ 104 := by
  let n := (z * z).toNat
  have hzsq : 0 ≤ z * z := mul_self_nonneg z
  have hncast : (n : Int) = z * z := Int.toNat_of_nonneg hzsq
  have hlo : (n / 2 ^ 104) * 2 ^ 104 ≤ n := Nat.div_mul_le_self _ _
  have hhi : n < (n / 2 ^ 104 + 1) * 2 ^ 104 := by
    have hmod := Nat.mod_lt n (show 0 < 2 ^ 104 by positivity)
    calc
      n = (n / 2 ^ 104) * 2 ^ 104 + n % 2 ^ 104 := by
        rw [mul_comm (n / 2 ^ 104)]
        exact (Nat.div_add_mod _ _).symm
      _ < (n / 2 ^ 104) * 2 ^ 104 + 2 ^ 104 :=
        Nat.add_lt_add_left hmod _
      _ = (n / 2 ^ 104 + 1) * 2 ^ 104 := by omega
  have hloI := Int.ofNat_le.mpr hlo
  have hhiI := Int.ofNat_lt.mpr hhi
  simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one,
    Int.natCast_pow] at hloI hhiI
  unfold uVal
  rw [show (z * z).toNat = n by rfl, pow_two, ← hncast]
  exact ⟨hloI, hhiI⟩

theorem low_u_facts {m : Nat} (hmlo : 2 ^ 95 ≤ m) (hmsc : m < Sc) :
    uWord (zWord m) ≤ Uc ∧
      (uWord (zWord m) : Int) * 2 ^ 104 ≤ int256 (zWord m) ^ 2 ∧
      int256 (zWord m) ^ 2 < ((uWord (zWord m) : Int) + 1) * 2 ^ 104 := by
  have hz := low_z_facts hmlo hmsc
  have huEq := low_u_eq hmlo hmsc
  have hu := uVal_le (int256 (zWord m)) (by simp only [Zc] at hz ⊢; omega)
    (by simp only [Zc] at hz ⊢; omega)
  have hf := uVal_floor (z := int256 (zWord m))
  rw [huEq]
  exact ⟨hu, hf⟩

theorem nat_div_floor_bounds (n d : Nat) (hd : 0 < d) :
    (n / d) * d ≤ n ∧ n < (n / d + 1) * d := by
  constructor
  · exact Nat.div_mul_le_self n d
  · have hmod := Nat.mod_lt n hd
    calc
      n = (n / d) * d + n % d := by
        rw [mul_comm (n / d)]
        exact (Nat.div_add_mod _ _).symm
      _ < (n / d) * d + d := Nat.add_lt_add_left hmod _
      _ = (n / d + 1) * d := by ring

private theorem low_z_num_toNat {m : Nat}
    (hmlo : 2 ^ 95 ≤ m) (hmsc : m < Sc) :
    (int256 (evmShl 100 (evmSub Sc m))).toNat =
      (Sc - m) * wordQ100 := by
  obtain ⟨e2, _⟩ := zWord_transport hmlo
    (by simp only [MHI, Sc] at *; omega)
  have hsub : (0 : Int) ≤ (Sc : Int) - m :=
    sub_nonneg.mpr (Int.ofNat_le.mpr (Nat.le_of_lt hmsc))
  have hsubNat : ((Sc : Int) - m).toNat = Sc - m := by
    simpa using Int.toNat_sub_of_le
      (Int.ofNat_le.mpr (Nat.le_of_lt hmsc))
  have hscale : (0 : Int) ≤ 1267650600228229401496703205376 := by norm_num
  have hscaleNat : (1267650600228229401496703205376 : Int).toNat =
      wordQ100 := by
    change ((1267650600228229401496703205376 : Nat) : Int).toNat = wordQ100
    rw [Int.toNat_natCast]
    norm_num [wordQ100]
  rw [e2, Int.toNat_mul hsub hscale, hsubNat, hscaleNat]

private theorem z_den_toNat {m : Nat} (hmlo : MLO ≤ m) (hmhi : m < MHI) :
    (int256 (evmAdd m Sc)).toNat = m + Sc := by
  obtain ⟨_, e3⟩ := zWord_transport hmlo hmhi
  rw [e3]
  exact_mod_cast Int.toNat_of_nonneg
    (Int.add_nonneg (Int.ofNat_zero_le m) (Int.ofNat_zero_le Sc))

set_option maxRecDepth 12000 in
private theorem low_z_int_eq {m : Nat} (hmlo : 2 ^ 95 ≤ m) (hmsc : m < Sc) :
    int256 (zWord m) =
      Int.ofNat ((Sc - m) * wordQ100 / (m + Sc)) := by
  obtain ⟨e2, e3⟩ := zWord_transport hmlo
    (by simp only [MHI, Sc] at *; omega)
  have hnum : 0 ≤ int256 (evmShl 100 (evmSub Sc m)) := by
    rw [e2]
    exact Int.mul_nonneg
      (sub_nonneg.mpr (Int.ofNat_le.mpr (Nat.le_of_lt hmsc))) (by norm_num)
  have hden : 0 < int256 (evmAdd m Sc) := by
    rw [e3]
    exact Int.add_pos_of_nonneg_of_pos (Int.ofNat_zero_le m) (by norm_num [Sc])
  have hz := evmSdiv_pos_pos (evmShl_lt _ _) (evmAdd_lt _ _) hnum hden
  rw [low_z_num_toNat hmlo hmsc,
    z_den_toNat hmlo (by simp only [MHI, Sc] at *; omega)] at hz
  exact hz

set_option maxRecDepth 32000 in
theorem low_z_nat_eq {m : Nat} (hmlo : 2 ^ 95 ≤ m) (hmsc : m < Sc) :
    (int256 (zWord m)).toNat = (Sc - m) * wordQ100 / (m + Sc) := by
  exact Eq.trans (congrArg Int.toNat (low_z_int_eq hmlo hmsc))
    (Int.toNat_natCast _)

set_option maxRecDepth 16000 in
theorem low_z_floor {m : Nat} (hmlo : 2 ^ 95 ≤ m) (hmsc : m < Sc) :
    let t := ((Sc : Real) - m) / ((Sc : Real) + m)
    normalizedZ m ≤ t ∧ t < normalizedZ m + 1 / wordQ100 := by
  dsimp
  have hzNat := low_z_nat_eq hmlo hmsc
  let n := (Sc - m) * wordQ100
  let d := m + Sc
  have hd : 0 < d := by dsimp [d]; norm_num [Sc]
  obtain ⟨hloNat, hhiNat⟩ := nat_div_floor_bounds n d hd
  dsimp [n, d] at hloNat hhiNat
  rw [← hzNat] at hloNat hhiNat
  have hz0 := (low_z_facts hmlo hmsc).1
  have hloR0 : (((int256 (zWord m)).toNat : Nat) : Real) * (m + Sc) ≤
      ((Sc : Real) - m) * wordQ100 := by
    have h := (Nat.cast_le (α := Real)).mpr hloNat
    push_cast at h
    rw [Nat.cast_sub (Nat.le_of_lt hmsc)] at h
    exact h
  have hhiR0 : ((Sc : Real) - m) * wordQ100 <
      ((((int256 (zWord m)).toNat : Nat) : Real) + 1) * (m + Sc) := by
    have h := (Nat.cast_lt (α := Real)).mpr hhiNat
    push_cast at h
    rw [Nat.cast_sub (Nat.le_of_lt hmsc)] at h
    exact h
  rw [real_cast_toNat hz0] at hloR0 hhiR0
  have hsum : (0 : Real) < (Sc : Real) + m := by
    exact add_pos_of_pos_of_nonneg (by norm_num [Sc]) (Nat.cast_nonneg m)
  have hq : (0 : Real) < wordQ100 := by norm_num [wordQ100]
  constructor
  · unfold normalizedZ
    rw [div_le_div_iff₀ hq hsum]
    simpa [add_comm] using hloR0
  · unfold normalizedZ
    rw [div_lt_iff₀ hsum]
    calc
      (Sc : Real) - m <
          ((int256 (zWord m) : Real) + 1) * (m + Sc) / wordQ100 := by
        rw [lt_div_iff₀ hq]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hhiR0
      _ = ((int256 (zWord m) : Real) / wordQ100 + 1 / wordQ100) *
          ((Sc : Real) + m) := by ring

theorem low_u_floor {m : Nat} (hmlo : 2 ^ 95 ≤ m) (hmsc : m < Sc) :
    normalizedU m ≤ normalizedZ m ^ 2 ∧
      normalizedZ m ^ 2 < normalizedU m + 1 / wordQ96 := by
  obtain ⟨_, hlo, hhi⟩ := low_u_facts hmlo hmsc
  have hloR : ((uWord (zWord m) : Int) : Real) * 2 ^ 104 ≤
      (int256 (zWord m) : Real) ^ 2 := by exact_mod_cast hlo
  have hhiR : (int256 (zWord m) : Real) ^ 2 <
      (((uWord (zWord m) : Int) : Real) + 1) * 2 ^ 104 := by exact_mod_cast hhi
  constructor
  · unfold normalizedU normalizedZ
    calc
      (uWord (zWord m) : Real) / wordQ96 =
          ((uWord (zWord m) : Real) * 2 ^ 104) / 2 ^ 200 := by
        norm_num [wordQ96]
        ring
      _ ≤ (int256 (zWord m) : Real) ^ 2 / 2 ^ 200 :=
        div_le_div_of_nonneg_right hloR (by positivity)
      _ = ((int256 (zWord m) : Real) / wordQ100) ^ 2 := by
        norm_num [wordQ100]
        ring
  · unfold normalizedU normalizedZ
    calc
      ((int256 (zWord m) : Real) / wordQ100) ^ 2 =
          (int256 (zWord m) : Real) ^ 2 / 2 ^ 200 := by
        norm_num [wordQ100]
        ring
      _ < (((uWord (zWord m) : Real) + 1) * 2 ^ 104) / 2 ^ 200 :=
        div_lt_div_of_pos_right hhiR (by positivity)
      _ = (uWord (zWord m) : Real) / wordQ96 + 1 / wordQ96 := by
        norm_num [wordQ96]
        ring

theorem low_endpoint_bounds {m : Nat} (hmlo : 2 ^ 95 ≤ m) (hmsc : m < Sc) :
    let t := ((Sc : Real) - m) / ((Sc : Real) + m)
    0 ≤ normalizedZ m ∧ normalizedZ m ≤ endpointZ ∧
      t ≤ endpointT ∧ endpointT < 1 := by
  dsimp
  have hz := low_z_facts hmlo hmsc
  have hq : (0 : Real) < wordQ100 := by norm_num [wordQ100]
  refine ⟨div_nonneg (by exact_mod_cast hz.1) hq.le, ?_, ?_, ?_⟩
  · unfold normalizedZ endpointZ endpointZWord
    rw [div_le_div_iff_of_pos_right hq]
    simpa only [Zc] using (show (int256 (zWord m) : Real) ≤
      (217494458298375249691265569565 : Real) by exact_mod_cast hz.2)
  · unfold endpointT
    have hd1 : (0 : Real) < (Sc : Real) + m := by
      exact add_pos_of_pos_of_nonneg (by norm_num [Sc]) (Nat.cast_nonneg m)
    have hd2 : (0 : Real) < (Sc : Real) + 2 ^ 95 := by norm_num [Sc]
    have hmloR : ((2 ^ 95 : Nat) : Real) ≤ m := by exact_mod_cast hmlo
    have hdelta : (0 : Real) ≤ (m : Real) - 2 ^ 95 := by
      rw [show (2 : Real) ^ 95 = ((2 ^ 95 : Nat) : Real) by norm_num]
      exact sub_nonneg.mpr hmloR
    rw [div_le_div_iff₀ hd1 hd2]
    have hdiff :
        0 ≤ ((Sc : Real) - 2 ^ 95) * ((Sc : Real) + m) -
          ((Sc : Real) - m) * ((Sc : Real) + 2 ^ 95) := by
      rw [show
        ((Sc : Real) - 2 ^ 95) * ((Sc : Real) + m) -
            ((Sc : Real) - m) * ((Sc : Real) + 2 ^ 95) =
          2 * Sc * (m - 2 ^ 95) by ring]
      exact mul_nonneg (mul_nonneg (by norm_num) (by norm_num [Sc]))
        hdelta
    exact sub_nonneg.mp hdiff
  · unfold endpointT
    rw [div_lt_one (by norm_num [Sc] : (0 : Real) < (Sc : Real) + 2 ^ 95)]
    norm_num [Sc]

theorem z_at_scale : int256 (zWord Sc) = 0 := by
  decide +kernel

theorem high_z_facts {m : Nat} (hscm : Sc ≤ m) (hmhi : m < 2 ^ 96) :
    -(217494458298375249691265569570 : Int) ≤ int256 (zWord m) ∧
      int256 (zWord m) ≤ 0 := by
  have hr := zWord_range (m := m) (by simp only [MLO, Sc] at *; omega)
    (by simpa only [MHI] using hmhi)
  have hz := zWord_antitone (m := Sc) (m' := m)
    (by simp only [MLO, Sc]; omega) hscm (by simpa only [MHI] using hmhi)
  rw [z_at_scale] at hz
  exact ⟨hr.1, hz⟩

theorem high_u_eq {m : Nat} (hscm : Sc ≤ m) (hmhi : m < 2 ^ 96) :
    uWord (zWord m) = uVal (int256 (zWord m)) := by
  have hr := zWord_range (m := m) (by simp only [MLO, Sc] at *; omega)
    (by simpa only [MHI] using hmhi)
  have hword := uint256OfInt_int256 (w := zWord m) (evmSdiv_lt _ _)
  calc
    uWord (zWord m) = uWord (uint256OfInt (int256 (zWord m))) :=
      congrArg uWord hword.symm
    _ = uVal (int256 (zWord m)) := uWord_eq _ hr.1 hr.2

theorem high_u_facts {m : Nat} (hscm : Sc ≤ m) (hmhi : m < 2 ^ 96) :
    uWord (zWord m) ≤ Uc ∧
      (uWord (zWord m) : Int) * 2 ^ 104 ≤ int256 (zWord m) ^ 2 ∧
      int256 (zWord m) ^ 2 < ((uWord (zWord m) : Int) + 1) * 2 ^ 104 := by
  have hz := high_z_facts hscm hmhi
  have huEq := high_u_eq hscm hmhi
  have hu := uVal_le (int256 (zWord m)) (by omega) (by omega)
  have hf := uVal_floor (z := int256 (zWord m))
  rw [huEq]
  exact ⟨hu, hf⟩

private theorem high_z_num_toNat {m : Nat}
    (hscm : Sc ≤ m) (hmhi : m < 2 ^ 96) :
    (-int256 (evmShl 100 (evmSub Sc m))).toNat =
      (m - Sc) * wordQ100 := by
  obtain ⟨e2, _⟩ := zWord_transport
    (m := m) (by simp only [MLO, Sc] at *; omega)
    (by simpa only [MHI] using hmhi)
  rw [e2]
  have he : -(((Sc : Int) - m) * 1267650600228229401496703205376) =
      ((m : Int) - Sc) * 1267650600228229401496703205376 := by ring
  have hsub : (0 : Int) ≤ (m : Int) - Sc :=
    sub_nonneg.mpr (Int.ofNat_le.mpr hscm)
  have hsubNat : ((m : Int) - Sc).toNat = m - Sc := by
    simpa using Int.toNat_sub_of_le (Int.ofNat_le.mpr hscm)
  have hscale : (0 : Int) ≤ 1267650600228229401496703205376 := by norm_num
  have hscaleNat : (1267650600228229401496703205376 : Int).toNat =
      wordQ100 := by
    change ((1267650600228229401496703205376 : Nat) : Int).toNat = wordQ100
    rw [Int.toNat_natCast]
    norm_num [wordQ100]
  rw [he, Int.toNat_mul hsub hscale, hsubNat, hscaleNat]

set_option maxRecDepth 12000 in
private theorem high_z_int_eq {m : Nat}
    (hscm : Sc < m) (hmhi : m < 2 ^ 96) :
    int256 (zWord m) =
      -Int.ofNat ((m - Sc) * wordQ100 / (m + Sc)) := by
  obtain ⟨e2, e3⟩ := zWord_transport
    (m := m) (by simp only [MLO, Sc] at *; omega)
    (by simpa only [MHI] using hmhi)
  have hnum : int256 (evmShl 100 (evmSub Sc m)) < 0 := by
    rw [e2]
    have hsubNeg : (Sc : Int) - m < 0 := sub_neg.mpr (Int.ofNat_lt.mpr hscm)
    exact Int.mul_neg_of_neg_of_pos hsubNeg (by norm_num)
  have hnumMin : -(2 ^ 255) < int256 (evmShl 100 (evmSub Sc m)) := by
    rw [e2]
    simp only [Sc, ipow255] at *
    omega
  have hden : 0 < int256 (evmAdd m Sc) := by
    rw [e3]
    exact Int.add_pos_of_nonneg_of_pos (Int.ofNat_zero_le m) (by norm_num [Sc])
  have hz := evmSdiv_neg_pos (evmShl_lt _ _) (evmAdd_lt _ _)
    hnum hnumMin hden
  have hMloSc : MLO ≤ Sc := by
    simp only [MLO, Sc]
    omega
  have hMloM : MLO ≤ m := hMloSc.trans (Nat.le_of_lt hscm)
  rw [high_z_num_toNat (Nat.le_of_lt hscm) hmhi,
    z_den_toNat hMloM
      (by simpa only [MHI] using hmhi)] at hz
  exact hz

private theorem neg_neg_toNat_natCast (n : Nat) :
    (-(-(n : Int))).toNat = n := by
  rw [neg_neg]
  exact Int.toNat_natCast n

set_option maxRecDepth 32000 in
theorem high_z_nat_eq {m : Nat} (hscm : Sc ≤ m) (hmhi : m < 2 ^ 96) :
    (-int256 (zWord m)).toNat = (m - Sc) * wordQ100 / (m + Sc) := by
  rcases hscm.eq_or_lt with rfl | hscm'
  · rw [z_at_scale]
    simp
  · exact Eq.trans
      (congrArg (fun z : Int => (-z).toNat) (high_z_int_eq hscm' hmhi))
      (neg_neg_toNat_natCast _)

set_option maxRecDepth 16000 in
theorem high_z_floor {m : Nat} (hscm : Sc ≤ m) (hmhi : m < 2 ^ 96) :
    let t := ((m : Real) - Sc) / ((m : Real) + Sc)
    highNormalizedZ m ≤ t ∧ t < highNormalizedZ m + 1 / wordQ100 := by
  dsimp
  rcases hscm.eq_or_lt with rfl | hscm'
  · unfold highNormalizedZ
    rw [z_at_scale]
    norm_num [highNormalizedZ, wordQ100]
  · have hzNat := high_z_nat_eq hscm hmhi
    let n := (m - Sc) * wordQ100
    let d := m + Sc
    have hd : 0 < d := by dsimp [d]; norm_num [Sc]
    obtain ⟨hloNat, hhiNat⟩ := nat_div_floor_bounds n d hd
    dsimp [n, d] at hloNat hhiNat
    rw [← hzNat] at hloNat hhiNat
    have hz0 : 0 ≤ -int256 (zWord m) := neg_nonneg.mpr (high_z_facts hscm hmhi).2
    have hloR0 : (((-int256 (zWord m)).toNat : Nat) : Real) * (m + Sc) ≤
        ((m : Real) - Sc) * wordQ100 := by
      have h := (Nat.cast_le (α := Real)).mpr hloNat
      push_cast at h
      rw [Nat.cast_sub hscm] at h
      exact h
    have hhiR0 : ((m : Real) - Sc) * wordQ100 <
        ((((-int256 (zWord m)).toNat : Nat) : Real) + 1) * (m + Sc) := by
      have h := (Nat.cast_lt (α := Real)).mpr hhiNat
      push_cast at h
      rw [Nat.cast_sub hscm] at h
      exact h
    rw [real_cast_toNat hz0] at hloR0 hhiR0
    have hsum : (0 : Real) < (m : Real) + Sc :=
      add_pos_of_nonneg_of_pos (Nat.cast_nonneg m) (by norm_num [Sc])
    have hq : (0 : Real) < wordQ100 := by norm_num [wordQ100]
    constructor
    · unfold highNormalizedZ
      rw [div_le_div_iff₀ hq hsum]
      simpa using hloR0
    · unfold highNormalizedZ
      rw [div_lt_iff₀ hsum]
      calc
        (m : Real) - Sc <
            ((-int256 (zWord m) : Int) + 1) * (m + Sc) / wordQ100 := by
          rw [lt_div_iff₀ hq]
          simpa [mul_comm, mul_left_comm, mul_assoc] using hhiR0
        _ = (((-int256 (zWord m) : Int) : Real) / wordQ100 + 1 / wordQ100) *
            ((m : Real) + Sc) := by ring

theorem high_u_floor {m : Nat} (hscm : Sc ≤ m) (hmhi : m < 2 ^ 96) :
    normalizedU m ≤ highNormalizedZ m ^ 2 ∧
      highNormalizedZ m ^ 2 < normalizedU m + 1 / wordQ96 := by
  obtain ⟨_, hlo, hhi⟩ := high_u_facts hscm hmhi
  have hloR : ((uWord (zWord m) : Int) : Real) * 2 ^ 104 ≤
      (int256 (zWord m) : Real) ^ 2 := by exact_mod_cast hlo
  have hhiR : (int256 (zWord m) : Real) ^ 2 <
      (((uWord (zWord m) : Int) : Real) + 1) * 2 ^ 104 := by exact_mod_cast hhi
  constructor
  · unfold normalizedU highNormalizedZ
    calc
      (uWord (zWord m) : Real) / wordQ96 =
          ((uWord (zWord m) : Real) * 2 ^ 104) / 2 ^ 200 := by
        norm_num [wordQ96]
        ring
      _ ≤ (int256 (zWord m) : Real) ^ 2 / 2 ^ 200 :=
        div_le_div_of_nonneg_right hloR (by positivity)
      _ = (((-int256 (zWord m) : Int) : Real) / wordQ100) ^ 2 := by
        norm_num [wordQ100]
        ring
  · unfold normalizedU highNormalizedZ
    calc
      (((-int256 (zWord m) : Int) : Real) / wordQ100) ^ 2 =
          (int256 (zWord m) : Real) ^ 2 / 2 ^ 200 := by
        norm_num [wordQ100]
        ring
      _ < (((uWord (zWord m) : Real) + 1) * 2 ^ 104) / 2 ^ 200 :=
        div_lt_div_of_pos_right hhiR (by positivity)
      _ = (uWord (zWord m) : Real) / wordQ96 + 1 / wordQ96 := by
        norm_num [wordQ96]
        ring

theorem high_endpoint_bounds {m : Nat} (hscm : Sc ≤ m) (hmhi : m < 2 ^ 96) :
    let t := ((m : Real) - Sc) / ((m : Real) + Sc)
    0 ≤ highNormalizedZ m ∧ highNormalizedZ m ≤ t ∧ t < 1 := by
  dsimp
  have hz := high_z_facts hscm hmhi
  have hq : (0 : Real) < wordQ100 := by norm_num [wordQ100]
  refine ⟨div_nonneg (by exact_mod_cast neg_nonneg.mpr hz.2) hq.le,
    (high_z_floor hscm hmhi).1, ?_⟩
  rw [div_lt_one (add_pos_of_nonneg_of_pos (Nat.cast_nonneg m)
    (by norm_num [Sc]) : (0 : Real) < (m : Real) + Sc)]
  linarith [show (0 : Real) < Sc by norm_num [Sc]]

end

end LnFloorCarry
