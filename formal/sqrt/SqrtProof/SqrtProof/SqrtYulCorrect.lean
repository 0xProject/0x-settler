import SqrtProof.SqrtYulProof
import SqrtProof.SqrtCorrect

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.style.nameCheck false

namespace SqrtYul

open FormalYul
open SqrtCertified
open SqrtCert

private theorem normStep_eq_bstep (x z : Nat) :
    normShr 1 (normAdd z (normDiv x z)) = bstep x z := by
  simp [normShr, normAdd, normDiv, bstep]

private theorem normSeed_eq_sqrtSeed_of_pos (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    normShl (normShr 1 (normSub 256 (normClz x))) 1 = sqrtSeed x := by
  unfold normShl normShr normSub normClz sqrtSeed
  simp [Nat.ne_of_gt hx]
  have hlog : Nat.log2 x < 256 := (Nat.log2_lt (Nat.ne_of_gt hx)).2 hx256
  have hlogle : Nat.log2 x <= 255 := by omega
  congr 1
  omega

private theorem word_mod_gt_256 : 256 < WORD_MOD := by
  unfold WORD_MOD
  decide

private theorem u256_eq_of_lt (x : Nat) (hx : x < WORD_MOD) : u256 x = x :=
  u256_eq_self_of_lt hx

private theorem evmClz_eq_normClz_of_u256 (x : Nat) (hx : x < WORD_MOD) :
    evmClz x = normClz x := by
  unfold evmClz normClz
  simp [u256_eq_of_lt x hx]

private theorem normClz_le_256 (x : Nat) : normClz x <= 256 := by
  unfold normClz
  split <;> omega

private theorem evmSub_eq_normSub_of_le
    (a b : Nat) (ha : a < WORD_MOD) (hb : b <= a) :
    evmSub a b = normSub a b := by
  have hb' : b < WORD_MOD := Nat.lt_of_le_of_lt hb ha
  have hab' : a - b < WORD_MOD := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
  unfold evmSub normSub
  simp [u256_eq_of_lt a ha, u256_eq_of_lt b hb']
  have hsplit : a + WORD_MOD - b = WORD_MOD + (a - b) := by omega
  unfold u256
  rw [hsplit, Nat.add_mod, Nat.mod_eq_zero_of_dvd (Nat.dvd_refl WORD_MOD), Nat.zero_add]
  simp [Nat.mod_eq_of_lt hab']

private theorem evmDiv_eq_normDiv_of_u256
    (x z : Nat) (hx : x < WORD_MOD) (hz : z < WORD_MOD) :
    evmDiv x z = normDiv x z := by
  by_cases hz0 : z = 0
  · subst hz0
    unfold evmDiv normDiv u256
    simp
  · unfold evmDiv normDiv
    rw [u256_eq_of_lt x hx, u256_eq_of_lt z hz]
    simp [hz0]

private theorem evmAdd_eq_normAdd_of_no_overflow
    (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) (hab : a + b < WORD_MOD) :
    evmAdd a b = normAdd a b := by
  unfold evmAdd normAdd
  simp [u256_eq_of_lt a ha, u256_eq_of_lt b hb, u256_eq_of_lt (a + b) hab]

private theorem evmLt_eq_normLt_of_u256
    (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmLt a b = normLt a b := by
  unfold evmLt normLt
  simp [u256_eq_of_lt a ha, u256_eq_of_lt b hb]

private theorem evmGt_eq_normGt_of_u256
    (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmGt a b = normGt a b := by
  unfold evmGt normGt
  simp [u256_eq_of_lt a ha, u256_eq_of_lt b hb]

private theorem evmShr_eq_normShr_of_u256
    (s v : Nat) (hs : s < 256) (hv : v < WORD_MOD) :
    evmShr s v = normShr s v := by
  unfold evmShr normShr
  have hs' : s < WORD_MOD := Nat.lt_of_lt_of_le hs (Nat.le_of_lt word_mod_gt_256)
  simp [u256_eq_of_lt s hs', u256_eq_of_lt v hv, hs]

private theorem evmShl_eq_normShl_of_safe
    (s v : Nat) (hs : s < 256) (hv : v < WORD_MOD) (hvs : v * 2 ^ s < WORD_MOD) :
    evmShl s v = normShl s v := by
  unfold evmShl normShl
  have hs' : s < WORD_MOD := Nat.lt_of_lt_of_le hs (Nat.le_of_lt word_mod_gt_256)
  simp [u256_eq_of_lt s hs', u256_eq_of_lt v hv, hs, Nat.shiftLeft_eq]
  exact u256_eq_of_lt (v * 2 ^ s) hvs

private theorem two_pow_lt_word (n : Nat) (hn : n < 256) :
    2 ^ n < WORD_MOD := by
  unfold WORD_MOD
  exact Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat)) hn

private theorem zero_lt_word : (0 : Nat) < WORD_MOD := by
  unfold WORD_MOD
  decide

private theorem one_lt_word : (1 : Nat) < WORD_MOD := by
  unfold WORD_MOD
  decide

private theorem pow128_plus_one_lt_word : 2 ^ 128 + 1 < WORD_MOD := by
  unfold WORD_MOD
  decide

private theorem evmLt_le_one (a b : Nat) : evmLt a b <= 1 := by
  unfold evmLt
  split <;> omega

private theorem sqrtLog_norm_lt_256 (x : Nat) :
    normShr 1 (normSub 256 (normClz x)) < 256 := by
  unfold normShr
  have hle : normSub 256 (normClz x) <= 256 := by
    unfold normSub
    exact Nat.sub_le _ _
  have hdiv : normSub 256 (normClz x) / 2 ^ 1 <= 256 / 2 ^ 1 := Nat.div_le_div_right hle
  have hdiv' : normSub 256 (normClz x) / 2 ^ 1 <= 128 := by simpa using hdiv
  omega

private theorem sqrtLog_evm_eq_norm (x : Nat) (hx : x < WORD_MOD) :
    evmShr 1 (evmSub 256 (evmClz x)) =
      normShr 1 (normSub 256 (normClz x)) := by
  have hclz : evmClz x = normClz x := evmClz_eq_normClz_of_u256 x hx
  have hclzLe : normClz x <= 256 := normClz_le_256 x
  have hsub : evmSub 256 (evmClz x) = normSub 256 (normClz x) := by
    have h256 : 256 < WORD_MOD := word_mod_gt_256
    simpa [hclz] using evmSub_eq_normSub_of_le 256 (normClz x) h256 hclzLe
  have hsubLt : normSub 256 (normClz x) < WORD_MOD := by
    have hle : normSub 256 (normClz x) <= 256 := by
      unfold normSub
      exact Nat.sub_le _ _
    exact Nat.lt_of_le_of_lt hle word_mod_gt_256
  have h1 : (1 : Nat) < 256 := by decide
  simpa [hsub] using evmShr_eq_normShr_of_u256 1 (normSub 256 (normClz x)) h1 hsubLt

private theorem seed_evm_eq_norm (x : Nat) (hx : x < WORD_MOD) :
    evmShl (evmShr 1 (evmSub 256 (evmClz x))) 1 =
      normShl (normShr 1 (normSub 256 (normClz x))) 1 := by
  have hshr : evmShr 1 (evmSub 256 (evmClz x)) =
      normShr 1 (normSub 256 (normClz x)) := sqrtLog_evm_eq_norm x hx
  have hsLt256 : normShr 1 (normSub 256 (normClz x)) < 256 := sqrtLog_norm_lt_256 x
  have hsafeMul : 1 * 2 ^ (normShr 1 (normSub 256 (normClz x))) < WORD_MOD := by
    simpa [Nat.one_mul] using two_pow_lt_word (normShr 1 (normSub 256 (normClz x))) hsLt256
  calc
    evmShl (evmShr 1 (evmSub 256 (evmClz x))) 1
        = evmShl (normShr 1 (normSub 256 (normClz x))) 1 := by simp [hshr]
    _ = normShl (normShr 1 (normSub 256 (normClz x))) 1 := by
          have h1word : 1 < WORD_MOD := by unfold WORD_MOD; decide
          simpa [Nat.one_mul] using
            evmShl_eq_normShl_of_safe
              (normShr 1 (normSub 256 (normClz x))) 1 hsLt256 h1word hsafeMul

private theorem step_evm_eq_norm_of_safe
    (x z : Nat) (hx : x < WORD_MOD) (_hzPos : 0 < z) (hz : z < WORD_MOD)
    (hsum : z + x / z < WORD_MOD) :
    evmShr 1 (evmAdd z (evmDiv x z)) = normShr 1 (normAdd z (normDiv x z)) := by
  have hdivLt : x / z < WORD_MOD := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  have hdiv : evmDiv x z = normDiv x z := evmDiv_eq_normDiv_of_u256 x z hx hz
  have hadd : evmAdd z (evmDiv x z) = normAdd z (normDiv x z) := by
    simpa [hdiv] using evmAdd_eq_normAdd_of_no_overflow z (x / z) hz hdivLt hsum
  have hsumLt : normAdd z (normDiv x z) < WORD_MOD := by simpa [normAdd, normDiv] using hsum
  have h1 : (1 : Nat) < 256 := by decide
  calc
    evmShr 1 (evmAdd z (evmDiv x z)) = evmShr 1 (normAdd z (normDiv x z)) := by simp [hadd]
    _ = normShr 1 (normAdd z (normDiv x z)) := by
          simpa using evmShr_eq_normShr_of_u256 1 (normAdd z (normDiv x z)) h1 hsumLt

private theorem m_lt_pow128_of_u256 (m x : Nat) (hmlo : m * m <= x) (hx : x < WORD_MOD) :
    m < 2 ^ 128 := by
  by_cases hm128 : m < 2 ^ 128
  · exact hm128
  · have hmGe : 2 ^ 128 <= m := Nat.le_of_not_lt hm128
    have hmSqGe : 2 ^ 256 <= m * m := by
      have hpow : 2 ^ 256 = (2 ^ 128) * (2 ^ 128) := by
        calc
          2 ^ 256 = 2 ^ (128 + 128) := by decide
          _ = (2 ^ 128) * (2 ^ 128) := by rw [Nat.pow_add]
      have hmul : (2 ^ 128) * (2 ^ 128) <= m * m := Nat.mul_le_mul hmGe hmGe
      simpa [hpow] using hmul
    have hxGe : 2 ^ 256 <= x := Nat.le_trans hmSqGe hmlo
    exact False.elim ((Nat.not_lt_of_ge hxGe) hx)

private theorem innerSqrt_lt_word (x : Nat) (hx : x < WORD_MOD) : innerSqrt x < WORD_MOD := by
  have hbracket := innerSqrt_bracket_u256_all x hx
  have hm128 : natSqrt x < 2 ^ 128 := m_lt_pow128_of_u256 (natSqrt x) x (natSqrt_sq_le x) hx
  have hle : innerSqrt x <= 2 ^ 128 := by
    omega
  have hpow : 2 ^ 128 < WORD_MOD := by
    unfold WORD_MOD
    decide
  exact Nat.lt_of_le_of_lt hle hpow

private theorem x_div_m_le_m_plus_two (x m : Nat) (hm : 0 < m)
    (hmhi : x < (m + 1) * (m + 1)) : x / m <= m + 2 := by
  have hmhi' : x < m * m + 2 * m + 1 := by
    have hsq : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega
    simpa [hsq] using hmhi
  have hmhi'' : x < (m * m + 2 * m) + 1 := by omega
  have hx_le : x <= m * m + 2 * m := Nat.lt_succ_iff.mp hmhi''
  calc
    x / m <= (m * m + 2 * m) / m := Nat.div_le_div_right hx_le
    _ = (m + 2) * m / m := by rw [Nat.add_mul]
    _ = m + 2 := Nat.mul_div_cancel (m + 2) hm

private theorem sum_lt_word_of_cert (x m z d : Nat) (hx : x < WORD_MOD) (hm : 0 < m)
    (hmlo : m * m <= x) (hmhi : x < (m + 1) * (m + 1))
    (hmz : m <= z) (hzd : z - m <= d) (hdm : d <= m) :
    z + x / z < WORD_MOD := by
  have hdiv_z_m : x / z <= x / m := Nat.div_le_div_left hmz hm
  have hdiv_m : x / m <= m + 2 := x_div_m_le_m_plus_two x m hm hmhi
  have hdiv : x / z <= m + 2 := Nat.le_trans hdiv_z_m hdiv_m
  have hz_le_md : z <= d + m := (Nat.sub_le_iff_le_add).1 hzd
  have hz_le_2m : z <= 2 * m := by omega
  have hsum_le : z + x / z <= 3 * m + 2 := by omega
  have hm128 : m < 2 ^ 128 := m_lt_pow128_of_u256 m x hmlo hx
  have hsum_lt_const : z + x / z < 3 * (2 ^ 128) + 2 := by omega
  have hconst : 3 * (2 ^ 128) + 2 < WORD_MOD := by unfold WORD_MOD; decide
  exact Nat.lt_trans hsum_lt_const hconst

private theorem seed_sum_lt_word (i : Fin 256) (x : Nat)
    (hOct : 2 ^ i.val <= x /\ x < 2 ^ (i.val + 1)) :
    seedOf i + x / seedOf i < WORD_MOD := by
  have hsPos : 0 < seedOf i := by
    have hpow : 0 < (2 : Nat) ^ ((i.val + 1) / 2) := Nat.pow_pos (by decide : 0 < (2 : Nat))
    rw [seedOf, Nat.shiftLeft_eq, Nat.one_mul]
    exact hpow
  have hk_le : (i.val + 1) / 2 <= 128 := by omega
  have hz_le : seedOf i <= 2 ^ 128 := by
    unfold seedOf
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.pow_le_pow_right (by decide : (2 : Nat) > 0) hk_le
  have hExp : i.val + 1 <= 2 * ((i.val + 1) / 2) + 1 := by omega
  have hPowLe : 2 ^ (i.val + 1) <= 2 ^ (2 * ((i.val + 1) / 2) + 1) :=
    Nat.pow_le_pow_right (by decide : (2 : Nat) > 0) hExp
  have hPowMul : 2 ^ (2 * ((i.val + 1) / 2) + 1) = 2 * seedOf i * seedOf i := by
    calc
      2 ^ (2 * ((i.val + 1) / 2) + 1) = 2 ^ (2 * ((i.val + 1) / 2)) * 2 := by rw [Nat.pow_add]
      _ = (2 ^ ((i.val + 1) / 2) * 2 ^ ((i.val + 1) / 2)) * 2 := by
            rw [show 2 * ((i.val + 1) / 2) = ((i.val + 1) / 2) + ((i.val + 1) / 2) by omega, Nat.pow_add]
      _ = 2 * seedOf i * seedOf i := by
            unfold seedOf
            simp [Nat.shiftLeft_eq, Nat.mul_comm, Nat.mul_left_comm]
  have hxmul : x < 2 * seedOf i * seedOf i :=
    Nat.lt_of_lt_of_le hOct.2 (by simpa [hPowMul] using hPowLe)
  have hdiv : x / seedOf i < 2 * seedOf i := by
    apply (Nat.div_lt_iff_lt_mul hsPos).2
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hxmul
  have hsum_lt : seedOf i + x / seedOf i < seedOf i + 2 * seedOf i := by omega
  have hsum_le : seedOf i + 2 * seedOf i <= 3 * (2 ^ 128) := by omega
  have hconst : 3 * (2 ^ 128) < WORD_MOD := by unfold WORD_MOD; decide
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hsum_lt hsum_le) (Nat.le_of_lt hconst)

private theorem normLt_div_le (x z : Nat) :
    normLt (normDiv x z) z <= z := by
  by_cases hz0 : z = 0
  · simp [normLt, normDiv, hz0]
  · have hzPos : 0 < z := Nat.pos_of_ne_zero hz0
    have h1 : 1 <= z := Nat.succ_le_of_lt hzPos
    by_cases hlt : x / z < z
    · simp [normLt, normDiv, hlt, h1]
    · simp [normLt, normDiv, hlt]

private theorem floor_correction_norm_eq_if (x z : Nat) :
    normSub z (normLt (normDiv x z) z) =
      (if z = 0 then 0 else if x / z < z then z - 1 else z) := by
  by_cases hz0 : z = 0
  · subst hz0
    simp [normSub, normLt, normDiv]
  · by_cases hlt : x / z < z
    · simp [normSub, normLt, normDiv, hz0, hlt]
    · simp [normSub, normLt, normDiv, hz0, hlt]

private theorem floor_step_evm_eq_norm
    (x z : Nat)
    (hx : x < WORD_MOD)
    (hz : z < WORD_MOD) :
    evmSub z (evmLt (evmDiv x z) z) =
      normSub z (normLt (normDiv x z) z) := by
  have hdiv : evmDiv x z = normDiv x z := evmDiv_eq_normDiv_of_u256 x z hx hz
  have hdivLt : normDiv x z < WORD_MOD := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  have hlt : evmLt (evmDiv x z) z = normLt (normDiv x z) z := by
    simpa [hdiv] using evmLt_eq_normLt_of_u256 (normDiv x z) z hdivLt hz
  have hbLe : normLt (normDiv x z) z <= z := normLt_div_le x z
  calc
    evmSub z (evmLt (evmDiv x z) z)
        = evmSub z (normLt (normDiv x z) z) := by simp [hlt]
    _ = normSub z (normLt (normDiv x z) z) :=
          evmSub_eq_normSub_of_le z (normLt (normDiv x z) z) hz hbLe

private theorem floorSqrt_evmCorrection_eq
    (x : Nat)
    (hx : x < WORD_MOD) :
    evmSub (innerSqrt x) (evmLt (evmDiv x (innerSqrt x)) (innerSqrt x)) =
      floorSqrt x := by
  have hz : innerSqrt x < WORD_MOD := innerSqrt_lt_word x hx
  have hstep := floor_step_evm_eq_norm x (innerSqrt x) hx hz
  unfold floorSqrt
  simpa [floor_correction_norm_eq_if] using hstep

private theorem floorSqrt_lt_word (x : Nat) (hx : x < WORD_MOD) :
    floorSqrt x < WORD_MOD := by
  have hinner : innerSqrt x < WORD_MOD := innerSqrt_lt_word x hx
  have hle : floorSqrt x <= innerSqrt x := by
    unfold floorSqrt
    by_cases hz : innerSqrt x = 0
    · simp [hz]
    · by_cases hlt : x / innerSqrt x < innerSqrt x
      · simp [hz, hlt]
      · simp [hz, hlt]
  exact Nat.lt_of_le_of_lt hle hinner

private theorem sqrtUp256_lt_word (x : Nat) (hx : x < WORD_MOD) :
    sqrtUp256 x < WORD_MOD := by
  have hfloor : floorSqrt x = natSqrt x :=
    floorSqrt_eq_natSqrt_u256 x (by simpa [WORD_MOD] using hx)
  have hm128 : natSqrt x < 2 ^ 128 :=
    m_lt_pow128_of_u256 (natSqrt x) x (natSqrt_sq_le x) hx
  have hpow : 2 ^ 128 < WORD_MOD := by
    unfold WORD_MOD
    decide
  unfold sqrtUp256
  rw [hfloor]
  change (if natSqrt x * natSqrt x < x then natSqrt x + 1 else natSqrt x) < WORD_MOD
  by_cases hlt : natSqrt x * natSqrt x < x
  · simp [hlt]
    exact Nat.lt_of_le_of_lt (by omega : natSqrt x + 1 <= 2 ^ 128) hpow
  · simp [hlt]
    exact Nat.lt_of_lt_of_le hm128 (Nat.le_of_lt hpow)

private theorem sqrtUp_step_evm_eq_inner_round
    (x z : Nat)
    (hxW : x < WORD_MOD)
    (hzLe128 : z <= 2 ^ 128) :
    evmAdd (evmGt (evmLt (evmMul z z) x) (evmLt (evmMul z z) z)) z =
      (if z * z < x then z + 1 else z) := by
  have hpow128 : 2 ^ 128 < WORD_MOD := two_pow_lt_word 128 (by decide)
  have hzW : z < WORD_MOD := Nat.lt_of_le_of_lt hzLe128 hpow128
  by_cases hzMax : z = 2 ^ 128
  · have hsqEq : z * z = WORD_MOD := by
      rw [hzMax]
      unfold WORD_MOD
      calc
        (2 ^ 128) * (2 ^ 128) = 2 ^ (128 + 128) := by rw [← Nat.pow_add]
        _ = 2 ^ 256 := by decide
    have hmul0 : evmMul z z = 0 := by
      unfold evmMul u256
      simp [hsqEq]
    have hzPos : 0 < z := by
      rw [hzMax]
      exact Nat.two_pow_pos 128
    have hltZ1 : evmLt (evmMul z z) z = 1 := by
      rw [hmul0]
      have hltEq : evmLt 0 z = normLt 0 z := evmLt_eq_normLt_of_u256 0 z zero_lt_word hzW
      have hnorm1 : normLt 0 z = 1 := by
        unfold normLt
        simp [hzPos]
      exact hltEq.trans hnorm1
    have hltXLe : evmLt (evmMul z z) x <= 1 := evmLt_le_one (evmMul z z) x
    have hltXW : evmLt (evmMul z z) x < WORD_MOD := Nat.lt_of_le_of_lt hltXLe one_lt_word
    have hgt0 : evmGt (evmLt (evmMul z z) x) (evmLt (evmMul z z) z) = 0 := by
      rw [hltZ1]
      have hgtEq :
          evmGt (evmLt (evmMul z z) x) 1 = normGt (evmLt (evmMul z z) x) 1 :=
        evmGt_eq_normGt_of_u256 (evmLt (evmMul z z) x) 1 hltXW one_lt_word
      have hnorm0 : normGt (evmLt (evmMul z z) x) 1 = 0 := by
        unfold normGt
        have hnot : ¬ evmLt (evmMul z z) x > 1 := Nat.not_lt_of_ge hltXLe
        simp [hnot]
      exact hgtEq.trans hnorm0
    have hadd0 : evmAdd 0 z = z := by
      have h := evmAdd_eq_normAdd_of_no_overflow 0 z zero_lt_word hzW (by simpa using hzW)
      simpa [normAdd] using h
    have hsqNotLt : ¬ z * z < x := by
      rw [hsqEq]
      exact Nat.not_lt_of_ge (Nat.le_of_lt hxW)
    calc
      evmAdd (evmGt (evmLt (evmMul z z) x) (evmLt (evmMul z z) z)) z
          = evmAdd 0 z := by simp [hgt0]
      _ = z := hadd0
      _ = if z * z < x then z + 1 else z := by simp [hsqNotLt]
  · have hzLt : z < 2 ^ 128 := Nat.lt_of_le_of_ne hzLe128 hzMax
    have hzzW : z * z < WORD_MOD := by
      have hmulLe : z * z <= z * (2 ^ 128) := Nat.mul_le_mul_left z (Nat.le_of_lt hzLt)
      have hmulLt : z * (2 ^ 128) < (2 ^ 128) * (2 ^ 128) :=
        Nat.mul_lt_mul_of_pos_right hzLt (Nat.two_pow_pos 128)
      have hlt : z * z < (2 ^ 128) * (2 ^ 128) := Nat.lt_of_le_of_lt hmulLe hmulLt
      have hpowEq : (2 ^ 128) * (2 ^ 128) = WORD_MOD := by
        unfold WORD_MOD
        calc
          (2 ^ 128) * (2 ^ 128) = 2 ^ (128 + 128) := by rw [← Nat.pow_add]
          _ = 2 ^ 256 := by decide
      simpa [hpowEq] using hlt
    have hmulNat : evmMul z z = z * z := by
      unfold evmMul
      simp [u256_eq_of_lt z hzW, u256_eq_of_lt (z * z) hzzW]
    have hsqGe : z <= z * z := by
      by_cases hz0 : z = 0
      · simp [hz0]
      · have hzPos : 0 < z := Nat.pos_of_ne_zero hz0
        have h1 : 1 <= z := Nat.succ_le_of_lt hzPos
        calc
          z = z * 1 := by simp
          _ <= z * z := Nat.mul_le_mul_left z h1
    have hltZ0 : evmLt (evmMul z z) z = 0 := by
      rw [hmulNat]
      unfold evmLt
      have hnot : ¬ z * z < z := Nat.not_lt_of_ge hsqGe
      simp [u256_eq_of_lt (z * z) hzzW, u256_eq_of_lt z hzW, hnot]
    by_cases hsqx : z * z < x
    · have hltX1 : evmLt (evmMul z z) x = 1 := by
        rw [hmulNat]
        unfold evmLt
        simp [u256_eq_of_lt (z * z) hzzW, u256_eq_of_lt x hxW, hsqx]
      have hgt1 : evmGt (evmLt (evmMul z z) x) (evmLt (evmMul z z) z) = 1 := by
        rw [hltX1, hltZ0]
        have hgtEq : evmGt 1 0 = normGt 1 0 :=
          evmGt_eq_normGt_of_u256 1 0 one_lt_word zero_lt_word
        have hnorm1 : normGt 1 0 = 1 := by
          unfold normGt
          decide
        exact hgtEq.trans hnorm1
      have hsum1 : 1 + z < WORD_MOD := by
        have hle : 1 + z <= 1 + 2 ^ 128 := by omega
        exact Nat.lt_of_le_of_lt hle pow128_plus_one_lt_word
      have hadd1 : evmAdd 1 z = z + 1 := by
        have h := evmAdd_eq_normAdd_of_no_overflow 1 z one_lt_word hzW hsum1
        simpa [normAdd, Nat.add_comm] using h
      calc
        evmAdd (evmGt (evmLt (evmMul z z) x) (evmLt (evmMul z z) z)) z
            = evmAdd 1 z := by simp [hgt1]
        _ = z + 1 := hadd1
        _ = if z * z < x then z + 1 else z := by simp [hsqx]
    · have hltX0 : evmLt (evmMul z z) x = 0 := by
        rw [hmulNat]
        unfold evmLt
        simp [u256_eq_of_lt (z * z) hzzW, u256_eq_of_lt x hxW, hsqx]
      have hgt0 : evmGt (evmLt (evmMul z z) x) (evmLt (evmMul z z) z) = 0 := by
        rw [hltX0, hltZ0]
        unfold evmGt
        simp
      have hadd0 : evmAdd 0 z = z := by
        have h := evmAdd_eq_normAdd_of_no_overflow 0 z zero_lt_word hzW (by simpa using hzW)
        simpa [normAdd] using h
      calc
        evmAdd (evmGt (evmLt (evmMul z z) x) (evmLt (evmMul z z) z)) z
            = evmAdd 0 z := by simp [hgt0]
        _ = z := hadd0
        _ = if z * z < x then z + 1 else z := by simp [hsqx]

private theorem innerSqrt_evmSteps_eq (x : Nat) (hx256 : x < WORD_MOD) :
    let q := evmShr 1 (evmSub 256 (evmClz x))
    let z0 := evmShl q 1
    let z1 := evmShr 1 (evmAdd z0 (evmShr q x))
    let z2 := evmShr 1 (evmAdd z1 (evmDiv x z1))
    let z3 := evmShr 1 (evmAdd z2 (evmDiv x z2))
    let z4 := evmShr 1 (evmAdd z3 (evmDiv x z3))
    let z5 := evmShr 1 (evmAdd z4 (evmDiv x z4))
    evmShr 1 (evmAdd z5 (evmDiv x z5)) = innerSqrt x := by
  by_cases hx0 : x = 0
  · subst hx0
    simp [innerSqrt, evmShr, evmSub, evmClz, evmShl, evmAdd, evmDiv, u256, WORD_MOD]
  · have hx : 0 < x := Nat.pos_of_ne_zero hx0
    let i : Fin 256 := ⟨Nat.log2 x, (Nat.log2_lt (Nat.ne_of_gt hx)).2 hx256⟩
    let m := natSqrt x
    have hmlo : m * m <= x := by simpa [m] using natSqrt_sq_le x
    have hmhi : x < (m + 1) * (m + 1) := by simpa [m] using natSqrt_lt_succ_sq x
    have hOct : 2 ^ i.val <= x /\ x < 2 ^ (i.val + 1) := by
      have hlog : 2 ^ Nat.log2 x <= x /\ x < 2 ^ (Nat.log2 x + 1) :=
        (SqrtCompat.log2_eq_iff (Nat.ne_of_gt hx)).1 rfl
      simpa [i]
    have hm : 0 < m := by
      by_cases hm0 : m = 0
      · have hx1 : 1 <= x := Nat.succ_le_of_lt hx
        have hlt1 : x < 1 := by
          have : x < (0 + 1) * (0 + 1) := by simpa [hm0, m] using hmhi
          simpa using this
        exact False.elim ((Nat.not_lt_of_ge hx1) hlt1)
      · exact Nat.pos_of_ne_zero hm0
    have hseedOf : sqrtSeed x = seedOf i := sqrtSeed_eq_seedOf_of_octave i x hOct
    have hseedNorm : normShl (normShr 1 (normSub 256 (normClz x))) 1 = seedOf i := by
      exact (normSeed_eq_sqrtSeed_of_pos x hx (by simpa [WORD_MOD] using hx256)).trans hseedOf
    have hseedEvm : evmShl (evmShr 1 (evmSub 256 (evmClz x))) 1 = seedOf i := by
      exact (seed_evm_eq_norm x hx256).trans hseedNorm
    have hqEvm : evmShr 1 (evmSub 256 (evmClz x)) = normShr 1 (normSub 256 (normClz x)) :=
      sqrtLog_evm_eq_norm x hx256
    have hqLt : normShr 1 (normSub 256 (normClz x)) < 256 := sqrtLog_norm_lt_256 x
    let z0 := seedOf i
    let z1 := bstep x z0
    let z2 := bstep x z1
    let z3 := bstep x z2
    let z4 := bstep x z3
    let z5 := bstep x z4
    let z6 := bstep x z5
    have hsPos : 0 < z0 := by
      dsimp [z0]
      have hpow : 0 < (2 : Nat) ^ ((i.val + 1) / 2) := Nat.pow_pos (by decide : 0 < (2 : Nat))
      rw [seedOf, Nat.shiftLeft_eq, Nat.one_mul]
      exact hpow
    have hmz1 : m <= z1 := by dsimp [z1, z0]; exact babylon_step_floor_bound x (seedOf i) m hsPos hmlo
    have hz1Pos : 0 < z1 := Nat.lt_of_lt_of_le hm hmz1
    have hmz2 : m <= z2 := by dsimp [z2]; exact babylon_step_floor_bound x z1 m hz1Pos hmlo
    have hz2Pos : 0 < z2 := Nat.lt_of_lt_of_le hm hmz2
    have hmz3 : m <= z3 := by dsimp [z3]; exact babylon_step_floor_bound x z2 m hz2Pos hmlo
    have hz3Pos : 0 < z3 := Nat.lt_of_lt_of_le hm hmz3
    have hmz4 : m <= z4 := by dsimp [z4]; exact babylon_step_floor_bound x z3 m hz3Pos hmlo
    have hz4Pos : 0 < z4 := Nat.lt_of_lt_of_le hm hmz4
    have hmz5 : m <= z5 := by dsimp [z5]; exact babylon_step_floor_bound x z4 m hz4Pos hmlo
    have hz5Pos : 0 < z5 := Nat.lt_of_lt_of_le hm hmz5
    have hinterval : loOf i <= m /\ m <= hiOf i := m_within_cert_interval i x m hmlo hmhi hOct
    have hrun5 := run5_error_bounds i x m hm hmlo hmhi hinterval.1 hinterval.2
    have hd1 : z1 - m <= d1 i := by simpa [z1, z2, z3, z4, z5] using hrun5.1
    have hd2 : z2 - m <= d2 i := by simpa [z1, z2, z3, z4, z5] using hrun5.2.1
    have hd3 : z3 - m <= d3 i := by simpa [z1, z2, z3, z4, z5] using hrun5.2.2.1
    have hd4 : z4 - m <= d4 i := by simpa [z1, z2, z3, z4, z5] using hrun5.2.2.2.1
    have hd5 : z5 - m <= d5 i := by simpa [z1, z2, z3, z4, z5] using hrun5.2.2.2.2
    have hd1m : d1 i <= m := Nat.le_trans (d1_le_lo i) hinterval.1
    have hd2m : d2 i <= m := Nat.le_trans (d2_le_lo i) hinterval.1
    have hd3m : d3 i <= m := Nat.le_trans (d3_le_lo i) hinterval.1
    have hd4m : d4 i <= m := Nat.le_trans (d4_le_lo i) hinterval.1
    have hd5m : d5 i <= m := Nat.le_trans (d5_le_lo i) hinterval.1
    have hsum0 : z0 + x / z0 < WORD_MOD := by simpa [z0] using seed_sum_lt_word i x hOct
    have hsum1 : z1 + x / z1 < WORD_MOD := sum_lt_word_of_cert x m z1 (d1 i) hx256 hm hmlo hmhi hmz1 hd1 hd1m
    have hsum2 : z2 + x / z2 < WORD_MOD := sum_lt_word_of_cert x m z2 (d2 i) hx256 hm hmlo hmhi hmz2 hd2 hd2m
    have hsum3 : z3 + x / z3 < WORD_MOD := sum_lt_word_of_cert x m z3 (d3 i) hx256 hm hmlo hmhi hmz3 hd3 hd3m
    have hsum4 : z4 + x / z4 < WORD_MOD := sum_lt_word_of_cert x m z4 (d4 i) hx256 hm hmlo hmhi hmz4 hd4 hd4m
    have hsum5 : z5 + x / z5 < WORD_MOD := sum_lt_word_of_cert x m z5 (d5 i) hx256 hm hmlo hmhi hmz5 hd5 hd5m
    have hz0 : z0 < WORD_MOD := Nat.lt_of_le_of_lt (Nat.le_add_right z0 (x / z0)) hsum0
    have hz1 : z1 < WORD_MOD := Nat.lt_of_le_of_lt (Nat.le_add_right z1 (x / z1)) hsum1
    have hz2 : z2 < WORD_MOD := Nat.lt_of_le_of_lt (Nat.le_add_right z2 (x / z2)) hsum2
    have hz3 : z3 < WORD_MOD := Nat.lt_of_le_of_lt (Nat.le_add_right z3 (x / z3)) hsum3
    have hz4 : z4 < WORD_MOD := Nat.lt_of_le_of_lt (Nat.le_add_right z4 (x / z4)) hsum4
    have hz5 : z5 < WORD_MOD := Nat.lt_of_le_of_lt (Nat.le_add_right z5 (x / z5)) hsum5
    have hshiftDiv : evmShr (evmShr 1 (evmSub 256 (evmClz x))) x = x / z0 := by
      calc
        evmShr (evmShr 1 (evmSub 256 (evmClz x))) x = evmShr (normShr 1 (normSub 256 (normClz x))) x := by simp [hqEvm]
        _ = normShr (normShr 1 (normSub 256 (normClz x))) x := by
              simpa using evmShr_eq_normShr_of_u256 (normShr 1 (normSub 256 (normClz x))) x hqLt hx256
        _ = x / z0 := by
              dsimp [z0]
              rw [<- hseedNorm]
              simp [normShr, normShl, Nat.shiftLeft_eq]
    have hfirstEvm : evmShr 1 (evmAdd z0 (evmShr (evmShr 1 (evmSub 256 (evmClz x))) x)) = z1 := by
      have hdivLt : x / z0 < WORD_MOD := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx256
      have hadd : evmAdd z0 (evmShr (evmShr 1 (evmSub 256 (evmClz x))) x) = normAdd z0 (normDiv x z0) := by
        simpa [hshiftDiv, normDiv] using evmAdd_eq_normAdd_of_no_overflow z0 (x / z0) hz0 hdivLt hsum0
      have hsumLt : normAdd z0 (normDiv x z0) < WORD_MOD := by simpa [normAdd, normDiv] using hsum0
      have h1 : (1 : Nat) < 256 := by decide
      calc
        evmShr 1 (evmAdd z0 (evmShr (evmShr 1 (evmSub 256 (evmClz x))) x)) = evmShr 1 (normAdd z0 (normDiv x z0)) := by simp [hadd]
        _ = normShr 1 (normAdd z0 (normDiv x z0)) := by
              simpa using evmShr_eq_normShr_of_u256 1 (normAdd z0 (normDiv x z0)) h1 hsumLt
        _ = z1 := by simp [z1, normStep_eq_bstep]
    have hstep2 : evmShr 1 (evmAdd z1 (evmDiv x z1)) = z2 := by
      have h := step_evm_eq_norm_of_safe x z1 hx256 hz1Pos hz1 hsum1
      simpa [z2, normStep_eq_bstep] using h
    have hstep3 : evmShr 1 (evmAdd z2 (evmDiv x z2)) = z3 := by
      have h := step_evm_eq_norm_of_safe x z2 hx256 hz2Pos hz2 hsum2
      simpa [z3, normStep_eq_bstep] using h
    have hstep4 : evmShr 1 (evmAdd z3 (evmDiv x z3)) = z4 := by
      have h := step_evm_eq_norm_of_safe x z3 hx256 hz3Pos hz3 hsum3
      simpa [z4, normStep_eq_bstep] using h
    have hstep5 : evmShr 1 (evmAdd z4 (evmDiv x z4)) = z5 := by
      have h := step_evm_eq_norm_of_safe x z4 hx256 hz4Pos hz4 hsum4
      simpa [z5, normStep_eq_bstep] using h
    have hstep6 : evmShr 1 (evmAdd z5 (evmDiv x z5)) = z6 := by
      have h := step_evm_eq_norm_of_safe x z5 hx256 hz5Pos hz5 hsum5
      simpa [z6, normStep_eq_bstep] using h
    unfold innerSqrt
    simp [Nat.ne_of_gt hx, hseedOf, hseedEvm, z0, z1, z2, z3, z4, z5, z6,
      hfirstEvm, hstep2, hstep3, hstep4, hstep5, hstep6]

 private theorem call_zero_value_for_split_t_uint256_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [] (.some "zero_value_for_split_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_zero_value_for_split_t_uint256]
  simp only [yulFunction_zero_value_for_split_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore, EvmYul.Yul.State.toMachineState,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne, FormalYul.word]

private theorem call_fun__sqrt_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 200) [FormalYul.word x] (.some yulName_fun__sqrt)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (innerSqrt (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__sqrt]
  simp only [yulFunction_fun__sqrt, yulFunction_fun__sqrt_11,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne, FormalYul.word,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 176)
      (shared := shared)
      (store := Finmap.insert "var_x_4" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_shiftRight, FormalYul.Preservation.wordNat_shiftLeft,
    FormalYul.Preservation.wordNat_add, FormalYul.Preservation.wordNat_sub,
    FormalYul.Preservation.wordNat_div, FormalYul.Preservation.wordNat_clz,
    FormalYul.Preservation.wordNat_ofNat]
  have hinnerLt : innerSqrt (FormalYul.u256 x) < WORD_MOD :=
    innerSqrt_lt_word (FormalYul.u256 x)
      (by exact Nat.mod_lt x (by unfold WORD_MOD; exact Nat.two_pow_pos 256))
  simpa [FormalYul.Preservation.evmShr_u256_left, FormalYul.Preservation.evmShr_u256_right,
    FormalYul.Preservation.evmShl_u256_left, FormalYul.Preservation.evmShl_u256_right,
    FormalYul.Preservation.evmSub_u256_left, FormalYul.Preservation.evmSub_u256_right,
    FormalYul.Preservation.evmAdd_u256_left, FormalYul.Preservation.evmAdd_u256_right,
    FormalYul.Preservation.evmDiv_u256_left, FormalYul.Preservation.evmDiv_u256_right,
    FormalYul.Preservation.evmClz_u256, FormalYul.u256_u256,
    FormalYul.Preservation.u256_evmShr, u256_eq_of_lt _ hinnerLt] using
    innerSqrt_evmSteps_eq (FormalYul.u256 x)
      (by exact Nat.mod_lt x (by unfold WORD_MOD; exact Nat.two_pow_pos 256))

private theorem call_fun_sqrt_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 360) [FormalYul.word x] (.some yulName_fun_sqrt)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (floorSqrt (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_sqrt]
  simp only [yulFunction_fun_sqrt, yulFunction_fun_sqrt_27,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hsqrtFuel : fuel + 352 = (fuel + 152) + 200 := by omega
  have hCallSqrt :=
    call_fun__sqrt_direct (x := x) (fuel := fuel + 152) (shared := shared)
      (store := Finmap.insert "expr_21"
        (EvmYul.UInt256.ofNat x)
        (Finmap.insert "_6"
          (EvmYul.UInt256.ofNat x)
          (Finmap.insert "var_z_17" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "zero_t_uint256_5" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "var_x_14" (EvmYul.UInt256.ofNat x)
                (Inhabited.default : EvmYul.Yul.VarStore))))))
      (hlookup := hlookup)
  simp [FormalYul.word, yulName_fun__sqrt] at hCallSqrt
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne, FormalYul.word, yulName_fun__sqrt,
    hsqrtFuel, hCallSqrt,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 336)
      (shared := shared)
      (store := Finmap.insert "var_x_14" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_sub, FormalYul.Preservation.wordNat_lt,
    FormalYul.Preservation.wordNat_div, FormalYul.Preservation.wordNat_ofNat]
  have hxW : FormalYul.u256 x < WORD_MOD :=
    Nat.mod_lt x (by unfold WORD_MOD; exact Nat.two_pow_pos 256)
  have hinnerW : innerSqrt (FormalYul.u256 x) < WORD_MOD :=
    innerSqrt_lt_word (FormalYul.u256 x) hxW
  have hfloorW : floorSqrt (FormalYul.u256 x) < WORD_MOD :=
    floorSqrt_lt_word (FormalYul.u256 x) hxW
  have hcorr := floorSqrt_evmCorrection_eq (FormalYul.u256 x) hxW
  simpa [FormalYul.Preservation.evmSub_u256_left, FormalYul.Preservation.evmSub_u256_right,
    FormalYul.Preservation.evmLt_u256_left, FormalYul.Preservation.evmLt_u256_right,
    FormalYul.Preservation.evmDiv_u256_left, FormalYul.Preservation.evmDiv_u256_right,
    FormalYul.u256_u256, u256_eq_of_lt _ hinnerW, u256_eq_of_lt _ hfloorW] using hcorr

private theorem call_fun_sqrtUp_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 420) [FormalYul.word x] (.some yulName_fun_sqrtUp)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (sqrtUp256 (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_sqrtUp]
  simp only [yulFunction_fun_sqrtUp, yulFunction_fun_sqrtUp_43,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hCallSqrt :=
    call_fun__sqrt_direct (x := x) (fuel := fuel + 212) (shared := shared)
      (store := Finmap.insert "expr_37"
        (EvmYul.UInt256.ofNat x)
        (Finmap.insert "_8"
          (EvmYul.UInt256.ofNat x)
          (Finmap.insert "var_z_33" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "zero_t_uint256_7" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "var_x_30" (EvmYul.UInt256.ofNat x)
                (Inhabited.default : EvmYul.Yul.VarStore))))))
      (hlookup := hlookup)
  simp [FormalYul.word, yulName_fun__sqrt] at hCallSqrt
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne, FormalYul.word, yulName_fun__sqrt,
    hCallSqrt,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 396)
      (shared := shared)
      (store := Finmap.insert "var_x_30" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_add, FormalYul.Preservation.wordNat_gt,
    FormalYul.Preservation.wordNat_lt, FormalYul.Preservation.wordNat_mul,
    FormalYul.Preservation.wordNat_ofNat]
  have hxW : FormalYul.u256 x < WORD_MOD :=
    Nat.mod_lt x (by unfold WORD_MOD; exact Nat.two_pow_pos 256)
  have hbr : natSqrt (FormalYul.u256 x) <= innerSqrt (FormalYul.u256 x) ∧
      innerSqrt (FormalYul.u256 x) <= natSqrt (FormalYul.u256 x) + 1 := by
    simpa using innerSqrt_bracket_u256_all (FormalYul.u256 x)
      (by simpa [WORD_MOD] using hxW)
  have hm128 : natSqrt (FormalYul.u256 x) < 2 ^ 128 :=
    m_lt_pow128_of_u256 (natSqrt (FormalYul.u256 x)) (FormalYul.u256 x)
      (natSqrt_sq_le (FormalYul.u256 x)) hxW
  have hinnerW : innerSqrt (FormalYul.u256 x) < WORD_MOD :=
    innerSqrt_lt_word (FormalYul.u256 x) hxW
  have hzLe128 : innerSqrt (FormalYul.u256 x) <= 2 ^ 128 := by omega
  have hround :=
    sqrtUp_step_evm_eq_inner_round (FormalYul.u256 x) (innerSqrt (FormalYul.u256 x))
      hxW hzLe128
  have hceil :=
    sqrtUpInner_eq_sqrtUp256_u256 (FormalYul.u256 x) (by simpa [WORD_MOD] using hxW)
  have hupW : sqrtUp256 (FormalYul.u256 x) < WORD_MOD := sqrtUp256_lt_word (FormalYul.u256 x) hxW
  simpa [FormalYul.Preservation.evmAdd_u256_left, FormalYul.Preservation.evmAdd_u256_right,
    FormalYul.Preservation.evmGt_u256_left, FormalYul.Preservation.evmGt_u256_right,
    FormalYul.Preservation.evmLt_u256_left, FormalYul.Preservation.evmLt_u256_right,
    FormalYul.Preservation.evmMul_u256_left, FormalYul.Preservation.evmMul_u256_right,
    FormalYul.u256_u256, u256_eq_of_lt _ hinnerW, u256_eq_of_lt _ hupW] using hround.trans hceil

private theorem call_fun_wrap_sqrt_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 460) [FormalYul.word x] (.some yulName_fun_wrap_sqrt)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (floorSqrt (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_wrap_sqrt]
  simp only [yulFunction_fun_wrap_sqrt, yulFunction_fun_wrap_sqrt_62,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hsqrtFuel : fuel + 451 = (fuel + 91) + 360 := by omega
  have hCallSqrt :=
    call_fun_sqrt_direct (x := x) (fuel := fuel + 91) (shared := shared)
      (store := Finmap.insert "expr_58"
        (EvmYul.UInt256.ofNat x)
        (Finmap.insert "_2"
          (EvmYul.UInt256.ofNat x)
          (Finmap.insert "expr_56_address" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "var__54" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "zero_t_uint256_1" (EvmYul.UInt256.ofNat 0)
                (Finmap.insert "var_x_51" (EvmYul.UInt256.ofNat x)
                  (Inhabited.default : EvmYul.Yul.VarStore)))))))
      (hlookup := hlookup)
  simp [FormalYul.word, yulName_fun_sqrt] at hCallSqrt
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne, FormalYul.word, yulName_fun_sqrt,
    hsqrtFuel, hCallSqrt,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 436)
      (shared := shared)
      (store := Finmap.insert "var_x_51" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]

private theorem call_fun_wrap_sqrtUp_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 520) [FormalYul.word x] (.some yulName_fun_wrap_sqrtUp)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (sqrtUp256 (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_wrap_sqrtUp]
  simp only [yulFunction_fun_wrap_sqrtUp, yulFunction_fun_wrap_sqrtUp_75,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hsqrtFuel : fuel + 511 = (fuel + 91) + 420 := by omega
  have hCallSqrt :=
    call_fun_sqrtUp_direct (x := x) (fuel := fuel + 91) (shared := shared)
      (store := Finmap.insert "expr_71"
        (EvmYul.UInt256.ofNat x)
        (Finmap.insert "_4"
          (EvmYul.UInt256.ofNat x)
          (Finmap.insert "expr_69_address" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "var__67" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "zero_t_uint256_3" (EvmYul.UInt256.ofNat 0)
                (Finmap.insert "var_x_64" (EvmYul.UInt256.ofNat x)
                  (Inhabited.default : EvmYul.Yul.VarStore)))))))
      (hlookup := hlookup)
  simp [FormalYul.word, yulName_fun_sqrtUp] at hCallSqrt
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne, FormalYul.word, yulName_fun_sqrtUp,
    hsqrtFuel, hCallSqrt,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 496)
      (shared := shared)
      (store := Finmap.insert "var_x_64" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]

private theorem call_cleanup_t_uint256_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v] (.some "cleanup_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_cleanup_t_uint256]
  simp only [yulFunction_cleanup_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

private theorem call_validator_revert_t_uint256_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [v] (.some "validator_revert_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, []) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_validator_revert_t_uint256]
  simp only [yulFunction_validator_revert_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcleanup :=
    call_cleanup_t_uint256_direct (v := v) (fuel := fuel + 31) (shared := shared)
      (store := Finmap.insert "value" v (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word] at hcleanup
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne, hcleanup]

private def sqrtSharedAfterFreePtr (x : Nat) : EvmYul.SharedState .Yul :=
  let shared := FormalYul.sharedFor yulContract (selector_sqrt ++ FormalYul.encodeWords [x])
  { shared with toMachineState := shared.toMachineState.mstore (FormalYul.word 64) (FormalYul.word 128) }

private def sqrtUpSharedAfterFreePtr (x : Nat) : EvmYul.SharedState .Yul :=
  let shared := FormalYul.sharedFor yulContract (selector_sqrtUp ++ FormalYul.encodeWords [x])
  { shared with toMachineState := shared.toMachineState.mstore (FormalYul.word 64) (FormalYul.word 128) }

private theorem sharedFor_mstore_eq_sqrtSharedAfterFreePtr (x : Nat) :
    { (FormalYul.sharedFor yulContract (selector_sqrt ++ FormalYul.encodeWords [x])) with
      toMachineState :=
        (FormalYul.sharedFor yulContract (selector_sqrt ++ FormalYul.encodeWords [x])).toMachineState.mstore
          (FormalYul.word 64) (FormalYul.word 128) } =
      sqrtSharedAfterFreePtr x := rfl

private theorem sharedFor_mstore_mk_eq_sqrtSharedAfterFreePtr (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_sqrt ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_sqrt ++ FormalYul.encodeWords [x])).toMachineState.mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      sqrtSharedAfterFreePtr x := rfl

private theorem sharedFor_mstore_eq_sqrtUpSharedAfterFreePtr (x : Nat) :
    { (FormalYul.sharedFor yulContract (selector_sqrtUp ++ FormalYul.encodeWords [x])) with
      toMachineState :=
        (FormalYul.sharedFor yulContract (selector_sqrtUp ++ FormalYul.encodeWords [x])).toMachineState.mstore
          (FormalYul.word 64) (FormalYul.word 128) } =
      sqrtUpSharedAfterFreePtr x := rfl

private theorem sharedFor_mstore_mk_eq_sqrtUpSharedAfterFreePtr (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_sqrtUp ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_sqrtUp ++ FormalYul.encodeWords [x])).toMachineState.mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      sqrtUpSharedAfterFreePtr x := rfl

private theorem sharedFor_inherited_mstore_mk_eq_sqrtSharedAfterFreePtr (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_sqrt ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      sqrtSharedAfterFreePtr x := rfl

private theorem sharedFor_inherited_mstore_mk_eq_sqrtSharedAfterFreePtr_raw (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_sqrt ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
          (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128))) =
      sqrtSharedAfterFreePtr x := by
  simpa [FormalYul.word] using sharedFor_inherited_mstore_mk_eq_sqrtSharedAfterFreePtr x

private theorem sharedFor_inherited_mstore_mk_eq_sqrtUpSharedAfterFreePtr (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_sqrtUp ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_sqrtUp ++ FormalYul.encodeWords [x])).mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      sqrtUpSharedAfterFreePtr x := rfl

private theorem sharedFor_inherited_mstore_mk_eq_sqrtUpSharedAfterFreePtr_raw (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_sqrtUp ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_sqrtUp ++ FormalYul.encodeWords [x])).mstore
          (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128))) =
      sqrtUpSharedAfterFreePtr x := by
  simpa [FormalYul.word] using sharedFor_inherited_mstore_mk_eq_sqrtUpSharedAfterFreePtr x

@[simp]
private theorem sqrtSharedAfterFreePtr_lookup (x : Nat) :
    (sqrtSharedAfterFreePtr x).accountMap.find?
        (sqrtSharedAfterFreePtr x).executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract) := by
  simp [sqrtSharedAfterFreePtr]

@[simp]
private theorem sqrtUpSharedAfterFreePtr_lookup (x : Nat) :
    (sqrtUpSharedAfterFreePtr x).accountMap.find?
        (sqrtUpSharedAfterFreePtr x).executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract) := by
  simp [sqrtUpSharedAfterFreePtr]

@[simp]
private theorem sqrtSharedAfterFreePtr_calldata (x : Nat) :
    (sqrtSharedAfterFreePtr x).executionEnv.calldata =
      selector_sqrt ++ FormalYul.encodeWords [x] := by
  simp [sqrtSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
private theorem sqrtUpSharedAfterFreePtr_calldata (x : Nat) :
    (sqrtUpSharedAfterFreePtr x).executionEnv.calldata =
      selector_sqrtUp ++ FormalYul.encodeWords [x] := by
  simp [sqrtUpSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
private theorem sqrtSharedAfterFreePtr_weiValue (x : Nat) :
    (sqrtSharedAfterFreePtr x).executionEnv.weiValue = ({ val := 0 } : EvmYul.UInt256) := by
  simp [sqrtSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
private theorem sqrtUpSharedAfterFreePtr_weiValue (x : Nat) :
    (sqrtUpSharedAfterFreePtr x).executionEnv.weiValue = ({ val := 0 } : EvmYul.UInt256) := by
  simp [sqrtUpSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
private theorem sqrt_calldata_size (x : Nat) :
    (selector_sqrt ++ FormalYul.encodeWords [x]).size = 36 := by
  simp [selector_sqrt, FormalYul.encodeWords,
    FormalYul.bytes, ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
    FormalYul.Preservation.encodeWord_size]

@[simp]
private theorem sqrtUp_calldata_size (x : Nat) :
    (selector_sqrtUp ++ FormalYul.encodeWords [x]).size = 36 := by
  simp [selector_sqrtUp, FormalYul.encodeWords,
    FormalYul.bytes, ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
    FormalYul.Preservation.encodeWord_size]

@[simp]
private theorem sharedFor_sqrt_calldata_size (x : Nat) :
    (FormalYul.sharedFor yulContract
      (selector_sqrt ++ FormalYul.encodeWords [x])).executionEnv.calldata.size = 36 := by
  simp [FormalYul.sharedFor, FormalYul.envFor, sqrt_calldata_size]

@[simp]
private theorem calldataload_sqrt_arg_of_calldata
    (x : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hdata : shared.executionEnv.calldata = selector_sqrt ++ FormalYul.encodeWords [x]) :
    EvmYul.State.calldataload
      (EvmYul.Yul.State.Ok shared store).toState (FormalYul.word 4) =
      FormalYul.word x := by
  simp [EvmYul.State.calldataload, EvmYul.Yul.State.toState, hdata,
    selector_sqrt, FormalYul.encodeWords]

@[simp]
private theorem calldataload_sqrtUp_arg_of_calldata
    (x : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hdata : shared.executionEnv.calldata = selector_sqrtUp ++ FormalYul.encodeWords [x]) :
    EvmYul.State.calldataload
      (EvmYul.Yul.State.Ok shared store).toState (FormalYul.word 4) =
      FormalYul.word x := by
  simp [EvmYul.State.calldataload, EvmYul.Yul.State.toState, hdata,
    selector_sqrtUp, FormalYul.encodeWords]

private theorem call_abi_decode_t_uint256_sqrt_of_calldata
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_sqrt ++ FormalYul.encodeWords [x]) :
    EvmYul.Yul.call (fuel + 80) [FormalYul.word 4, FormalYul.word 36]
      (.some "abi_decode_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word x]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_abi_decode_t_uint256]
  simp only [yulFunction_abi_decode_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hvalidator :=
    call_validator_revert_t_uint256_direct (v := FormalYul.word x) (fuel := fuel + 15)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word x)
        (Finmap.insert "offset" (FormalYul.word 4)
          (Finmap.insert "end" (FormalYul.word 36) (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup)
  simp [FormalYul.word] at hvalidator
  have hload :=
    calldataload_sqrt_arg_of_calldata x shared
      (Finmap.insert "offset" (FormalYul.word 4)
        (Finmap.insert "end" (FormalYul.word 36) (Inhabited.default : EvmYul.Yul.VarStore)))
      hdata
  simp [FormalYul.word] at hload
  simp +decide [hdata, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne, FormalYul.word, hload, hvalidator,
    calldataload_sqrt_arg_of_calldata x shared _ hdata]

private theorem call_abi_decode_tuple_t_uint256_sqrt_of_calldata
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_sqrt ++ FormalYul.encodeWords [x]) :
    EvmYul.Yul.call (fuel + 130) [FormalYul.word 4, FormalYul.word 36]
      (.some "abi_decode_tuple_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word x]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_abi_decode_tuple_t_uint256]
  simp only [yulFunction_abi_decode_tuple_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hdecode :=
    call_abi_decode_t_uint256_sqrt_of_calldata (x := x) (fuel := fuel + 43)
      (shared := shared)
      (store := Finmap.insert "offset" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "headStart" (FormalYul.word 4)
          (Finmap.insert "dataEnd" (FormalYul.word 36)
            (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup) (hdata := hdata)
  simp [FormalYul.word] at hdecode
  simp +decide [hlookup, hdata, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne, FormalYul.word, hdecode]

private theorem call_abi_decode_t_uint256_sqrtUp_of_calldata
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_sqrtUp ++ FormalYul.encodeWords [x]) :
    EvmYul.Yul.call (fuel + 80) [FormalYul.word 4, FormalYul.word 36]
      (.some "abi_decode_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word x]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_abi_decode_t_uint256]
  simp only [yulFunction_abi_decode_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hvalidator :=
    call_validator_revert_t_uint256_direct (v := FormalYul.word x) (fuel := fuel + 15)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word x)
        (Finmap.insert "offset" (FormalYul.word 4)
          (Finmap.insert "end" (FormalYul.word 36) (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup)
  simp [FormalYul.word] at hvalidator
  have hload :=
    calldataload_sqrtUp_arg_of_calldata x shared
      (Finmap.insert "offset" (FormalYul.word 4)
        (Finmap.insert "end" (FormalYul.word 36) (Inhabited.default : EvmYul.Yul.VarStore)))
      hdata
  simp [FormalYul.word] at hload
  simp +decide [hdata, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne, FormalYul.word, hload, hvalidator,
    calldataload_sqrtUp_arg_of_calldata x shared _ hdata]

private theorem call_abi_decode_tuple_t_uint256_sqrtUp_of_calldata
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_sqrtUp ++ FormalYul.encodeWords [x]) :
    EvmYul.Yul.call (fuel + 130) [FormalYul.word 4, FormalYul.word 36]
      (.some "abi_decode_tuple_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word x]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_abi_decode_tuple_t_uint256]
  simp only [yulFunction_abi_decode_tuple_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hdecode :=
    call_abi_decode_t_uint256_sqrtUp_of_calldata (x := x) (fuel := fuel + 43)
      (shared := shared)
      (store := Finmap.insert "offset" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "headStart" (FormalYul.word 4)
          (Finmap.insert "dataEnd" (FormalYul.word 36)
            (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup) (hdata := hdata)
  simp [FormalYul.word] at hdecode
  simp +decide [hlookup, hdata, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne, FormalYul.word, hdecode]

private theorem call_allocate_unbounded_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [] (.some "allocate_unbounded") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok
      ((EvmYul.Yul.State.Ok shared store).setMachineState
        (((EvmYul.Yul.State.Ok shared store).toMachineState.mload (FormalYul.word 64)).2),
        [((EvmYul.Yul.State.Ok shared store).toMachineState.mload (FormalYul.word 64)).1]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_allocate_unbounded]
  simp only [yulFunction_allocate_unbounded,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne, FormalYul.word]

private theorem call_abi_encode_t_uint256_to_t_uint256_fromStack_direct
    (value pos : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 90) [value, pos] (.some "abi_encode_t_uint256_to_t_uint256_fromStack")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok ((EvmYul.Yul.State.Ok shared store).setMachineState
      ((EvmYul.Yul.State.Ok shared store).toMachineState.mstore pos value), []) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_abi_encode_t_uint256_to_t_uint256_fromStack]
  simp only [yulFunction_abi_encode_t_uint256_to_t_uint256_fromStack,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcleanup :=
    call_cleanup_t_uint256_direct (v := value) (fuel := fuel + 64) (shared := shared)
      (store := Finmap.insert "value" value
        (Finmap.insert "pos" pos (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup)
  simp [FormalYul.word] at hcleanup
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne, FormalYul.word, hcleanup]

private theorem call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack_direct
    (headStart value : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 150) [headStart, value]
      (.some "abi_encode_tuple_t_uint256__to_t_uint256__fromStack")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok ((EvmYul.Yul.State.Ok shared store).setMachineState
      ((EvmYul.Yul.State.Ok shared store).toMachineState.mstore headStart value),
      [headStart + FormalYul.word 32]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_abi_encode_tuple_t_uint256__to_t_uint256__fromStack]
  simp only [yulFunction_abi_encode_tuple_t_uint256__to_t_uint256__fromStack,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hencode :=
    call_abi_encode_t_uint256_to_t_uint256_fromStack_direct
      (value := value) (pos := headStart + FormalYul.word 0) (fuel := fuel + 55)
      (shared := shared)
      (store := Finmap.insert "tail" (headStart + FormalYul.word 32)
        (Finmap.insert "headStart" headStart
          (Finmap.insert "value0" value (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup)
  simp [FormalYul.word] at hencode
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne, FormalYul.word, hencode]

@[simp]
private theorem sqrtSharedAfterFreePtr_mload64 (x : Nat) :
    ((sqrtSharedAfterFreePtr x).mload (FormalYul.word 64)).1 = FormalYul.word 128 := by
  exact FormalYul.Preservation.sharedFor_mload_freePtr_after_mstore yulContract
    (selector_sqrt ++ FormalYul.encodeWords [x])

@[simp]
private theorem sqrtUpSharedAfterFreePtr_mload64 (x : Nat) :
    ((sqrtUpSharedAfterFreePtr x).mload (FormalYul.word 64)).1 = FormalYul.word 128 := by
  exact FormalYul.Preservation.sharedFor_mload_freePtr_after_mstore yulContract
    (selector_sqrtUp ++ FormalYul.encodeWords [x])

private theorem call_shift_right_224_unsigned_direct
    (v : EvmYul.UInt256) (fuel : Nat)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v] (.some "shift_right_224_unsigned")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [EvmYul.UInt256.shiftRight v (FormalYul.word 224)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_shift_right_224_unsigned]
  simp only [yulFunction_shift_right_224_unsigned,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne, FormalYul.word]

@[simp]
private theorem sqrt_selector_afterFreePtr (x : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok (sqrtSharedAfterFreePtr x)
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 1529414794 := by
  let tail : List UInt8 := (FormalYul.encodeWord x).data.toList.take 28
  have htailLen : tail.length = 28 := by
    simp [tail, FormalYul.Preservation.encodeWord_data_toList]
  have hread :
      ((selector_sqrt ++ FormalYul.encodeWords [x]).readBytes 0 32).data.toList =
        [0x5b, 0x29, 0x04, 0x8a] ++ tail := by
    simp [tail, ByteArray.readBytes, selector_sqrt, FormalYul.encodeWords, FormalYul.bytes,
      ByteArray.push, ByteArray.empty, ByteArray.emptyWithCapacity]
    change (ffi.ByteArray.zeroes
        (OfNat.ofNat 32 - OfNat.ofNat
          (4 + (List.take 28
            (List.map (fun i => FormalYul.byteAt (FormalYul.u256 x) (31 - i))
              (List.range 32))).length))).data = #[]
    rw [show (List.take 28
        (List.map (fun i => FormalYul.byteAt (FormalYul.u256 x) (31 - i))
          (List.range 32))).length = 28 by simp]
    have hz : (OfNat.ofNat 32 - OfNat.ofNat (4 + 28) : USize) = 0 := by
      apply USize.ext
      simp
    rw [hz]
    rfl
  have hbytesLt :
      EvmYul.fromBytesBigEndian ([0x5b, 0x29, 0x04, 0x8a] ++ tail) <
        FormalYul.WORD_MOD := by
    have hlt := FormalYul.Preservation.fromBytesBigEndian_lt_pow_length
      ([0x5b, 0x29, 0x04, 0x8a] ++ tail)
    simpa [htailLen, FormalYul.WORD_MOD] using hlt
  have hload :
      FormalYul.wordNat
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok (sqrtSharedAfterFreePtr x)
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (FormalYul.word 0)) =
        EvmYul.fromBytesBigEndian ([0x5b, 0x29, 0x04, 0x8a] ++ tail) := by
    simp only [EvmYul.State.calldataload, EvmYul.Yul.State.toState,
      EvmYul.uInt256OfByteArray, sqrtSharedAfterFreePtr_calldata, FormalYul.word]
    change FormalYul.wordNat
        (EvmYul.UInt256.ofNat
          (EvmYul.fromBytesBigEndian
            ((selector_sqrt ++ FormalYul.encodeWords [x]).readBytes
              (EvmYul.UInt256.ofNat 0).toNat 32).data.toList)) =
      EvmYul.fromBytesBigEndian ([0x5b, 0x29, 0x04, 0x8a] ++ tail)
    rw [show (EvmYul.UInt256.ofNat 0).toNat = 0 by rfl]
    rw [hread]
    change FormalYul.wordNat
        (EvmYul.UInt256.ofNat
          (EvmYul.fromBytesBigEndian ([0x5b, 0x29, 0x04, 0x8a] ++ tail))) =
      EvmYul.fromBytesBigEndian ([0x5b, 0x29, 0x04, 0x8a] ++ tail)
    rw [FormalYul.Preservation.wordNat_ofNat]
    exact u256_eq_of_lt _ hbytesLt
  apply FormalYul.Preservation.eq_of_wordNat_eq
  rw [FormalYul.Preservation.wordNat_shiftRight]
  rw [hload]
  change FormalYul.evmShr (FormalYul.wordNat (FormalYul.word 224))
      (EvmYul.fromBytesBigEndian ([0x5b, 0x29, 0x04, 0x8a] ++ tail)) =
    FormalYul.wordNat (FormalYul.word 1529414794)
  rw [FormalYul.Preservation.wordNat_word, FormalYul.Preservation.wordNat_word]
  simp [FormalYul.evmShr]
  change FormalYul.u256
      (EvmYul.fromBytesBigEndian ([0x5b, 0x29, 0x04, 0x8a] ++ tail)) /
      26959946667150639794667015087019630673637144422540572481103610249216 =
    FormalYul.u256 1529414794
  rw [u256_eq_of_lt _ hbytesLt]
  rw [FormalYul.Preservation.fromBytesBigEndian_append]
  rw [htailLen]
  have htailDiv :
      EvmYul.fromBytesBigEndian tail / 256 ^ 28 = 0 := by
    apply Nat.div_eq_of_lt
    simpa [htailLen] using
      FormalYul.Preservation.fromBytesBigEndian_lt_pow_length tail
  change
    (26959946667150639794667015087019630673637144422540572481103610249216 *
          1529414794 + EvmYul.fromBytes' tail.reverse) /
        26959946667150639794667015087019630673637144422540572481103610249216 =
      FormalYul.u256 1529414794
  rw [Nat.mul_add_div (by norm_num :
    0 < 26959946667150639794667015087019630673637144422540572481103610249216)]
  have htailDiv' :
      EvmYul.fromBytes' tail.reverse /
          26959946667150639794667015087019630673637144422540572481103610249216 = 0 := by
    simpa [EvmYul.fromBytesBigEndian] using htailDiv
  rw [htailDiv']
  norm_num [FormalYul.u256, FormalYul.WORD_MOD]

@[simp]
private theorem sqrt_selector_sharedFor_mk (x : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_sqrt ++ FormalYul.encodeWords [x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
                (FormalYul.word 64) (FormalYul.word 128)))
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 1529414794 := by
  simpa [sharedFor_inherited_mstore_mk_eq_sqrtSharedAfterFreePtr] using
    sqrt_selector_afterFreePtr x

@[simp]
private theorem selectSwitchCase_sqrt_sharedFor_mk (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (EvmYul.SharedState.mk
              (FormalYul.sharedFor yulContract
                (selector_sqrt ++ FormalYul.encodeWords [x])).toState
              ((FormalYul.sharedFor yulContract
                (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
                  (FormalYul.word 64) (FormalYul.word 128)))
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (FormalYul.word 0))
        (FormalYul.word 224))
      [(FormalYul.word 1529414794,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrt_62") [])]),
        (FormalYul.word 1707723681,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrtUp_75") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrt_62") [])] := by
  rw [sqrt_selector_sharedFor_mk]
  rfl

private theorem selectSwitchCase_sqrt_sharedFor_mk_raw (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (EvmYul.SharedState.mk
              (FormalYul.sharedFor yulContract
                (selector_sqrt ++ FormalYul.encodeWords [x])).toState
              ((FormalYul.sharedFor yulContract
                (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
                  (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224))
      [(EvmYul.UInt256.ofNat 1529414794,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrt_62") [])]),
        (EvmYul.UInt256.ofNat 1707723681,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrtUp_75") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrt_62") [])] := by
  simpa [FormalYul.word] using selectSwitchCase_sqrt_sharedFor_mk x

private theorem sqrtUp_selector_afterFreePtr (x : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x)
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 1707723681 := by
  let tail : List UInt8 := (FormalYul.encodeWord x).data.toList.take 28
  have htailLen : tail.length = 28 := by
    simp [tail, FormalYul.Preservation.encodeWord_data_toList]
  have hread :
      ((selector_sqrtUp ++ FormalYul.encodeWords [x]).readBytes 0 32).data.toList =
        [0x65, 0xc9, 0xcb, 0xa1] ++ tail := by
    simp [tail, ByteArray.readBytes, selector_sqrtUp, FormalYul.encodeWords, FormalYul.bytes,
      ByteArray.push, ByteArray.empty, ByteArray.emptyWithCapacity]
    change (ffi.ByteArray.zeroes
        (OfNat.ofNat 32 - OfNat.ofNat
          (4 + (List.take 28
            (List.map (fun i => FormalYul.byteAt (FormalYul.u256 x) (31 - i))
              (List.range 32))).length))).data = #[]
    rw [show (List.take 28
        (List.map (fun i => FormalYul.byteAt (FormalYul.u256 x) (31 - i))
          (List.range 32))).length = 28 by simp]
    have hz : (OfNat.ofNat 32 - OfNat.ofNat (4 + 28) : USize) = 0 := by
      apply USize.ext
      simp
    rw [hz]
    rfl
  have hbytesLt :
      EvmYul.fromBytesBigEndian ([0x65, 0xc9, 0xcb, 0xa1] ++ tail) <
        FormalYul.WORD_MOD := by
    have hlt := FormalYul.Preservation.fromBytesBigEndian_lt_pow_length
      ([0x65, 0xc9, 0xcb, 0xa1] ++ tail)
    simpa [htailLen, FormalYul.WORD_MOD] using hlt
  have hload :
      FormalYul.wordNat
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x)
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (FormalYul.word 0)) =
        EvmYul.fromBytesBigEndian ([0x65, 0xc9, 0xcb, 0xa1] ++ tail) := by
    simp only [EvmYul.State.calldataload, EvmYul.Yul.State.toState,
      EvmYul.uInt256OfByteArray, sqrtUpSharedAfterFreePtr_calldata, FormalYul.word]
    change FormalYul.wordNat
        (EvmYul.UInt256.ofNat
          (EvmYul.fromBytesBigEndian
            ((selector_sqrtUp ++ FormalYul.encodeWords [x]).readBytes
              (EvmYul.UInt256.ofNat 0).toNat 32).data.toList)) =
      EvmYul.fromBytesBigEndian ([0x65, 0xc9, 0xcb, 0xa1] ++ tail)
    rw [show (EvmYul.UInt256.ofNat 0).toNat = 0 by rfl]
    rw [hread]
    change FormalYul.wordNat
        (EvmYul.UInt256.ofNat
          (EvmYul.fromBytesBigEndian ([0x65, 0xc9, 0xcb, 0xa1] ++ tail))) =
      EvmYul.fromBytesBigEndian ([0x65, 0xc9, 0xcb, 0xa1] ++ tail)
    rw [FormalYul.Preservation.wordNat_ofNat]
    exact u256_eq_of_lt _ hbytesLt
  apply FormalYul.Preservation.eq_of_wordNat_eq
  rw [FormalYul.Preservation.wordNat_shiftRight]
  rw [hload]
  rw [FormalYul.Preservation.wordNat_word, FormalYul.Preservation.wordNat_word]
  simp [FormalYul.evmShr]
  change FormalYul.u256
      (EvmYul.fromBytesBigEndian ([0x65, 0xc9, 0xcb, 0xa1] ++ tail)) /
      26959946667150639794667015087019630673637144422540572481103610249216 =
    FormalYul.u256 1707723681
  rw [u256_eq_of_lt _ hbytesLt]
  rw [FormalYul.Preservation.fromBytesBigEndian_append]
  rw [htailLen]
  have htailDiv :
      EvmYul.fromBytesBigEndian tail / 256 ^ 28 = 0 := by
    apply Nat.div_eq_of_lt
    simpa [htailLen] using
      FormalYul.Preservation.fromBytesBigEndian_lt_pow_length tail
  change
    (26959946667150639794667015087019630673637144422540572481103610249216 *
          1707723681 + EvmYul.fromBytes' tail.reverse) /
        26959946667150639794667015087019630673637144422540572481103610249216 =
      FormalYul.u256 1707723681
  rw [Nat.mul_add_div (by norm_num :
    0 < 26959946667150639794667015087019630673637144422540572481103610249216)]
  have htailDiv' :
      EvmYul.fromBytes' tail.reverse /
          26959946667150639794667015087019630673637144422540572481103610249216 = 0 := by
    simpa [EvmYul.fromBytesBigEndian] using htailDiv
  rw [htailDiv']
  norm_num [FormalYul.u256, FormalYul.WORD_MOD]

private theorem selectSwitchCase_sqrtUp_sharedFor_mk_raw (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (EvmYul.SharedState.mk
              (FormalYul.sharedFor yulContract
                (selector_sqrtUp ++ FormalYul.encodeWords [x])).toState
              ((FormalYul.sharedFor yulContract
                (selector_sqrtUp ++ FormalYul.encodeWords [x])).mstore
                  (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224))
      [(EvmYul.UInt256.ofNat 1529414794,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrt_62") [])]),
        (EvmYul.UInt256.ofNat 1707723681,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrtUp_75") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrtUp_75") [])] := by
  rw [show
    (EvmYul.SharedState.mk
      (FormalYul.sharedFor yulContract
        (selector_sqrtUp ++ FormalYul.encodeWords [x])).toState
      ((FormalYul.sharedFor yulContract
        (selector_sqrtUp ++ FormalYul.encodeWords [x])).mstore
          (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128))) =
      sqrtUpSharedAfterFreePtr x by
        simpa [FormalYul.word] using sharedFor_inherited_mstore_mk_eq_sqrtUpSharedAfterFreePtr x]
  rw [show EvmYul.UInt256.ofNat 0 = FormalYul.word 0 by rfl]
  rw [show EvmYul.UInt256.ofNat 224 = FormalYul.word 224 by rfl]
  rw [sqrtUp_selector_afterFreePtr x]
  rfl

private theorem selectSwitchCase_sqrt_sharedFor_mk_raw_method (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (((EvmYul.Yul.State.Ok
        (EvmYul.SharedState.mk
          (FormalYul.sharedFor yulContract
            (selector_sqrt ++ FormalYul.encodeWords [x])).toState
          ((FormalYul.sharedFor yulContract
            (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
              (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
        (Inhabited.default : EvmYul.Yul.VarStore)).toState.calldataload
          (EvmYul.UInt256.ofNat 0)).shiftRight
        (EvmYul.UInt256.ofNat 224))
      [(EvmYul.UInt256.ofNat 1529414794,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrt_62") [])]),
        (EvmYul.UInt256.ofNat 1707723681,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrtUp_75") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrt_62") [])] := by
  simpa using selectSwitchCase_sqrt_sharedFor_mk_raw x

private theorem selectSwitchCase_sqrt_sharedFor_record_raw_method (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (((EvmYul.Yul.State.Ok
        { toState :=
            (FormalYul.sharedFor yulContract
              (selector_sqrt ++ FormalYul.encodeWords [x])).toState,
          toMachineState :=
            (FormalYul.sharedFor yulContract
              (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128) }
        (Inhabited.default : EvmYul.Yul.VarStore)).toState.calldataload
          (EvmYul.UInt256.ofNat 0)).shiftRight
        (EvmYul.UInt256.ofNat 224))
      [(EvmYul.UInt256.ofNat 1529414794,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrt_62") [])]),
        (EvmYul.UInt256.ofNat 1707723681,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrtUp_75") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrt_62") [])] := by
  simpa using selectSwitchCase_sqrt_sharedFor_mk_raw_method x

private theorem selectSwitchCase_sqrt_sharedFor_let_raw_method (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (((EvmYul.Yul.State.Ok
        (let __State :=
            (FormalYul.sharedFor yulContract
              (selector_sqrt ++ FormalYul.encodeWords [x])).toState
         let __MachineState :=
            (FormalYul.sharedFor yulContract
              (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)
         { toState := __State, toMachineState := __MachineState })
        (Inhabited.default : EvmYul.Yul.VarStore)).toState.calldataload
          (EvmYul.UInt256.ofNat 0)).shiftRight
        (EvmYul.UInt256.ofNat 224))
      [(EvmYul.UInt256.ofNat 1529414794,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrt_62") [])]),
        (EvmYul.UInt256.ofNat 1707723681,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrtUp_75") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrt_62") [])] := by
  simpa using selectSwitchCase_sqrt_sharedFor_record_raw_method x

private theorem selectSwitchCase_sqrt_sharedFor_have_raw_method (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (((EvmYul.Yul.State.Ok
        (have __State :=
            (FormalYul.sharedFor yulContract
              (selector_sqrt ++ FormalYul.encodeWords [x])).toState
         have __MachineState :=
            (FormalYul.sharedFor yulContract
              (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)
         { toState := __State, toMachineState := __MachineState })
        (Inhabited.default : EvmYul.Yul.VarStore)).toState.calldataload
          (EvmYul.UInt256.ofNat 0)).shiftRight
        (EvmYul.UInt256.ofNat 224))
      [(EvmYul.UInt256.ofNat 1529414794,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrt_62") [])]),
        (EvmYul.UInt256.ofNat 1707723681,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrtUp_75") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrt_62") [])] := by
  simpa using selectSwitchCase_sqrt_sharedFor_record_raw_method x

private theorem external_fun_wrap_sqrt_sqrt_calldata_result_999989
    (x : Nat) (store : EvmYul.Yul.VarStore) :
    ((match
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_sqrt) (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrtSharedAfterFreePtr x) store)
    with
    | .error (.YulHalt state _) => FormalYul.resultWord (FormalYul.returnOf state)
    | .error .Revert => .error "revert"
    | .error err => .error (reprStr err)
    | .ok (state, _) => FormalYul.resultWord (FormalYul.returnOf state)) :
      Except String Nat) =
      .ok (floorSqrt (FormalYul.u256 x)) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv,
    sqrtSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_sqrt]
  simp only [yulFunction_external_fun_wrap_sqrt, yulFunction_external_fun_wrap_sqrt_62,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := floorSqrt (FormalYul.u256 x)
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word ret)
      (Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let memPos :=
    ((EvmYul.Yul.State.Ok (sqrtSharedAfterFreePtr x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { sqrtSharedAfterFreePtr x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (sqrtSharedAfterFreePtr x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_uint256_sqrt_of_calldata (x := x) (fuel := 999854)
      (shared := sqrtSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := sqrtSharedAfterFreePtr_lookup x) (hdata := sqrtSharedAfterFreePtr_calldata x)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_sqrt_direct (x := x) (fuel := 999523) (shared := sqrtSharedAfterFreePtr x)
      (store := Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := sqrtSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, yulName_fun_wrap_sqrt, ret] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := sqrtSharedAfterFreePtr x)
      (store := baseStore) (hlookup := sqrtSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, baseStore, memShared, memPos] at halloc
  have hencode :=
    call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack_direct
      (headStart := memPos) (value := FormalYul.word ret) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by
        simp [memShared, sqrtSharedAfterFreePtr_lookup x])
  simp [FormalYul.word, memShared, encStore, memPos, baseStore, ret] at hencode
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    EvmYul.Yul.State.toMachineState, FormalYul.returnOf, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    hdecode, hwrap, halloc, hencode, ret, baseStore, memPos, memShared, encStore]
  have hmload :
      ((sqrtSharedAfterFreePtr x).mload (EvmYul.UInt256.ofNat 64)).1 =
        EvmYul.UInt256.ofNat 128 := by
    simpa [FormalYul.word] using sqrtSharedAfterFreePtr_mload64 x
  rw [hmload]
  have hretLen :
      EvmYul.UInt256.ofNat 128 + EvmYul.UInt256.ofNat 32 -
          EvmYul.UInt256.ofNat 128 =
        FormalYul.word 32 := by
    decide
  rw [hretLen]
  rw [FormalYul.Preservation.resultWord_evmReturn_mstore_word]
  have hnat :
      (EvmYul.UInt256.ofNat (floorSqrt (FormalYul.u256 x))).toNat =
        floorSqrt (FormalYul.u256 x) := by
    change FormalYul.wordNat (EvmYul.UInt256.ofNat (floorSqrt (FormalYul.u256 x))) =
      floorSqrt (FormalYul.u256 x)
    exact (FormalYul.Preservation.wordNat_ofNat (floorSqrt (FormalYul.u256 x))).trans
      (u256_eq_of_lt _ (floorSqrt_lt_word _ (Nat.mod_lt x (by
        unfold WORD_MOD
        exact Nat.two_pow_pos 256))))
  rw [hnat]

private theorem external_fun_wrap_sqrt_sqrt_calldata_halts_999989
    (x : Nat) (store : EvmYul.Yul.VarStore) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_sqrt) (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrtSharedAfterFreePtr x) store) =
        .error (.YulHalt state value) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv,
    sqrtSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_sqrt]
  simp only [yulFunction_external_fun_wrap_sqrt, yulFunction_external_fun_wrap_sqrt_62,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := floorSqrt (FormalYul.u256 x)
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word ret)
      (Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let memPos :=
    ((EvmYul.Yul.State.Ok (sqrtSharedAfterFreePtr x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { sqrtSharedAfterFreePtr x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (sqrtSharedAfterFreePtr x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_uint256_sqrt_of_calldata (x := x) (fuel := 999854)
      (shared := sqrtSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := sqrtSharedAfterFreePtr_lookup x) (hdata := sqrtSharedAfterFreePtr_calldata x)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_sqrt_direct (x := x) (fuel := 999523) (shared := sqrtSharedAfterFreePtr x)
      (store := Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := sqrtSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, yulName_fun_wrap_sqrt, ret] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := sqrtSharedAfterFreePtr x)
      (store := baseStore) (hlookup := sqrtSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, baseStore, memShared, memPos] at halloc
  have hencode :=
    call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack_direct
      (headStart := memPos) (value := FormalYul.word ret) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by
        simp [memShared, sqrtSharedAfterFreePtr_lookup x])
  simp [FormalYul.word, memShared, encStore, memPos, baseStore, ret] at hencode
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    EvmYul.Yul.State.toMachineState, FormalYul.returnOf, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    hdecode, hwrap, halloc, hencode, ret, baseStore, memPos, memShared, encStore]

private theorem external_fun_wrap_sqrtUp_sqrtUp_calldata_result_999989
    (x : Nat) (store : EvmYul.Yul.VarStore) :
    ((match
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_sqrtUp) (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x) store)
    with
    | .error (.YulHalt state _) => FormalYul.resultWord (FormalYul.returnOf state)
    | .error .Revert => .error "revert"
    | .error err => .error (reprStr err)
    | .ok (state, _) => FormalYul.resultWord (FormalYul.returnOf state)) :
      Except String Nat) =
      .ok (sqrtUp256 (FormalYul.u256 x)) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv,
    sqrtUpSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_sqrtUp]
  simp only [yulFunction_external_fun_wrap_sqrtUp, yulFunction_external_fun_wrap_sqrtUp_75,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := sqrtUp256 (FormalYul.u256 x)
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word ret)
      (Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let memPos :=
    ((EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { sqrtUpSharedAfterFreePtr x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_uint256_sqrtUp_of_calldata (x := x) (fuel := 999854)
      (shared := sqrtUpSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := sqrtUpSharedAfterFreePtr_lookup x) (hdata := sqrtUpSharedAfterFreePtr_calldata x)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_sqrtUp_direct (x := x) (fuel := 999463) (shared := sqrtUpSharedAfterFreePtr x)
      (store := Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := sqrtUpSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, yulName_fun_wrap_sqrtUp, ret] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := sqrtUpSharedAfterFreePtr x)
      (store := baseStore) (hlookup := sqrtUpSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, baseStore, memShared, memPos] at halloc
  have hencode :=
    call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack_direct
      (headStart := memPos) (value := FormalYul.word ret) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by
        simp [memShared, sqrtUpSharedAfterFreePtr_lookup x])
  simp [FormalYul.word, memShared, encStore, memPos, baseStore, ret] at hencode
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    EvmYul.Yul.State.toMachineState, FormalYul.returnOf, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    hdecode, hwrap, halloc, hencode, ret, baseStore, memPos, memShared, encStore]
  have hmload :
      ((sqrtUpSharedAfterFreePtr x).mload (EvmYul.UInt256.ofNat 64)).1 =
        EvmYul.UInt256.ofNat 128 := by
    simpa [FormalYul.word] using sqrtUpSharedAfterFreePtr_mload64 x
  rw [hmload]
  have hretLen :
      EvmYul.UInt256.ofNat 128 + EvmYul.UInt256.ofNat 32 -
          EvmYul.UInt256.ofNat 128 =
        FormalYul.word 32 := by
    decide
  rw [hretLen]
  rw [FormalYul.Preservation.resultWord_evmReturn_mstore_word]
  have hnat :
      (EvmYul.UInt256.ofNat (sqrtUp256 (FormalYul.u256 x))).toNat =
        sqrtUp256 (FormalYul.u256 x) := by
    change FormalYul.wordNat (EvmYul.UInt256.ofNat (sqrtUp256 (FormalYul.u256 x))) =
      sqrtUp256 (FormalYul.u256 x)
    exact (FormalYul.Preservation.wordNat_ofNat (sqrtUp256 (FormalYul.u256 x))).trans
      (u256_eq_of_lt _ (sqrtUp256_lt_word _ (Nat.mod_lt x (by
        unfold WORD_MOD
        exact Nat.two_pow_pos 256))))
  rw [hnat]

private theorem external_fun_wrap_sqrtUp_sqrtUp_calldata_halts_999989
    (x : Nat) (store : EvmYul.Yul.VarStore) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_sqrtUp) (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x) store) =
        .error (.YulHalt state value) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv,
    sqrtUpSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_sqrtUp]
  simp only [yulFunction_external_fun_wrap_sqrtUp, yulFunction_external_fun_wrap_sqrtUp_75,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := sqrtUp256 (FormalYul.u256 x)
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word ret)
      (Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let memPos :=
    ((EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { sqrtUpSharedAfterFreePtr x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_uint256_sqrtUp_of_calldata (x := x) (fuel := 999854)
      (shared := sqrtUpSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := sqrtUpSharedAfterFreePtr_lookup x) (hdata := sqrtUpSharedAfterFreePtr_calldata x)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_sqrtUp_direct (x := x) (fuel := 999463) (shared := sqrtUpSharedAfterFreePtr x)
      (store := Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := sqrtUpSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, yulName_fun_wrap_sqrtUp, ret] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := sqrtUpSharedAfterFreePtr x)
      (store := baseStore) (hlookup := sqrtUpSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, baseStore, memShared, memPos] at halloc
  have hencode :=
    call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack_direct
      (headStart := memPos) (value := FormalYul.word ret) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by
        simp [memShared, sqrtUpSharedAfterFreePtr_lookup x])
  simp [FormalYul.word, memShared, encStore, memPos, baseStore, ret] at hencode
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    EvmYul.Yul.State.toMachineState, FormalYul.returnOf, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    hdecode, hwrap, halloc, hencode, ret, baseStore, memPos, memShared, encStore]

private theorem external_fun_wrap_sqrt_dispatcher_state_result (x : Nat) :
    ((match
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_sqrt) (.some yulContract)
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_sqrt ++ FormalYul.encodeWords [x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
          (Finmap.insert "selector"
            (EvmYul.UInt256.shiftRight
              (EvmYul.State.calldataload
                (EvmYul.Yul.State.Ok
                  (EvmYul.SharedState.mk
                    (FormalYul.sharedFor yulContract
                      (selector_sqrt ++ FormalYul.encodeWords [x])).toState
                    ((FormalYul.sharedFor yulContract
                      (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
                        (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
                  (Inhabited.default : EvmYul.Yul.VarStore)).toState
                (EvmYul.UInt256.ofNat 0))
              (EvmYul.UInt256.ofNat 224))
            (Inhabited.default : EvmYul.Yul.VarStore)))
    with
    | .error (.YulHalt state _) => FormalYul.resultWord (FormalYul.returnOf state)
    | .error .Revert => .error "revert"
    | .error err => .error (reprStr err)
    | .ok (state, _) => FormalYul.resultWord (FormalYul.returnOf state)) :
      Except String Nat) =
      .ok (floorSqrt (FormalYul.u256 x)) := by
  rw [sharedFor_inherited_mstore_mk_eq_sqrtSharedAfterFreePtr_raw]
  exact external_fun_wrap_sqrt_sqrt_calldata_result_999989 (x := x)
    (store := Finmap.insert "selector"
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok (sqrtSharedAfterFreePtr x)
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224))
      (Inhabited.default : EvmYul.Yul.VarStore))

private theorem external_fun_wrap_sqrt_dispatcher_state_halts (x : Nat) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_sqrt) (.some yulContract)
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_sqrt ++ FormalYul.encodeWords [x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
          (Finmap.insert "selector"
            (EvmYul.UInt256.shiftRight
              (EvmYul.State.calldataload
                (EvmYul.Yul.State.Ok
                  (EvmYul.SharedState.mk
                    (FormalYul.sharedFor yulContract
                      (selector_sqrt ++ FormalYul.encodeWords [x])).toState
                    ((FormalYul.sharedFor yulContract
                      (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
                        (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
                  (Inhabited.default : EvmYul.Yul.VarStore)).toState
                (EvmYul.UInt256.ofNat 0))
              (EvmYul.UInt256.ofNat 224))
            (Inhabited.default : EvmYul.Yul.VarStore))) =
        .error (.YulHalt state value) := by
  rw [sharedFor_inherited_mstore_mk_eq_sqrtSharedAfterFreePtr_raw]
  exact external_fun_wrap_sqrt_sqrt_calldata_halts_999989 (x := x)
    (store := Finmap.insert "selector"
        (EvmYul.UInt256.shiftRight
          (EvmYul.State.calldataload
            (EvmYul.Yul.State.Ok (sqrtSharedAfterFreePtr x)
              (Inhabited.default : EvmYul.Yul.VarStore)).toState
            (EvmYul.UInt256.ofNat 0))
          (EvmYul.UInt256.ofNat 224))
        (Inhabited.default : EvmYul.Yul.VarStore))

private theorem dispatcherReturn_sqrtUp
    (x : Nat) (haltState : EvmYul.Yul.State) (haltValue : EvmYul.Literal)
    (hhalt :
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_sqrtUp) (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x)
          (Finmap.insert "selector" (FormalYul.word 1707723681)
            (Inhabited.default : EvmYul.Yul.VarStore))) =
        .error (.YulHalt haltState haltValue)) :
    FormalYul.Preservation.DispatcherReturn yulContract
      (FormalYul.calldata selector_sqrtUp [x]) 999998 (FormalYul.returnOf haltState) := by
  let start := FormalYul.stateFor yulContract (FormalYul.calldata selector_sqrtUp [x])
  let afterFreePtr : EvmYul.Yul.State :=
    EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x)
      (Inhabited.default : EvmYul.Yul.VarStore)
  let afterSelector : EvmYul.Yul.State :=
    EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x)
      (Finmap.insert "selector" (FormalYul.word 1707723681)
        (Inhabited.default : EvmYul.Yul.VarStore))
  apply FormalYul.Preservation.dispatcherReturn_of_execReturn
    (hdispatcher := yulContract_dispatcher)
  simpa [start, afterFreePtr, afterSelector, yulDispatcher, FormalYul.calldata,
      yulName_external_fun_wrap_sqrtUp] using
    (FormalYul.Preservation.execReturn_block_if_switch_selected_call_nil
      (fuel := 999989)
      (first :=
        EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call
            (Sum.inl (EvmYul.Operation.StackMemFlow EvmYul.Operation.SMSFOp.MSTORE))
            [EvmYul.Yul.Ast.Expr.Lit (EvmYul.UInt256.ofNat 64),
              EvmYul.Yul.Ast.Expr.Lit (EvmYul.UInt256.ofNat 128)]))
      (fallback :=
        EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call
            (Sum.inr "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74")
            []))
      (letStmt :=
        EvmYul.Yul.Ast.Stmt.Let ["selector"]
          (some
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "shift_right_224_unsigned")
              [EvmYul.Yul.Ast.Expr.Call
                (Sum.inl (EvmYul.Operation.Env EvmYul.Operation.EOp.CALLDATALOAD))
                [EvmYul.Yul.Ast.Expr.Lit (EvmYul.UInt256.ofNat 0)]])))
      (ifCond :=
        EvmYul.Yul.Ast.Expr.Call
          (Sum.inl (EvmYul.Operation.CompBit EvmYul.Operation.CBLOp.ISZERO))
          [EvmYul.Yul.Ast.Expr.Call
            (Sum.inl (EvmYul.Operation.CompBit EvmYul.Operation.CBLOp.LT))
            [EvmYul.Yul.Ast.Expr.Call
              (Sum.inl (EvmYul.Operation.Env EvmYul.Operation.EOp.CALLDATASIZE)) [],
              EvmYul.Yul.Ast.Expr.Lit (EvmYul.UInt256.ofNat 4)]])
      (switchCond := EvmYul.Yul.Ast.Expr.Var "selector")
      (cases :=
        [(FormalYul.word 1529414794,
            [EvmYul.Yul.Ast.Stmt.ExprStmtCall
              (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_sqrt) [])]),
          (FormalYul.word 1707723681,
            [EvmYul.Yul.Ast.Stmt.ExprStmtCall
              (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_sqrtUp) [])])])
      (defaultStmts := [])
      (fn := yulName_external_fun_wrap_sqrtUp)
      (code := .some yulContract)
      (start := start)
      (afterFirst := afterFreePtr)
      (branchStart := afterFreePtr)
      (afterLet := afterSelector)
      (switchStart := afterSelector)
      (condValue := FormalYul.word 1)
      (selector := FormalYul.word 1707723681)
      (result := FormalYul.returnOf haltState)
      (hfirst := by
        simp +decide [start, afterFreePtr, FormalYul.stateFor, FormalYul.calldata,
          EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
          EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
          EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
          EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
          EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
          EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
          EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
          EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.reviveJump,
          EvmYul.Yul.State.overwrite?, EvmYul.Yul.State.toMachineState,
          FormalYul.returnOf, FormalYul.word,
          sharedFor_mstore_eq_sqrtUpSharedAfterFreePtr,
          sharedFor_mstore_mk_eq_sqrtUpSharedAfterFreePtr,
          sharedFor_inherited_mstore_mk_eq_sqrtUpSharedAfterFreePtr,
          sharedFor_inherited_mstore_mk_eq_sqrtUpSharedAfterFreePtr_raw])
      (hcond := by
        simp +decide [afterFreePtr, EvmYul.Yul.evalCall.eq_def,
          EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
          EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
          EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
          EvmYul.Yul.State.executionEnv, FormalYul.word,
          sqrtUpSharedAfterFreePtr_calldata, sqrtUp_calldata_size])
      (hcondNe := by decide)
      (hlet := by
        have hselector :
            ((EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x)
                (Inhabited.default : EvmYul.Yul.VarStore)).toState.calldataload
                (EvmYul.UInt256.ofNat 0)).shiftRight
              (EvmYul.UInt256.ofNat 224) =
              EvmYul.UInt256.ofNat 1707723681 := by
          simpa [FormalYul.word] using sqrtUp_selector_afterFreePtr x
        simp +decide [afterFreePtr, afterSelector,
          EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
          EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
          EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
          EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
          EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
          EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
          EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
          EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.reviveJump,
          EvmYul.Yul.State.overwrite?, EvmYul.Yul.State.toMachineState,
          FormalYul.returnOf, FormalYul.word, call_shift_right_224_unsigned_direct,
          hselector, Finmap.lookup_insert,
          Finmap.lookup_insert_of_ne])
      (hswitchEval := by
        simp [afterSelector, EvmYul.Yul.State.lookup!, Finmap.lookup_insert])
      (hselect := by
        rfl)
      (hcall := by
        exact ⟨haltState, haltValue, hhalt, rfl⟩))

theorem run_sqrt_floor_evm_eq_floorSqrt (x : Nat) :
    run_sqrt_floor_evm x = .ok (floorSqrt (FormalYul.u256 x)) := by
  obtain ⟨haltState, _haltValue, hhalt⟩ :=
    external_fun_wrap_sqrt_dispatcher_state_halts x
  have hresult := external_fun_wrap_sqrt_dispatcher_state_result x
  rw [hhalt] at hresult
  have hReturn :
      FormalYul.Preservation.DispatcherReturn yulContract
        (FormalYul.calldata selector_sqrt [x]) 999998 (FormalYul.returnOf haltState) := by
    apply FormalYul.Preservation.dispatcherReturn_of_exec_halt
      (hdispatcher := yulContract_dispatcher)
    refine ⟨haltState, _haltValue, ?_, rfl⟩
    simp +decide [FormalYul.calldata, FormalYul.stateFor,
      yulContract_dispatcher, yulDispatcher, EvmYul.Yul.execCall.eq_def,
      EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
      EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
      EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
      EvmYul.Yul.execSwitchCases.eq_def,
      EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk, EvmYul.Yul.State.insert,
      EvmYul.Yul.State.multifill, EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
      EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.reviveJump,
      EvmYul.Yul.State.overwrite?, EvmYul.Yul.State.toMachineState,
      FormalYul.returnOf, FormalYul.word, sharedFor_mstore_eq_sqrtSharedAfterFreePtr,
      sharedFor_mstore_mk_eq_sqrtSharedAfterFreePtr,
      sharedFor_inherited_mstore_mk_eq_sqrtSharedAfterFreePtr,
      call_shift_right_224_unsigned_direct,
      Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
    rw [selectSwitchCase_sqrt_sharedFor_mk_raw x]
    simpa +decide [hhalt, EvmYul.Yul.exec.eq_def,
      EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
      EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
      EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
      EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
      EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
      EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.reviveJump,
      EvmYul.Yul.State.overwrite?, EvmYul.Yul.State.toMachineState,
      FormalYul.returnOf, FormalYul.word, sharedFor_mstore_eq_sqrtSharedAfterFreePtr,
      sharedFor_mstore_mk_eq_sqrtSharedAfterFreePtr,
      sharedFor_inherited_mstore_mk_eq_sqrtSharedAfterFreePtr,
      call_shift_right_224_unsigned_direct,
      Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  unfold run_sqrt_floor_evm run_sqrt_evm
  exact FormalYul.Preservation.callWord_ok_of_dispatcherReturn_result_1000000
    (contract := yulContract) (selector := selector_sqrt) (args := [x])
    (hReturn := hReturn) (by simpa using hresult)

theorem run_sqrt_floor_evm_eq_natSqrt (x : Nat) :
    run_sqrt_floor_evm x = .ok (natSqrt (FormalYul.u256 x)) := by
  rw [run_sqrt_floor_evm_eq_floorSqrt]
  rw [floorSqrt_eq_natSqrt_u256]
  simpa [FormalYul.u256, FormalYul.WORD_MOD] using Nat.mod_lt x (Nat.two_pow_pos 256)

theorem run_sqrt_up_evm_eq_sqrtUp256 (x : Nat) :
    run_sqrt_up_evm x = .ok (sqrtUp256 (FormalYul.u256 x)) := by
  let selectorStore :=
    Finmap.insert "selector" (FormalYul.word 1707723681)
      (Inhabited.default : EvmYul.Yul.VarStore)
  obtain ⟨haltState, haltValue, hhalt⟩ :=
    external_fun_wrap_sqrtUp_sqrtUp_calldata_halts_999989 (x := x)
      (store := selectorStore)
  have hresult :=
    external_fun_wrap_sqrtUp_sqrtUp_calldata_result_999989 (x := x)
      (store := selectorStore)
  rw [hhalt] at hresult
  have hReturn :
      FormalYul.Preservation.DispatcherReturn yulContract
        (FormalYul.calldata selector_sqrtUp [x]) 999998 (FormalYul.returnOf haltState) :=
    dispatcherReturn_sqrtUp x haltState haltValue (by
      simpa [selectorStore] using hhalt)
  unfold run_sqrt_up_evm
  exact FormalYul.Preservation.callWord_ok_of_dispatcherReturn_result_1000000
    (contract := yulContract) (selector := selector_sqrtUp) (args := [x])
    (hReturn := hReturn) (by simpa using hresult)

end SqrtYul
