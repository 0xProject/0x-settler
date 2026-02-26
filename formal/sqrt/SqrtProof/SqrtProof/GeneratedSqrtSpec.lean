import Init
import SqrtProof.GeneratedSqrtModel
import SqrtProof.SqrtCorrect
import SqrtProof.CertifiedChain

namespace SqrtGeneratedModel

open SqrtGeneratedModel
open SqrtCertified
open SqrtCert

private theorem normStep_eq_bstep (x z : Nat) :
    normShr 1 (normAdd z (normDiv x z)) = bstep x z := by
  simp [normShr, normAdd, normDiv, bstep]

private theorem normSeed_eq_sqrtSeed_of_pos
    (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    normShl (normShr 1 (normSub 256 (normClz x))) 1 = sqrtSeed x := by
  unfold normShl normShr normSub normClz sqrtSeed
  simp [Nat.ne_of_gt hx]
  have hlog : Nat.log2 x < 256 := (Nat.log2_lt (Nat.ne_of_gt hx)).2 hx256
  have hlogle : Nat.log2 x ≤ 255 := by omega
  congr 1
  omega

private theorem model_sqrt_zero : model_sqrt 0 = 0 := by
  simp [model_sqrt, normShl, normShr, normSub, normClz, normAdd, normDiv]

private theorem word_mod_gt_256 : 256 < WORD_MOD := by
  unfold WORD_MOD
  decide

private theorem u256_eq_of_lt (x : Nat) (hx : x < WORD_MOD) : u256 x = x := by
  unfold u256
  exact Nat.mod_eq_of_lt hx

private theorem evmClz_eq_normClz_of_u256 (x : Nat) (hx : x < WORD_MOD) :
    evmClz x = normClz x := by
  unfold evmClz normClz
  simp [u256_eq_of_lt x hx]

private theorem normClz_le_256 (x : Nat) : normClz x ≤ 256 := by
  unfold normClz
  split <;> omega

private theorem evmSub_eq_normSub_of_le
    (a b : Nat) (ha : a < WORD_MOD) (hb : b ≤ a) :
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
    (a b : Nat)
    (ha : a < WORD_MOD)
    (hb : b < WORD_MOD)
    (hab : a + b < WORD_MOD) :
    evmAdd a b = normAdd a b := by
  unfold evmAdd normAdd
  simp [u256_eq_of_lt a ha, u256_eq_of_lt b hb, u256_eq_of_lt (a + b) hab]

private theorem evmLt_eq_normLt_of_u256
    (a b : Nat)
    (ha : a < WORD_MOD)
    (hb : b < WORD_MOD) :
    evmLt a b = normLt a b := by
  unfold evmLt normLt
  simp [u256_eq_of_lt a ha, u256_eq_of_lt b hb]

private theorem evmGt_eq_normGt_of_u256
    (a b : Nat)
    (ha : a < WORD_MOD)
    (hb : b < WORD_MOD) :
    evmGt a b = normGt a b := by
  unfold evmGt normGt
  simp [u256_eq_of_lt a ha, u256_eq_of_lt b hb]

private theorem evmShr_eq_normShr_of_u256
    (s v : Nat)
    (hs : s < 256)
    (hv : v < WORD_MOD) :
    evmShr s v = normShr s v := by
  unfold evmShr normShr
  have hs' : s < WORD_MOD := Nat.lt_of_lt_of_le hs (Nat.le_of_lt word_mod_gt_256)
  simp [u256_eq_of_lt s hs', u256_eq_of_lt v hv, hs]

private theorem evmShl_eq_normShl_of_safe
    (s v : Nat)
    (hs : s < 256)
    (hv : v < WORD_MOD)
    (hvs : v * 2 ^ s < WORD_MOD) :
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

private theorem evmLt_le_one (a b : Nat) : evmLt a b ≤ 1 := by
  unfold evmLt
  split <;> omega

private theorem seed_evm_eq_norm (x : Nat) (hx : x < WORD_MOD) :
    evmShl (evmShr 1 (evmSub 256 (evmClz x))) 1 =
      normShl (normShr 1 (normSub 256 (normClz x))) 1 := by
  have hclz : evmClz x = normClz x := evmClz_eq_normClz_of_u256 x hx
  have hclzLe : normClz x ≤ 256 := normClz_le_256 x
  have hsub :
      evmSub 256 (evmClz x) = normSub 256 (normClz x) := by
    have h256 : 256 < WORD_MOD := word_mod_gt_256
    simpa [hclz] using
      (evmSub_eq_normSub_of_le 256 (normClz x) h256 hclzLe)
  have hsubLt : normSub 256 (normClz x) < WORD_MOD := by
    have hle : normSub 256 (normClz x) ≤ 256 := by
      unfold normSub
      exact Nat.sub_le _ _
    exact Nat.lt_of_le_of_lt hle word_mod_gt_256
  have hshr :
      evmShr 1 (evmSub 256 (evmClz x)) =
        normShr 1 (normSub 256 (normClz x)) := by
    have h1 : (1 : Nat) < 256 := by decide
    simpa [hsub] using
      (evmShr_eq_normShr_of_u256 1 (normSub 256 (normClz x)) h1 hsubLt)
  have hsLt256 : normShr 1 (normSub 256 (normClz x)) < 256 := by
    unfold normShr
    have hle : normSub 256 (normClz x) ≤ 256 := by
      unfold normSub
      exact Nat.sub_le _ _
    have hdiv : normSub 256 (normClz x) / 2 ^ 1 ≤ 256 / 2 ^ 1 := Nat.div_le_div_right hle
    have hdiv' : normSub 256 (normClz x) / 2 ^ 1 ≤ 128 := by simpa using hdiv
    omega
  have hsLtWord : normShr 1 (normSub 256 (normClz x)) < WORD_MOD :=
    Nat.lt_of_lt_of_le hsLt256 (Nat.le_of_lt word_mod_gt_256)
  have hsafeMul :
      1 * 2 ^ (normShr 1 (normSub 256 (normClz x))) < WORD_MOD := by
    simpa [Nat.one_mul] using two_pow_lt_word (normShr 1 (normSub 256 (normClz x))) hsLt256
  calc
    evmShl (evmShr 1 (evmSub 256 (evmClz x))) 1
        = evmShl (normShr 1 (normSub 256 (normClz x))) 1 := by simp [hshr]
    _ = normShl (normShr 1 (normSub 256 (normClz x))) 1 := by
          have h1word : 1 < WORD_MOD := by
            unfold WORD_MOD
            decide
          simpa [Nat.one_mul] using
            (evmShl_eq_normShl_of_safe
              (normShr 1 (normSub 256 (normClz x))) 1 hsLt256 h1word hsafeMul)

private theorem step_evm_eq_norm_of_safe
    (x z : Nat)
    (hx : x < WORD_MOD)
    (_hzPos : 0 < z)
    (hz : z < WORD_MOD)
    (hsum : z + x / z < WORD_MOD) :
    evmShr 1 (evmAdd z (evmDiv x z)) = normShr 1 (normAdd z (normDiv x z)) := by
  have hdivLt : x / z < WORD_MOD := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  have hdiv : evmDiv x z = normDiv x z := evmDiv_eq_normDiv_of_u256 x z hx hz
  have hadd : evmAdd z (evmDiv x z) = normAdd z (normDiv x z) := by
    simpa [hdiv] using evmAdd_eq_normAdd_of_no_overflow z (x / z) hz hdivLt hsum
  have hsumLt : normAdd z (normDiv x z) < WORD_MOD := by
    simpa [normAdd, normDiv] using hsum
  have h1 : (1 : Nat) < 256 := by decide
  calc
    evmShr 1 (evmAdd z (evmDiv x z))
        = evmShr 1 (normAdd z (normDiv x z)) := by simp [hadd]
    _ = normShr 1 (normAdd z (normDiv x z)) := by
          simpa using evmShr_eq_normShr_of_u256 1 (normAdd z (normDiv x z)) h1 hsumLt

private theorem m_lt_pow128_of_u256
    (m x : Nat)
    (hmlo : m * m ≤ x)
    (hx : x < WORD_MOD) :
    m < 2 ^ 128 := by
  by_cases hm128 : m < 2 ^ 128
  · exact hm128
  · have hmGe : 2 ^ 128 ≤ m := Nat.le_of_not_lt hm128
    have hmSqGe : 2 ^ 256 ≤ m * m := by
      have hpow : 2 ^ 256 = (2 ^ 128) * (2 ^ 128) := by
        calc
          2 ^ 256 = 2 ^ (128 + 128) := by decide
          _ = (2 ^ 128) * (2 ^ 128) := by rw [Nat.pow_add]
      have hmul : (2 ^ 128) * (2 ^ 128) ≤ m * m := Nat.mul_le_mul hmGe hmGe
      simpa [hpow] using hmul
    have hxGe : 2 ^ 256 ≤ x := Nat.le_trans hmSqGe hmlo
    exact False.elim ((Nat.not_lt_of_ge hxGe) hx)

private theorem x_div_m_le_m_plus_two
    (x m : Nat)
    (hm : 0 < m)
    (hmhi : x < (m + 1) * (m + 1)) :
    x / m ≤ m + 2 := by
  have hmhi' : x < m * m + 2 * m + 1 := by
    have hsq : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega
    simpa [hsq] using hmhi
  have hmhi'' : x < (m * m + 2 * m) + 1 := by omega
  have hx_le : x ≤ m * m + 2 * m := Nat.lt_succ_iff.mp hmhi''
  calc
    x / m ≤ (m * m + 2 * m) / m := Nat.div_le_div_right hx_le
    _ = (m + 2) * m / m := by rw [Nat.add_mul]
    _ = m + 2 := Nat.mul_div_cancel (m + 2) hm

private theorem sum_lt_word_of_cert
    (x m z d : Nat)
    (hx : x < WORD_MOD)
    (hm : 0 < m)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hmz : m ≤ z)
    (hzd : z - m ≤ d)
    (hdm : d ≤ m) :
    z + x / z < WORD_MOD := by
  have hdiv_z_m : x / z ≤ x / m := Nat.div_le_div_left hmz hm
  have hdiv_m : x / m ≤ m + 2 := x_div_m_le_m_plus_two x m hm hmhi
  have hdiv : x / z ≤ m + 2 := Nat.le_trans hdiv_z_m hdiv_m
  have hz_le_md : z ≤ d + m := (Nat.sub_le_iff_le_add).1 hzd
  have hz_le_2m : z ≤ 2 * m := by omega
  have hsum_le : z + x / z ≤ 3 * m + 2 := by omega
  have hm128 : m < 2 ^ 128 := m_lt_pow128_of_u256 m x hmlo hx
  have hsum_lt_const : z + x / z < 3 * (2 ^ 128) + 2 := by omega
  have hconst : 3 * (2 ^ 128) + 2 < WORD_MOD := by
    unfold WORD_MOD
    decide
  exact Nat.lt_trans hsum_lt_const hconst

private theorem seed_sum_lt_word
    (i : Fin 256) (x : Nat)
    (hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1)) :
    seedOf i + x / seedOf i < WORD_MOD := by
  have hsPos : 0 < seedOf i := by
    have hpow : 0 < (2 : Nat) ^ ((i.val + 1) / 2) := Nat.pow_pos (by decide : 0 < (2 : Nat))
    simpa [seedOf, Nat.shiftLeft_eq, Nat.one_mul] using hpow
  have hk_le : (i.val + 1) / 2 ≤ 128 := by omega
  have hz_le : seedOf i ≤ 2 ^ 128 := by
    unfold seedOf
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.pow_le_pow_right (by decide : (2 : Nat) > 0) hk_le
  have hExp : i.val + 1 ≤ 2 * ((i.val + 1) / 2) + 1 := by omega
  have hPowLe : 2 ^ (i.val + 1) ≤ 2 ^ (2 * ((i.val + 1) / 2) + 1) :=
    Nat.pow_le_pow_right (by decide : (2 : Nat) > 0) hExp
  have hPowMul : 2 ^ (2 * ((i.val + 1) / 2) + 1) = 2 * seedOf i * seedOf i := by
    calc
      2 ^ (2 * ((i.val + 1) / 2) + 1) = 2 ^ (2 * ((i.val + 1) / 2)) * 2 := by rw [Nat.pow_add]
      _ = (2 ^ ((i.val + 1) / 2) * 2 ^ ((i.val + 1) / 2)) * 2 := by
            rw [show 2 * ((i.val + 1) / 2) = ((i.val + 1) / 2) + ((i.val + 1) / 2) by omega, Nat.pow_add]
      _ = 2 * seedOf i * seedOf i := by
            unfold seedOf
            simp [Nat.shiftLeft_eq, Nat.one_mul, Nat.mul_comm, Nat.mul_left_comm]
  have hxmul : x < 2 * seedOf i * seedOf i := by
    exact Nat.lt_of_lt_of_le hOct.2 (by simpa [hPowMul] using hPowLe)
  have hdiv : x / seedOf i < 2 * seedOf i := by
    apply (Nat.div_lt_iff_lt_mul hsPos).2
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hxmul
  have hsum_lt : seedOf i + x / seedOf i < seedOf i + 2 * seedOf i := by omega
  have hsum_le : seedOf i + 2 * seedOf i ≤ 3 * (2 ^ 128) := by omega
  have hconst : 3 * (2 ^ 128) < WORD_MOD := by
    unfold WORD_MOD
    decide
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hsum_lt hsum_le) (Nat.le_of_lt hconst)

private theorem normLt_div_le (x z : Nat) :
    normLt (normDiv x z) z ≤ z := by
  by_cases hz0 : z = 0
  · simp [normLt, normDiv, hz0]
  · have hzPos : 0 < z := Nat.pos_of_ne_zero hz0
    have h1 : 1 ≤ z := Nat.succ_le_of_lt hzPos
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

theorem model_sqrt_evm_eq_model_sqrt
    (x : Nat)
    (hx256 : x < WORD_MOD) :
    model_sqrt_evm x = model_sqrt x := by
  by_cases hx0 : x = 0
  · subst hx0
    decide
  · have hx : 0 < x := Nat.pos_of_ne_zero hx0
    let i : Fin 256 := ⟨Nat.log2 x, (Nat.log2_lt (Nat.ne_of_gt hx)).2 hx256⟩
    let m := natSqrt x
    have hmlo : m * m ≤ x := by simpa [m] using natSqrt_sq_le x
    have hmhi : x < (m + 1) * (m + 1) := by simpa [m] using natSqrt_lt_succ_sq x
    have hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1) := by
      have hlog : 2 ^ Nat.log2 x ≤ x ∧ x < 2 ^ (Nat.log2 x + 1) :=
        (Nat.log2_eq_iff (Nat.ne_of_gt hx)).1 rfl
      simpa [i]
    have hm : 0 < m := by
      by_cases hm0 : m = 0
      ·
        have hx1 : 1 ≤ x := Nat.succ_le_of_lt hx
        have hlt1 : x < 1 := by
          have : x < (0 + 1) * (0 + 1) := by simpa [hm0] using hmhi
          simpa using this
        exact False.elim ((Nat.not_lt_of_ge hx1) hlt1)
      · exact Nat.pos_of_ne_zero hm0
    have hseedOf : sqrtSeed x = seedOf i := sqrtSeed_eq_seedOf_of_octave i x hOct
    have hseedNorm :
        normShl (normShr 1 (normSub 256 (normClz x))) 1 = seedOf i := by
      exact (normSeed_eq_sqrtSeed_of_pos x hx hx256).trans hseedOf
    have hseedEvm :
        evmShl (evmShr 1 (evmSub 256 (evmClz x))) 1 = seedOf i := by
      exact (seed_evm_eq_norm x hx256).trans hseedNorm
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
      simpa [seedOf, Nat.shiftLeft_eq, Nat.one_mul] using hpow
    have hmz1 : m ≤ z1 := by
      dsimp [z1, z0]
      exact babylon_step_floor_bound x (seedOf i) m hsPos hmlo
    have hz1Pos : 0 < z1 := Nat.lt_of_lt_of_le hm hmz1
    have hmz2 : m ≤ z2 := by
      dsimp [z2]
      exact babylon_step_floor_bound x z1 m hz1Pos hmlo
    have hz2Pos : 0 < z2 := Nat.lt_of_lt_of_le hm hmz2
    have hmz3 : m ≤ z3 := by
      dsimp [z3]
      exact babylon_step_floor_bound x z2 m hz2Pos hmlo
    have hz3Pos : 0 < z3 := Nat.lt_of_lt_of_le hm hmz3
    have hmz4 : m ≤ z4 := by
      dsimp [z4]
      exact babylon_step_floor_bound x z3 m hz3Pos hmlo
    have hz4Pos : 0 < z4 := Nat.lt_of_lt_of_le hm hmz4
    have hmz5 : m ≤ z5 := by
      dsimp [z5]
      exact babylon_step_floor_bound x z4 m hz4Pos hmlo
    have hz5Pos : 0 < z5 := Nat.lt_of_lt_of_le hm hmz5
    have hinterval : loOf i ≤ m ∧ m ≤ hiOf i := m_within_cert_interval i x m hmlo hmhi hOct
    have hrun5 := run5_error_bounds i x m hm hmlo hmhi hinterval.1 hinterval.2
    have hd1 : z1 - m ≤ d1 i := by simpa [z1, z2, z3, z4, z5] using hrun5.1
    have hd2 : z2 - m ≤ d2 i := by simpa [z1, z2, z3, z4, z5] using hrun5.2.1
    have hd3 : z3 - m ≤ d3 i := by simpa [z1, z2, z3, z4, z5] using hrun5.2.2.1
    have hd4 : z4 - m ≤ d4 i := by simpa [z1, z2, z3, z4, z5] using hrun5.2.2.2.1
    have hd5 : z5 - m ≤ d5 i := by simpa [z1, z2, z3, z4, z5] using hrun5.2.2.2.2
    have hd1m : d1 i ≤ m := Nat.le_trans (d1_le_lo i) hinterval.1
    have hd2m : d2 i ≤ m := Nat.le_trans (d2_le_lo i) hinterval.1
    have hd3m : d3 i ≤ m := Nat.le_trans (d3_le_lo i) hinterval.1
    have hd4m : d4 i ≤ m := Nat.le_trans (d4_le_lo i) hinterval.1
    have hd5m : d5 i ≤ m := Nat.le_trans (d5_le_lo i) hinterval.1
    have hsum0 : z0 + x / z0 < WORD_MOD := by
      simpa [z0] using seed_sum_lt_word i x hOct
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
    have hstep1 : evmShr 1 (evmAdd z0 (evmDiv x z0)) = z1 := by
      have h := step_evm_eq_norm_of_safe x z0 hx256 hsPos hz0 hsum0
      simpa [z1, normStep_eq_bstep] using h
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
    have hxmod : u256 x = x := u256_eq_of_lt x hx256
    unfold model_sqrt_evm model_sqrt
    simp [hxmod, hseedEvm, hseedNorm, z0, z1, z2, z3, z4, z5, z6,
      hstep1, hstep2, hstep3, hstep4, hstep5, hstep6, normStep_eq_bstep]

theorem model_sqrt_eq_innerSqrt (x : Nat) (hx256 : x < 2 ^ 256) :
    model_sqrt x = innerSqrt x := by
  by_cases hx0 : x = 0
  · subst hx0
    simp [innerSqrt, model_sqrt_zero]
  · have hx : 0 < x := Nat.pos_of_ne_zero hx0
    have hseed : normShl (normShr 1 (normSub 256 (normClz x))) 1 = sqrtSeed x :=
      normSeed_eq_sqrtSeed_of_pos x hx hx256
    unfold model_sqrt innerSqrt
    simp [Nat.ne_of_gt hx, hseed, normStep_eq_bstep]

theorem model_sqrt_bracket_u256_all
  (x : Nat)
  (hx256 : x < 2 ^ 256) :
  let m := natSqrt x
  m ≤ model_sqrt x ∧ model_sqrt x ≤ m + 1 := by
  simpa [model_sqrt_eq_innerSqrt x hx256] using innerSqrt_bracket_u256_all x hx256

theorem model_sqrt_evm_bracket_u256_all
    (x : Nat)
    (hx256 : x < 2 ^ 256) :
    let m := natSqrt x
    m ≤ model_sqrt_evm x ∧ model_sqrt_evm x ≤ m + 1 := by
  have hxW : x < WORD_MOD := by simpa [WORD_MOD] using hx256
  simpa [model_sqrt_evm_eq_model_sqrt x hxW] using model_sqrt_bracket_u256_all x hx256

theorem model_sqrt_floor_eq_floorSqrt
    (x : Nat)
    (hx256 : x < 2 ^ 256) :
    model_sqrt_floor x = floorSqrt x := by
  have hinner : model_sqrt x = innerSqrt x := model_sqrt_eq_innerSqrt x hx256
  unfold model_sqrt_floor floorSqrt
  simp [hinner, floor_correction_norm_eq_if]

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
  have hbLe : normLt (normDiv x z) z ≤ z := normLt_div_le x z
  calc
    evmSub z (evmLt (evmDiv x z) z)
        = evmSub z (normLt (normDiv x z) z) := by simp [hlt]
    _ = normSub z (normLt (normDiv x z) z) :=
          evmSub_eq_normSub_of_le z (normLt (normDiv x z) z) hz hbLe

theorem model_sqrt_floor_evm_eq_model_sqrt_floor
    (x : Nat)
    (hxW : x < WORD_MOD) :
    model_sqrt_floor_evm x = model_sqrt_floor x := by
  have hx256 : x < 2 ^ 256 := by simpa [WORD_MOD] using hxW
  have hbr := model_sqrt_evm_bracket_u256_all x hx256
  have hzLe : model_sqrt_evm x ≤ natSqrt x + 1 := by simpa using hbr.2
  have hm128 : natSqrt x < 2 ^ 128 :=
    m_lt_pow128_of_u256 (natSqrt x) x (natSqrt_sq_le x) hxW
  have hz128 : model_sqrt_evm x ≤ 2 ^ 128 := by omega
  have hpow128 : 2 ^ 128 < WORD_MOD := two_pow_lt_word 128 (by decide)
  have hzW : model_sqrt_evm x < WORD_MOD := Nat.lt_of_le_of_lt hz128 hpow128
  have hroot : model_sqrt_evm x = model_sqrt x := model_sqrt_evm_eq_model_sqrt x hxW
  have hxmod : u256 x = x := u256_eq_of_lt x hxW
  unfold model_sqrt_floor_evm model_sqrt_floor
  simp [hxmod]
  simpa [hroot] using floor_step_evm_eq_norm x (model_sqrt_evm x) hxW hzW

theorem model_sqrt_floor_evm_eq_floorSqrt
    (x : Nat)
    (hx256 : x < 2 ^ 256) :
    model_sqrt_floor_evm x = floorSqrt x := by
  have hxW : x < WORD_MOD := by simpa [WORD_MOD] using hx256
  calc
    model_sqrt_floor_evm x = model_sqrt_floor x := model_sqrt_floor_evm_eq_model_sqrt_floor x hxW
    _ = floorSqrt x := model_sqrt_floor_eq_floorSqrt x hx256

/-- Specification-level model for `sqrtUp`: round `innerSqrt` upward if needed. -/
def sqrtUpSpec (x : Nat) : Nat :=
  let z := innerSqrt x
  if z * z < x then z + 1 else z

private theorem model_sqrt_up_norm_eq_sqrtUpSpec
    (x : Nat)
    (hx256 : x < 2 ^ 256) :
    model_sqrt_up x = sqrtUpSpec x := by
  have hinner : model_sqrt x = innerSqrt x := model_sqrt_eq_innerSqrt x hx256
  have hsqge : innerSqrt x ≤ innerSqrt x * innerSqrt x := by
    by_cases hz0 : innerSqrt x = 0
    · simp [hz0]
    · have hzPos : 0 < innerSqrt x := Nat.pos_of_ne_zero hz0
      have h1 : 1 ≤ innerSqrt x := Nat.succ_le_of_lt hzPos
      calc
        innerSqrt x = innerSqrt x * 1 := by simp
        _ ≤ innerSqrt x * innerSqrt x := Nat.mul_le_mul_left _ h1
  unfold model_sqrt_up sqrtUpSpec
  by_cases hlt : innerSqrt x * innerSqrt x < x
  · simp [normAdd, normMul, normLt, normGt, hinner, hlt, hsqge, Nat.add_comm]
  · simp [normAdd, normMul, normLt, normGt, hinner, hlt]

private theorem sqrtUp_step_evm_eq_spec
    (x z : Nat)
    (hxW : x < WORD_MOD)
    (hzLe128 : z ≤ 2 ^ 128) :
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
    have hltXLe : evmLt (evmMul z z) x ≤ 1 := evmLt_le_one (evmMul z z) x
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
      have hmulLe : z * z ≤ z * (2 ^ 128) := Nat.mul_le_mul_left z (Nat.le_of_lt hzLt)
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
    have hsqGe : z ≤ z * z := by
      by_cases hz0 : z = 0
      · simp [hz0]
      · have hzPos : 0 < z := Nat.pos_of_ne_zero hz0
        have h1 : 1 ≤ z := Nat.succ_le_of_lt hzPos
        calc
          z = z * 1 := by simp
          _ ≤ z * z := Nat.mul_le_mul_left z h1
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
        have hle : 1 + z ≤ 1 + 2 ^ 128 := by omega
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

theorem model_sqrt_up_eq_sqrtUpSpec
    (x : Nat)
    (hx256 : x < 2 ^ 256) :
    model_sqrt_up x = sqrtUpSpec x :=
  model_sqrt_up_norm_eq_sqrtUpSpec x hx256

theorem model_sqrt_up_evm_eq_sqrtUpSpec
    (x : Nat)
    (hx256 : x < 2 ^ 256) :
    model_sqrt_up_evm x = sqrtUpSpec x := by
  have hxW : x < WORD_MOD := by simpa [WORD_MOD] using hx256
  have hbr := model_sqrt_evm_bracket_u256_all x hx256
  have hzLe : model_sqrt_evm x ≤ natSqrt x + 1 := by simpa using hbr.2
  have hm128 : natSqrt x < 2 ^ 128 :=
    m_lt_pow128_of_u256 (natSqrt x) x (natSqrt_sq_le x) hxW
  have hzLe128 : model_sqrt_evm x ≤ 2 ^ 128 := by omega
  have hroot : model_sqrt_evm x = innerSqrt x := by
    exact (model_sqrt_evm_eq_model_sqrt x hxW).trans (model_sqrt_eq_innerSqrt x hx256)
  have hxmod : u256 x = x := u256_eq_of_lt x hxW
  unfold model_sqrt_up_evm sqrtUpSpec
  simp [hxmod]
  simpa [hroot] using sqrtUp_step_evm_eq_spec x (model_sqrt_evm x) hxW hzLe128

private theorem step_error_bound_square
    (m d : Nat)
    (hm : 0 < m)
    (hmd : d ≤ m) :
    bstep (m * m) (m + d) - m ≤ d * d / (2 * m) := by
  unfold bstep
  have hpos : 0 < m + d := by omega
  have hsq : m * m = (m + d) * (m - d) + d * d := by
    have h := sq_identity_ge (m + d) m (by omega) (by omega)
    have hsub : 2 * m - (m + d) = m - d := by omega
    have hdm' : (m + d) - m = d := by rw [Nat.add_sub_cancel_left]
    simpa [hsub, hdm'] using h.symm
  have hdiv : m * m / (m + d) = (m - d) + d * d / (m + d) := by
    rw [hsq]
    rw [Nat.mul_add_div hpos]
  have hrewrite :
      (m + d + m * m / (m + d)) / 2 - m = (d * d / (m + d)) / 2 := by
    rw [hdiv]
    let q := d * d / (m + d)
    have htmp : (m + d + (m - d + q)) / 2 = m + q / 2 := by
      have hsum : m + d + (m - d + q) = 2 * m + q := by omega
      rw [hsum]
      have htmp2 : (2 * m + q) / 2 = m + q / 2 := by
        have hswap : 2 * m + q = q + m * 2 := by omega
        rw [hswap, Nat.add_mul_div_right q m (by decide : 0 < 2)]
        omega
      exact htmp2
    rw [htmp, Nat.add_sub_cancel_left]
  rw [hrewrite]
  have hden : m ≤ m + d := by omega
  have hdivLe : d * d / (m + d) ≤ d * d / m := Nat.div_le_div_left hden hm
  have hhalf : (d * d / (m + d)) / 2 ≤ (d * d / m) / 2 := Nat.div_le_div_right hdivLe
  have hmain : (d * d / m) / 2 = d * d / (2 * m) := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm m 2]
  exact Nat.le_trans hhalf (by simp [hmain])

private theorem step_from_bound_square
    (m lo z D : Nat)
    (hm : 0 < m)
    (hloPos : 0 < lo)
    (hlo : lo ≤ m)
    (hmz : m ≤ z)
    (hzD : z - m ≤ D)
    (hDlo : D ≤ lo) :
    bstep (m * m) z - m ≤ D * D / (2 * lo) := by
  let d := z - m
  have hdEq : z = m + d := by
    dsimp [d]
    omega
  have hdm : d ≤ m := by
    dsimp [d]
    omega
  have hstep : bstep (m * m) (m + d) - m ≤ d * d / (2 * m) :=
    step_error_bound_square m d hm hdm
  have hbase : bstep (m * m) z - m ≤ d * d / (2 * m) := by
    simpa [hdEq] using hstep
  have hdD : d ≤ D := by
    simpa [d] using hzD
  have hsq : d * d ≤ D * D := Nat.mul_le_mul hdD hdD
  have hdiv : d * d / (2 * m) ≤ D * D / (2 * m) := Nat.div_le_div_right hsq
  have hden : 2 * lo ≤ 2 * m := Nat.mul_le_mul_left 2 hlo
  have hdivDen : D * D / (2 * m) ≤ D * D / (2 * lo) :=
    Nat.div_le_div_left hden (by omega : 0 < 2 * lo)
  exact Nat.le_trans hbase (Nat.le_trans hdiv hdivDen)

private def sqNext (lo d : Nat) : Nat := d * d / (2 * lo)

private def sqD2 (i : Fin 256) : Nat := sqNext (loOf i) (d1 i)
private def sqD3 (i : Fin 256) : Nat := sqNext (loOf i) (sqD2 i)
private def sqD4 (i : Fin 256) : Nat := sqNext (loOf i) (sqD3 i)
private def sqD5 (i : Fin 256) : Nat := sqNext (loOf i) (sqD4 i)
private def sqD6 (i : Fin 256) : Nat := sqNext (loOf i) (sqD5 i)

private theorem sqNext_mono_right (lo a b : Nat) (hab : a ≤ b) :
    sqNext lo a ≤ sqNext lo b := by
  unfold sqNext
  exact Nat.div_le_div_right (Nat.mul_le_mul hab hab)

private theorem sqNext_le_lo
    (lo d : Nat)
    (hlo : 0 < lo)
    (hd : d ≤ lo) :
    sqNext lo d ≤ lo := by
  unfold sqNext
  have hsq : d * d ≤ lo * lo := Nat.mul_le_mul hd hd
  have hdiv : d * d / (2 * lo) ≤ lo * lo / (2 * lo) := Nat.div_le_div_right hsq
  have hden : lo ≤ 2 * lo := by omega
  have hdiv' : lo * lo / (2 * lo) ≤ lo * lo / lo := Nat.div_le_div_left hden hlo
  have hmul : lo * lo / lo = lo := by simpa [Nat.mul_comm] using Nat.mul_div_right lo hlo
  exact Nat.le_trans hdiv (by simpa [hmul] using hdiv')

private theorem sqD2_le_lo : ∀ i : Fin 256, sqD2 i ≤ loOf i := by
  intro i
  unfold sqD2
  exact sqNext_le_lo (loOf i) (d1 i) (lo_pos i) (d1_le_lo i)

private theorem sqD3_le_lo : ∀ i : Fin 256, sqD3 i ≤ loOf i := by
  intro i
  unfold sqD3
  exact sqNext_le_lo (loOf i) (sqD2 i) (lo_pos i) (sqD2_le_lo i)

private theorem sqD4_le_lo : ∀ i : Fin 256, sqD4 i ≤ loOf i := by
  intro i
  unfold sqD4
  exact sqNext_le_lo (loOf i) (sqD3 i) (lo_pos i) (sqD3_le_lo i)

private theorem sqD5_le_lo : ∀ i : Fin 256, sqD5 i ≤ loOf i := by
  intro i
  unfold sqD5
  exact sqNext_le_lo (loOf i) (sqD4 i) (lo_pos i) (sqD4_le_lo i)

private theorem sqD2_le_d2 : ∀ i : Fin 256, sqD2 i ≤ d2 i := by
  intro i
  simp [sqD2, d2, sqNext, nextD]

private theorem sqD3_le_d3 : ∀ i : Fin 256, sqD3 i ≤ d3 i := by
  intro i
  have hmono : sqNext (loOf i) (sqD2 i) ≤ sqNext (loOf i) (d2 i) :=
    sqNext_mono_right (loOf i) (sqD2 i) (d2 i) (sqD2_le_d2 i)
  unfold sqD3 d3 nextD
  exact Nat.le_trans hmono (Nat.le_succ _)

private theorem sqD4_le_d4 : ∀ i : Fin 256, sqD4 i ≤ d4 i := by
  intro i
  have hmono : sqNext (loOf i) (sqD3 i) ≤ sqNext (loOf i) (d3 i) :=
    sqNext_mono_right (loOf i) (sqD3 i) (d3 i) (sqD3_le_d3 i)
  unfold sqD4 d4 nextD
  exact Nat.le_trans hmono (Nat.le_succ _)

private theorem sqD5_le_d5 : ∀ i : Fin 256, sqD5 i ≤ d5 i := by
  intro i
  have hmono : sqNext (loOf i) (sqD4 i) ≤ sqNext (loOf i) (d4 i) :=
    sqNext_mono_right (loOf i) (sqD4 i) (d4 i) (sqD4_le_d4 i)
  unfold sqD5 d5 nextD
  exact Nat.le_trans hmono (Nat.le_succ _)

private theorem sqD6_eq_zero : ∀ i : Fin 256, sqD6 i = 0 := by
  intro i
  have hsqLe : sqD6 i ≤ sqNext (loOf i) (d5 i) := by
    unfold sqD6
    exact sqNext_mono_right (loOf i) (sqD5 i) (d5 i) (sqD5_le_d5 i)
  have hd6le : d6 i ≤ 1 := d6_le_one i
  have hd6ge : 1 ≤ d6 i := by
    unfold d6 nextD
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hd6eq : d6 i = 1 := Nat.le_antisymm hd6le hd6ge
  have hsq0 : sqNext (loOf i) (d5 i) = 0 := by
    have hq : sqNext (loOf i) (d5 i) + 1 = d6 i := by
      simp [sqNext, d6, nextD]
    omega
  have hsqD6le0 : sqD6 i ≤ 0 := Nat.le_trans hsqLe (by simp [hsq0])
  exact Nat.eq_zero_of_le_zero hsqD6le0

private theorem innerSqrt_eq_natSqrt_of_square
    (x : Nat)
    (hx256 : x < 2 ^ 256)
    (hsq : natSqrt x * natSqrt x = x) :
    innerSqrt x = natSqrt x := by
  by_cases hx0 : x = 0
  · subst hx0
    simp [innerSqrt, natSqrt]
  · have hx : 0 < x := Nat.pos_of_ne_zero hx0
    let m := natSqrt x
    have hmSq : m * m = x := by simpa [m] using hsq
    have hmlo : m * m ≤ x := by simp [m, hmSq]
    have hmhi : x < (m + 1) * (m + 1) := by simpa [m] using natSqrt_lt_succ_sq x
    have hm : 0 < m := by
      by_cases hm0 : m = 0
      · have hx0' : x = 0 := by simpa [m, hm0] using hmSq.symm
        exact False.elim (hx0 hx0')
      · exact Nat.pos_of_ne_zero hm0
    let i : Fin 256 := ⟨Nat.log2 x, (Nat.log2_lt (Nat.ne_of_gt hx)).2 (by simpa [WORD_MOD] using hx256)⟩
    have hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1) := by
      have hlog : 2 ^ Nat.log2 x ≤ x ∧ x < 2 ^ (Nat.log2 x + 1) :=
        (Nat.log2_eq_iff (Nat.ne_of_gt hx)).1 rfl
      simpa [i]
    have hseed : sqrtSeed x = seedOf i := sqrtSeed_eq_seedOf_of_octave i x hOct
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
      simpa [seedOf, Nat.shiftLeft_eq, Nat.one_mul] using hpow
    have hmz1 : m ≤ z1 := by
      dsimp [z1, z0]
      exact babylon_step_floor_bound x (seedOf i) m hsPos hmlo
    have hz1Pos : 0 < z1 := Nat.lt_of_lt_of_le hm hmz1
    have hmz2 : m ≤ z2 := by
      dsimp [z2]
      exact babylon_step_floor_bound x z1 m hz1Pos hmlo
    have hz2Pos : 0 < z2 := Nat.lt_of_lt_of_le hm hmz2
    have hmz3 : m ≤ z3 := by
      dsimp [z3]
      exact babylon_step_floor_bound x z2 m hz2Pos hmlo
    have hz3Pos : 0 < z3 := Nat.lt_of_lt_of_le hm hmz3
    have hmz4 : m ≤ z4 := by
      dsimp [z4]
      exact babylon_step_floor_bound x z3 m hz3Pos hmlo
    have hz4Pos : 0 < z4 := Nat.lt_of_lt_of_le hm hmz4
    have hmz5 : m ≤ z5 := by
      dsimp [z5]
      exact babylon_step_floor_bound x z4 m hz4Pos hmlo
    have hz5Pos : 0 < z5 := Nat.lt_of_lt_of_le hm hmz5
    have hmz6 : m ≤ z6 := by
      dsimp [z6]
      exact babylon_step_floor_bound x z5 m hz5Pos hmlo
    have hinterval : loOf i ≤ m ∧ m ≤ hiOf i := m_within_cert_interval i x m hmlo hmhi hOct
    have hrun5 := run5_error_bounds i x m hm hmlo hmhi hinterval.1 hinterval.2
    have hd1 : z1 - m ≤ d1 i := by simpa [z1, z2, z3, z4, z5] using hrun5.1
    have hd2 : z2 - m ≤ sqD2 i := by
      have h := step_from_bound_square m (loOf i) z1 (d1 i) hm (lo_pos i) hinterval.1 hmz1 hd1 (d1_le_lo i)
      simpa [z2, hmSq, sqD2, sqNext] using h
    have hd3 : z3 - m ≤ sqD3 i := by
      have h := step_from_bound_square m (loOf i) z2 (sqD2 i) hm (lo_pos i) hinterval.1 hmz2 hd2 (sqD2_le_lo i)
      simpa [z3, hmSq, sqD3, sqNext] using h
    have hd4 : z4 - m ≤ sqD4 i := by
      have h := step_from_bound_square m (loOf i) z3 (sqD3 i) hm (lo_pos i) hinterval.1 hmz3 hd3 (sqD3_le_lo i)
      simpa [z4, hmSq, sqD4, sqNext] using h
    have hd5 : z5 - m ≤ sqD5 i := by
      have h := step_from_bound_square m (loOf i) z4 (sqD4 i) hm (lo_pos i) hinterval.1 hmz4 hd4 (sqD4_le_lo i)
      simpa [z5, hmSq, sqD5, sqNext] using h
    have hd6 : z6 - m ≤ sqD6 i := by
      have h := step_from_bound_square m (loOf i) z5 (sqD5 i) hm (lo_pos i) hinterval.1 hmz5 hd5 (sqD5_le_lo i)
      simpa [z6, hmSq, sqD6, sqNext] using h
    have hz6le : z6 ≤ m := by
      have h0 : z6 - m = 0 := by
        have h0le : z6 - m ≤ 0 := by simpa [sqD6_eq_zero i] using hd6
        exact Nat.eq_zero_of_le_zero h0le
      exact (Nat.sub_eq_zero_iff_le).1 h0
    have hz6eq : z6 = m := Nat.le_antisymm hz6le hmz6
    have hrun : innerSqrt x = run6From x (seedOf i) := by
      calc
        innerSqrt x = run6From x (sqrtSeed x) := innerSqrt_eq_run6From x hx
        _ = run6From x (seedOf i) := by simp [hseed]
    have hrun6 : run6From x (seedOf i) = z6 := by
      unfold run6From
      simp [z1, z2, z3, z4, z5, z6, z0, SqrtBridge.bstep, bstep]
    calc
      innerSqrt x = run6From x (seedOf i) := hrun
      _ = z6 := hrun6
      _ = m := hz6eq
      _ = natSqrt x := by rfl

private theorem minimal_of_pred_lt
    (x r : Nat)
    (hpred : r = 0 ∨ (r - 1) * (r - 1) < x) :
    ∀ y, x ≤ y * y → r ≤ y := by
  intro y hy
  by_cases hry : r ≤ y
  · exact hry
  · have hylt : y < r := Nat.lt_of_not_ge hry
    cases hpred with
    | inl hr0 =>
        exact False.elim ((Nat.not_lt_of_ge hylt) (by simp [hr0]))
    | inr hpredlt =>
        have hyle : y ≤ r - 1 := by omega
        have hysq : y * y ≤ (r - 1) * (r - 1) := Nat.mul_le_mul hyle hyle
        have hcontra : x ≤ (r - 1) * (r - 1) := Nat.le_trans hy hysq
        exact False.elim ((Nat.not_lt_of_ge hcontra) hpredlt)

theorem model_sqrt_up_evm_ceil_u256
    (x : Nat)
    (hx256 : x < 2 ^ 256) :
    let r := model_sqrt_up_evm x
    x ≤ r * r ∧ ∀ y, x ≤ y * y → r ≤ y := by
  have hUp : model_sqrt_up_evm x = sqrtUpSpec x := model_sqrt_up_evm_eq_sqrtUpSpec x hx256
  rw [hUp]
  unfold sqrtUpSpec
  let m := natSqrt x
  have hmlo : m * m ≤ x := by simpa [m] using natSqrt_sq_le x
  have hmhi : x < (m + 1) * (m + 1) := by simpa [m] using natSqrt_lt_succ_sq x
  have hbr : m ≤ innerSqrt x ∧ innerSqrt x ≤ m + 1 := by
    simpa [m] using innerSqrt_bracket_u256_all x hx256
  by_cases hlt : innerSqrt x * innerSqrt x < x
  · have hinter : innerSqrt x = m := by
      have hneq : innerSqrt x ≠ m + 1 := by
        intro hce
        have hbad : (m + 1) * (m + 1) < x := by simpa [hce] using hlt
        exact False.elim ((Nat.not_lt_of_ge (Nat.le_of_lt hmhi)) hbad)
      omega
    simp [hlt]
    constructor
    · have hupper : x ≤ (m + 1) * (m + 1) := Nat.le_of_lt hmhi
      simpa [hinter]
    · exact minimal_of_pred_lt x (innerSqrt x + 1) (Or.inr (by simpa using hlt))
  · simp [hlt]
    constructor
    · exact Nat.le_of_not_gt hlt
    · have hpred :
          innerSqrt x = 0 ∨ (innerSqrt x - 1) * (innerSqrt x - 1) < x := by
        have hsqCases : m * m < x ∨ m * m = x := Nat.lt_or_eq_of_le hmlo
        cases hsqCases with
        | inl hsqLt =>
            have hle : innerSqrt x - 1 ≤ m := by omega
            have hsqle : (innerSqrt x - 1) * (innerSqrt x - 1) ≤ m * m := Nat.mul_le_mul hle hle
            right
            exact Nat.lt_of_le_of_lt hsqle hsqLt
        | inr hsqEq =>
            have hinnerEq : innerSqrt x = m := by
              have hsqNat : natSqrt x * natSqrt x = x := by simpa [m] using hsqEq
              simpa [m] using innerSqrt_eq_natSqrt_of_square x hx256 hsqNat
            by_cases hm0 : m = 0
            · left
              simp [hinnerEq, hm0]
            · right
              have hmPos : 0 < m := Nat.pos_of_ne_zero hm0
              have hpredm : (m - 1) * (m - 1) < x := by
                have hsubLt : m - 1 < m := by
                  simpa [Nat.pred_eq_sub_one] using Nat.pred_lt (Nat.ne_of_gt hmPos)
                have hle : (m - 1) * (m - 1) ≤ (m - 1) * m :=
                  Nat.mul_le_mul_left (m - 1) (Nat.sub_le _ _)
                have hlt : (m - 1) * m < m * m := Nat.mul_lt_mul_of_pos_right hsubLt hmPos
                have hltm : (m - 1) * (m - 1) < m * m := Nat.lt_of_le_of_lt hle hlt
                simpa [hsqEq] using hltm
              simpa [hinnerEq] using hpredm
      exact minimal_of_pred_lt x (innerSqrt x) hpred

end SqrtGeneratedModel
