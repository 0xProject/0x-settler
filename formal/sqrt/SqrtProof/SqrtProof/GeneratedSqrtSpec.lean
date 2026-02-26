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

end SqrtGeneratedModel
