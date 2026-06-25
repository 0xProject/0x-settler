import Mathlib.Tactic
import LnProof.OctaveMono

/-!
# Monotonicity certificates for the `lnWadToRay` Yul body

`Ln.lnWad` maps a wad-basis input to a ray-basis `int256` encoded as a
two's-complement word, so ordering statements use the sign-bit-biased
unsigned comparison `sle`.

Monotonicity of `lnWad` over its whole domain `0 < x < 2^255` decomposes as:

* adjacent inputs that share the Q103 mantissa and exponent return the same
  word;
* within an octave, the mantissa-to-result map is nondecreasing -- proven in
  `LnProof.StepMono`/`LnProof.ZOctave`/`LnProof.OctaveMono` from the
  polynomial certificates in `LnProof.Certs`;
* across the 254 clz seams, the adjacent pair `(2^t - 1, 2^t)` is decided
  here by kernel evaluation of the body decomposition;
* the single corrected point `x = 10^18` (whose exact result, 0, is the only
  integer value of the function) is decided here together with its
  neighbors.

The theorems in this file are the finitely-decidable legs of that argument.
`LnProof.TopMono` composes all of the legs into `lnWadToRayBody_mono`,
monotonicity over the whole domain.
-/

set_option maxRecDepth 20000

namespace LnYul

/-- Signed (two's complement) `≤` on uint256 words: unsigned comparison with
the sign bit flipped. -/
def sle (a b : Nat) : Bool :=
  decide ((a + 2 ^ 255) % WORD_MOD ≤ (b + 2 ^ 255) % WORD_MOD)

/-- One comparison per clz seam: `f(2^t) ≥ f(2^t - 1)` for `t ∈ [1, 254]`. -/
def seamMono (f : Nat → Nat) : Bool :=
  (List.range 254).all fun t => sle (f (2 ^ (t + 1) - 1)) (f (2 ^ (t + 1)))

def lnWadFromRayWord (r : Nat) : Nat :=
  evmSdiv (evmSub r (evmMul 999999999 (evmSgt 0 r))) 1000000000

def seamMantissaPred (t : Nat) : Nat :=
  ((2 ^ t - 1) * 2 ^ (256 - t)) / 2 ^ 160

theorem log2_pow_sub_one {t : Nat} (ht : 1 ≤ t) : Nat.log2 (2 ^ t - 1) = t - 1 := by
  cases t with
  | zero => omega
  | succ s =>
    have hx0 : 2 ^ (s + 1) - 1 ≠ 0 := by
      have hpow : 2 ^ (s + 1) = 2 ^ s * 2 := by rw [Nat.pow_succ]
      have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
      omega
    have hlo : s ≤ Nat.log2 (2 ^ (s + 1) - 1) := by
      refine (Nat.le_log2 hx0).mpr ?_
      have hpow : 2 ^ (s + 1) = 2 ^ s * 2 := by rw [Nat.pow_succ]
      have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
      omega
    have hhi : Nat.log2 (2 ^ (s + 1) - 1) < s + 1 := by
      refine (Nat.log2_lt hx0).mpr ?_
      have hpow : 0 < 2 ^ (s + 1) := Nat.two_pow_pos (s + 1)
      omega
    omega

theorem bodyClz_eq {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 256) :
    evmClz x = 255 - Nat.log2 x := by
  unfold evmClz
  rw [u256_of_lt h2, if_neg (by omega)]

theorem bodyClz_pow {t : Nat} (ht : t ≤ 255) : evmClz (2 ^ t) = 255 - t := by
  rw [bodyClz_eq (by exact Nat.two_pow_pos t)
    (by exact Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega : t < 256)),
    Nat.log2_two_pow]

theorem bodyClz_pow_pred {t : Nat} (ht1 : 1 ≤ t) (ht2 : t ≤ 255) :
    evmClz (2 ^ t - 1) = 256 - t := by
  rw [bodyClz_eq (by
      have hpow : 2 ^ t ≥ 2 := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) ht1
      omega)
    (by
      have hlt : 2 ^ t ≤ 2 ^ 255 := Nat.pow_le_pow_right (by omega) ht2
      omega), log2_pow_sub_one ht1]
  omega

theorem bodyMantissa_pow {t : Nat} (ht : t ≤ 255) :
    evmShr 160 (evmShl (evmClz (2 ^ t)) (2 ^ t)) = MLO := by
  rw [bodyClz_pow ht]
  have hprod : 2 ^ t * 2 ^ (255 - t) = 2 ^ 255 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [evmShl_eq (by omega : 255 - t < 256) (by rw [hprod]; omega),
    evmShr_eq_div_160 (by rw [hprod]; omega)]
  rw [hprod]
  simp only [MLO]
  decide

theorem bodyMantissa_pow_pred {t : Nat} (ht1 : 1 ≤ t) (ht2 : t ≤ 255) :
    evmShr 160 (evmShl (evmClz (2 ^ t - 1)) (2 ^ t - 1)) = seamMantissaPred t := by
  rw [bodyClz_pow_pred ht1 ht2]
  have hfit : (2 ^ t - 1) * 2 ^ (256 - t) < 2 ^ 256 := by
    have hlt : 2 ^ t - 1 < 2 ^ t := by
      have hp : 0 < 2 ^ t := Nat.two_pow_pos t
      omega
    have hmul := (Nat.mul_lt_mul_right (Nat.two_pow_pos (256 - t))).mpr hlt
    have hpow : 2 ^ t * 2 ^ (256 - t) = 2 ^ 256 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hpow] at hmul
    exact hmul
  rw [evmShl_eq (by omega : 256 - t < 256) hfit, evmShr_eq_div_160 hfit]
  rfl

theorem bodyClz_wad_minus :
    evmClz 999999999999999999 = 196 := by
  rw [bodyClz_eq (by norm_num) (by norm_num)]
  have hlog : Nat.log2 999999999999999999 = 59 := by
    have hx0 : 999999999999999999 ≠ 0 := by omega
    have hlo : 59 ≤ Nat.log2 999999999999999999 :=
      (Nat.le_log2 hx0).mpr (by norm_num)
    have hhi : Nat.log2 999999999999999999 < 60 :=
      (Nat.log2_lt hx0).mpr (by norm_num)
    omega
  rw [hlog]

theorem bodyClz_wad :
    evmClz 1000000000000000000 = 196 := by
  rw [bodyClz_eq (by norm_num) (by norm_num)]
  have hlog : Nat.log2 1000000000000000000 = 59 := by
    have hx0 : 1000000000000000000 ≠ 0 := by omega
    have hlo : 59 ≤ Nat.log2 1000000000000000000 :=
      (Nat.le_log2 hx0).mpr (by norm_num)
    have hhi : Nat.log2 1000000000000000000 < 60 :=
      (Nat.log2_lt hx0).mpr (by norm_num)
    omega
  rw [hlog]

theorem bodyClz_wad_plus :
    evmClz 1000000000000000001 = 196 := by
  rw [bodyClz_eq (by norm_num) (by norm_num)]
  have hlog : Nat.log2 1000000000000000001 = 59 := by
    have hx0 : 1000000000000000001 ≠ 0 := by omega
    have hlo : 59 ≤ Nat.log2 1000000000000000001 :=
      (Nat.le_log2 hx0).mpr (by norm_num)
    have hhi : Nat.log2 1000000000000000001 < 60 :=
      (Nat.log2_lt hx0).mpr (by norm_num)
    omega
  rw [hlog]

theorem bodyMantissa_wad_minus :
    evmShr 160 (evmShl (evmClz 999999999999999999) 999999999999999999) =
      68719476735999999931280523264 := by
  rw [bodyClz_wad_minus, evmShl_eq (by omega : 196 < 256) (by norm_num),
    evmShr_eq_div_160 (by norm_num)]
  norm_num

theorem bodyMantissa_wad :
    evmShr 160 (evmShl (evmClz 1000000000000000000) 1000000000000000000) =
      68719476736000000000000000000 := by
  rw [bodyClz_wad, evmShl_eq (by omega : 196 < 256) (by norm_num),
    evmShr_eq_div_160 (by norm_num)]
  norm_num

theorem bodyMantissa_wad_plus :
    evmShr 160 (evmShl (evmClz 1000000000000000001) 1000000000000000001) =
      68719476736000000068719476736 := by
  rw [bodyClz_wad_plus, evmShl_eq (by omega : 196 < 256) (by norm_num),
    evmShr_eq_div_160 (by norm_num)]
  norm_num

theorem lnTail_one_wad : lnTail (evmSub 160 196) 68719476736000000000000000000 = 0 := by
  decide

/-- `lnWad(10**18) = 0` exactly (the branchless `eq` correction in the
implementation lands the lone integer-valued point of the function). -/
theorem lnWadToRayBody_one_wad : lnWadToRayBody (10 ^ 18) = 0 := by
  rw [show (10 : Nat) ^ 18 = 1000000000000000000 by decide]
  rw [lnWadToRayBody_eq_tail (by norm_num), bodyMantissa_wad, bodyClz_wad]
  exact lnTail_one_wad

/-- `lnWadToWad(10**18) = 0` exactly. -/
theorem lnWadBody_one_wad : lnWadBody (10 ^ 18) = 0 := by
  unfold lnWadBody
  rw [lnWadToRayBody_one_wad]
  decide

/-- The `x = 10**18` correction preserves order against both neighbors. -/
theorem lnTail_one_wad_mono_left :
    sle (lnTail (evmSub 160 196) 68719476735999999931280523264)
      (lnTail (evmSub 160 196) 68719476736000000000000000000) = true := by
  decide

theorem lnTail_one_wad_mono_right :
    sle (lnTail (evmSub 160 196) 68719476736000000000000000000)
      (lnTail (evmSub 160 196) 68719476736000000068719476736) = true := by
  decide

theorem lnWadToRayBody_one_wad_mono :
    (sle (lnWadToRayBody (10 ^ 18 - 1)) (lnWadToRayBody (10 ^ 18))
      && sle (lnWadToRayBody (10 ^ 18)) (lnWadToRayBody (10 ^ 18 + 1))) = true := by
  rw [Bool.and_eq_true]
  constructor
  · rw [show (10 : Nat) ^ 18 - 1 = 999999999999999999 by decide,
      show (10 : Nat) ^ 18 = 1000000000000000000 by decide]
    rw [lnWadToRayBody_eq_tail (by norm_num : 999999999999999999 < 2 ^ 256),
      lnWadToRayBody_eq_tail (by norm_num : 1000000000000000000 < 2 ^ 256),
      bodyMantissa_wad_minus, bodyMantissa_wad, bodyClz_wad_minus, bodyClz_wad]
    exact lnTail_one_wad_mono_left
  · rw [show (10 : Nat) ^ 18 = 1000000000000000000 by decide]
    change sle (lnWadToRayBody 1000000000000000000)
      (lnWadToRayBody 1000000000000000001) = true
    rw [lnWadToRayBody_eq_tail (by norm_num : 1000000000000000000 < 2 ^ 256),
      lnWadToRayBody_eq_tail (by norm_num : 1000000000000000001 < 2 ^ 256),
      bodyMantissa_wad, bodyMantissa_wad_plus, bodyClz_wad, bodyClz_wad_plus]
    exact lnTail_one_wad_mono_right

theorem lnTail_seam_at {t : Nat} (ht1 : 1 ≤ t) (ht2 : t ≤ 254) :
    sle (lnTail (evmSub 160 (256 - t)) (seamMantissaPred t))
      (lnTail (evmSub 160 (255 - t)) MLO) = true := by
  interval_cases t <;> decide

theorem lnWadTail_seam_at {t : Nat} (ht1 : 1 ≤ t) (ht2 : t ≤ 254) :
    sle (lnWadFromRayWord (lnTail (evmSub 160 (256 - t)) (seamMantissaPred t)))
      (lnWadFromRayWord (lnTail (evmSub 160 (255 - t)) MLO)) = true := by
  interval_cases t <;> decide

theorem lnWadToRayBody_seam_at {t : Nat} (ht1 : 1 ≤ t) (ht2 : t ≤ 254) :
    sle (lnWadToRayBody (2 ^ t - 1)) (lnWadToRayBody (2 ^ t)) = true := by
  rw [lnWadToRayBody_eq_tail (by
      have hpow : 2 ^ t ≤ 2 ^ 254 := Nat.pow_le_pow_right (by omega) ht2
      omega : 2 ^ t - 1 < 2 ^ 256),
    lnWadToRayBody_eq_tail (by
      have hpow : 2 ^ t ≤ 2 ^ 254 := Nat.pow_le_pow_right (by omega) ht2
      omega : 2 ^ t < 2 ^ 256),
    bodyMantissa_pow_pred ht1 (by omega : t ≤ 255), bodyMantissa_pow (by omega : t ≤ 255),
    bodyClz_pow_pred ht1 (by omega : t ≤ 255), bodyClz_pow (by omega : t ≤ 255)]
  exact lnTail_seam_at ht1 ht2

theorem lnWadBody_seam_at {t : Nat} (ht1 : 1 ≤ t) (ht2 : t ≤ 254) :
    sle (lnWadBody (2 ^ t - 1)) (lnWadBody (2 ^ t)) = true := by
  unfold lnWadBody
  rw [lnWadToRayBody_eq_tail (by
      have hpow : 2 ^ t ≤ 2 ^ 254 := Nat.pow_le_pow_right (by omega) ht2
      omega : 2 ^ t - 1 < 2 ^ 256),
    lnWadToRayBody_eq_tail (by
      have hpow : 2 ^ t ≤ 2 ^ 254 := Nat.pow_le_pow_right (by omega) ht2
      omega : 2 ^ t < 2 ^ 256),
    bodyMantissa_pow_pred ht1 (by omega : t ≤ 255), bodyMantissa_pow (by omega : t ≤ 255),
    bodyClz_pow_pred ht1 (by omega : t ≤ 255), bodyClz_pow (by omega : t ≤ 255)]
  exact lnWadTail_seam_at ht1 ht2

/-- `lnWad` is monotone across every clz seam. -/
theorem lnWadToRayBody_seam_mono : seamMono lnWadToRayBody = true := by
  rw [seamMono, List.all_eq_true]
  intro t ht
  exact lnWadToRayBody_seam_at (t := t + 1) (by omega)
    (by exact Nat.succ_le_of_lt (List.mem_range.mp ht))

/-- `lnWadToWad` is monotone across every clz seam. -/
theorem lnWadBody_seam_mono : seamMono lnWadBody = true := by
  rw [seamMono, List.all_eq_true]
  intro t ht
  exact lnWadBody_seam_at (t := t + 1) (by omega)
    (by exact Nat.succ_le_of_lt (List.mem_range.mp ht))

end LnYul
