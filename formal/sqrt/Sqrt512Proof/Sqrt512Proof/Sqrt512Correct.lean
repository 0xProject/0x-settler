/-
  End-to-end correctness of 512-bit square root.

  Composes normalization, Karatsuba step, correction, and un-normalization:

    sqrt512(x) = natSqrt(x) for x < 2^512
-/
import SqrtProof.SqrtCorrect
import Sqrt512Proof.Normalization
import Sqrt512Proof.KaratsubaStep
import Sqrt512Proof.Correction

-- ============================================================================
-- Part 1: Karatsuba uncorrected and corrected
-- ============================================================================

/-- Uncorrected Karatsuba result (before correction step). -/
noncomputable def karatsubaR (x_hi x_lo : Nat) : Nat :=
  let H := 2 ^ 128
  let r_hi := natSqrt x_hi
  let res := x_hi - r_hi * r_hi
  let x_lo_hi := x_lo / H
  let n := res * H + x_lo_hi
  let d := 2 * r_hi
  let q := n / d
  r_hi * H + q

/-- The full Karatsuba floor sqrt with correction. -/
noncomputable def karatsubaFloor (x_hi x_lo : Nat) : Nat :=
  let H := 2 ^ 128
  let x_lo_hi := x_lo / H
  let x_lo_lo := x_lo % H
  let x := x_hi * (H * H) + x_lo_hi * H + x_lo_lo
  let r := karatsubaR x_hi x_lo
  if x < r * r then r - 1 else r

/-- karatsubaR satisfies the Karatsuba bracket for normalized inputs. -/
theorem karatsubaR_bracket (x_hi x_lo : Nat)
    (hxhi_lo : 2 ^ 254 ≤ x_hi) (hxhi_hi : x_hi < 2 ^ 256)
    (hxlo : x_lo < 2 ^ 256) :
    let H := 2 ^ 128
    let x_lo_hi := x_lo / H
    let x_lo_lo := x_lo % H
    let x := x_hi * (H * H) + x_lo_hi * H + x_lo_lo
    let r := karatsubaR x_hi x_lo
    natSqrt x ≤ r ∧ r ≤ natSqrt x + 1 := by
  simp only
  have h128sq : (2 : Nat) ^ 128 * 2 ^ 128 = 2 ^ 256 := by rw [← Nat.pow_add]
  exact karatsuba_bracket_512 x_hi (x_lo / 2 ^ 128) (x_lo % 2 ^ 128)
    hxhi_lo hxhi_hi
    (Nat.div_lt_of_lt_mul (by rwa [h128sq]))
    (Nat.mod_lt x_lo (Nat.two_pow_pos 128))

/-- karatsubaFloor = natSqrt for normalized inputs. -/
theorem karatsubaFloor_eq_natSqrt (x_hi x_lo : Nat)
    (hxhi_lo : 2 ^ 254 ≤ x_hi) (hxhi_hi : x_hi < 2 ^ 256)
    (hxlo : x_lo < 2 ^ 256) :
    karatsubaFloor x_hi x_lo = natSqrt (x_hi * 2 ^ 256 + x_lo) := by
  have hHsq : (2 : Nat) ^ 128 * ((2 : Nat) ^ 128) = (2 : Nat) ^ 256 := by rw [← Nat.pow_add]
  have hxlo_decomp : x_lo = x_lo / (2 : Nat) ^ 128 * (2 : Nat) ^ 128 + x_lo % (2 : Nat) ^ 128 := by
    have := (Nat.div_add_mod x_lo ((2 : Nat) ^ 128)).symm
    rw [Nat.mul_comm] at this; exact this

  have hx_eq : x_hi * 2 ^ 256 + x_lo =
      x_hi * ((2 : Nat) ^ 128 * (2 : Nat) ^ 128) +
      x_lo / (2 : Nat) ^ 128 * (2 : Nat) ^ 128 + x_lo % (2 : Nat) ^ 128 := by
    rw [← hHsq, hxlo_decomp]; omega

  have hbracket := karatsubaR_bracket x_hi x_lo hxhi_lo hxhi_hi hxlo

  rw [hx_eq]
  unfold karatsubaFloor
  simp only
  exact correction_correct
    (x_hi * ((2 : Nat) ^ 128 * (2 : Nat) ^ 128) +
      x_lo / (2 : Nat) ^ 128 * (2 : Nat) ^ 128 + x_lo % (2 : Nat) ^ 128)
    (karatsubaR x_hi x_lo) hbracket.1 hbracket.2

-- ============================================================================
-- Part 2: Normalization bounds
-- ============================================================================

private theorem four_pow_eq_two_pow' (shift : Nat) : 4 ^ shift = 2 ^ (2 * shift) := by
  have : (4 : Nat) = 2 ^ 2 := by decide
  rw [this, ← Nat.pow_mul]

/-- x * 4^shift < 2^512 when x and shift are properly constrained. -/
private theorem normalized_lt_512 (x x_hi : Nat)
    (hxhi_pos : 0 < x_hi) (hxhi_lt : x_hi < 2 ^ 256)
    (hx_lt : x < (x_hi + 1) * 2 ^ 256) :
    let shift := (255 - Nat.log2 x_hi) / 2
    x * 4 ^ shift < 2 ^ 512 := by
  intro shift
  have hne : x_hi ≠ 0 := Nat.ne_of_gt hxhi_pos
  have hlog := (Nat.log2_eq_iff hne).1 rfl
  have hL : Nat.log2 x_hi ≤ 255 := by have := (Nat.log2_lt hne).2 hxhi_lt; omega
  have h2shift : 2 * shift ≤ 255 - Nat.log2 x_hi := Nat.mul_div_le (255 - Nat.log2 x_hi) 2
  rw [four_pow_eq_two_pow']
  calc x * 2 ^ (2 * shift)
      < (x_hi + 1) * 2 ^ 256 * 2 ^ (2 * shift) :=
        Nat.mul_lt_mul_of_pos_right hx_lt (Nat.two_pow_pos _)
    _ ≤ 2 ^ (Nat.log2 x_hi + 1) * 2 ^ 256 * 2 ^ (2 * shift) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hlog.2)
    _ = 2 ^ (Nat.log2 x_hi + 1 + 256 + 2 * shift) := by
        rw [← Nat.pow_add, ← Nat.pow_add]
    _ ≤ 2 ^ 512 := Nat.pow_le_pow_right (by omega) (by omega)

/-- The normalized top word is >= 2^254. -/
private theorem normalized_hi_lower (x x_hi : Nat)
    (hxhi_pos : 0 < x_hi) (hxhi_lt : x_hi < 2 ^ 256)
    (hx_ge : x_hi * 2 ^ 256 ≤ x) :
    let shift := (255 - Nat.log2 x_hi) / 2
    2 ^ 254 ≤ x * 4 ^ shift / 2 ^ 256 := by
  intro shift
  have hsr := shift_range x_hi hxhi_pos hxhi_lt
  have h1 : x_hi * 2 ^ 256 * 4 ^ shift ≤ x * 4 ^ shift :=
    Nat.mul_le_mul_right _ hx_ge
  have h2 : x_hi * 4 ^ shift ≤ x * 4 ^ shift / 2 ^ 256 := by
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos 256)]
    calc x_hi * 4 ^ shift * 2 ^ 256
        = x_hi * 2 ^ 256 * 4 ^ shift := by
          rw [Nat.mul_assoc, Nat.mul_comm (4 ^ shift) (2 ^ 256), ← Nat.mul_assoc]
      _ ≤ x * 4 ^ shift := h1
  exact Nat.le_trans hsr.1 h2

-- ============================================================================
-- Part 3: The full 512-bit sqrt
-- ============================================================================

/-- 512-bit floor square root (Nat model). -/
noncomputable def sqrt512 (x : Nat) : Nat :=
  if x < 2 ^ 256 then
    natSqrt x
  else
    let x_hi := x / 2 ^ 256
    let x_lo := x % 2 ^ 256
    let shift := (255 - Nat.log2 x_hi) / 2
    let x' := x * 4 ^ shift
    karatsubaFloor (x' / 2 ^ 256) (x' % 2 ^ 256) / 2 ^ shift

/-- sqrt512 is correct for x < 2^512. -/
theorem sqrt512_correct (x : Nat) (hx : x < 2 ^ 512) :
    sqrt512 x = natSqrt x := by
  unfold sqrt512
  by_cases hlt : x < 2 ^ 256
  · simp [hlt]
  · simp [hlt]
    have hge : 2 ^ 256 ≤ x := by omega
    have hxhi_pos : 0 < x / 2 ^ 256 :=
      Nat.div_pos hge (Nat.two_pow_pos 256)
    have hxhi_lt : x / 2 ^ 256 < 2 ^ 256 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 256)]
      calc x < 2 ^ 512 := hx
        _ = 2 ^ 256 * 2 ^ 256 := by rw [← Nat.pow_add]
    have hxlo_bound : x % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt x (Nat.two_pow_pos 256)
    have hx_decomp : x = x / 2 ^ 256 * 2 ^ 256 + x % 2 ^ 256 := by
      have := (Nat.div_add_mod x (2 ^ 256)).symm
      rw [Nat.mul_comm] at this; exact this

    have hx_lt : x < (x / 2 ^ 256 + 1) * 2 ^ 256 := by omega
    have hx'_lt := normalized_lt_512 x (x / 2 ^ 256) hxhi_pos hxhi_lt hx_lt
    have hx_ge : x / 2 ^ 256 * 2 ^ 256 ≤ x := by omega
    have hxhi'_lo := normalized_hi_lower x (x / 2 ^ 256) hxhi_pos hxhi_lt hx_ge
    have h256sq : (2 : Nat) ^ 256 * 2 ^ 256 = 2 ^ 512 := by rw [← Nat.pow_add]
    have hxhi'_lt : x * 4 ^ ((255 - Nat.log2 (x / 2 ^ 256)) / 2) / 2 ^ 256 < 2 ^ 256 :=
      Nat.div_lt_of_lt_mul (by rwa [h256sq])
    have hxlo'_bound : x * 4 ^ ((255 - Nat.log2 (x / 2 ^ 256)) / 2) % 2 ^ 256 < 2 ^ 256 :=
      Nat.mod_lt _ (Nat.two_pow_pos 256)

    have hkf := karatsubaFloor_eq_natSqrt
      (x * 4 ^ ((255 - Nat.log2 (x / 2 ^ 256)) / 2) / 2 ^ 256)
      (x * 4 ^ ((255 - Nat.log2 (x / 2 ^ 256)) / 2) % 2 ^ 256)
      hxhi'_lo hxhi'_lt hxlo'_bound
    -- hkf : karatsubaFloor (x'/2^256) (x'%2^256) = natSqrt (x'/2^256 * 2^256 + x'%2^256)
    -- We need: karatsubaFloor (x'/2^256) (x'%2^256) / 2^shift = natSqrt x
    -- Since x'/2^256 * 2^256 + x'%2^256 = x' (Euclidean decomposition)
    -- hkf gives karatsubaFloor ... = natSqrt x'
    -- Then natSqrt x' / 2^shift = natSqrt x (by natSqrt_shift_div)
    have hx'_eq : x * 4 ^ ((255 - Nat.log2 (x / 2 ^ 256)) / 2) / 2 ^ 256 * 2 ^ 256 +
        x * 4 ^ ((255 - Nat.log2 (x / 2 ^ 256)) / 2) % 2 ^ 256 =
        x * 4 ^ ((255 - Nat.log2 (x / 2 ^ 256)) / 2) := by
      have := Nat.div_add_mod (x * 4 ^ ((255 - Nat.log2 (x / 2 ^ 256)) / 2)) (2 ^ 256)
      rw [Nat.mul_comm] at this; omega
    rw [hkf, hx'_eq]
    exact natSqrt_shift_div x ((255 - Nat.log2 (x / 2 ^ 256)) / 2)

/-- sqrt512 satisfies the integer square root spec. -/
theorem sqrt512_spec (x : Nat) (hx : x < 2 ^ 512) :
    let r := sqrt512 x
    r * r ≤ x ∧ x < (r + 1) * (r + 1) := by
  simp only; rw [sqrt512_correct x hx]
  exact ⟨natSqrt_sq_le x, natSqrt_lt_succ_sq x⟩
