import LnProof.Floor.CarryIndependent.Phase
import LnProof.Floor.Model
import LnProof.Seam.RealLog

open FormalYul
open FormalYul.Preservation

namespace LnFloorCarry

open LnYul LnFloor LnFloorCert

set_option maxRecDepth 8192

noncomputable section

private theorem real_int_natCast (n : Nat) : (((n : Int) : Real)) = (n : Real) := by
  norm_cast

private theorem exp_natCast_mul_log_two (n : Nat) :
    Real.exp ((n : Real) * Real.log 2) = (2 : Real) ^ n := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : Real) < 2)]

private theorem exp_neg_natCast_mul_log_two (n : Nat) :
    Real.exp (-(n : Real) * Real.log 2) = ((2 : Real) ^ n)⁻¹ := by
  rw [neg_mul, Real.exp_neg, exp_natCast_mul_log_two]

def signedOctave (c : Nat) : Int := 160 - (c : Int)

def coreErrorRay (m : Nat) (X : Int) : Real :=
  10 ^ 27 * ((X : Real) / 2 ^ 99 - Real.log ((m : Real) / Sc))

def accumulatorI (X : Int) (c : Nat) : Int :=
  X * 7450580596923828125 + ln2kInt c + (BIASc : Int)

theorem scaledAccumulator_eq (X : Int) (c : Nat) :
    (accumulatorI X c : Real) / (2 ^ 72 * 10 ^ 27) =
      (X : Real) / 2 ^ 99 + (signedOctave c : Real) * ln2Word + biasNatural := by
  by_cases hc : c ≤ 160
  · have hcast : ((160 - c : Nat) : Real) = 160 - (c : Real) := by
      rw [Nat.cast_sub hc]
      norm_num
    simp only [accumulatorI, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
      Int.cast_natCast]
    rw [show ln2kInt c = (LN2c : Int) * ((160 - c : Nat) : Int) by
      unfold ln2kInt; rw [if_pos hc]]
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [hcast]
    norm_num [signedOctave, ln2Word, biasNatural, LN2c, BIASc, QS]
    ring
  · have hct : 160 ≤ c := by omega
    have hcast : ((c - 160 : Nat) : Real) = (c : Real) - 160 := by
      rw [Nat.cast_sub hct]
      norm_num
    simp only [accumulatorI, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
      Int.cast_natCast]
    rw [show ln2kInt c = -((LN2c : Int) * ((c - 160 : Nat) : Int)) by
      unfold ln2kInt; rw [if_neg hc]]
    simp only [Int.cast_neg, Int.cast_mul, Int.cast_natCast]
    rw [hcast]
    norm_num [signedOctave, ln2Word, biasNatural, LN2c, BIASc, QS]
    ring

theorem scaledAccumulator_error_decomposition (m : Nat) (X : Int) (c : Nat) :
    (accumulatorI X c : Real) / (2 ^ 72 * 10 ^ 27) =
      Real.log ((m : Real) / Sc) +
        (signedOctave c : Real) * Real.log 2 + biasNatural +
        (coreErrorRay m X + phaseErrorRay (signedOctave c)) / 10 ^ 27 := by
  rw [scaledAccumulator_eq]
  unfold coreErrorRay phaseErrorRay phaseDeltaRay
  ring

theorem accumulator_exp_lt_wadRatio_of_nonnegative_octave
    {m c x : Nat} {X : Int} (hm : 0 < m) (hc1 : 1 ≤ c) (hc : c ≤ 160)
    (hmx : m * 2 ^ (160 - c) ≤ x)
    (hcore : coreErrorRay m X < (coreErrorNum : Real) / coreErrorDen) :
    Real.exp ((accumulatorI X c : Real) / (2 ^ 72 * 10 ^ 27)) <
      (x : Real) / 10 ^ 18 := by
  let k : Int := signedOctave c
  let n : Nat := 160 - c
  have hk : k = (n : Int) := by unfold k n signedOctave; omega
  have hklo : -95 ≤ k := by rw [hk]; omega
  have hkhi : k ≤ 159 := by rw [hk]; omega
  have hextra := bias_add_core_phase_exp_lt hcore hklo hkhi
  have hmR : 0 < (m : Real) := by exact_mod_cast hm
  have hmratio : 0 < (m : Real) / (Sc : Real) :=
    div_pos hmR (by norm_num [Sc])
  have hpow : Real.exp ((k : Real) * Real.log 2) = (2 : Real) ^ n := by
    have hkR : (k : Real) = (n : Real) :=
      (congrArg (fun z : Int => (z : Real)) hk).trans (real_int_natCast n)
    exact (congrArg (fun z : Real => Real.exp (z * Real.log 2)) hkR).trans
      (exp_natCast_mul_log_two n)
  have hdecomp := scaledAccumulator_error_decomposition m X c
  have hdecomp' :
      (accumulatorI X c : Real) / (2 ^ 72 * 10 ^ 27) =
        Real.log ((m : Real) / Sc) + (k : Real) * Real.log 2 +
          (biasNatural + (coreErrorRay m X + phaseErrorRay k) / 10 ^ 27) := by
    calc
      (accumulatorI X c : Real) / (2 ^ 72 * 10 ^ 27) =
          Real.log ((m : Real) / Sc) +
            (signedOctave c : Real) * Real.log 2 + biasNatural +
            (coreErrorRay m X + phaseErrorRay (signedOctave c)) / 10 ^ 27 := hdecomp
      _ = Real.log ((m : Real) / Sc) + (k : Real) * Real.log 2 +
          (biasNatural + (coreErrorRay m X + phaseErrorRay k) / 10 ^ 27) := by
        dsimp [k]
        ring
  have hfactor :
      Real.exp ((accumulatorI X c : Real) / (2 ^ 72 * 10 ^ 27)) =
        ((m : Real) / Sc) * (2 : Real) ^ n *
          Real.exp (biasNatural +
            (coreErrorRay m X + phaseErrorRay k) / 10 ^ 27) := by
    calc
      Real.exp ((accumulatorI X c : Real) / (2 ^ 72 * 10 ^ 27)) =
          Real.exp (Real.log ((m : Real) / Sc) + (k : Real) * Real.log 2 +
            (biasNatural + (coreErrorRay m X + phaseErrorRay k) / 10 ^ 27)) :=
        congrArg Real.exp hdecomp'
      _ = Real.exp (Real.log ((m : Real) / Sc)) *
          Real.exp ((k : Real) * Real.log 2) *
          Real.exp (biasNatural +
            (coreErrorRay m X + phaseErrorRay k) / 10 ^ 27) := by
        rw [Real.exp_add, Real.exp_add]
      _ = ((m : Real) / Sc) * (2 : Real) ^ n *
          Real.exp (biasNatural +
            (coreErrorRay m X + phaseErrorRay k) / 10 ^ 27) := by
        rw [Real.exp_log hmratio, hpow]
  rw [hfactor]
  have hleftPos : 0 < ((m : Real) / Sc) * (2 : Real) ^ n :=
    mul_pos hmratio (pow_pos (by norm_num) n)
  have hstrict :
      ((m : Real) / Sc) * (2 : Real) ^ n *
          Real.exp (biasNatural +
            (coreErrorRay m X + phaseErrorRay k) / 10 ^ 27) <
        ((m : Real) / Sc) * (2 : Real) ^ n * ((Sc : Real) / 10 ^ 18) :=
    mul_lt_mul_of_pos_left hextra hleftPos
  have hcancel :
      ((m : Real) / Sc) * (2 : Real) ^ n * ((Sc : Real) / 10 ^ 18) =
        ((m : Real) * (2 : Real) ^ n) / 10 ^ 18 := by
    norm_num [Sc]
    ring
  rw [hcancel] at hstrict
  have hmxCast := (Nat.cast_le (α := Real)).mpr hmx
  have hmxR : (m : Real) * (2 : Real) ^ n ≤ (x : Real) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, n] using hmxCast
  exact hstrict.trans_le ((div_le_div_iff_of_pos_right (by positivity)).2 hmxR)

theorem accumulator_exp_lt_wadRatio_of_negative_octave
    {m c x : Nat} {X : Int} (hm : 0 < m) (hc : 160 < c) (hc255 : c ≤ 255)
    (hmx : m = x * 2 ^ (c - 160))
    (hcore : coreErrorRay m X < (coreErrorNum : Real) / coreErrorDen) :
    Real.exp ((accumulatorI X c : Real) / (2 ^ 72 * 10 ^ 27)) <
      (x : Real) / 10 ^ 18 := by
  let k : Int := signedOctave c
  let n : Nat := c - 160
  have hk : k = -(n : Int) := by unfold k n signedOctave; omega
  have hklo : -95 ≤ k := by rw [hk]; omega
  have hkhi : k ≤ 159 := by rw [hk]; omega
  have hextra := bias_add_core_phase_exp_lt hcore hklo hkhi
  have hmR : 0 < (m : Real) := by exact_mod_cast hm
  have hmratio : 0 < (m : Real) / (Sc : Real) :=
    div_pos hmR (by norm_num [Sc])
  have hpow : Real.exp ((k : Real) * Real.log 2) = ((2 : Real) ^ n)⁻¹ := by
    have hkR : (k : Real) = -(n : Real) := by
      calc
        (k : Real) = ((-(n : Int) : Int) : Real) :=
          congrArg (fun z : Int => (z : Real)) hk
        _ = -(((n : Int) : Real)) := by rw [Int.cast_neg]
        _ = -(n : Real) := congrArg Neg.neg (real_int_natCast n)
    exact (congrArg (fun z : Real => Real.exp (z * Real.log 2)) hkR).trans
      (exp_neg_natCast_mul_log_two n)
  have hdecomp := scaledAccumulator_error_decomposition m X c
  have hdecomp' :
      (accumulatorI X c : Real) / (2 ^ 72 * 10 ^ 27) =
        Real.log ((m : Real) / Sc) + (k : Real) * Real.log 2 +
          (biasNatural + (coreErrorRay m X + phaseErrorRay k) / 10 ^ 27) := by
    calc
      (accumulatorI X c : Real) / (2 ^ 72 * 10 ^ 27) =
          Real.log ((m : Real) / Sc) +
            (signedOctave c : Real) * Real.log 2 + biasNatural +
            (coreErrorRay m X + phaseErrorRay (signedOctave c)) / 10 ^ 27 := hdecomp
      _ = Real.log ((m : Real) / Sc) + (k : Real) * Real.log 2 +
          (biasNatural + (coreErrorRay m X + phaseErrorRay k) / 10 ^ 27) := by
        dsimp [k]
        ring
  have hfactor :
      Real.exp ((accumulatorI X c : Real) / (2 ^ 72 * 10 ^ 27)) =
        ((m : Real) / Sc) * ((2 : Real) ^ n)⁻¹ *
          Real.exp (biasNatural +
            (coreErrorRay m X + phaseErrorRay k) / 10 ^ 27) := by
    calc
      Real.exp ((accumulatorI X c : Real) / (2 ^ 72 * 10 ^ 27)) =
          Real.exp (Real.log ((m : Real) / Sc) + (k : Real) * Real.log 2 +
            (biasNatural + (coreErrorRay m X + phaseErrorRay k) / 10 ^ 27)) :=
        congrArg Real.exp hdecomp'
      _ = Real.exp (Real.log ((m : Real) / Sc)) *
          Real.exp ((k : Real) * Real.log 2) *
          Real.exp (biasNatural +
            (coreErrorRay m X + phaseErrorRay k) / 10 ^ 27) := by
        rw [Real.exp_add, Real.exp_add]
      _ = ((m : Real) / Sc) * ((2 : Real) ^ n)⁻¹ *
          Real.exp (biasNatural +
            (coreErrorRay m X + phaseErrorRay k) / 10 ^ 27) := by
        rw [Real.exp_log hmratio, hpow]
  rw [hfactor]
  have hleftPos : 0 < ((m : Real) / Sc) * ((2 : Real) ^ n)⁻¹ :=
    mul_pos hmratio (inv_pos.mpr (pow_pos (by norm_num) n))
  have hstrict :
      ((m : Real) / Sc) * ((2 : Real) ^ n)⁻¹ *
          Real.exp (biasNatural +
            (coreErrorRay m X + phaseErrorRay k) / 10 ^ 27) <
        ((m : Real) / Sc) * ((2 : Real) ^ n)⁻¹ * ((Sc : Real) / 10 ^ 18) :=
    mul_lt_mul_of_pos_left hextra hleftPos
  have hmxCast := congrArg (fun y : Nat => (y : Real)) hmx
  have hmxR : (m : Real) = (x : Real) * (2 : Real) ^ n := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, n] using hmxCast
  have hcancel :
      ((m : Real) / Sc) * ((2 : Real) ^ n)⁻¹ * ((Sc : Real) / 10 ^ 18) =
        (x : Real) / 10 ^ 18 := by
    rw [hmxR]
    have hpowne : (2 : Real) ^ n ≠ 0 := by positivity
    field_simp [Sc, hpowne]
    ring
  rw [hcancel] at hstrict
  exact hstrict

theorem cut_of_accumulator_bracket {r A : Int} {x : Nat} (hx : 0 < x)
    (hbr : r * 2 ^ 72 ≤ A)
    (hacc : Real.exp ((A : Real) / (2 ^ 72 * 10 ^ 27)) <
      (x : Real) / 10 ^ 18) :
    CutLeLogWadRay r x := by
  have hbrR : (r : Real) * 2 ^ 72 ≤ (A : Real) := by exact_mod_cast hbr
  have hscale : (r : Real) / 10 ^ 27 ≤
      (A : Real) / (2 ^ 72 * 10 ^ 27) := by
    have hdiv := (div_le_div_iff_of_pos_right
      (show (0 : Real) < 2 ^ 72 * 10 ^ 27 by positivity)).2 hbrR
    have hcancel : (r : Real) / 10 ^ 27 =
        ((r : Real) * 2 ^ 72) / (2 ^ 72 * 10 ^ 27) := by ring
    rw [hcancel]
    exact hdiv
  have hratio : 0 < (x : Real) / 10 ^ 18 := by
    exact div_pos (by exact_mod_cast hx) (by positivity)
  have haccLog : (A : Real) / (2 ^ 72 * 10 ^ 27) <
      Real.log ((x : Real) / 10 ^ 18) :=
    (Real.lt_log_iff_exp_lt hratio).2 hacc
  have hlog := hscale.trans_lt haccLog
  apply LnRealBridge.cutLeLogWadRay_of_lt hx
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hlog

theorem normalized_cut_of_core_bound
    {m c x : Nat} {X r : Int} (hx : 0 < x) (hm : 0 < m)
    (hc1 : 1 ≤ c) (hc255 : c ≤ 255)
    (hwindow : (c ≤ 160 ∧ m * 2 ^ (160 - c) ≤ x) ∨
      (160 < c ∧ m = x * 2 ^ (c - 160)))
    (hbr : r * 2 ^ 72 ≤ accumulatorI X c)
    (hcore : coreErrorRay m X < (coreErrorNum : Real) / coreErrorDen) :
    CutLeLogWadRay r x := by
  have hacc : Real.exp ((accumulatorI X c : Real) / (2 ^ 72 * 10 ^ 27)) <
      (x : Real) / 10 ^ 18 := by
    rcases hwindow with ⟨hc, hmx⟩ | ⟨hc, hmx⟩
    · exact accumulator_exp_lt_wadRatio_of_nonnegative_octave hm hc1 hc hmx hcore
    · exact accumulator_exp_lt_wadRatio_of_negative_octave hm hc hc255 hmx hcore
  exact cut_of_accumulator_bracket hx hbr hacc

end

end LnFloorCarry
