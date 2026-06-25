import LnProof.StepMono

/-!
# The mantissa-to-`z` map and the within-octave chain

`zWord m` is antitone in the mantissa (consecutive cross-products reduce to
the `P + Q = 2S` identity after sharing the single bilinear atom `P*Q`),
stays within `[-Zc, Zc]`, and `hAt` is antitone over any interval of
`z`-values by chaining `hI_step`.
-/

set_option maxRecDepth 4096

namespace LnYul

open LnPoly

def MLO : Nat := 2 ^ 95
def MHI : Nat := 2 ^ 96

theorem zWord_transport {m : Nat} (h1 : MLO ≤ m) (h2 : m < MHI) :
    toInt (evmShl 100 (evmSub Sc m)) =
        ((Sc : Int) - (m : Int)) * 1267650600228229401496703205376 ∧
      toInt (evmAdd m Sc) = (m : Int) + (Sc : Int) := by
  simp only [MLO, MHI] at h1 h2
  have hSc : toInt Sc = (Sc : Int) := toInt_of_lt (by simp only [Sc]; omega)
  have hm : toInt m = (m : Int) := toInt_of_lt (by simp only [Sc] at *; omega)
  have e1 : toInt (evmSub Sc m) = (Sc : Int) - (m : Int) := by
    rw [← hSc, ← hm]
    refine evmSub_transport (by simp only [Sc]; omega) (by omega) ?_ ?_ <;>
      rw [hSc, hm] <;> simp only [Sc, ipow255] <;> omega
  have e2 : toInt (evmShl 100 (evmSub Sc m)) =
      ((Sc : Int) - (m : Int)) * 1267650600228229401496703205376 := by
    rw [← e1]
    refine evmShl_transport_100 (evmSub_lt _ _) ?_ ?_ <;> rw [e1] <;>
      simp only [Sc, ipow255] <;> omega
  have e3 : toInt (evmAdd m Sc) = (m : Int) + (Sc : Int) := by
    rw [← hSc, ← hm]
    refine evmAdd_transport (by omega) (by simp only [Sc]; omega) ?_ ?_ <;>
      rw [hSc, hm] <;> simp only [Sc, ipow255] <;> omega
  exact ⟨e2, e3⟩

/-- Value, range and unit-step antitonicity of `zWord`, proven together so the
sign analysis is shared. -/
theorem zWord_range {m : Nat} (h1 : MLO ≤ m) (h2 : m < MHI) :
    -(217494458298375249691265569570 : Int) ≤ toInt (zWord m) ∧
      toInt (zWord m) ≤ (217494458298375249691265569570 : Int) := by
  obtain ⟨e2, e3⟩ := zWord_transport h1 h2
  simp only [MLO, MHI] at h1 h2
  have hden : (0 : Int) < toInt (evmAdd m Sc) := by
    rw [e3]; simp only [Sc]; omega
  have hdenv : toInt (evmAdd m Sc) = (m : Int) + (Sc : Int) := e3
  unfold zWord
  rcases Int.le_total ((m : Int)) ((Sc : Int)) with hms | hms
  · -- numerator ≥ 0
    have hnum : (0 : Int) ≤ toInt (evmShl 100 (evmSub Sc m)) := by
      rw [e2]; exact Int.mul_nonneg (by omega) (by omega)
    rw [evmSdiv_pos_pos (evmShl_lt _ _) (evmAdd_lt _ _) hnum hden]
    constructor
    · have := Int.natCast_nonneg
        ((toInt (evmShl 100 (evmSub Sc m))).toNat / (toInt (evmAdd m Sc)).toNat)
      omega
    · have hq : (toInt (evmShl 100 (evmSub Sc m))).toNat /
          (toInt (evmAdd m Sc)).toNat < 217494458298375249691265569571 := by
        rw [Nat.div_lt_iff_lt_mul (by rw [hdenv]; simp only [Sc]; omega)]
        rw [e2, hdenv]
        simp only [Sc] at *
        omega
      omega
  · -- numerator ≤ 0
    rcases Int.lt_or_le (toInt (evmShl 100 (evmSub Sc m))) 0 with hneg | hpos
    · rw [evmSdiv_neg_pos (evmShl_lt _ _) (evmAdd_lt _ _) hneg
        (by rw [e2]; simp only [Sc, ipow255] at *; omega) hden]
      constructor
      · have hq : (-toInt (evmShl 100 (evmSub Sc m))).toNat /
            (toInt (evmAdd m Sc)).toNat < 217494458298375249691265569571 := by
          rw [Nat.div_lt_iff_lt_mul (by rw [hdenv]; simp only [Sc]; omega)]
          rw [hdenv]
          have he2' : -toInt (evmShl 100 (evmSub Sc m)) =
              ((m : Int) - (Sc : Int)) * 1267650600228229401496703205376 := by
            rw [e2]
            rw [show ((m : Int) - Sc) = -((Sc : Int) - m) by omega, Int.neg_mul]
          rw [he2']
          simp only [Sc] at *
          omega
        omega
      · have := Int.natCast_nonneg
          ((-toInt (evmShl 100 (evmSub Sc m))).toNat / (toInt (evmAdd m Sc)).toNat)
        omega
    · rw [evmSdiv_pos_pos (evmShl_lt _ _) (evmAdd_lt _ _) hpos hden]
      constructor
      · have := Int.natCast_nonneg
          ((toInt (evmShl 100 (evmSub Sc m))).toNat / (toInt (evmAdd m Sc)).toNat)
        omega
      · have hq : (toInt (evmShl 100 (evmSub Sc m))).toNat /
            (toInt (evmAdd m Sc)).toNat < 217494458298375249691265569571 := by
          rw [Nat.div_lt_iff_lt_mul (by rw [hdenv]; simp only [Sc]; omega)]
          rw [e2, hdenv]
          simp only [Sc] at *
          omega
        omega

/-- Cross inequalities for consecutive mantissas, linearized through the
single bilinear atom `P*E*Q`. -/
theorem zcross_pos {P Q E : Int} (hE : 0 ≤ E) (hPQ : 0 ≤ P + Q) :
    (P - 1) * E * Q ≤ P * E * (Q + 1) := by
  have e1 : (P - 1) * E * Q = P * E * Q - E * Q := by
    rw [Int.sub_mul, Int.one_mul, Int.sub_mul]
  have e2 : P * E * (Q + 1) = P * E * Q + P * E := by
    rw [Int.mul_add, Int.mul_one]
  have e3 : 0 ≤ E * (P + Q) := Int.mul_nonneg hE hPQ
  have e4 : E * (P + Q) = E * P + E * Q := by rw [Int.mul_add]
  have e5 : E * P = P * E := Int.mul_comm E P
  omega

theorem zcross_neg {P Q E : Int} (hE : 0 ≤ E) (hPQ : 0 ≤ P + Q) :
    -P * E * (Q + 1) ≤ (-P + 1) * E * Q := by
  have e1 : -P * E * (Q + 1) = -P * E * Q + -P * E := by
    rw [Int.mul_add, Int.mul_one]
  have e2 : (-P + 1) * E * Q = -P * E * Q + E * Q := by
    rw [Int.add_mul, Int.one_mul, Int.add_mul]
  have e3 : 0 ≤ E * (P + Q) := Int.mul_nonneg hE hPQ
  have e4 : E * (P + Q) = E * P + E * Q := by rw [Int.mul_add]
  have e5 : E * P = P * E := Int.mul_comm E P
  have e6 : -P * E = -(P * E) := by rw [Int.neg_mul]
  omega

/-- Unit-step antitonicity of `zWord`. -/
theorem zWord_antitone_step {m : Nat} (h1 : MLO ≤ m) (h2 : m + 1 < MHI) :
    toInt (zWord (m + 1)) ≤ toInt (zWord m) := by
  obtain ⟨e2, e3⟩ := zWord_transport h1 (by simp only [MLO, MHI] at *; omega)
  obtain ⟨f2, f3⟩ := zWord_transport (m := m + 1)
    (by simp only [MLO, MHI] at *; omega) h2
  simp only [MLO, MHI] at h1 h2
  have hden1 : (0 : Int) < toInt (evmAdd m Sc) := by rw [e3]; simp only [Sc]; omega
  have hden2 : (0 : Int) < toInt (evmAdd (m + 1) Sc) := by
    rw [f3]; simp only [Sc]; omega
  have hc1 : ((m + 1 : Nat) : Int) = (m : Int) + 1 := by omega
  have f2' : toInt (evmShl 100 (evmSub Sc (m + 1))) =
      ((Sc : Int) - (m : Int) - 1) * 1267650600228229401496703205376 := by
    rw [f2, hc1]
    rw [show ((Sc : Int) - ((m : Int) + 1)) = (Sc : Int) - (m : Int) - 1 by omega]
  have f3' : toInt (evmAdd (m + 1) Sc) = ((m : Int) + (Sc : Int)) + 1 := by
    rw [f3, hc1]
    omega
  have hPQ : (0 : Int) ≤ ((Sc : Int) - (m : Int)) + ((m : Int) + (Sc : Int)) := by
    simp only [Sc]
    omega
  unfold zWord
  rcases Int.lt_or_le 0 ((Sc : Int) - (m : Int)) with hP1 | hP0
  · -- both numerators nonnegative
    have hn1 : (0 : Int) ≤ toInt (evmShl 100 (evmSub Sc m)) := by
      rw [e2]; exact Int.mul_nonneg (by omega) (by omega)
    have hn2 : (0 : Int) ≤ toInt (evmShl 100 (evmSub Sc (m + 1))) := by
      rw [f2']; exact Int.mul_nonneg (by omega) (by omega)
    rw [evmSdiv_pos_pos (evmShl_lt _ _) (evmAdd_lt _ _) hn2 hden2,
      evmSdiv_pos_pos (evmShl_lt _ _) (evmAdd_lt _ _) hn1 hden1]
    have hcross : toInt (evmShl 100 (evmSub Sc (m + 1))) * toInt (evmAdd m Sc) ≤
        toInt (evmShl 100 (evmSub Sc m)) * toInt (evmAdd (m + 1) Sc) := by
      rw [e2, e3, f2', f3']
      have := zcross_pos (P := (Sc : Int) - (m : Int)) (Q := (m : Int) + (Sc : Int))
        (E := 1267650600228229401496703205376) (by omega) hPQ
      rw [show ((Sc : Int) - (m : Int) - 1) = ((Sc : Int) - (m : Int)) - 1 by omega]
      exact this
    have hdd := cross_to_div hn2 hn1 hden2 hden1 hcross
    omega
  · -- P ≤ 0
    rcases Int.lt_or_le (toInt (evmShl 100 (evmSub Sc m))) 0 with hneg1 | hpos1
    · -- both numerators negative
      have hPneg : (Sc : Int) - (m : Int) ≤ 0 := by omega
      have hneg2 : toInt (evmShl 100 (evmSub Sc (m + 1))) < 0 := by
        rw [f2']
        have h := mul_le_mul_right_nonneg
          (show ((Sc : Int) - (m : Int) - 1) ≤ -1 by omega)
          (by omega : (0 : Int) ≤ 1267650600228229401496703205376)
        omega
      have hbnd1 : -(2 ^ 255) < toInt (evmShl 100 (evmSub Sc m)) := by
        rw [e2]
        have h := mul_le_mul_right_nonneg
          (show (-(2 ^ 104) : Int) ≤ (Sc : Int) - (m : Int) by simp only [Sc]; omega)
          (by omega : (0 : Int) ≤ 1267650600228229401496703205376)
        have e : (-(2 ^ 104) : Int) * 1267650600228229401496703205376 =
            -(2 ^ 104 * 1267650600228229401496703205376) := by
          rw [Int.neg_mul]
        simp only [ipow255] at *
        omega
      have hbnd2 : -(2 ^ 255) < toInt (evmShl 100 (evmSub Sc (m + 1))) := by
        rw [f2']
        have h := mul_le_mul_right_nonneg
          (show (-(2 ^ 104) : Int) ≤ (Sc : Int) - (m : Int) - 1 by
            simp only [Sc]; omega)
          (by omega : (0 : Int) ≤ 1267650600228229401496703205376)
        have e : (-(2 ^ 104) : Int) * 1267650600228229401496703205376 =
            -(2 ^ 104 * 1267650600228229401496703205376) := by
          rw [Int.neg_mul]
        simp only [ipow255] at *
        omega
      rw [evmSdiv_neg_pos (evmShl_lt _ _) (evmAdd_lt _ _) hneg2 hbnd2 hden2,
        evmSdiv_neg_pos (evmShl_lt _ _) (evmAdd_lt _ _) hneg1 hbnd1 hden1]
      have hcross : (-toInt (evmShl 100 (evmSub Sc m))) * toInt (evmAdd (m + 1) Sc) ≤
          (-toInt (evmShl 100 (evmSub Sc (m + 1)))) * toInt (evmAdd m Sc) := by
        rw [e2, e3, f2', f3']
        have hz := zcross_neg (P := (Sc : Int) - (m : Int))
          (Q := (m : Int) + (Sc : Int))
          (E := 1267650600228229401496703205376) (by omega) hPQ
        have m1 : -(((Sc : Int) - (m : Int)) * 1267650600228229401496703205376) =
            -((Sc : Int) - (m : Int)) * 1267650600228229401496703205376 := by
          rw [Int.neg_mul]
        have m2 : -(((Sc : Int) - (m : Int) - 1) * 1267650600228229401496703205376) =
            (-((Sc : Int) - (m : Int)) + 1) * 1267650600228229401496703205376 := by
          rw [show (-((Sc : Int) - (m : Int)) + 1) = -((Sc : Int) - (m : Int) - 1) by
            omega, Int.neg_mul]
        rw [m1, m2]
        exact hz
      have hk1 : (0 : Int) ≤ -toInt (evmShl 100 (evmSub Sc m)) := by omega
      have hk2 : (0 : Int) ≤ -toInt (evmShl 100 (evmSub Sc (m + 1))) := by omega
      have hdd := cross_to_div hk1 hk2 hden1 hden2 hcross
      omega
    · -- P = 0: z(m) = 0, z(m+1) ≤ 0
      have hP0' : (Sc : Int) - (m : Int) = 0 := by
        rcases Int.lt_or_le ((Sc : Int) - (m : Int)) 0 with hlt | hge
        · exfalso
          have h := mul_le_mul_right_nonneg
            (show ((Sc : Int) - (m : Int)) ≤ -1 by omega)
            (by omega : (0 : Int) ≤ 1267650600228229401496703205376)
          rw [e2] at hpos1
          omega
        · omega
      have hneg2 : toInt (evmShl 100 (evmSub Sc (m + 1))) < 0 := by
        rw [f2', hP0']
        omega
      have hbnd2 : -(2 ^ 255) < toInt (evmShl 100 (evmSub Sc (m + 1))) := by
        rw [f2', hP0']
        simp only [ipow255]
        omega
      rw [evmSdiv_neg_pos (evmShl_lt _ _) (evmAdd_lt _ _) hneg2 hbnd2 hden2,
        evmSdiv_pos_pos (evmShl_lt _ _) (evmAdd_lt _ _) hpos1 hden1]
      have h0 : toInt (evmShl 100 (evmSub Sc m)) = 0 := by
        rw [e2, hP0']
        omega
      rw [h0]
      simp only [Int.toNat_zero, Nat.zero_div]
      have := Int.natCast_nonneg
        ((-toInt (evmShl 100 (evmSub Sc (m + 1)))).toNat /
          (toInt (evmAdd (m + 1) Sc)).toNat)
      omega

/-- `hAt` is antitone over any interval of `z`-values in `[-Zc, Zc]`,
by chaining `hI_step`. -/
theorem hAt_antitone {v w : Int}
    (h1 : -(217494458298375249691265569570 : Int) ≤ v) (h2 : v ≤ w)
    (h3 : w ≤ (217494458298375249691265569570 : Int)) :
    toInt (hAt w) ≤ toInt (hAt v) := by
  have key : ∀ n : Nat, v + (n : Int) ≤ (217494458298375249691265569570 : Int) →
      toInt (hAt (v + (n : Int))) ≤ toInt (hAt v) := by
    intro n
    induction n with
    | zero =>
      intro _
      have he : v + ((0 : Nat) : Int) = v := by omega
      rw [he]
    | succ k ih =>
      intro hk
      have he : v + ((k + 1 : Nat) : Int) = v + (k : Int) + 1 := by omega
      rw [he]
      have hs := hI_step (v + (k : Int) + 1) (by omega) (by omega)
      have hsimp : v + (k : Int) + 1 - 1 = v + (k : Int) := by omega
      rw [hsimp] at hs
      exact Int.le_trans hs (ih (by omega))
  have hn : v + (((w - v).toNat : Nat) : Int) = w := by omega
  have hkey := key (w - v).toNat (by omega)
  rw [hn] at hkey
  exact hkey

/-- `zWord` is antitone over the whole mantissa range, by chaining
`zWord_antitone_step`. -/
theorem zWord_antitone {m m' : Nat} (h1 : MLO ≤ m) (h2 : m ≤ m') (h3 : m' < MHI) :
    toInt (zWord m') ≤ toInt (zWord m) := by
  have key : ∀ n : Nat, m + n < MHI → toInt (zWord (m + n)) ≤ toInt (zWord m) := by
    intro n
    induction n with
    | zero => intro _; exact Int.le_refl _
    | succ k ih =>
      intro hk
      have hs := zWord_antitone_step (m := m + k)
        (by simp only [MLO, MHI] at *; omega) (by simp only [MLO, MHI] at *; omega)
      have he : m + (k + 1) = m + k + 1 := by omega
      rw [he]
      exact Int.le_trans hs (ih (by simp only [MLO, MHI] at *; omega))
  have he : m + (m' - m) = m' := by omega
  have hkey := key (m' - m) (by omega)
  rw [he] at hkey
  exact hkey

/-- Magnitude bound on the quotient pipeline: `|X1| ≤ 2.4e29` (the true
extremum is `≈ 2.34e29`). -/
theorem hAt_bound {w : Int}
    (h1 : -(217494458298375249691265569570 : Int) ≤ w)
    (h2 : w ≤ (217494458298375249691265569570 : Int)) :
    -(240000000000000000000000000000 : Int) ≤ toInt (hAt w) ∧
      toInt (hAt w) ≤ (240000000000000000000000000000 : Int) := by
  obtain ⟨heq, hmul⟩ := hAt_facts w h1 h2
  have hul := uVal_le w h1 h2
  obtain ⟨pw, plo, phi, _, _⟩ := pS4_facts hul
  obtain ⟨qw, qlo, qhi, _, _⟩ := qS5_facts hul
  have hb := pz_bound plo phi h1 h2
  have hmw : evmMul (pS4 (uVal w)) (ofInt w) < 2 ^ 256 := evmMul_lt _ _
  rw [heq]
  clear heq hul
  generalize pS4 (uVal w) = pword at *
  generalize qS5 (uVal w) = qword at *
  rcases Int.le_total 0 w with hw | hw
  · -- numerator `P * w ≥ 0`
    have hnum : (0 : Int) ≤ toInt (evmMul pword (ofInt w)) := by
      rw [hmul]; exact Int.mul_nonneg (by omega) hw
    rw [evmSdiv_pos_neg hmw qw hnum (by omega)]
    have s1 : toInt (evmMul pword (ofInt w)) ≤
        toInt pword * 217494458298375249691265569570 := by
      rw [hmul]; exact mul_le_mul_left_nonneg h2 (by omega)
    have s2 : toInt pword * 217494458298375249691265569570 ≤
        13972178604861559108982341686387 * 217494458298375249691265569570 :=
      mul_le_mul_right_nonneg phi (by omega)
    have hdiv : (toInt (evmMul pword (ofInt w))).toNat /
        (-toInt qword).toNat < 240000000000000000000000000001 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    have hge := Int.natCast_nonneg ((toInt (evmMul pword (ofInt w))).toNat /
      (-toInt qword).toNat)
    omega
  · -- numerator `P * w ≤ 0`
    have hPnegw : (0 : Int) ≤ toInt pword * (-w) :=
      Int.mul_nonneg (by omega) (by omega)
    have hPe : toInt pword * (-w) = -(toInt pword * w) :=
      Int.mul_neg _ _
    rcases Int.lt_or_le (toInt (evmMul pword (ofInt w))) 0 with hneg | hpos
    · rw [evmSdiv_neg_neg hmw qw hneg (by rw [hmul]; exact hb.1) (by omega)]
      have s1 : -toInt (evmMul pword (ofInt w)) ≤
          toInt pword * 217494458298375249691265569570 := by
        rw [hmul, ← hPe]
        exact mul_le_mul_left_nonneg (by omega) (by omega)
      have s2 : toInt pword * 217494458298375249691265569570 ≤
          13972178604861559108982341686387 * 217494458298375249691265569570 :=
        mul_le_mul_right_nonneg phi (by omega)
      have hdiv : (-toInt (evmMul pword (ofInt w))).toNat /
          (-toInt qword).toNat < 240000000000000000000000000001 := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        omega
      have hge := Int.natCast_nonneg ((-toInt (evmMul pword (ofInt w))).toNat /
        (-toInt qword).toNat)
      omega
    · rw [evmSdiv_pos_neg hmw qw hpos (by omega)]
      have hz : (toInt (evmMul pword (ofInt w))).toNat = 0 := by omega
      rw [hz, Nat.zero_div]
      omega

/-- The model's `r_1` (as a function of the mantissa) is monotone
nondecreasing across the whole octave. -/
theorem r1_mono {m m' : Nat} (h1 : MLO ≤ m) (h2 : m ≤ m') (h3 : m' < MHI) :
    toInt (x1W (zWord m)) ≤ toInt (x1W (zWord m')) := by
  have hz := zWord_antitone h1 h2 h3
  have hr := zWord_range h1 (by simp only [MLO, MHI] at *; omega)
  have hr' := zWord_range (m := m') (by simp only [MLO, MHI] at *; omega) h3
  have hwlt : zWord m < 2 ^ 256 := by unfold zWord; exact evmSdiv_lt _ _
  have hwlt' : zWord m' < 2 ^ 256 := by unfold zWord; exact evmSdiv_lt _ _
  have e : x1W (zWord m) = hAt (toInt (zWord m)) := by
    unfold hAt; rw [ofInt_toInt hwlt]
  have e' : x1W (zWord m') = hAt (toInt (zWord m')) := by
    unfold hAt; rw [ofInt_toInt hwlt']
  rw [e, e']
  exact hAt_antitone hr'.1 hz hr.2

/-- Magnitude bound on the model's `r_1` over the whole octave. -/
theorem r1_bound {m : Nat} (h1 : MLO ≤ m) (h2 : m < MHI) :
    -(240000000000000000000000000000 : Int) ≤ toInt (x1W (zWord m)) ∧
      toInt (x1W (zWord m)) ≤ (240000000000000000000000000000 : Int) := by
  have hr := zWord_range h1 h2
  have hwlt : zWord m < 2 ^ 256 := by unfold zWord; exact evmSdiv_lt _ _
  have e : x1W (zWord m) = hAt (toInt (zWord m)) := by
    unfold hAt; rw [ofInt_toInt hwlt]
  rw [e]
  exact hAt_bound hr.1 hr.2

end LnYul
