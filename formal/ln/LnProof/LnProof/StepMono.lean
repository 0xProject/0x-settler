import LnProof.Certs

/-!
# The within-octave step

`hAt v` is the model's quotient pipeline applied to an arbitrary `z`-value
`v` (as a two's-complement word). This file proves it antitone over
consecutive integers in `[-Zc, Zc]`: the same-`u` case is division
monotonicity; the `u`-step cases are the `G1`/`G2` certificates pushed
through the truncation sandwiches.
-/

namespace LnYul

open LnPoly

def x1W (z : Nat) : Nat := evmSdiv (evmMul (pS4 (uWord z)) z) (qS5 (uWord z))

def hAt (v : Int) : Nat := x1W (ofInt v)

/-- Nat-level `u` of an integer `z`-value. -/
def uVal (v : Int) : Nat := (v * v).toNat / 2 ^ 104

theorem sq_bound {v Z : Int} (hZ : 0 ≤ Z) (h1 : -Z ≤ v) (h2 : v ≤ Z) :
    0 ≤ v * v ∧ v * v ≤ Z * Z := by
  rcases Int.le_total 0 v with hv | hv
  · refine ⟨Int.mul_nonneg hv hv, ?_⟩
    have a1 : v * v ≤ v * Z := mul_le_mul_left_nonneg h2 hv
    have a2 : v * Z ≤ Z * Z := mul_le_mul_right_nonneg h2 hZ
    omega
  · have hnv : 0 ≤ -v := by omega
    have e1 : v * v = -v * -v := by rw [Int.neg_mul_neg]
    refine ⟨by rw [e1]; exact Int.mul_nonneg hnv hnv, ?_⟩
    have a1 : -v * -v ≤ -v * Z := mul_le_mul_left_nonneg (by omega) hnv
    have a2 : -v * Z ≤ Z * Z := mul_le_mul_right_nonneg (by omega) hZ
    omega

theorem zsq_facts (v : Int) (h1 : -(217494458298375249691265569570 : Int) ≤ v)
    (h2 : v ≤ (217494458298375249691265569570 : Int)) :
    toInt (evmMul (ofInt v) (ofInt v)) = v * v ∧
      evmMul (ofInt v) (ofInt v) = (v * v).toNat := by
  have hsq := sq_bound (by omega : (0:Int) ≤ 217494458298375249691265569570) h1 h2
  have hb : -(2 ^ 255) ≤ v ∧ v < 2 ^ 255 := by
    simp only [ipow255]; omega
  have ht : toInt (ofInt v) = v := toInt_ofInt hb.1 hb.2
  have hsqB : v * v < 2 ^ 255 := by
    simp only [ipow255]
    omega
  have hT : toInt (evmMul (ofInt v) (ofInt v)) = v * v := by
    have := evmMul_transport (ofInt_lt v) (ofInt_lt v)
      (by rw [ht]; omega) (by rw [ht]; exact hsqB)
    rw [ht] at this
    exact this
  refine ⟨hT, ?_⟩
  have hlt : evmMul (ofInt v) (ofInt v) < 2 ^ 256 := evmMul_lt _ _
  have ht2 : evmMul (ofInt v) (ofInt v) < 2 ^ 255 := by
    have h' := hT
    unfold toInt at h'
    split at h' <;> simp only [ipow255, ipow256] at * <;> omega
  have ht3 := toInt_of_lt ht2
  omega

theorem uWord_eq (v : Int) (h1 : -(217494458298375249691265569570 : Int) ≤ v)
    (h2 : v ≤ (217494458298375249691265569570 : Int)) :
    uWord (ofInt v) = uVal v := by
  obtain ⟨_, hw⟩ := zsq_facts v h1 h2
  unfold uWord uVal
  rw [hw]
  refine evmShr_eq_div_104 ?_
  have hsq := sq_bound (by omega : (0:Int) ≤ 217494458298375249691265569570) h1 h2
  omega

theorem uVal_le (v : Int) (h1 : -(217494458298375249691265569570 : Int) ≤ v)
    (h2 : v ≤ (217494458298375249691265569570 : Int)) :
    uVal v ≤ Uc := by
  have hsq := sq_bound (by omega : (0:Int) ≤ 217494458298375249691265569570) h1 h2
  unfold uVal Uc
  omega

/-- One `z`-step moves `u` by at most one (downward for `v ≥ 1`). -/
theorem uVal_step_pos (v : Int) (hv : 1 ≤ v)
    (h2 : v ≤ (217494458298375249691265569570 : Int)) :
    uVal v - 1 ≤ uVal (v - 1) ∧ uVal (v - 1) ≤ uVal v := by
  have e1 : (v - 1) * (v - 1) = v * v - 2 * v + 1 := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
    omega
  have hsq := sq_bound (by omega : (0:Int) ≤ 217494458298375249691265569570)
    (by omega) h2
  unfold uVal
  rw [e1]
  omega

/-- One `z`-step moves `u` by at most one (upward for `v ≤ 0`). -/
theorem uVal_step_nonpos (v : Int) (hv : v ≤ 0)
    (h1 : -(217494458298375249691265569570 : Int) ≤ v - 1) :
    uVal v ≤ uVal (v - 1) ∧ uVal (v - 1) ≤ uVal v + 1 := by
  have e1 : (v - 1) * (v - 1) = v * v - 2 * v + 1 := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
    omega
  have hsq := sq_bound (by omega : (0:Int) ≤ 217494458298375249691265569570)
    (by omega) (by omega)
  unfold uVal
  rw [e1]
  omega

/-! ## Product helpers -/

theorem toNat_mul_of_nonneg {x y : Int} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x.toNat * y.toNat = (x * y).toNat := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hy
  rfl

theorem triple_mono {a1 b1 c1 a2 b2 c2 : Int} (ha : 0 ≤ a1) (hb : 0 ≤ b1) (hc : 0 ≤ c1)
    (h1 : a1 ≤ a2) (h2 : b1 ≤ b2) (h3 : c1 ≤ c2) : a1 * b1 * c1 ≤ a2 * b2 * c2 := by
  have s1 : a1 * b1 ≤ a2 * b1 := mul_le_mul_right_nonneg h1 hb
  have s2 : a2 * b1 ≤ a2 * b2 := mul_le_mul_left_nonneg h2 (by omega)
  have s3 : a1 * b1 * c1 ≤ a2 * b2 * c1 := mul_le_mul_right_nonneg (by omega) hc
  have s4 : a2 * b2 * c1 ≤ a2 * b2 * c2 := by
    refine mul_le_mul_left_nonneg h3 ?_
    have : (0 : Int) ≤ a2 * b1 := by
      have := Int.mul_nonneg (by omega : (0:Int) ≤ a2) hb
      omega
    have : (0 : Int) ≤ a2 * b2 := by omega
    omega
  omega

/-- `((x*A)*y)*(z*B) = ((x*y)*z)*(A*B)` — regroup scale factors. -/
theorem regroup (x A y z B : Int) :
    x * A * y * (z * B) = x * y * z * (A * B) := by
  simp [Int.mul_comm, Int.mul_left_comm]

/-- Positive-branch certificate application: for `w ∈ [1, Zc]` and a `u`-step
down, the slop-worst-case cross inequality. -/
theorem g1_step {um1 : Int} (h0 : 0 ≤ um1) (h1 : um1 ≤ UcI - 1) {w : Int}
    (hw1 : 1 ≤ w) (hw2 : w ≤ ZcI) :
    evalPoly PPc um1 * (-evalPoly QQc (um1 + 1) + SLOPQc) * (w - 1) ≤
      (evalPoly PPc (um1 + 1) + -SLOPPc) * -evalPoly QQc um1 * w := by
  have hG := G1_all h0 h1
  have hPm := certP_all h0 (by omega)
  have hP1 := certP_all (v := um1 + 1) (by omega) (by omega)
  have hQ1 := certQ_all (v := um1 + 1) (by omega) (by omega)
  have hQ0 := certQ_all (v := um1) h0 (by omega)
  have hSP : (0 : Int) ≤ SLOPPc := by simp only [SLOPPc]; omega
  have hSQ : (0 : Int) ≤ SLOPQc := by simp only [SLOPQc]; omega
  have hA0 : (0 : Int) ≤ evalPoly PPc um1 * (-evalPoly QQc (um1 + 1) + SLOPQc) :=
    Int.mul_nonneg (by omega) (by omega)
  have hC0 : (0 : Int) ≤ (evalPoly PPc (um1 + 1) + -SLOPPc) * -evalPoly QQc um1 :=
    Int.mul_nonneg (by omega) (by omega)
  generalize hA : evalPoly PPc um1 * (-evalPoly QQc (um1 + 1) + SLOPQc) = A at hG hA0 ⊢
  generalize hC : (evalPoly PPc (um1 + 1) + -SLOPPc) * -evalPoly QQc um1 = C at hG hC0 ⊢
  simp only [ZcI] at hG hw2
  rcases Int.le_total A C with hAC | hAC
  · -- A ≤ C: A*(w-1) ≤ C*(w-1) ≤ C*w
    have s1 : A * (w - 1) ≤ C * (w - 1) := mul_le_mul_right_nonneg hAC (by omega)
    have s2 : C * (w - 1) ≤ C * w := mul_le_mul_left_nonneg (by omega) hC0
    omega
  · -- A > C: from Zc*(A-C) ≤ A and w ≤ Zc
    have hZ : (217494458298375249691265569570 : Int) * (A - C) ≤ A := by omega
    have s1 : w * (A - C) ≤ (217494458298375249691265569570 : Int) * (A - C) :=
      mul_le_mul_right_nonneg hw2 (by omega)
    have e1 : w * (A - C) = w * A - w * C := by rw [Int.mul_sub]
    have e2 : A * (w - 1) = A * w - A := by rw [Int.mul_sub]; omega
    have e3 : A * w = w * A := Int.mul_comm A w
    have e4 : C * w = w * C := Int.mul_comm C w
    have e5 : ZcI * (A - C) = ZcI * A - ZcI * C := by rw [Int.mul_sub]
    omega

/-- Nonpositive-branch certificate application: for `m = -w ∈ [0, Zc - 1]` and
a `u`-step up. -/
theorem g2_step {um1 : Int} (h0 : 0 ≤ um1) (h1 : um1 ≤ UcI - 1) {m : Int}
    (hm0 : 0 ≤ m) (hm1 : m ≤ ZcI) :
    evalPoly PPc um1 * (-evalPoly QQc (um1 + 1) + SLOPQc) * m ≤
      (evalPoly PPc (um1 + 1) + -SLOPPc) * -evalPoly QQc um1 * (m + 1) := by
  have hG2 := G2_all h0 h1
  have hPm := certP_all h0 (by omega)
  have hP1 := certP_all (v := um1 + 1) (by omega) (by omega)
  have hQ1 := certQ_all (v := um1 + 1) (by omega) (by omega)
  have hQ0 := certQ_all (v := um1) h0 (by omega)
  have hSP : (0 : Int) ≤ SLOPPc := by simp only [SLOPPc]; omega
  have hSQ : (0 : Int) ≤ SLOPQc := by simp only [SLOPQc]; omega
  have hA0 : (0 : Int) ≤ evalPoly PPc um1 * (-evalPoly QQc (um1 + 1) + SLOPQc) :=
    Int.mul_nonneg (by omega) (by omega)
  have hC0 : (0 : Int) ≤ (evalPoly PPc (um1 + 1) + -SLOPPc) * -evalPoly QQc um1 :=
    Int.mul_nonneg (by omega) (by omega)
  generalize hA : evalPoly PPc um1 * (-evalPoly QQc (um1 + 1) + SLOPQc) = A at hG2 hA0 ⊢
  generalize hC : (evalPoly PPc (um1 + 1) + -SLOPPc) * -evalPoly QQc um1 = C at hG2 hC0 ⊢
  simp only [ZcI] at hG2 hm1
  rcases Int.le_total A C with hAC | hAC
  · -- A ≤ C: A*m ≤ C*m ≤ C*(m+1)
    have s1 : A * m ≤ C * m := mul_le_mul_right_nonneg hAC hm0
    have s2 : C * m ≤ C * (m + 1) := mul_le_mul_left_nonneg (by omega) hC0
    omega
  · -- A > C: from Zc*(A-C) ≤ C and m ≤ Zc:
    -- A*m ≤ C*(m+1) ⟺ m*(A-C) ≤ C
    have hZ : (217494458298375249691265569570 : Int) * (A - C) ≤ C := by omega
    have s1 : m * (A - C) ≤ (217494458298375249691265569570 : Int) * (A - C) :=
      mul_le_mul_right_nonneg hm1 (by omega)
    have e1 : m * (A - C) = m * A - m * C := by rw [Int.mul_sub]
    have e2 : A * m = m * A := Int.mul_comm A m
    have e3 : C * (m + 1) = m * C + C := by
      rw [Int.mul_comm C (m + 1), Int.add_mul, Int.one_mul]
    omega

/-! ## Cross-multiplication to Nat division -/

theorem cross_to_div {n1 n2 W1 W2 : Int} (hn1 : 0 ≤ n1) (hn2 : 0 ≤ n2)
    (hW1 : 0 < W1) (hW2 : 0 < W2) (hcross : n1 * W2 ≤ n2 * W1) :
    n1.toNat / W1.toNat ≤ n2.toNat / W2.toNat := by
  refine nat_div_cross_mono (by omega) (by omega) ?_
  have e1 := toNat_mul_of_nonneg hn1 (by omega : (0:Int) ≤ W2)
  have e2 := toNat_mul_of_nonneg hn2 (by omega : (0:Int) ≤ W1)
  omega

/-- `(P * w * W) * (E1 * E2) = (P * E1) * (W * E2) * w`. -/
theorem ident1 (P w W E1 E2 : Int) :
    P * w * W * (E1 * E2) = P * E1 * (W * E2) * w := by
  simp [Int.mul_comm, Int.mul_left_comm]

/-- Numerator product bound: `|P * w| < 2^255` for the certified ranges. -/
theorem pz_bound {P w : Int}
    (hP1 : (13131151825116561693704478250792 : Int) ≤ P)
    (hP2 : P ≤ (13972178604861559108982341686387 : Int))
    (h1 : -(217494458298375249691265569570 : Int) ≤ w)
    (h2 : w ≤ (217494458298375249691265569570 : Int)) :
    -(2 ^ 255) < P * w ∧ P * w < 2 ^ 255 := by
  rcases Int.le_total 0 w with hw | hw
  · have := mul_range hP1 hP2 hw h2
    simp only [ipow255]
    omega
  · have hnw : 0 ≤ -w := by omega
    have e1 : P * w = -(P * -w) := by
      rw [Int.mul_neg]
      omega
    have := mul_range hP1 hP2 hnw (by omega : -w ≤ (217494458298375249691265569570 : Int))
    simp only [ipow255]
    omega

/-! ## The step lemma -/

/-- Bundle of facts about the quotient pipeline at an integer `z`-value. -/
theorem hAt_facts (w : Int)
    (h1 : -(217494458298375249691265569570 : Int) ≤ w)
    (h2 : w ≤ (217494458298375249691265569570 : Int)) :
    hAt w = evmSdiv (evmMul (pS4 (uVal w)) (ofInt w)) (qS5 (uVal w)) ∧
      toInt (evmMul (pS4 (uVal w)) (ofInt w)) = toInt (pS4 (uVal w)) * w := by
  have hue := uWord_eq w h1 h2
  have hul := uVal_le w h1 h2
  obtain ⟨pw, plo, phi, _, _⟩ := pS4_facts hul
  have hofw : toInt (ofInt w) = w :=
    toInt_ofInt (by simp only [ipow255]; omega) (by simp only [ipow255]; omega)
  have hb := pz_bound plo phi h1 h2
  constructor
  · unfold hAt x1W
    rw [hue]
  · have := evmMul_transport pw (ofInt_lt w)
      (by rw [hofw]; omega) (by rw [hofw]; omega)
    rw [hofw] at this
    exact this

/-- Cancellation of a positive literal factor. -/
theorem le_of_mul_le_mul_pos {a b c : Int} (h : a * c ≤ b * c) (hc : 0 < c) :
    a ≤ b := by
  rcases Int.lt_or_le b a with hlt | hle
  · exfalso
    have := Int.mul_lt_mul_of_pos_right hlt hc
    omega
  · exact hle

theorem hI_step (v : Int)
    (hlo : -(217494458298375249691265569570 : Int) ≤ v - 1)
    (hhi : v ≤ (217494458298375249691265569570 : Int)) :
    toInt (hAt v) ≤ toInt (hAt (v - 1)) := by
  have hv1 : -(217494458298375249691265569570 : Int) ≤ v := by omega
  have hv2 : v - 1 ≤ (217494458298375249691265569570 : Int) := by omega
  have hu2le := uVal_le v hv1 hhi
  have hu1le := uVal_le (v - 1) hlo hv2
  have hub2 : uVal v ≤ 2332259347626381040680638252 := by
    simp only [Uc] at hu2le; exact hu2le
  have hub1 : uVal (v - 1) ≤ 2332259347626381040680638252 := by
    simp only [Uc] at hu1le; exact hu1le
  have hstepP : 1 ≤ v → uVal v - 1 ≤ uVal (v - 1) ∧ uVal (v - 1) ≤ uVal v :=
    fun h => uVal_step_pos v h hhi
  have hstepN : v ≤ 0 → uVal v ≤ uVal (v - 1) ∧ uVal (v - 1) ≤ uVal v + 1 :=
    fun h => uVal_step_nonpos v h hlo
  obtain ⟨pw2, plo2, phi2, psl2, psh2⟩ := pS4_facts hu2le
  obtain ⟨pw1, plo1, phi1, psl1, psh1⟩ := pS4_facts hu1le
  obtain ⟨qw2, qlo2, qhi2, qsl2, qsh2⟩ := qS5_facts hu2le
  obtain ⟨qw1, qlo1, qhi1, qsl1, qsh1⟩ := qS5_facts hu1le
  have hb2 := pz_bound plo2 phi2 hv1 hhi
  have hb1 := pz_bound plo1 phi1 hlo hv2
  have hcP2 := certP_all (v := ((uVal v : Nat) : Int)) (by omega)
    (by simp only [UcI]; omega)
  have hcP1 := certP_all (v := ((uVal (v - 1) : Nat) : Int)) (by omega)
    (by simp only [UcI]; omega)
  have hcQ2 := certQ_all (v := ((uVal v : Nat) : Int)) (by omega)
    (by simp only [UcI]; omega)
  have hcQ1 := certQ_all (v := ((uVal (v - 1) : Nat) : Int)) (by omega)
    (by simp only [UcI]; omega)
  have hSP : (0 : Int) ≤ SLOPPc := by simp only [SLOPPc]; omega
  have hSQ : (0 : Int) ≤ SLOPQc := by simp only [SLOPQc]; omega
  obtain ⟨he2, hn2⟩ := hAt_facts v hv1 hhi
  obtain ⟨he1, hn1⟩ := hAt_facts (v - 1) hlo hv2
  rw [he2, he1]
  clear he2 he1 hu2le hu1le
  have hpeq : uVal (v - 1) = uVal v → pS4 (uVal (v - 1)) = pS4 (uVal v) :=
    fun h => by rw [h]
  have hqeq : uVal (v - 1) = uVal v → qS5 (uVal (v - 1)) = qS5 (uVal v) :=
    fun h => by rw [h]
  have hm2lt := evmMul_lt (pS4 (uVal v)) (ofInt v)
  have hm1lt := evmMul_lt (pS4 (uVal (v - 1))) (ofInt (v - 1))
  generalize hu2g : uVal v = u2 at *
  generalize hu1g : uVal (v - 1) = u1 at *
  generalize hp2g : pS4 u2 = pword2 at *
  generalize hp1g : pS4 u1 = pword1 at *
  generalize hq2g : qS5 u2 = qword2 at *
  generalize hq1g : qS5 u1 = qword1 at *
  generalize hm2g : evmMul pword2 (ofInt v) = mword2 at *
  generalize hm1g : evmMul pword1 (ofInt (v - 1)) = mword1 at *
  clear hu2g hu1g hp2g hp1g hq2g hq1g hm2g hm1g
  have hq2neg : toInt qword2 < 0 := by omega
  have hq1neg : toInt qword1 < 0 := by omega
  have hp2pos : (0 : Int) ≤ toInt pword2 := by omega
  have hp1pos : (0 : Int) ≤ toInt pword1 := by omega
  rcases Int.lt_or_le v 1 with hneg | hpos
  · -- v ≤ 0, v - 1 ≤ -1
    have hv0 : v ≤ 0 := by omega
    obtain ⟨hus1, hus2⟩ := hstepN hv0
    have hnum1neg : toInt pword1 * (v - 1) < 0 := by
      have h := mul_le_mul_left_nonneg (show v - 1 ≤ -1 by omega) hp1pos
      omega
    have hf1 := evmSdiv_neg_neg hm1lt qw1
      (hn1 ▸ hnum1neg) (hn1 ▸ (by omega : -(2 ^ 255) < toInt pword1 * (v - 1)))
      hq1neg
    rcases Int.lt_or_le v 0 with hvneg | hveq
    · -- v ≤ -1
      have hnum2neg : toInt pword2 * v < 0 := by
        have h := mul_le_mul_left_nonneg (show v ≤ -1 by omega) hp2pos
        omega
      have hf2 := evmSdiv_neg_neg hm2lt qw2
        (hn2 ▸ hnum2neg) (hn2 ▸ (by omega : -(2 ^ 255) < toInt pword2 * v))
        hq2neg
      rw [hf2, hf1, hn2, hn1]
      clear hf2 hf1 hn2 hn1 hb2 hb1
      have hcross : -(toInt pword2 * v) * (-toInt qword1) ≤
          -(toInt pword1 * (v - 1)) * (-toInt qword2) := by
        rcases Nat.lt_or_ge u2 u1 with hustep | husame
        · have hcast : ((u1 : Nat) : Int) = ((u2 : Nat) : Int) + 1 := by omega
          have hg := g2_step (um1 := ((u2 : Nat) : Int))
            (by omega) (by simp only [UcI]; omega)
            (m := -v) (by omega) (by simp only [ZcI]; omega)
          rw [← hcast] at hg
          have lhsP : (0 : Int) ≤ toInt pword2 * 587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744 := by omega
          have lhsW : (0 : Int) ≤ -toInt qword1 * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264 := by omega
          have lb : -toInt qword1 * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264 ≤
              -evalPoly QQc ((u1 : Nat) : Int) + SLOPQc := by omega
          have l1 : toInt pword2 * 587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744 * (-toInt qword1 * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264) * -v ≤
              evalPoly PPc ((u2 : Nat) : Int) *
                (-evalPoly QQc ((u1 : Nat) : Int) + SLOPQc) * -v :=
            triple_mono lhsP lhsW (by omega) psh2 lb (by omega)
          have rb1 : evalPoly PPc ((u1 : Nat) : Int) + -SLOPPc ≤
              toInt pword1 * 587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744 := by omega
          have rb2 : -evalPoly QQc ((u2 : Nat) : Int) ≤ -toInt qword2 * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264 := by
            omega
          have r1 : (evalPoly PPc ((u1 : Nat) : Int) + -SLOPPc) *
              -evalPoly QQc ((u2 : Nat) : Int) * (-v + 1) ≤
              toInt pword1 * 587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744 * (-toInt qword2 * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264) * (-v + 1) :=
            triple_mono (by omega) (by omega) (by omega) rb1 rb2 (by omega)
          have eL := ident1 (toInt pword2) (-v) (-toInt qword1) (587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744) (157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264)
          have eR := ident1 (toInt pword1) (-v + 1) (-toInt qword2) (587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744) (157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264)
          refine le_of_mul_le_mul_pos (c := (587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744 : Int) * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264) ?_ (by omega)
          have m1 : -(toInt pword2 * v) = toInt pword2 * -v := by rw [Int.mul_neg]
          have m2 : -(toInt pword1 * (v - 1)) = toInt pword1 * (-v + 1) := by
            rw [show (-v + 1 : Int) = -(v - 1) by omega, Int.mul_neg]
          rw [m1, m2, eL, eR]
          generalize gA : toInt pword2 * 587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744 * (-toInt qword1 * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264) * -v = A at l1 ⊢
          generalize gB : evalPoly PPc ((u2 : Nat) : Int) *
            (-evalPoly QQc ((u1 : Nat) : Int) + SLOPQc) * -v = B at l1 hg
          generalize gC : (evalPoly PPc ((u1 : Nat) : Int) + -SLOPPc) *
            -evalPoly QQc ((u2 : Nat) : Int) * (-v + 1) = C at hg r1
          generalize gD : toInt pword1 * 587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744 *
            (-toInt qword2 * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264) * (-v + 1) = D at r1 ⊢
          omega
        · have huv : u1 = u2 := by omega
          have hpe := hpeq huv
          have hqe := hqeq huv
          rw [hpe, hqe]
          have m1 : -(toInt pword2 * v) = toInt pword2 * -v := by rw [Int.mul_neg]
          have m2 : -(toInt pword2 * (v - 1)) = toInt pword2 * (-v + 1) := by
            rw [show (-v + 1 : Int) = -(v - 1) by omega, Int.mul_neg]
          rw [m1, m2]
          have hmono : toInt pword2 * -v ≤ toInt pword2 * (-v + 1) :=
            mul_le_mul_left_nonneg (by omega) hp2pos
          exact mul_le_mul_right_nonneg hmono (by omega)
      have hdd := cross_to_div (by omega) (by omega) (by omega) (by omega) hcross
      omega
    · -- v = 0
      have hveq0 : v = 0 := by omega
      subst hveq0
      have hf2 := evmSdiv_pos_neg hm2lt qw2
        (hn2 ▸ (by omega : (0 : Int) ≤ toInt pword2 * 0)) hq2neg
      rw [hf2, hf1, hn2, hn1]
      clear hf2 hf1 hn2 hn1 hb2 hb1
      simp only [Int.mul_zero, Int.toNat_zero, Nat.zero_div]
      have hq := Int.natCast_nonneg
        ((-(toInt pword1 * (0 - 1))).toNat / (-toInt qword1).toNat)
      omega
  · -- v ≥ 1, v - 1 ≥ 0
    obtain ⟨hus1, hus2⟩ := hstepP hpos
    have hnum2pos : 0 ≤ toInt pword2 * v := Int.mul_nonneg hp2pos (by omega)
    have hnum1pos : 0 ≤ toInt pword1 * (v - 1) := Int.mul_nonneg hp1pos (by omega)
    have hf2 := evmSdiv_pos_neg hm2lt qw2 (hn2 ▸ hnum2pos) hq2neg
    have hf1 := evmSdiv_pos_neg hm1lt qw1 (hn1 ▸ hnum1pos) hq1neg
    rw [hf2, hf1, hn2, hn1]
    clear hf2 hf1 hn2 hn1 hb2 hb1
    have hcross : toInt pword1 * (v - 1) * (-toInt qword2) ≤
        toInt pword2 * v * (-toInt qword1) := by
      rcases Nat.lt_or_ge u1 u2 with hustep | husame
      · have hcast : ((u1 : Nat) : Int) = ((u2 : Nat) : Int) - 1 := by omega
        have hg := g1_step (um1 := ((u2 : Nat) : Int) - 1)
          (by omega) (by simp only [UcI]; omega)
          (w := v) hpos (by simp only [ZcI]; omega)
        rw [show ((u2 : Nat) : Int) - 1 + 1 = ((u2 : Nat) : Int) by omega,
          ← hcast] at hg
        have lhsP : (0 : Int) ≤ toInt pword1 * 587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744 := by omega
        have lhsW : (0 : Int) ≤ -toInt qword2 * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264 := by omega
        have lb : -toInt qword2 * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264 ≤
            -evalPoly QQc ((u2 : Nat) : Int) + SLOPQc := by omega
        have l1 : toInt pword1 * 587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744 * (-toInt qword2 * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264) * (v - 1) ≤
            evalPoly PPc ((u1 : Nat) : Int) *
              (-evalPoly QQc ((u2 : Nat) : Int) + SLOPQc) * (v - 1) :=
          triple_mono lhsP lhsW (by omega) psh1 lb (by omega)
        have rb1 : evalPoly PPc ((u2 : Nat) : Int) + -SLOPPc ≤
            toInt pword2 * 587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744 := by omega
        have rb2 : -evalPoly QQc ((u1 : Nat) : Int) ≤ -toInt qword1 * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264 := by
          omega
        have r1 : (evalPoly PPc ((u2 : Nat) : Int) + -SLOPPc) *
            -evalPoly QQc ((u1 : Nat) : Int) * v ≤
            toInt pword2 * 587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744 * (-toInt qword1 * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264) * v :=
          triple_mono (by omega) (by omega) (by omega) rb1 rb2 (by omega)
        have eL := ident1 (toInt pword1) (v - 1) (-toInt qword2) (587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744) (157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264)
        have eR := ident1 (toInt pword2) v (-toInt qword1) (587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744) (157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264)
        refine le_of_mul_le_mul_pos (c := (587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744 : Int) * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264) ?_ (by omega)
        rw [eL, eR]
        generalize gA : toInt pword1 * 587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744 * (-toInt qword2 * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264) * (v - 1) = A at l1 ⊢
        generalize gB : evalPoly PPc ((u1 : Nat) : Int) *
          (-evalPoly QQc ((u2 : Nat) : Int) + SLOPQc) * (v - 1) = B at l1 hg
        generalize gC : (evalPoly PPc ((u2 : Nat) : Int) + -SLOPPc) *
          -evalPoly QQc ((u1 : Nat) : Int) * v = C at hg r1
        generalize gD : toInt pword2 * 587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744 * (-toInt qword1 * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264) * v = D at r1 ⊢
        omega
      · have huv : u1 = u2 := by omega
        have hpe := hpeq huv
        have hqe := hqeq huv
        rw [hpe, hqe]
        have hmono : toInt pword2 * (v - 1) ≤ toInt pword2 * v :=
          mul_le_mul_left_nonneg (by omega) hp2pos
        exact mul_le_mul_right_nonneg hmono (by omega)
    have hdd := cross_to_div hnum1pos hnum2pos (by omega) (by omega) hcross
    omega

end LnYul