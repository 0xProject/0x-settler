import LnProof.ZOctave
import LnProof.FloorCertAux

/-!
# Pipeline brackets against the certificate rationals

For each mantissa `m`, the pipeline value `X1 = toInt (x1W (zWord m))`
is trapped between the certificate bracket rationals: on `m ≥ S`,
`geTN2b/geTD2b ≤ X1/2^99 ≤ geTN/geTD`, and on `m ≤ S` the mirrored
brackets hold for `-X1`. The chains run through the exact division
brackets of `z` and `u`, the Stages sandwiches for the Horner stages, and
divided-difference monotonicity of the homogenized `p`/`q` polynomials.
-/

set_option maxRecDepth 4096

namespace LnFloorCert

open LnGeneratedModel LnPoly

/-- `z`-magnitude division bracket on the `m ≥ S` branch:
`q = ⌊(m-S) 2^100 / (m+S)⌋` and `toInt (zWord m) = -q`. -/
theorem z_bracket_ge {m : Nat} (hS : Sc ≤ m) (h2 : m < MHI) :
    ∃ q : Nat,
      toInt (zWord m) = -(q : Int) ∧
      (q : Int) * ((m : Int) + Sc) ≤ ((m : Int) - Sc) * 2 ^ 100 ∧
      ((m : Int) - Sc) * 2 ^ 100 < ((q : Int) + 1) * ((m : Int) + Sc) := by
  have h1 : MLO ≤ m := by simp only [MLO]; simp only [Sc] at hS ⊢; omega
  obtain ⟨e2, e3⟩ := zWord_transport h1 h2
  simp only [MLO, MHI] at h1 h2
  have hden : (0 : Int) < toInt (evmAdd m Sc) := by
    rw [e3]; simp only [Sc]; omega
  have hSpos : (0 : Nat) < Sc := by simp only [Sc]; omega
  rcases Nat.eq_or_lt_of_le hS with heq | hlt
  · -- m = Sc: z = 0
    refine ⟨0, ?_, ?_, ?_⟩
    · have hz : toInt (evmShl 100 (evmSub Sc m)) = 0 := by
        rw [e2, show ((Sc : Int) - m) = 0 by omega, Int.zero_mul]
      unfold zWord
      rw [evmSdiv_pos_pos (evmShl_lt _ _) (evmAdd_lt _ _) (by omega) hden, hz]
      simp [Int.toNat_zero, Nat.zero_div]
    · rw [show ((m : Int) - Sc) = 0 by omega]
      omega
    · rw [show ((m : Int) - Sc) = 0 by omega]
      omega
  · -- m > Sc
    have hND : 0 < m + Sc := by omega
    refine ⟨(m - Sc) * 2 ^ 100 / (m + Sc), ?_, ?_, ?_⟩
    · have hneg : toInt (evmShl 100 (evmSub Sc m)) < 0 := by
        rw [e2]
        have h := mul_le_mul_right_nonneg
          (show ((Sc : Int) - m) ≤ -1 by omega)
          (by omega : (0 : Int) ≤ 1267650600228229401496703205376)
        omega
      unfold zWord
      rw [evmSdiv_neg_pos (evmShl_lt _ _) (evmAdd_lt _ _) hneg
        (by rw [e2]; simp only [Sc, ipow255] at *; omega) hden]
      have hnum : (-toInt (evmShl 100 (evmSub Sc m))).toNat =
          (m - Sc) * 2 ^ 100 := by
        rw [e2]
        have : -(((Sc : Int) - m) * 1267650600228229401496703205376) =
            (((m - Sc) * 2 ^ 100 : Nat) : Int) := by
          rw [show ((Sc : Int) - m) = -(((m - Sc : Nat) : Int)) by omega, Int.neg_mul]
          omega
        omega
      have hdenn : (toInt (evmAdd m Sc)).toNat = m + Sc := by
        rw [e3]; omega
      rw [hnum, hdenn]
    · have hdm := Nat.div_add_mod ((m - Sc) * 2 ^ 100) (m + Sc)
      have hml := Nat.mod_lt ((m - Sc) * 2 ^ 100) hND
      generalize hq : (m - Sc) * 2 ^ 100 / (m + Sc) = q at *
      generalize hr : (m - Sc) * 2 ^ 100 % (m + Sc) = r at *
      have e : (q : Int) * ((m : Int) + Sc) = (((m + Sc) * q : Nat) : Int) := by
        rw [Int.natCast_mul]
        have : ((m + Sc : Nat) : Int) = (m : Int) + Sc := by omega
        rw [this, Int.mul_comm]
      rw [e]
      omega
    · have hdm := Nat.div_add_mod ((m - Sc) * 2 ^ 100) (m + Sc)
      have hml := Nat.mod_lt ((m - Sc) * 2 ^ 100) hND
      generalize hq : (m - Sc) * 2 ^ 100 / (m + Sc) = q at *
      generalize hr : (m - Sc) * 2 ^ 100 % (m + Sc) = r at *
      have e : ((q : Int) + 1) * ((m : Int) + Sc) =
          (((m + Sc) * q : Nat) : Int) + ((m : Int) + Sc) := by
        rw [Int.add_mul, Int.one_mul, Int.natCast_mul]
        have : ((m + Sc : Nat) : Int) = (m : Int) + Sc := by omega
        rw [this, Int.mul_comm]
      rw [e]
      omega

/-- `z` division bracket on the `m ≤ S` branch: `toInt (zWord m) = q`. -/
theorem z_bracket_lt {m : Nat} (h1 : MLO ≤ m) (hS : m ≤ Sc) :
    ∃ q : Nat,
      toInt (zWord m) = (q : Int) ∧
      (q : Int) * ((m : Int) + Sc) ≤ ((Sc : Int) - m) * 2 ^ 100 ∧
      ((Sc : Int) - m) * 2 ^ 100 < ((q : Int) + 1) * ((m : Int) + Sc) := by
  have h2 : m < MHI := by simp only [MHI]; simp only [Sc] at hS; omega
  obtain ⟨e2, e3⟩ := zWord_transport h1 h2
  simp only [MLO, MHI] at h1 h2
  have hden : (0 : Int) < toInt (evmAdd m Sc) := by
    rw [e3]; simp only [Sc]; omega
  have hND : 0 < m + Sc := by simp only [Sc]; omega
  have hpos : (0 : Int) ≤ toInt (evmShl 100 (evmSub Sc m)) := by
    rw [e2]
    exact Int.mul_nonneg (by omega) (by omega)
  refine ⟨(Sc - m) * 2 ^ 100 / (m + Sc), ?_, ?_, ?_⟩
  · unfold zWord
    rw [evmSdiv_pos_pos (evmShl_lt _ _) (evmAdd_lt _ _) hpos hden]
    have hnum : (toInt (evmShl 100 (evmSub Sc m))).toNat = (Sc - m) * 2 ^ 100 := by
      rw [e2]
      have : ((Sc : Int) - m) * 1267650600228229401496703205376 =
          (((Sc - m) * 2 ^ 100 : Nat) : Int) := by
        rw [show ((Sc : Int) - m) = (((Sc - m : Nat)) : Int) by omega]
        omega
      omega
    have hdenn : (toInt (evmAdd m Sc)).toNat = m + Sc := by
      rw [e3]; omega
    rw [hnum, hdenn]
  · have hdm := Nat.div_add_mod ((Sc - m) * 2 ^ 100) (m + Sc)
    have hml := Nat.mod_lt ((Sc - m) * 2 ^ 100) hND
    generalize hq : (Sc - m) * 2 ^ 100 / (m + Sc) = q at *
    generalize hr : (Sc - m) * 2 ^ 100 % (m + Sc) = r at *
    have e : (q : Int) * ((m : Int) + Sc) = (((m + Sc) * q : Nat) : Int) := by
      rw [Int.natCast_mul]
      have : ((m + Sc : Nat) : Int) = (m : Int) + Sc := by omega
      rw [this, Int.mul_comm]
    rw [e]
    omega
  · have hdm := Nat.div_add_mod ((Sc - m) * 2 ^ 100) (m + Sc)
    have hml := Nat.mod_lt ((Sc - m) * 2 ^ 100) hND
    generalize hq : (Sc - m) * 2 ^ 100 / (m + Sc) = q at *
    generalize hr : (Sc - m) * 2 ^ 100 % (m + Sc) = r at *
    have e : ((q : Int) + 1) * ((m : Int) + Sc) =
        (((m + Sc) * q : Nat) : Int) + ((m : Int) + Sc) := by
      rw [Int.add_mul, Int.one_mul, Int.natCast_mul]
      have : ((m + Sc : Nat) : Int) = (m : Int) + Sc := by omega
      rw [this, Int.mul_comm]
    rw [e]
    omega

/-- Square monotonicity over nonnegative integers. -/
theorem sq_le_sq' {a b : Int} (h0 : 0 ≤ a) (h : a ≤ b) : a * a ≤ b * b := by
  calc a * a ≤ a * b := mul_le_mul_left_nonneg h h0
    _ ≤ b * b := mul_le_mul_right_nonneg h (by omega)

theorem lt_of_mul_lt_mul_right' {a b c : Int} (h : a * c < b * c) (hc : 0 < c) :
    a < b := by
  rcases Int.lt_or_le a b with h1 | h1
  · exact h1
  · exfalso
    have := mul_le_mul_right_nonneg h1 (by omega : (0 : Int) ≤ c)
    omega

theorem ipow_num :
    (2 : Int) ^ 99 = 633825300114114700748351602688 ∧
    (2 : Int) ^ 100 = 1267650600228229401496703205376 ∧
    (2 : Int) ^ 101 = 2535301200456458802993406410752 ∧
    (2 : Int) ^ 104 = 20282409603651670423947251286016 ∧
    (2 : Int) ^ 96 = 79228162514264337593543950336 ∧
    (2 : Int) ^ 200 = 1606938044258990275541962092341162602522202993782792835301376 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The certificate's `wlo` numerator sits strictly below `8 u B²`:
`d² 2^99 - d B - 8 B² < 8 u B²`, given the `z` and `u` division brackets. -/
theorem wlo_lt_un {d q u B : Nat} (hd : 46 ≤ d)
    (hB : 0 < B) (hBmax : B ≤ 34683664033617306847215100133375)
    (hq2 : (d : Int) * 2 ^ 100 < ((q : Int) + 1) * B)
    (hu : (q : Int) * q ≤ (u : Int) * 2 ^ 104 + 2 ^ 104 - 1) :
    ((d : Int) * d) * 2 ^ 99 - (d : Int) * B - 8 * ((B : Int) * B) <
      8 * ((u : Int) * ((B : Int) * B)) := by
  have hAB : (B : Int) ≤ (d : Int) * 2 ^ 100 := by
    have : (46 : Int) * 2 ^ 100 ≤ (d : Int) * 2 ^ 100 :=
      mul_le_mul_right_nonneg (by omega) (by omega)
    obtain ⟨-, h100, -⟩ := ipow_num
    rw [h100] at this ⊢
    omega
  have s3 : (d : Int) * 2 ^ 100 - B ≤ (q : Int) * B := by
    have e : ((q : Int) + 1) * B = (q : Int) * B + B := by
      rw [Int.add_mul, Int.one_mul]
    omega
  have s4 : ((d : Int) * 2 ^ 100 - B) * ((d : Int) * 2 ^ 100 - B) ≤
      ((q : Int) * B) * ((q : Int) * B) := sq_le_sq' (by omega) s3
  have e1 : ((d : Int) * 2 ^ 100 - B) * ((d : Int) * 2 ^ 100 - B) =
      (d : Int) * 2 ^ 100 * ((d : Int) * 2 ^ 100) -
        B * ((d : Int) * 2 ^ 100) - ((d : Int) * 2 ^ 100 * B - B * B) := by
    rw [Int.mul_sub, Int.sub_mul, Int.sub_mul]
  have e2 : (d : Int) * 2 ^ 100 * ((d : Int) * 2 ^ 100) =
      ((d : Int) * d) * 2 ^ 200 := by
    have h : (d : Int) * 2 ^ 100 * ((d : Int) * 2 ^ 100) =
        ((d : Int) * d) * ((2 : Int) ^ 100 * 2 ^ 100) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [h, show ((2 : Int) ^ 100 * 2 ^ 100) = 2 ^ 200 from by decide]
  have e3 : (d : Int) * 2 ^ 100 * B = ((d : Int) * B) * 2 ^ 100 := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have e3' : (B : Int) * ((d : Int) * 2 ^ 100) = ((d : Int) * B) * 2 ^ 100 := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have e5 : ((q : Int) * B) * ((q : Int) * B) = ((q : Int) * q) * ((B : Int) * B) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have s6 : ((q : Int) * q) * ((B : Int) * B) ≤
      ((u : Int) * 2 ^ 104 + 2 ^ 104 - 1) * ((B : Int) * B) :=
    mul_le_mul_right_nonneg hu (Int.mul_nonneg (by omega) (by omega))
  have e6 : ((u : Int) * 2 ^ 104 + 2 ^ 104 - 1) * ((B : Int) * B) =
      ((u : Int) * ((B : Int) * B)) * 2 ^ 104 +
        ((B : Int) * B) * 2 ^ 104 - (B : Int) * B := by
    rw [Int.sub_mul, Int.add_mul, Int.one_mul]
    have h1 : (u : Int) * 2 ^ 104 * ((B : Int) * B) =
        (u : Int) * ((B : Int) * B) * 2 ^ 104 := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have h2 : (2 : Int) ^ 104 * ((B : Int) * B) = ((B : Int) * B) * 2 ^ 104 := by
      rw [Int.mul_comm]
    omega
  have hBB : (0 : Int) < (B : Int) * B := Int.mul_pos (by omega) (by omega)
  have key : (((d : Int) * d) * 2 ^ 99 - (d : Int) * B - 8 * ((B : Int) * B)) * 2 ^ 104 <
      (8 * ((u : Int) * ((B : Int) * B))) * 2 ^ 104 := by
    have lhs : (((d : Int) * d) * 2 ^ 99 - (d : Int) * B - 8 * ((B : Int) * B)) * 2 ^ 104 =
        ((d : Int) * d) * (2 ^ 99 * 2 ^ 104) - ((d : Int) * B) * 2 ^ 104 -
          8 * (((B : Int) * B) * 2 ^ 104) := by
      rw [Int.sub_mul, Int.sub_mul]
      have b1 : ((d : Int) * d) * 2 ^ 99 * 2 ^ 104 = ((d : Int) * d) * (2 ^ 99 * 2 ^ 104) := by
        rw [Int.mul_assoc]
      have b2 : 8 * ((B : Int) * B) * 2 ^ 104 = 8 * (((B : Int) * B) * 2 ^ 104) := by
        rw [Int.mul_assoc]
      omega
    have rhs : (8 * ((u : Int) * ((B : Int) * B))) * 2 ^ 104 =
        8 * (((u : Int) * ((B : Int) * B)) * 2 ^ 104) := by
      rw [Int.mul_assoc]
    rw [lhs, rhs]
    obtain ⟨h99, h100, h101, h104, h96, h200⟩ := ipow_num
    rw [show ((2 : Int) ^ 99 * 2 ^ 104) =
      8 * 1606938044258990275541962092341162602522202993782792835301376 from by decide]
    rw [h104, h200] at *
    -- generalize every variable product, then close linearly
    generalize ((d : Int) * 2 ^ 100 - B) * ((d : Int) * 2 ^ 100 - B) = SQ at *
    generalize (d : Int) * 2 ^ 100 * ((d : Int) * 2 ^ 100) = X2 at *
    generalize (B : Int) * ((d : Int) * 2 ^ 100) = X4 at *
    generalize (d : Int) * 2 ^ 100 * (B : Int) = X3 at *
    generalize hg1 : ((q : Int) * B) = QB at *
    generalize QB * QB = QB2 at *
    generalize (q : Int) * q = QQ at *
    generalize (d : Int) * d = DD at *
    generalize (B : Int) * B = BB at *
    generalize (u : Int) * BB = UB at *
    generalize ((u : Int) * 20282409603651670423947251286016 +
      20282409603651670423947251286016 - 1) * BB = R6 at *
    generalize QQ * BB = QQBB at *
    generalize (d : Int) * B = DB at *
    clear hq2 hu hAB s3 hg1
    omega
  exact lt_of_mul_lt_mul_right' key (by decide)

/-- `u B² ≤ 2^96 d²` from the division brackets. -/
theorem un_le_dsq {d q u B : Nat} (hB : 0 < B)
    (hq1 : (q : Int) * B ≤ (d : Int) * 2 ^ 100)
    (hu : (u : Int) * 2 ^ 104 ≤ (q : Int) * q) :
    (u : Int) * ((B : Int) * B) ≤ 2 ^ 96 * ((d : Int) * d) := by
  have s1 : ((q : Int) * B) * ((q : Int) * B) ≤
      ((d : Int) * 2 ^ 100) * ((d : Int) * 2 ^ 100) :=
    sq_le_sq' (Int.mul_nonneg (by omega) (by omega)) hq1
  have e1 : ((q : Int) * B) * ((q : Int) * B) = ((q : Int) * q) * ((B : Int) * B) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have e2 : ((d : Int) * 2 ^ 100) * ((d : Int) * 2 ^ 100) =
      ((d : Int) * d) * 2 ^ 200 := by
    have h : ((d : Int) * 2 ^ 100) * ((d : Int) * 2 ^ 100) =
        ((d : Int) * d) * ((2 : Int) ^ 100 * 2 ^ 100) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [h, show ((2 : Int) ^ 100 * 2 ^ 100) = 2 ^ 200 from by decide]
  have s2 : ((u : Int) * 2 ^ 104) * ((B : Int) * B) ≤
      ((q : Int) * q) * ((B : Int) * B) :=
    mul_le_mul_right_nonneg hu (Int.mul_nonneg (by omega) (by omega))
  have e3 : ((u : Int) * 2 ^ 104) * ((B : Int) * B) =
      ((u : Int) * ((B : Int) * B)) * 2 ^ 104 := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have key : ((u : Int) * ((B : Int) * B)) * 2 ^ 104 ≤
      (2 ^ 96 * ((d : Int) * d)) * 2 ^ 104 := by
    have e4 : (2 ^ 96 * ((d : Int) * d)) * 2 ^ 104 = ((d : Int) * d) * 2 ^ 200 := by
      have h : (2 ^ 96 * ((d : Int) * d)) * 2 ^ 104 =
          ((d : Int) * d) * ((2 : Int) ^ 96 * 2 ^ 104) := by
        simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      rw [h, show ((2 : Int) ^ 96 * 2 ^ 104) = 2 ^ 200 from by decide]
    clear hq1 hu
    generalize (q : Int) * (B : Int) = QB at *
    generalize (q : Int) * (q : Int) = QQ at *
    generalize (d : Int) * (d : Int) = DD at *
    generalize (B : Int) * (B : Int) = BB at *
    generalize (u : Int) * BB = UB at *
    omega
  exact Int.le_of_mul_le_mul_right key (by decide)

/-! ## Divided-difference dominance for the homogenized stage polynomials

`homEvalI PPc · D` is decreasing and `homEvalI QQc · D` is increasing on
`|n| 2^96 ≤ Uc D`: the divided difference is dominated by its linear
coefficient (`-P1c 2^263` resp. `Q1c 2^291`), with every higher term
crudely bounded through the box radius. -/

/-- Unfolded quartic form of `homEvalI PPc`. -/
theorem homEvalI_PPc_eq (n D : Int) :
    homEvalI PPc n D =
      (8203564106909714963200842018493798951984754309521818719427488640634114742013119919947469548416190884842555317059682247072626112599280320512 : Int) * D ^ 4 +
        n * (-(211724653123857194763950383719813360812387246807907859655976840812609762088646804783336607575824561935839395840 : Int) * D ^ 3 +
          n * ((1798175745614395766239082622521528960720477616324792863638563111730471590055378944 : Int) * D ^ 2 +
            n * (-(5562590447406762316237749022682109217671325297934336 : Int) * D ^ 1 +
              n * ((4542704643877621417440 : Int) * D ^ 0 + n * 0)))) := rfl

/-- Unfolded quintic form of `homEvalI QQc`. -/
theorem homEvalI_QQc_eq (n D : Int) :
    homEvalI QQc n D =
      (-(2202127471863542086976841246818343354848349628124454549898853972183438719928614203693782484275214277955754824740140383208045055653095158108464873472 : Int)) * D ^ 5 +
        n * ((66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) * D ^ 4 +
          n * (-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int) * D ^ 3 +
            n * ((2925363287404360843667081097142065961887817512291358090461184 : Int) * D ^ 2 +
              n * (-(4299840983308505679614339668442 : Int) * D ^ 1 +
                n * ((1 : Int) * D ^ 0 + n * 0))))) := rfl

/-- `a² ≤ b²` whenever `-b ≤ a ≤ b`. -/
theorem sq_le_of_abs_le {a b : Int} (h1 : -b ≤ a) (h2 : a ≤ b) : a * a ≤ b * b := by
  rcases Int.le_total 0 a with h0 | h0
  · exact sq_le_sq' h0 h2
  · have := sq_le_sq' (a := -a) (b := b) (by omega) (by omega)
    have e : (-a) * (-a) = a * a := by
      rw [Int.neg_mul, Int.mul_neg]
      omega
    omega

/-- Nested-Horner quartic distributes onto power-products. -/
theorem quartic_expand (c1 c2 c3 c4 n E3 E2 E1 : Int) :
    n * (c1 * E3 + n * (c2 * E2 + n * (c3 * E1 + n * c4))) =
      c1 * n * E3 + c2 * (n * n) * E2 + c3 * (n * n * n) * E1 +
        c4 * (n * n * n * n) := by
  have a0 : n * (c3 * E1 + n * c4) = n * (c3 * E1) + n * (n * c4) :=
    Int.mul_add n (c3 * E1) (n * c4)
  have a0' : n * (c2 * E2 + n * (c3 * E1 + n * c4)) =
      n * (c2 * E2) + n * (n * (c3 * E1) + n * (n * c4)) := by
    rw [Int.mul_add n (c2 * E2) (n * (c3 * E1 + n * c4)), a0]
  have a0'' : n * (n * (c3 * E1) + n * (n * c4)) =
      n * (n * (c3 * E1)) + n * (n * (n * c4)) :=
    Int.mul_add n (n * (c3 * E1)) (n * (n * c4))
  rw [Int.mul_add n (c1 * E3) _, a0', a0'']
  have a0''' : n * (n * (c2 * E2) + (n * (n * (c3 * E1)) + n * (n * (n * c4)))) =
      n * (n * (c2 * E2)) + (n * (n * (n * (c3 * E1))) + n * (n * (n * (n * c4)))) := by
    rw [Int.mul_add n (n * (c2 * E2)) _, Int.mul_add n (n * (n * (c3 * E1))) _]
  have a1 : n * (c1 * E3) = c1 * n * E3 := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have a2 : n * (n * (c2 * E2)) = c2 * (n * n) * E2 := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have a3 : n * (n * (n * (c3 * E1))) = c3 * (n * n * n) * E1 := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have a4 : n * (n * (n * (n * c4))) = c4 * (n * n * n * n) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

theorem df2 (x y : Int) : x * x - y * y = (x - y) * (x + y) := by
  rw [Int.sub_mul, Int.mul_add, Int.mul_add]
  have : y * x = x * y := Int.mul_comm y x
  omega

theorem df3 (x y : Int) :
    x * x * x - y * y * y = (x - y) * (x * x + x * y + y * y) := by
  rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_add, Int.mul_add]
  have a1 : y * (x * x) = x * (x * y) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have a2 : x * (x * x) = x * x * x := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have a3 : y * (x * y) = y * y * x := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have a4 : x * (y * y) = y * y * x := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have a5 : y * (y * y) = y * y * y := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have a6 : x * (x * y) = x * (x * y) := rfl
  omega

theorem df4 (x y : Int) :
    x * x * x * x - y * y * y * y =
      (x - y) * ((x + y) * (x * x + y * y)) := by
  have h1 : x * x * x * x = (x * x) * (x * x) := by
    simp only [Int.mul_assoc]
  have h2 : y * y * y * y = (y * y) * (y * y) := by
    simp only [Int.mul_assoc]
  have h3 := df2 (x * x) (y * y)
  have h4 := df2 x y
  -- (x² - y²)(x² + y²) = ((x-y)(x+y))(x² + y²)
  rw [h1, h2, h3, h4, Int.mul_assoc]

theorem sq_nonneg' (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have h2 := Int.mul_nonneg (a := -a) (b := -a) (by omega) (by omega)
    have e : (-a) * (-a) = a * a := by
      rw [Int.neg_mul, Int.mul_neg]
      omega
    omega

/-- Interval bound for a product: `|a| ≤ A`, `0 ≤ b ≤ B` give `|ab| ≤ AB`. -/
theorem mul_bound {a A b B : Int} (ha1 : -A ≤ a) (ha2 : a ≤ A)
    (hb0 : 0 ≤ b) (hb : b ≤ B) : -(A * B) ≤ a * b ∧ a * b ≤ A * B := by
  have hA : 0 ≤ A := by omega
  have hB : 0 ≤ B := by omega
  constructor
  · rcases Int.le_total 0 a with h | h
    · have h1 : 0 ≤ a * b := Int.mul_nonneg h hb0
      have h2 : 0 ≤ A * B := Int.mul_nonneg hA hB
      omega
    · have h1 : a * B ≤ a * b := mul_le_mul_left_nonpos hb h
      have h2 : (-A) * B ≤ a * B := mul_le_mul_right_nonneg ha1 hB
      have e : (-A) * B = -(A * B) := Int.neg_mul A B
      omega
  · rcases Int.le_total 0 a with h | h
    · have h1 : a * b ≤ a * B := mul_le_mul_left_nonneg hb h
      have h2 : a * B ≤ A * B := mul_le_mul_right_nonneg ha2 hB
      omega
    · have h1 : a * b ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg h hb0
      have h2 : 0 ≤ A * B := Int.mul_nonneg hA hB
      omega

/-- Two-sided interval bound for a product of two signed factors. -/
theorem mul_bound2 {a b A : Int} (ha1 : -A ≤ a) (ha2 : a ≤ A)
    (hb1 : -A ≤ b) (hb2 : b ≤ A) : -(A * A) ≤ a * b ∧ a * b ≤ A * A := by
  rcases Int.le_total 0 b with h | h
  · exact mul_bound ha1 ha2 h hb2
  · have h1 := mul_bound (a := a) (A := A) (b := -b) (B := A) ha1 ha2 (by omega) (by omega)
    have e : a * (-b) = -(a * b) := Int.mul_neg a b
    omega

/-- `homEvalI PPc · D` is decreasing for `|n| ≤ Uc D`. -/
theorem homEvalI_PPc_anti {n1 n2 D : Int} (hD : 0 < D) (h21 : n2 ≤ n1)
    (hb1 : n1 ≤ 2333000000000000000000000000 * D)
    (hb2 : -(2333000000000000000000000000 * D) ≤ n2) :
    homEvalI PPc n1 D ≤ homEvalI PPc n2 D := by
  rw [homEvalI_PPc_eq, homEvalI_PPc_eq]
  simp only [Int.pow_zero, Int.pow_one, Int.mul_one, Int.mul_zero, Int.add_zero]
  rw [quartic_expand, quartic_expand]
  have hb1' : -(2333000000000000000000000000 * D) ≤ n1 := by omega
  have hb2' : n2 ≤ 2333000000000000000000000000 * D := by omega
  have hUD : (0 : Int) ≤ 2333000000000000000000000000 * D :=
    Int.mul_nonneg (by omega) (by omega)
  -- squares and cross products
  have hUDsq : (2333000000000000000000000000 * D) * (2333000000000000000000000000 * D) =
      5442889000000000000000000000000000000000000000000000000 * (D * D) := by
    have h : (2333000000000000000000000000 * D) * (2333000000000000000000000000 * D) =
        ((2333000000000000000000000000 : Int) * 2333000000000000000000000000) * (D * D) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [h, show ((2333000000000000000000000000 : Int) * 2333000000000000000000000000) =
      5442889000000000000000000000000000000000000000000000000 from by decide]
  have hsq1 := sq_le_of_abs_le hb1' hb1
  have hsq2 := sq_le_of_abs_le hb2 hb2'
  have hcross := mul_bound2 hb1' hb1 hb2 hb2'
  rw [hUDsq] at hsq1 hsq2 hcross
  -- H3 facts
  have hH3nn : 0 ≤ n1 * n1 + n1 * n2 + n2 * n2 := by
    have hid : (n1 + n2) * (n1 + n2) = n1 * n1 + n1 * n2 + (n1 * n2 + n2 * n2) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
      have : n2 * n1 = n1 * n2 := Int.mul_comm n2 n1
      omega
    have s1 := sq_nonneg' (n1 + n2)
    have s2 := sq_nonneg' n1
    have s3 := sq_nonneg' n2
    omega
  -- sum-of-squares bound for H4
  have hss_nn : 0 ≤ n1 * n1 + n2 * n2 := by
    have s2 := sq_nonneg' n1
    have s3 := sq_nonneg' n2
    omega
  have hss_ub : n1 * n1 + n2 * n2 ≤
      10885778000000000000000000000000000000000000000000000000 * (D * D) := by
    omega
  have hsum_ub : n1 + n2 ≤ 4666000000000000000000000000 * D := by omega
  have hsum_lb : -(4666000000000000000000000000 * D) ≤ n1 + n2 := by omega
  have hH4 := mul_bound (a := n1 + n2) (A := 4666000000000000000000000000 * D)
    (b := n1 * n1 + n2 * n2)
    (B := 10885778000000000000000000000000000000000000000000000000 * (D * D))
    hsum_lb hsum_ub hss_nn hss_ub
  have hH4ub : (4666000000000000000000000000 * D) *
      (10885778000000000000000000000000000000000000000000000000 * (D * D)) =
      50793040148000000000000000000000000000000000000000000000000000000000000000000000000 *
        (D * (D * D)) := by
    have h : (4666000000000000000000000000 * D) *
        (10885778000000000000000000000000000000000000000000000000 * (D * D)) =
        ((4666000000000000000000000000 : Int) *
          10885778000000000000000000000000000000000000000000000000) * (D * (D * D)) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [h, show ((4666000000000000000000000000 : Int) *
      10885778000000000000000000000000000000000000000000000000) =
      50793040148000000000000000000000000000000000000000000000000000000000000000000000000
      from by decide]
  rw [hH4ub] at hH4
  -- powers as products
  have p2 : D ^ 2 = D * D := by
    have h := Int.pow_succ D 1
    rw [Int.pow_one] at h
    exact h
  have p3 : D ^ 3 = D * D * D := by
    have h := Int.pow_succ D 2
    rw [p2] at h
    exact h
  rw [p2, p3]
  have hDDD : (0 : Int) ≤ D * D * D :=
    Int.le_of_lt (Int.mul_pos (Int.mul_pos hD hD) hD)
  have hAC : D * (D * D) = D * D * D := by
    rw [Int.mul_assoc]
  rw [hAC] at hH4
  -- column-difference identities
  have hd2 := df2 n1 n2
  have hd3 := df3 n1 n2
  have hd4 := df4 n1 n2
  have hmono : 0 ≤ n1 - n2 := by omega
  -- T1: exact column difference
  have hT1 : (-(211724653123857194763950383719813360812387246807907859655976840812609762088646804783336607575824561935839395840 : Int)) * n1 * (D * D * D) - (-(211724653123857194763950383719813360812387246807907859655976840812609762088646804783336607575824561935839395840 : Int)) * n2 * (D * D * D) =
      (n1 - n2) * (-(211724653123857194763950383719813360812387246807907859655976840812609762088646804783336607575824561935839395840 : Int)) * (D * D * D) := by
    rw [← Int.sub_mul, ← Int.mul_sub]
    have : (-(211724653123857194763950383719813360812387246807907859655976840812609762088646804783336607575824561935839395840 : Int)) * (n1 - n2) = (n1 - n2) * (-(211724653123857194763950383719813360812387246807907859655976840812609762088646804783336607575824561935839395840 : Int)) := Int.mul_comm _ _
    rw [this]
  -- T2
  have hT2 : (1798175745614395766239082622521528960720477616324792863638563111730471590055378944 : Int) * (n1 * n1) * (D * D) - (1798175745614395766239082622521528960720477616324792863638563111730471590055378944 : Int) * (n2 * n2) * (D * D) ≤
      (n1 - n2) * (8390288029036770645271559516685454130721748557771483501737535479334380439198398152704000000000000000000000000 : Int) * (D * D * D) := by
    have e1 : (1798175745614395766239082622521528960720477616324792863638563111730471590055378944 : Int) * (n1 * n1) * (D * D) - (1798175745614395766239082622521528960720477616324792863638563111730471590055378944 : Int) * (n2 * n2) * (D * D) =
        ((1798175745614395766239082622521528960720477616324792863638563111730471590055378944 : Int) * (n1 - n2) * (D * D)) * (n1 + n2) := by
      rw [← Int.sub_mul, ← Int.mul_sub, hd2]
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [e1]
    have hf : (0 : Int) ≤ (1798175745614395766239082622521528960720477616324792863638563111730471590055378944 : Int) * (n1 - n2) * (D * D) :=
      Int.mul_nonneg (Int.mul_nonneg (by decide) hmono)
        (Int.mul_nonneg (by omega) (by omega))
    have step := mul_le_mul_left_nonneg hsum_ub hf
    have e2 : ((1798175745614395766239082622521528960720477616324792863638563111730471590055378944 : Int) * (n1 - n2) * (D * D)) * (4666000000000000000000000000 * D) =
        (n1 - n2) * (8390288029036770645271559516685454130721748557771483501737535479334380439198398152704000000000000000000000000 : Int) * (D * D * D) := by
      have h : ((1798175745614395766239082622521528960720477616324792863638563111730471590055378944 : Int) * (n1 - n2) * (D * D)) * (4666000000000000000000000000 * D) =
          (n1 - n2) * ((1798175745614395766239082622521528960720477616324792863638563111730471590055378944 : Int) * 4666000000000000000000000000) * (D * D * D) := by
        simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      rw [h, show ((1798175745614395766239082622521528960720477616324792863638563111730471590055378944 : Int) * 4666000000000000000000000000) = (8390288029036770645271559516685454130721748557771483501737535479334380439198398152704000000000000000000000000 : Int) from by decide]
    omega
  -- T3 (nonpositive)
  have hT3 : (-(5562590447406762316237749022682109217671325297934336 : Int)) * (n1 * n1 * n1) * D - (-(5562590447406762316237749022682109217671325297934336 : Int)) * (n2 * n2 * n2) * D ≤ 0 := by
    have e1 : (-(5562590447406762316237749022682109217671325297934336 : Int)) * (n1 * n1 * n1) * D - (-(5562590447406762316237749022682109217671325297934336 : Int)) * (n2 * n2 * n2) * D =
        (-(5562590447406762316237749022682109217671325297934336 : Int)) * ((n1 - n2) * ((n1 * n1 + n1 * n2 + n2 * n2) * D)) := by
      rw [← Int.sub_mul, ← Int.mul_sub, hd3]
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [e1]
    refine Int.mul_nonpos_of_nonpos_of_nonneg (by decide) ?_
    exact Int.mul_nonneg hmono (Int.mul_nonneg hH3nn (by omega))
  -- T4
  have hT4 : (4542704643877621417440 : Int) * (n1 * n1 * n1 * n1) - (4542704643877621417440 : Int) * (n2 * n2 * n2 * n2) ≤
      (n1 - n2) * (230737779356982067054774587381120000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D) := by
    have e1 : (4542704643877621417440 : Int) * (n1 * n1 * n1 * n1) - (4542704643877621417440 : Int) * (n2 * n2 * n2 * n2) =
        ((4542704643877621417440 : Int) * (n1 - n2)) * ((n1 + n2) * (n1 * n1 + n2 * n2)) := by
      rw [← Int.mul_sub, hd4]
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [e1]
    have hf : (0 : Int) ≤ (4542704643877621417440 : Int) * (n1 - n2) :=
      Int.mul_nonneg (by decide) hmono
    have step := mul_le_mul_left_nonneg hH4.2 hf
    have e2 : ((4542704643877621417440 : Int) * (n1 - n2)) *
        (50793040148000000000000000000000000000000000000000000000000000000000000000000000000 *
          (D * D * D)) =
        (n1 - n2) * (230737779356982067054774587381120000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D) := by
      have h : ((4542704643877621417440 : Int) * (n1 - n2)) *
          (50793040148000000000000000000000000000000000000000000000000000000000000000000000000 *
            (D * D * D)) =
          (n1 - n2) * ((4542704643877621417440 : Int) *
            50793040148000000000000000000000000000000000000000000000000000000000000000000000000) *
            (D * D * D) := by
        simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      rw [h, show ((4542704643877621417440 : Int) *
        50793040148000000000000000000000000000000000000000000000000000000000000000000000000) =
        (230737779356982067054774587381120000000000000000000000000000000000000000000000000000000000000000000000000 : Int) from by decide]
    omega
  -- sum of the bounds is nonpositive
  have hsum : (n1 - n2) * (-(211724653123857194763950383719813360812387246807907859655976840812609762088646804783336607575824561935839395840 : Int)) * (D * D * D) +
      (n1 - n2) * (8390288029036770645271559516685454130721748557771483501737535479334380439198398152704000000000000000000000000 : Int) * (D * D * D) +
      (n1 - n2) * (230737779356982067054774587381120000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D) ≤ 0 := by
    have e1 : (n1 - n2) * (-(211724653123857194763950383719813360812387246807907859655976840812609762088646804783336607575824561935839395840 : Int)) * (D * D * D) +
        (n1 - n2) * (8390288029036770645271559516685454130721748557771483501737535479334380439198398152704000000000000000000000000 : Int) * (D * D * D) +
        (n1 - n2) * (230737779356982067054774587381120000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D) =
        (n1 - n2) * (-(203334134357041067136611769428540525561665498250136376154239305333275381649448406630632607575824561935839395840 : Int)) * (D * D * D) := by
      have h : (n1 - n2) * (-(211724653123857194763950383719813360812387246807907859655976840812609762088646804783336607575824561935839395840 : Int)) * (D * D * D) +
          (n1 - n2) * (8390288029036770645271559516685454130721748557771483501737535479334380439198398152704000000000000000000000000 : Int) * (D * D * D) +
          (n1 - n2) * (230737779356982067054774587381120000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D) =
          (n1 - n2) * ((-(211724653123857194763950383719813360812387246807907859655976840812609762088646804783336607575824561935839395840 : Int)) + (8390288029036770645271559516685454130721748557771483501737535479334380439198398152704000000000000000000000000 : Int) + (230737779356982067054774587381120000000000000000000000000000000000000000000000000000000000000000000000000 : Int)) * (D * D * D) := by
        rw [Int.mul_add, Int.mul_add, Int.add_mul, Int.add_mul]
      rw [h, show ((-(211724653123857194763950383719813360812387246807907859655976840812609762088646804783336607575824561935839395840 : Int)) + (8390288029036770645271559516685454130721748557771483501737535479334380439198398152704000000000000000000000000 : Int) + (230737779356982067054774587381120000000000000000000000000000000000000000000000000000000000000000000000000 : Int)) = -(203334134357041067136611769428540525561665498250136376154239305333275381649448406630632607575824561935839395840 : Int) from by decide]
    rw [e1]
    have h1 : (n1 - n2) * (-(203334134357041067136611769428540525561665498250136376154239305333275381649448406630632607575824561935839395840 : Int)) ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos hmono (by decide)
    exact Int.mul_nonpos_of_nonpos_of_nonneg h1 hDDD
  -- conclude
  generalize (-(211724653123857194763950383719813360812387246807907859655976840812609762088646804783336607575824561935839395840 : Int)) * n1 * (D * D * D) = a1 at *
  generalize (-(211724653123857194763950383719813360812387246807907859655976840812609762088646804783336607575824561935839395840 : Int)) * n2 * (D * D * D) = a2 at *
  generalize (1798175745614395766239082622521528960720477616324792863638563111730471590055378944 : Int) * (n1 * n1) * (D * D) = b1 at *
  generalize (1798175745614395766239082622521528960720477616324792863638563111730471590055378944 : Int) * (n2 * n2) * (D * D) = b2 at *
  generalize (-(5562590447406762316237749022682109217671325297934336 : Int)) * (n1 * n1 * n1) * D = c1v at *
  generalize (-(5562590447406762316237749022682109217671325297934336 : Int)) * (n2 * n2 * n2) * D = c2v at *
  generalize (4542704643877621417440 : Int) * (n1 * n1 * n1 * n1) = d1v at *
  generalize (4542704643877621417440 : Int) * (n2 * n2 * n2 * n2) = d2v at *
  generalize (n1 - n2) * (-(211724653123857194763950383719813360812387246807907859655976840812609762088646804783336607575824561935839395840 : Int)) * (D * D * D) = g1 at *
  generalize (n1 - n2) * (8390288029036770645271559516685454130721748557771483501737535479334380439198398152704000000000000000000000000 : Int) * (D * D * D) = g2 at *
  generalize (n1 - n2) * (230737779356982067054774587381120000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D) = g4 at *
  omega

/-- Nested-Horner quintic distributes onto power-products. -/
theorem quintic_expand (c1 c2 c3 c4 c5 n E4 E3 E2 E1 : Int) :
    n * (c1 * E4 + n * (c2 * E3 + n * (c3 * E2 + n * (c4 * E1 + n * c5)))) =
      c1 * n * E4 + (c2 * (n * n) * E3 + c3 * (n * n * n) * E2 +
        c4 * (n * n * n * n) * E1 + c5 * (n * n * n * n * n)) := by
  rw [Int.mul_add n (c1 * E4) _]
  have h := quartic_expand c2 c3 c4 c5 n E3 E2 E1
  rw [show n * (c2 * E3 + n * (c3 * E2 + n * (c4 * E1 + n * c5))) =
    c2 * n * E3 + c3 * (n * n) * E2 + c4 * (n * n * n) * E1 +
      c5 * (n * n * n * n) from h]
  rw [Int.mul_add n (c2 * n * E3 + c3 * (n * n) * E2 + c4 * (n * n * n) * E1)
      (c5 * (n * n * n * n)),
    Int.mul_add n (c2 * n * E3 + c3 * (n * n) * E2) (c4 * (n * n * n) * E1),
    Int.mul_add n (c2 * n * E3) (c3 * (n * n) * E2)]
  have a1 : n * (c1 * E4) = c1 * n * E4 := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have a2 : n * (c2 * n * E3) = c2 * (n * n) * E3 := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have a3 : n * (c3 * (n * n) * E2) = c3 * (n * n * n) * E2 := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have a4 : n * (c4 * (n * n * n) * E1) = c4 * (n * n * n * n) * E1 := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have a5 : n * (c5 * (n * n * n * n)) = c5 * (n * n * n * n * n) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

/-- Fifth-power difference, asymmetric factorization. -/
theorem df5 (x y : Int) :
    x * x * x * x * x - y * y * y * y * y =
      (x - y) * (x * ((x + y) * (x * x + y * y)) + y * y * y * y) := by
  have h4 := df4 x y
  have e1 : x * x * x * x * x - y * y * y * y * y =
      x * (x * x * x * x - y * y * y * y) + (x - y) * (y * y * y * y) := by
    rw [Int.mul_sub, Int.sub_mul]
    have a1 : x * (x * x * x * x) = x * x * x * x * x := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have a2 : x * (y * y * y * y) = x * (y * y * y * y) := rfl
    have a3 : y * (y * y * y * y) = y * y * y * y * y := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  rw [e1, h4]
  have e2 : x * ((x - y) * ((x + y) * (x * x + y * y))) =
      (x - y) * (x * ((x + y) * (x * x + y * y))) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [e2, ← Int.mul_add]

theorem mul_le_mul_right_nonpos {a b c : Int} (h : a ≤ b) (hc : c ≤ 0) :
    b * c ≤ a * c := by
  have h1 := mul_le_mul_right_nonneg h (by omega : (0 : Int) ≤ -c)
  have e1 : a * (-c) = -(a * c) := Int.mul_neg a c
  have e2 : b * (-c) = -(b * c) := Int.mul_neg b c
  omega

/-- `homEvalI QQc · D` is increasing for `|n| ≤ Uc D`. -/
theorem homEvalI_QQc_mono {n1 n2 D : Int} (hD : 0 < D) (h21 : n2 ≤ n1)
    (hb1 : n1 ≤ 2333000000000000000000000000 * D)
    (hb2 : -(2333000000000000000000000000 * D) ≤ n2) :
    homEvalI QQc n2 D ≤ homEvalI QQc n1 D := by
  rw [homEvalI_QQc_eq, homEvalI_QQc_eq]
  simp only [Int.pow_zero, Int.pow_one, Int.mul_one, Int.mul_zero, Int.add_zero]
  have qe1 := quintic_expand
    (66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int)
    (-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int))
    (2925363287404360843667081097142065961887817512291358090461184 : Int)
    (-(4299840983308505679614339668442 : Int)) 1 n1 (D ^ 4) (D ^ 3) (D ^ 2) D
  have qe2 := quintic_expand
    (66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int)
    (-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int))
    (2925363287404360843667081097142065961887817512291358090461184 : Int)
    (-(4299840983308505679614339668442 : Int)) 1 n2 (D ^ 4) (D ^ 3) (D ^ 2) D
  simp only [Int.mul_one, Int.one_mul] at qe1 qe2
  rw [qe1, qe2]
  have hb1' : -(2333000000000000000000000000 * D) ≤ n1 := by omega
  have hb2' : n2 ≤ 2333000000000000000000000000 * D := by omega
  have hUDsq : (2333000000000000000000000000 * D) * (2333000000000000000000000000 * D) =
      (5442889000000000000000000000000000000000000000000000000 : Int) * (D * D) := by
    have h : (2333000000000000000000000000 * D) * (2333000000000000000000000000 * D) =
        ((2333000000000000000000000000 : Int) * 2333000000000000000000000000) * (D * D) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [h, show ((2333000000000000000000000000 : Int) * 2333000000000000000000000000) =
      (5442889000000000000000000000000000000000000000000000000 : Int) from by decide]
  have hsq1 := sq_le_of_abs_le hb1' hb1
  have hsq2 := sq_le_of_abs_le hb2 hb2'
  rw [hUDsq] at hsq1 hsq2
  have hH3nn : 0 ≤ n1 * n1 + n1 * n2 + n2 * n2 := by
    have hid : (n1 + n2) * (n1 + n2) = n1 * n1 + n1 * n2 + (n1 * n2 + n2 * n2) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
      have : n2 * n1 = n1 * n2 := Int.mul_comm n2 n1
      omega
    have s1 := sq_nonneg' (n1 + n2)
    have s2 := sq_nonneg' n1
    have s3 := sq_nonneg' n2
    omega
  have hss_nn : 0 ≤ n1 * n1 + n2 * n2 := by
    have s2 := sq_nonneg' n1
    have s3 := sq_nonneg' n2
    omega
  have hss_ub : n1 * n1 + n2 * n2 ≤ (10885778000000000000000000000000000000000000000000000000 : Int) * (D * D) := by omega
  have hsum_ub : n1 + n2 ≤ (4666000000000000000000000000 : Int) * D := by omega
  have hsum_lb : -((4666000000000000000000000000 : Int) * D) ≤ n1 + n2 := by omega
  have hmono : 0 ≤ n1 - n2 := by omega
  have hUD : (0 : Int) ≤ 2333000000000000000000000000 * D :=
    Int.mul_nonneg (by omega) (by omega)
  have hDD : (0 : Int) ≤ D * D := Int.mul_nonneg (by omega) (by omega)
  have hDDD : (0 : Int) ≤ D * D * D := Int.mul_nonneg hDD (by omega)
  have hDDDD : (0 : Int) ≤ D * D * D * D := Int.mul_nonneg hDDD (by omega)
  have p2 : D ^ 2 = D * D := by
    have h := Int.pow_succ D 1
    rw [Int.pow_one] at h
    exact h
  have p3 : D ^ 3 = D * D * D := by
    have h := Int.pow_succ D 2
    rw [p2] at h
    exact h
  have p4 : D ^ 4 = D * D * D * D := by
    have h := Int.pow_succ D 3
    rw [p3] at h
    exact h
  rw [p2, p3, p4]
  -- H4 interval (for the q4 column)
  have hH4 := mul_bound (a := n1 + n2) (A := (4666000000000000000000000000 : Int) * D)
    (b := n1 * n1 + n2 * n2) (B := (10885778000000000000000000000000000000000000000000000000 : Int) * (D * D)) hsum_lb hsum_ub hss_nn hss_ub
  have hH4m : ((4666000000000000000000000000 : Int) * D) * ((10885778000000000000000000000000000000000000000000000000 : Int) * (D * D)) =
      (50793040148000000000000000000000000000000000000000000000000000000000000000000000000 : Int) *
        (D * D * D) := by
    have h : ((4666000000000000000000000000 : Int) * D) * ((10885778000000000000000000000000000000000000000000000000 : Int) * (D * D)) =
        ((4666000000000000000000000000 : Int) * (10885778000000000000000000000000000000000000000000000000 : Int)) * (D * D * D) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [h, show ((4666000000000000000000000000 : Int) * (10885778000000000000000000000000000000000000000000000000 : Int)) =
      (50793040148000000000000000000000000000000000000000000000000000000000000000000000000 : Int)
      from by decide]
  rw [hH4m] at hH4
  -- column differences from below
  have hd2 := df2 n1 n2
  have hd3 := df3 n1 n2
  have hd4 := df4 n1 n2
  have hd5 := df5 n1 n2
  -- T2 lower bound
  have hT2 : (-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int)) * (n1 * n1) * (D * D * D) -
      (-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int)) * (n2 * n2) * (D * D * D) ≥
      -((n1 - n2) * (3222466568322584035023748083458858048680556628142048161663360032733083916947184966115495247872000000000000000000000000 : Int) * (D * D * D * D)) := by
    have e1 : (-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int)) * (n1 * n1) * (D * D * D) -
        (-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int)) * (n2 * n2) * (D * D * D) =
        ((-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int)) * (n1 - n2) * (D * D * D)) * (n1 + n2) := by
      rw [← Int.sub_mul, ← Int.mul_sub, hd2]
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [e1]
    have hf : (-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int)) * (n1 - n2) * (D * D * D) ≤ 0 := by
      refine Int.mul_nonpos_of_nonpos_of_nonneg ?_ hDDD
      exact Int.mul_nonpos_of_nonpos_of_nonneg (by decide) hmono
    have step := mul_le_mul_left_nonpos hsum_ub hf
    have e2 : (-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int)) * (n1 - n2) * (D * D * D) * ((4666000000000000000000000000 : Int) * D) =
        -((n1 - n2) * (3222466568322584035023748083458858048680556628142048161663360032733083916947184966115495247872000000000000000000000000 : Int) * (D * D * D * D)) := by
      have h : (-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int)) * (n1 - n2) * (D * D * D) * ((4666000000000000000000000000 : Int) * D) =
          (n1 - n2) * ((-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int)) * 4666000000000000000000000000) * (D * D * D * D) := by
        simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      rw [h, show ((-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int)) * 4666000000000000000000000000) = -(3222466568322584035023748083458858048680556628142048161663360032733083916947184966115495247872000000000000000000000000 : Int) from by decide]
      rw [Int.mul_neg, Int.neg_mul]
    omega
  -- T3 nonnegative
  have hT3 : ((2925363287404360843667081097142065961887817512291358090461184 : Int)) * (n1 * n1 * n1) * (D * D) - ((2925363287404360843667081097142065961887817512291358090461184 : Int)) * (n2 * n2 * n2) * (D * D) ≥ 0 := by
    have e1 : ((2925363287404360843667081097142065961887817512291358090461184 : Int)) * (n1 * n1 * n1) * (D * D) - ((2925363287404360843667081097142065961887817512291358090461184 : Int)) * (n2 * n2 * n2) * (D * D) =
        ((2925363287404360843667081097142065961887817512291358090461184 : Int)) * ((n1 - n2) * ((n1 * n1 + n1 * n2 + n2 * n2) * (D * D))) := by
      rw [← Int.sub_mul, ← Int.mul_sub, hd3]
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [e1]
    refine Int.mul_nonneg (by decide) ?_
    exact Int.mul_nonneg hmono (Int.mul_nonneg hH3nn hDD)
  -- T4 lower bound
  have hT4 : (-(4299840983308505679614339668442 : Int)) * (n1 * n1 * n1 * n1) * D - (-(4299840983308505679614339668442 : Int)) * (n2 * n2 * n2 * n2) * D ≥
      -((n1 - n2) * (218401995695204726854537179935683514609416000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D)) := by
    have e1 : (-(4299840983308505679614339668442 : Int)) * (n1 * n1 * n1 * n1) * D - (-(4299840983308505679614339668442 : Int)) * (n2 * n2 * n2 * n2) * D =
        ((-(4299840983308505679614339668442 : Int)) * (n1 - n2) * D) * ((n1 + n2) * (n1 * n1 + n2 * n2)) := by
      rw [← Int.sub_mul, ← Int.mul_sub, hd4]
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [e1]
    have hf : (-(4299840983308505679614339668442 : Int)) * (n1 - n2) * D ≤ 0 := by
      refine Int.mul_nonpos_of_nonpos_of_nonneg ?_ (by omega)
      exact Int.mul_nonpos_of_nonpos_of_nonneg (by decide) hmono
    have step := mul_le_mul_left_nonpos hH4.2 hf
    have e2 : (-(4299840983308505679614339668442 : Int)) * (n1 - n2) * D * ((50793040148000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D)) =
        -((n1 - n2) * (218401995695204726854537179935683514609416000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D)) := by
      have h : (-(4299840983308505679614339668442 : Int)) * (n1 - n2) * D * ((50793040148000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D)) =
          (n1 - n2) * ((-(4299840983308505679614339668442 : Int)) * (50793040148000000000000000000000000000000000000000000000000000000000000000000000000 : Int)) * (D * D * D * D) := by
        simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      rw [h, show ((-(4299840983308505679614339668442 : Int)) * (50793040148000000000000000000000000000000000000000000000000000000000000000000000000 : Int)) = -(218401995695204726854537179935683514609416000000000000000000000000000000000000000000000000000000000000000000000000 : Int) from by decide, Int.mul_neg, Int.neg_mul]
    omega
  -- T5 lower bound via the asymmetric quintic factor
  have hT5 : n1 * n1 * n1 * n1 * n1 - n2 * n2 * n2 * n2 * n2 ≥
      -((n1 - n2) * (118500162665284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D)) := by
    rw [hd5]
    -- inner = (n1+n2)(n1²+n2²) is bounded by hH4; n1 inner ≥ -(UD)·4U³DDD
    have hxin : n1 * ((n1 + n2) * (n1 * n1 + n2 * n2)) ≥
        -(((2333000000000000000000000000 : Int) * D) * ((50793040148000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D))) := by
      rcases Int.le_total 0 ((n1 + n2) * (n1 * n1 + n2 * n2)) with h | h
      · have s1 : n1 * ((n1 + n2) * (n1 * n1 + n2 * n2)) ≥
            (-((2333000000000000000000000000 : Int) * D)) * ((n1 + n2) * (n1 * n1 + n2 * n2)) :=
          mul_le_mul_right_nonneg hb1' h
        have s2 : (-((2333000000000000000000000000 : Int) * D)) * ((n1 + n2) * (n1 * n1 + n2 * n2)) ≥
            (-((2333000000000000000000000000 : Int) * D)) * ((50793040148000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D)) := by
          refine mul_le_mul_left_nonpos hH4.2 (by omega)
        have e : (-((2333000000000000000000000000 : Int) * D)) * ((50793040148000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D)) =
            -(((2333000000000000000000000000 : Int) * D) * ((50793040148000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D))) := Int.neg_mul _ _
        omega
      · have s1 : n1 * ((n1 + n2) * (n1 * n1 + n2 * n2)) ≥
            ((2333000000000000000000000000 : Int) * D) * ((n1 + n2) * (n1 * n1 + n2 * n2)) :=
          mul_le_mul_right_nonpos hb1 h
        have s2 : ((2333000000000000000000000000 : Int) * D) * ((n1 + n2) * (n1 * n1 + n2 * n2)) ≥
            ((2333000000000000000000000000 : Int) * D) * (-((50793040148000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D))) :=
          mul_le_mul_left_nonneg hH4.1 hUD
        have e : ((2333000000000000000000000000 : Int) * D) * (-((50793040148000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D))) =
            -(((2333000000000000000000000000 : Int) * D) * ((50793040148000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D))) := Int.mul_neg _ _
        omega
    have hy4 : 0 ≤ n2 * n2 * n2 * n2 := by
      have h : n2 * n2 * n2 * n2 = (n2 * n2) * (n2 * n2) := by
        simp only [Int.mul_assoc]
      rw [h]
      exact sq_nonneg' (n2 * n2)
    have hmerge : ((2333000000000000000000000000 : Int) * D) * ((50793040148000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D)) =
        (118500162665284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D) := by
      have h : ((2333000000000000000000000000 : Int) * D) * ((50793040148000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D)) =
          ((2333000000000000000000000000 : Int) * (50793040148000000000000000000000000000000000000000000000000000000000000000000000000 : Int)) * (D * D * D * D) := by
        simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      rw [h, show ((2333000000000000000000000000 : Int) * (50793040148000000000000000000000000000000000000000000000000000000000000000000000000 : Int)) = (118500162665284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Int) from by decide]
    have hkey : n1 * ((n1 + n2) * (n1 * n1 + n2 * n2)) + n2 * n2 * n2 * n2 ≥
        -((118500162665284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D)) := by
      rw [← hmerge]
      omega
    have step : (n1 - n2) * (n1 * ((n1 + n2) * (n1 * n1 + n2 * n2)) + n2 * n2 * n2 * n2) ≥
        (n1 - n2) * (-((118500162665284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D))) :=
      mul_le_mul_left_nonneg hkey hmono
    have e : (n1 - n2) * (-((118500162665284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D))) =
        -((n1 - n2) * (118500162665284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D)) := by
      rw [Int.mul_neg]
      have h : (n1 - n2) * (118500162665284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D) =
          (n1 - n2) * ((118500162665284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D)) := by
        rw [Int.mul_assoc]
      rw [h]
    omega
  -- T1 exact
  have hT1 : (66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) * n1 * (D * D * D * D) - (66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) * n2 * (D * D * D * D) =
      (n1 - n2) * (66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) * (D * D * D * D) := by
    rw [← Int.sub_mul, ← Int.mul_sub]
    have : (66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) * (n1 - n2) = (n1 - n2) * (66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) := Int.mul_comm _ _
    rw [this]
  -- the bounds sum to something nonnegative
  have hsumQ : (n1 - n2) * (66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) * (D * D * D * D) -
      (n1 - n2) * (3222466568322584035023748083458858048680556628142048161663360032733083916947184966115495247872000000000000000000000000 : Int) * (D * D * D * D) -
      (n1 - n2) * (218401995695204726854537179935683514609416000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D) -
      (n1 - n2) * (118500162665284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D) ≥ 0 := by
    have e1 : (n1 - n2) * (66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) * (D * D * D * D) -
        (n1 - n2) * (3222466568322584035023748083458858048680556628142048161663360032733083916947184966115495247872000000000000000000000000 : Int) * (D * D * D * D) -
        (n1 - n2) * (218401995695204726854537179935683514609416000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D) -
        (n1 - n2) * (118500162665284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D) =
        (n1 - n2) * (62876637496879759399862214498438820436182586606529832473300549855511637940656756793209095903651373370374573118109777920 : Int) * (D * D * D * D) := by
      have h : (n1 - n2) * (66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) * (D * D * D * D) -
          (n1 - n2) * (3222466568322584035023748083458858048680556628142048161663360032733083916947184966115495247872000000000000000000000000 : Int) * (D * D * D * D) -
          (n1 - n2) * (218401995695204726854537179935683514609416000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D) -
          (n1 - n2) * (118500162665284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D) =
          (n1 - n2) * ((66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) - (3222466568322584035023748083458858048680556628142048161663360032733083916947184966115495247872000000000000000000000000 : Int) - (218401995695204726854537179935683514609416000000000000000000000000000000000000000000000000000000000000000000000000 : Int) - (118500162665284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Int)) * (D * D * D * D) := by
        generalize n1 - n2 = w
        have a1 : w * (66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) * (D * D * D * D) = (66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) * (w * (D * D * D * D)) := by
          simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        have a2 : w * (3222466568322584035023748083458858048680556628142048161663360032733083916947184966115495247872000000000000000000000000 : Int) * (D * D * D * D) = (3222466568322584035023748083458858048680556628142048161663360032733083916947184966115495247872000000000000000000000000 : Int) * (w * (D * D * D * D)) := by
          simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        have a3 : w * (218401995695204726854537179935683514609416000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D) = (218401995695204726854537179935683514609416000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (w * (D * D * D * D)) := by
          simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        have a4 : w * (118500162665284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D) = (118500162665284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (w * (D * D * D * D)) := by
          simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        have a5 : w * ((66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) - (3222466568322584035023748083458858048680556628142048161663360032733083916947184966115495247872000000000000000000000000 : Int) - (218401995695204726854537179935683514609416000000000000000000000000000000000000000000000000000000000000000000000000 : Int) - (118500162665284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Int)) * (D * D * D * D) =
            ((66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) - (3222466568322584035023748083458858048680556628142048161663360032733083916947184966115495247872000000000000000000000000 : Int) - (218401995695204726854537179935683514609416000000000000000000000000000000000000000000000000000000000000000000000000 : Int) - (118500162665284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Int)) * (w * (D * D * D * D)) := by
          simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        omega
      rw [h, show ((66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) - (3222466568322584035023748083458858048680556628142048161663360032733083916947184966115495247872000000000000000000000000 : Int) - (218401995695204726854537179935683514609416000000000000000000000000000000000000000000000000000000000000000000000000 : Int) - (118500162665284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Int)) = (62876637496879759399862214498438820436182586606529832473300549855511637940656756793209095903651373370374573118109777920 : Int) from by decide]
    rw [e1]
    exact Int.mul_nonneg (Int.mul_nonneg hmono (by decide)) hDDDD
  generalize (66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) * n1 * (D * D * D * D) = a1 at *
  generalize (66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) * n2 * (D * D * D * D) = a2 at *
  generalize (-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int)) * (n1 * n1) * (D * D * D) = b1 at *
  generalize (-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int)) * (n2 * n2) * (D * D * D) = b2 at *
  generalize ((2925363287404360843667081097142065961887817512291358090461184 : Int)) * (n1 * n1 * n1) * (D * D) = c1v at *
  generalize ((2925363287404360843667081097142065961887817512291358090461184 : Int)) * (n2 * n2 * n2) * (D * D) = c2v at *
  generalize (-(4299840983308505679614339668442 : Int)) * (n1 * n1 * n1 * n1) * D = d1v at *
  generalize (-(4299840983308505679614339668442 : Int)) * (n2 * n2 * n2 * n2) * D = d2v at *
  generalize n1 * n1 * n1 * n1 * n1 = e1v at *
  generalize n2 * n2 * n2 * n2 * n2 = e2v at *
  generalize (n1 - n2) * (66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) * (D * D * D * D) = g1 at *
  generalize (n1 - n2) * (3222466568322584035023748083458858048680556628142048161663360032733083916947184966115495247872000000000000000000000000 : Int) * (D * D * D * D) = g2 at *
  generalize (n1 - n2) * (218401995695204726854537179935683514609416000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D) = g4 at *
  generalize (n1 - n2) * (118500162665284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Int) * (D * D * D * D) = g5 at *
  omega

/-! ## Cross-theorems: the pipeline value against the certificate rationals -/

/-- Small-list evaluations for the certificate building blocks. -/
theorem pow_pos' {a : Int} (h : 0 < a) : ∀ n, 0 < a ^ n := by
  intro n
  induction n with
  | zero =>
    show (0 : Int) < a ^ 0
    rw [Int.pow_zero]
    omega
  | succ k ih =>
    rw [Int.pow_succ]
    exact Int.mul_pos ih h

theorem pow_nonneg' {a : Int} (h : 0 ≤ a) : ∀ n, 0 ≤ a ^ n := by
  intro n
  induction n with
  | zero =>
    show (0 : Int) ≤ a ^ 0
    rw [Int.pow_zero]
    omega
  | succ k ih =>
    rw [Int.pow_succ]
    exact Int.mul_nonneg ih h
theorem evalA_ge (m : Nat) : evalPoly geA (m : Int) = (m : Int) - Sc := by
  show -(Sc : Int) + (m : Int) * (1 + (m : Int) * 0) = _
  omega

theorem evalB_ge (m : Nat) : evalPoly geB (m : Int) = (m : Int) + Sc := by
  show (Sc : Int) + (m : Int) * (1 + (m : Int) * 0) = _
  omega

theorem evalB2_ge (m : Nat) :
    evalPoly geB2 (m : Int) = ((m : Int) + Sc) * ((m : Int) + Sc) := by
  show evalPoly (polyMul geB geB) (m : Int) = _
  rw [evalPoly_polyMul, evalB_ge]

theorem evalA2_ge (m : Nat) :
    evalPoly geA2 (m : Int) = ((m : Int) - Sc) * ((m : Int) - Sc) := by
  show evalPoly (polyMul geA geA) (m : Int) = _
  rw [evalPoly_polyMul, evalA_ge]

theorem evalD8_ge (m : Nat) :
    evalPoly geD8 (m : Int) = 8 * (((m : Int) + Sc) * ((m : Int) + Sc)) := by
  show evalPoly (polyScale 8 geB2) (m : Int) = _
  rw [evalPoly_polyScale, evalB2_ge]

theorem evalA96_ge (m : Nat) :
    evalPoly geA96 (m : Int) = 2 ^ 96 * (((m : Int) - Sc) * ((m : Int) - Sc)) := by
  show evalPoly (polyScale (2 ^ 96) geA2) (m : Int) = _
  rw [evalPoly_polyScale, evalA2_ge]

theorem evalWLO_ge (m : Nat) :
    evalPoly geWLO (m : Int) =
      2 ^ 99 * (((m : Int) - Sc) * ((m : Int) - Sc)) -
        ((m : Int) - Sc) * ((m : Int) + Sc) -
        8 * (((m : Int) + Sc) * ((m : Int) + Sc)) := by
  show evalPoly (polyAdd (polyAdd (polyScale (2 ^ 99) geA2)
    (polyNeg (polyMul geA geB))) (polyScale (-8) geB2)) (m : Int) = _
  rw [evalPoly_polyAdd, evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyNeg,
    evalPoly_polyMul, evalPoly_polyScale, evalA2_ge, evalA_ge, evalB_ge, evalB2_ge]
  omega

theorem evalTN_ge (m : Nat) :
    evalPoly geTN (m : Int) =
      2 ^ 17 * ((((m : Int) - Sc) * (((m : Int) + Sc))) *
        homEvalI PPc (evalPoly geWLO (m : Int)) (evalPoly geD8 (m : Int))) := by
  show evalPoly (polyScale (2 ^ 17) (polyMul (polyMul geA geB) gePPHwlo)) (m : Int) = _
  rw [evalPoly_polyScale, evalPoly_polyMul, evalPoly_polyMul, evalA_ge, evalB_ge]
  have h : evalPoly gePPHwlo (m : Int) =
      homEvalI PPc (evalPoly geWLO (m : Int)) (evalPoly geD8 (m : Int)) := by
    show evalPoly (homPoly PPc geWLO geD8) (m : Int) = _
    exact evalPoly_homPoly PPc geWLO geD8 (m : Int)
  rw [h]

theorem evalTD_ge (m : Nat) :
    evalPoly geTD (m : Int) =
      -homEvalI QQc (evalPoly geA96 (m : Int)) (evalPoly geB2 (m : Int)) := by
  show evalPoly (polyNeg geQQHws) (m : Int) = _
  rw [evalPoly_polyNeg]
  have h : evalPoly geQQHws (m : Int) =
      homEvalI QQc (evalPoly geA96 (m : Int)) (evalPoly geB2 (m : Int)) := by
    show evalPoly (homPoly QQc geA96 geB2) (m : Int) = _
    exact evalPoly_homPoly QQc geA96 geB2 (m : Int)
  rw [h]

theorem evalWS_ge (m : Nat) :
    evalPoly certGeWS (m : Int) =
      2333000000000000000000000000 * (((m : Int) + Sc) * ((m : Int) + Sc)) -
        2 ^ 96 * (((m : Int) - Sc) * ((m : Int) - Sc)) := by
  show evalPoly (polyAdd (polyScale UB geB2) (polyScale (-(2 ^ 96)) geA2)) (m : Int) = _
  rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyScale, evalB2_ge, evalA2_ge]
  show UB * _ + _ = _
  rw [show UB = (2333000000000000000000000000 : Int) from rfl]
  omega

theorem evalPLOP_ge (m : Nat) :
    evalPoly gePLOP (m : Int) =
      homEvalI PPc (evalPoly geA96 (m : Int)) (evalPoly geB2 (m : Int)) -
        SLOPPc * evalPoly geB2 (m : Int) ^ 4 := by
  show evalPoly (polyAdd gePPHws (polyScale (-SLOPPc) (polyPow geB2 4))) (m : Int) = _
  rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyPow]
  have h : evalPoly gePPHws (m : Int) =
      homEvalI PPc (evalPoly geA96 (m : Int)) (evalPoly geB2 (m : Int)) := by
    show evalPoly (homPoly PPc geA96 geB2) (m : Int) = _
    exact evalPoly_homPoly PPc geA96 geB2 (m : Int)
  rw [h, Int.sub_eq_add_neg, Int.neg_mul]

theorem evalDLO_ge (m : Nat) :
    evalPoly geDLO (m : Int) =
      -homEvalI QQc (evalPoly geWLO (m : Int)) (evalPoly geD8 (m : Int)) +
        SLOPQc * evalPoly geD8 (m : Int) ^ 5 := by
  show evalPoly (polyAdd (polyNeg geQQHwlo) (polyScale SLOPQc (polyPow geD8 5))) (m : Int) = _
  rw [evalPoly_polyAdd, evalPoly_polyNeg, evalPoly_polyScale, evalPoly_polyPow]
  have h : evalPoly geQQHwlo (m : Int) =
      homEvalI QQc (evalPoly geWLO (m : Int)) (evalPoly geD8 (m : Int)) := by
    show evalPoly (homPoly QQc geWLO geD8) (m : Int) = _
    exact evalPoly_homPoly QQc geWLO geD8 (m : Int)
  rw [h]

theorem evalAZ_ge (m : Nat) :
    evalPoly geAZ (m : Int) = 2 ^ 100 * ((m : Int) - Sc) - ((m : Int) + Sc) := by
  show evalPoly (polyAdd (polyScale (2 ^ 100) geA) (polyNeg geB)) (m : Int) = _
  rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyNeg, evalA_ge, evalB_ge]
  have e : (2 : Int) ^ 100 * ((m : Int) - Sc) = 2 ^ 100 * (m : Int) - 2 ^ 100 * Sc := by
    rw [Int.mul_sub]
  omega

theorem evalTN2b_ge (m : Nat) :
    evalPoly geTN2b (m : Int) =
      2 ^ 99 * (evalPoly gePLOP (m : Int) * evalPoly geAZ (m : Int) *
        ((m : Int) + Sc)) - 2 ^ 56 * evalPoly geDLO (m : Int) := by
  show evalPoly (polyAdd (polyScale (2 ^ 99) geTN2) (polyNeg geTD2)) (m : Int) = _
  rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyNeg]
  have h1 : evalPoly geTN2 (m : Int) =
      evalPoly gePLOP (m : Int) * evalPoly geAZ (m : Int) * ((m : Int) + Sc) := by
    show evalPoly (polyMul (polyMul gePLOP geAZ) geB) (m : Int) = _
    rw [evalPoly_polyMul, evalPoly_polyMul, evalB_ge]
  have h2 : evalPoly geTD2 (m : Int) = 2 ^ 56 * evalPoly geDLO (m : Int) := by
    show evalPoly (polyScale (2 ^ 56) geDLO) (m : Int) = _
    rw [evalPoly_polyScale]
  rw [h1, h2, Int.sub_eq_add_neg]

theorem evalTD2b_ge (m : Nat) :
    evalPoly geTD2b (m : Int) = 2 ^ 99 * (2 ^ 56 * evalPoly geDLO (m : Int)) := by
  show evalPoly (polyScale (2 ^ 99) geTD2) (m : Int) = _
  rw [evalPoly_polyScale]
  have h2 : evalPoly geTD2 (m : Int) = 2 ^ 56 * evalPoly geDLO (m : Int) := by
    show evalPoly (polyScale (2 ^ 56) geDLO) (m : Int) = _
    rw [evalPoly_polyScale]
  rw [h2]

/-- The pipeline value sits below the upper certificate rational on the
`m ≥ S` branch: `X1 · TD(m) ≤ TN(m) · 2^99`. -/
theorem bracket_ge_up {m : Nat} (h1 : Sc + 46 ≤ m) (h2 : m < MHI) :
    toInt (x1W (zWord m)) * evalPoly geTD (m : Int) ≤
      evalPoly geTN (m : Int) * 2 ^ 99 := by
  have hMLO : MLO ≤ m := by
    simp only [MLO]; simp only [Sc] at h1; omega
  have hSle : Sc ≤ m := by simp only [Sc] at h1 ⊢; omega
  -- z and its division bracket
  obtain ⟨q, hzq, hq1, hq2⟩ := z_bracket_ge hSle h2
  have hzr := zWord_range hMLO h2
  have hwlt : zWord m < 2 ^ 256 := by unfold zWord; exact evmSdiv_lt _ _
  have hx1 : x1W (zWord m) = hAt (toInt (zWord m)) := by
    unfold hAt; rw [ofInt_toInt hwlt]
  obtain ⟨heq, hmul⟩ := hAt_facts (toInt (zWord m)) hzr.1 hzr.2
  -- u-hat and its division bracket
  have huv : uVal (toInt (zWord m)) = q * q / 2 ^ 104 := by
    unfold uVal
    rw [hzq]
    have e : -(q : Int) * -(q : Int) = ((q * q : Nat) : Int) := by
      rw [Int.neg_mul_neg]
      omega
    rw [e]
    omega
  have hu_le : q * q / 2 ^ 104 ≤ Uc := by
    have := uVal_le (toInt (zWord m)) hzr.1 hzr.2
    rw [huv] at this
    exact this
  have hudm := Nat.div_add_mod (q * q) (2 ^ 104)
  have huml := Nat.mod_lt (q * q) (y := 2 ^ 104) (by omega)
  -- the quotient is at least one on this branch
  have hq_ge1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h0 | h
    · exfalso
      subst h0
      have hA46 : (46 : Int) ≤ (m : Int) - Sc := by simp only [Sc] at h1 ⊢; omega
      have hBmax : (m : Int) + Sc ≤ 34624238973196922243142627472244 := by
        simp only [MHI] at h2; simp only [Sc]; omega
      have h46 : (46 : Int) * 2 ^ 100 ≤ ((m : Int) - Sc) * 2 ^ 100 :=
        mul_le_mul_right_nonneg hA46 (by omega)
      omega
    · exact h
  -- stage sandwiches at u-hat, with every heavy term made opaque
  obtain ⟨pw, plo, phi, psl, psh⟩ := pS4_facts hu_le
  obtain ⟨qw, qlo, qhi, qsl, qsh⟩ := qS5_facts hu_le
  rw [huv] at heq hmul
  generalize hw1 : pS4 (q * q / 2 ^ 104) = pword at heq hmul pw plo phi psl psh
  generalize hw2 : qS5 (q * q / 2 ^ 104) = qword at heq qw qlo qhi qsl qsh
  generalize hPP : evalPoly PPc ((q * q / 2 ^ 104 : Nat) : Int) = PPv at psl psh
  generalize hQQ : evalPoly QQc ((q * q / 2 ^ 104 : Nat) : Int) = QQv at qsl qsh
  have hxe : x1W (zWord m) = evmSdiv (evmMul pword (ofInt (toInt (zWord m)))) qword :=
    hx1.trans heq
  have hnum_neg : toInt (evmMul pword (ofInt (toInt (zWord m)))) < 0 := by
    rw [hmul, hzq]
    have h := mul_le_mul_left_nonneg (show (1 : Int) ≤ (q : Int) by omega)
      (show (0 : Int) ≤ toInt pword by omega)
    have e : toInt pword * -(q : Int) = -(toInt pword * (q : Int)) := Int.mul_neg _ _
    omega
  have hpz := pz_bound plo phi hzr.1 hzr.2
  have hX1v : toInt (x1W (zWord m)) =
      (((toInt pword * (q : Int)).toNat / (-toInt qword).toNat : Nat) : Int) := by
    rw [hxe, evmSdiv_neg_neg (evmMul_lt _ _) qw hnum_neg
      (by rw [hmul]; exact hpz.1) (by omega), hmul, hzq]
    have e : -(toInt pword * -(q : Int)) = toInt pword * (q : Int) := by
      rw [Int.mul_neg]
      omega
    rw [e]
  have hpq_pos : (0 : Int) ≤ toInt pword * (q : Int) :=
    Int.mul_nonneg (by omega) (by omega)
  have hX1_nn : (0 : Int) ≤ toInt (x1W (zWord m)) := by
    rw [hX1v]
    exact Int.natCast_nonneg _
  -- the division bracket for X1
  have hdiv := Nat.div_mul_le_self (toInt pword * (q : Int)).toNat (-toInt qword).toNat
  have hX1br : toInt (x1W (zWord m)) * (-toInt qword) ≤ toInt pword * (q : Int) := by
    rw [hX1v]
    have e : (((toInt pword * (q : Int)).toNat / (-toInt qword).toNat : Nat) : Int) *
        (-toInt qword) =
        ((((toInt pword * (q : Int)).toNat / (-toInt qword).toNat) *
          (-toInt qword).toNat : Nat) : Int) := by
      rw [Int.natCast_mul]
      have : ((-toInt qword).toNat : Int) = -toInt qword := by omega
      rw [this]
    rw [e]
    omega
  clear heq hxe hmul hX1v hnum_neg hdiv hpz hx1 hzr hwlt hudm huml hzq hw1 hw2
  generalize hXg : toInt (x1W (zWord m)) = X1v at hX1br hX1_nn ⊢
  -- value abbreviations
  have huI1 : ((q * q / 2 ^ 104 : Nat) : Int) * 2 ^ 104 ≤ (q : Int) * q := by
    have e : (q : Int) * q = ((q * q : Nat) : Int) := by omega
    rw [e]
    omega
  have huI2 : (q : Int) * q ≤ ((q * q / 2 ^ 104 : Nat) : Int) * 2 ^ 104 + 2 ^ 104 - 1 := by
    have e : (q : Int) * q = ((q * q : Nat) : Int) := by omega
    rw [e]
    omega
  -- ordering of the P arguments: WLO ≤ u-hat · D8
  have hcastA : ((m - Sc : Nat) : Int) = (m : Int) - Sc := by omega
  have hcastB : ((m + Sc : Nat) : Int) = (m : Int) + Sc := by omega
  have hwloLt := wlo_lt_un (d := m - Sc) (q := q) (u := q * q / 2 ^ 104)
    (B := m + Sc) (by omega)
    (by omega) (by simp only [MHI] at h2; simp only [Sc] at *; omega)
    (by rw [hcastA, hcastB]; exact hq2)
    huI2
  have hordP : evalPoly geWLO (m : Int) ≤
      ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly geD8 (m : Int) := by
    rw [evalWLO_ge, evalD8_ge]
    rw [hcastA, hcastB] at hwloLt
    have e1 : ((q * q / 2 ^ 104 : Nat) : Int) * (8 * (((m : Int) + Sc) * ((m : Int) + Sc))) =
        8 * (((q * q / 2 ^ 104 : Nat) : Int) * (((m : Int) + Sc) * ((m : Int) + Sc))) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have e2 : (((m : Int) - Sc) * ((m : Int) - Sc)) * 2 ^ 99 =
        2 ^ 99 * (((m : Int) - Sc) * ((m : Int) - Sc)) := Int.mul_comm _ _
    omega
  -- ordering of the Q arguments: u-hat · B2 ≤ A96
  have hunle := un_le_dsq (d := m - Sc) (q := q) (u := q * q / 2 ^ 104)
    (B := m + Sc) (by omega)
    (by rw [hcastA, hcastB]; exact hq1) huI1
  have hordQ : ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly geB2 (m : Int) ≤
      evalPoly geA96 (m : Int) := by
    rw [evalB2_ge, evalA96_ge]
    rw [hcastA, hcastB] at hunle
    exact hunle
  -- box bounds
  have hB2nn : (0 : Int) ≤ evalPoly geB2 (m : Int) := by
    rw [evalB2_ge]
    exact Int.mul_nonneg (by simp only [Sc]; omega) (by simp only [Sc]; omega)
  have hD8nn : (0 : Int) ≤ evalPoly geD8 (m : Int) := by
    rw [evalD8_ge]
    refine Int.mul_nonneg (by omega) (Int.mul_nonneg ?_ ?_) <;>
      simp only [Sc] <;> omega
  have hu_lt_UB : ((q * q / 2 ^ 104 : Nat) : Int) ≤ 2333000000000000000000000000 := by
    simp only [Uc] at hu_le
    omega
  have hb1P : ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly geD8 (m : Int) ≤
      2333000000000000000000000000 * evalPoly geD8 (m : Int) :=
    mul_le_mul_right_nonneg hu_lt_UB hD8nn
  have hb2P : -(2333000000000000000000000000 * evalPoly geD8 (m : Int)) ≤
      evalPoly geWLO (m : Int) := by
    rw [evalWLO_ge, evalD8_ge]
    have hAB : ((m : Int) - Sc) * ((m : Int) + Sc) ≤
        ((m : Int) + Sc) * ((m : Int) + Sc) :=
      mul_le_mul_right_nonneg (by omega) (by simp only [Sc]; omega)
    have hsq : (0 : Int) ≤ (((m : Int) - Sc) * ((m : Int) - Sc)) := by
      refine Int.mul_nonneg ?_ ?_ <;> simp only [Sc] at h1 ⊢ <;> omega
    have hBB : (0 : Int) ≤ ((m : Int) + Sc) * ((m : Int) + Sc) := by
      refine Int.mul_nonneg ?_ ?_ <;> simp only [Sc] <;> omega
    generalize ((m : Int) - Sc) * ((m : Int) - Sc) = AA at *
    generalize ((m : Int) - Sc) * ((m : Int) + Sc) = AB at *
    generalize ((m : Int) + Sc) * ((m : Int) + Sc) = BB at *
    have h99 : (0 : Int) ≤ 2 ^ 99 * AA := Int.mul_nonneg (by omega) hsq
    omega
  -- P comparison through collapse and monotonicity
  have hcolP : homEvalI PPc (((q * q / 2 ^ 104 : Nat) : Int) *
      evalPoly geD8 (m : Int)) (evalPoly geD8 (m : Int)) =
      evalPoly geD8 (m : Int) ^ 4 * PPv := by
    rw [show PPc = (8203564106909714963200842018493798951984754309521818719427488640634114742013119919947469548416190884842555317059682247072626112599280320512 : Int) :: PP3c from rfl,
      homEvalI_collapse, ← hPP]
    rfl
  have hBpos : (0 : Int) < (m : Int) + Sc := by simp only [Sc]; omega
  have hD8pos : (0 : Int) < evalPoly geD8 (m : Int) := by
    rw [evalD8_ge]
    exact Int.mul_pos (by omega) (Int.mul_pos hBpos hBpos)
  have hB2pos : (0 : Int) < evalPoly geB2 (m : Int) := by
    rw [evalB2_ge]
    exact Int.mul_pos hBpos hBpos
  have hPanti := homEvalI_PPc_anti (n1 := ((q * q / 2 ^ 104 : Nat) : Int) *
      evalPoly geD8 (m : Int)) (n2 := evalPoly geWLO (m : Int))
    (D := evalPoly geD8 (m : Int)) hD8pos hordP hb1P hb2P
  have hPfin : toInt pword * 2 ^ 358 * evalPoly geD8 (m : Int) ^ 4 ≤
      homEvalI PPc (evalPoly geWLO (m : Int)) (evalPoly geD8 (m : Int)) := by
    have hD84 : (0 : Int) ≤ evalPoly geD8 (m : Int) ^ 4 := by
      have h2' : evalPoly geD8 (m : Int) ^ 2 = evalPoly geD8 (m : Int) *
          evalPoly geD8 (m : Int) := by
        have h := Int.pow_succ (evalPoly geD8 (m : Int)) 1
        rw [Int.pow_one] at h
        exact h
      have h4' : evalPoly geD8 (m : Int) ^ 4 = evalPoly geD8 (m : Int) ^ 2 *
          evalPoly geD8 (m : Int) ^ 2 := by
        have h3 := Int.pow_succ (evalPoly geD8 (m : Int)) 2
        have h4 := Int.pow_succ (evalPoly geD8 (m : Int)) 3
        rw [h3] at h4
        rw [h4, h2']
        simp only [Int.mul_assoc]
      rw [h4', h2']
      exact Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega))
        (Int.mul_nonneg (by omega) (by omega))
    have s1 : toInt pword * 2 ^ 358 * evalPoly geD8 (m : Int) ^ 4 ≤
        PPv * evalPoly geD8 (m : Int) ^ 4 :=
      mul_le_mul_right_nonneg psh hD84
    have e1 : PPv * evalPoly geD8 (m : Int) ^ 4 =
        evalPoly geD8 (m : Int) ^ 4 * PPv := Int.mul_comm _ _
    generalize hg1 : homEvalI PPc (((q * q / 2 ^ 104 : Nat) : Int) *
      evalPoly geD8 (m : Int)) (evalPoly geD8 (m : Int)) = HU at hPanti hcolP
    generalize hg2 : homEvalI PPc (evalPoly geWLO (m : Int))
      (evalPoly geD8 (m : Int)) = HW at hPanti ⊢
    generalize hg3 : PPv * evalPoly geD8 (m : Int) ^ 4 = P1 at s1 e1
    generalize hg4 : evalPoly geD8 (m : Int) ^ 4 * PPv = P2 at e1 hcolP
    generalize hg5 : toInt pword * 2 ^ 358 * evalPoly geD8 (m : Int) ^ 4 = P0 at s1 ⊢
    omega
  -- Q comparison
  have hb1Q : evalPoly geA96 (m : Int) ≤
      2333000000000000000000000000 * evalPoly geB2 (m : Int) := by
    have hws := geWS_nonneg (m := (m : Int))
      (by simp only [Sc] at h1; omega) (by simp only [MHI] at h2; omega)
    rw [evalWS_ge] at hws
    rw [evalA96_ge, evalB2_ge]
    omega
  have hb2Q : -(2333000000000000000000000000 * evalPoly geB2 (m : Int)) ≤
      ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly geB2 (m : Int) := by
    have h := Int.mul_nonneg (Int.natCast_nonneg (q * q / 2 ^ 104)) (by omega :
      (0 : Int) ≤ evalPoly geB2 (m : Int))
    have h2' : (0 : Int) ≤ 2333000000000000000000000000 * evalPoly geB2 (m : Int) :=
      Int.mul_nonneg (by omega) (by omega)
    omega
  have hQmono := homEvalI_QQc_mono (n1 := evalPoly geA96 (m : Int))
    (n2 := ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly geB2 (m : Int))
    (D := evalPoly geB2 (m : Int)) hB2pos hordQ hb1Q hb2Q
  have hcolQ : homEvalI QQc (((q * q / 2 ^ 104 : Nat) : Int) *
      evalPoly geB2 (m : Int)) (evalPoly geB2 (m : Int)) =
      evalPoly geB2 (m : Int) ^ 5 * QQv := by
    rw [show QQc = (-(2202127471863542086976841246818343354848349628124454549898853972183438719928614203693782484275214277955754824740140383208045055653095158108464873472 : Int)) :: QQ4c from rfl,
      homEvalI_collapse, ← hQQ]
    rfl
  have hQfin : -homEvalI QQc (evalPoly geA96 (m : Int)) (evalPoly geB2 (m : Int)) ≤
      -toInt qword * 2 ^ 386 * evalPoly geB2 (m : Int) ^ 5 := by
    have hB25 : (0 : Int) ≤ evalPoly geB2 (m : Int) ^ 5 := pow_nonneg' (by omega) 5
    have s1 : evalPoly geB2 (m : Int) ^ 5 * QQv ≤
        homEvalI QQc (evalPoly geA96 (m : Int)) (evalPoly geB2 (m : Int)) := by
      rw [← hcolQ]
      exact hQmono
    have s2 : toInt qword * 2 ^ 386 * evalPoly geB2 (m : Int) ^ 5 ≤
        QQv * evalPoly geB2 (m : Int) ^ 5 :=
      mul_le_mul_right_nonneg qsh hB25
    have e1 : QQv * evalPoly geB2 (m : Int) ^ 5 =
        evalPoly geB2 (m : Int) ^ 5 * QQv := Int.mul_comm _ _
    have e2 : -toInt qword * 2 ^ 386 * evalPoly geB2 (m : Int) ^ 5 =
        -(toInt qword * 2 ^ 386 * evalPoly geB2 (m : Int) ^ 5) := by
      rw [Int.neg_mul, Int.neg_mul]
    omega
  -- final assembly
  rw [evalTD_ge, evalTN_ge]
  generalize hPHV : homEvalI PPc (evalPoly geWLO (m : Int))
    (evalPoly geD8 (m : Int)) = PHV at hPfin ⊢
  generalize hQHVg : homEvalI QQc (evalPoly geA96 (m : Int))
    (evalPoly geB2 (m : Int)) = QHV at hQfin ⊢
  have hD8e := evalD8_ge m
  have hB2e := evalB2_ge m
  generalize hD8g : evalPoly geD8 (m : Int) = D8v at hPfin hD8e
  generalize hB2g : evalPoly geB2 (m : Int) = B2v at hQfin hB2e
  have hqpos : (0 : Int) < -toInt qword := by omega
  have hppos : (0 : Int) ≤ toInt pword := by omega
  have hApos : (0 : Int) ≤ (m : Int) - Sc := by simp only [Sc] at h1 ⊢; omega
  have hB25 : (0 : Int) ≤ B2v ^ 5 := by
    rw [hB2e]
    exact pow_nonneg' (Int.mul_nonneg (by omega) (by omega)) 5
  have hD84 : (0 : Int) ≤ D8v ^ 4 := by
    rw [hD8e]
    refine pow_nonneg' (Int.mul_nonneg (by omega) (Int.mul_nonneg ?_ ?_)) 4 <;>
      simp only [Sc] <;> omega
  -- step 1: X1v (-QHV) ≤ X1v ((-qword) 2^386 B2v^5)
  have s1 : X1v * -QHV ≤ X1v * (-toInt qword * 2 ^ 386 * B2v ^ 5) := by
    have h := mul_le_mul_left_nonneg hQfin hX1_nn
    exact h
  -- step 2: pull the division bracket through
  have s2 : X1v * (-toInt qword * 2 ^ 386 * B2v ^ 5) ≤
      toInt pword * (q : Int) * (2 ^ 386 * B2v ^ 5) := by
    have e1 : X1v * (-toInt qword * 2 ^ 386 * B2v ^ 5) =
        (X1v * -toInt qword) * (2 ^ 386 * B2v ^ 5) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have hf : (0 : Int) ≤ 2 ^ 386 * B2v ^ 5 := Int.mul_nonneg (by omega) hB25
    have h := mul_le_mul_right_nonneg hX1br hf
    omega
  -- step 3: multiply by B and use the z bracket
  have s3 : toInt pword * (q : Int) * (2 ^ 386 * B2v ^ 5) * ((m : Int) + Sc) ≤
      toInt pword * (((m : Int) - Sc) * 2 ^ 100) * (2 ^ 386 * B2v ^ 5) := by
    have e1 : toInt pword * (q : Int) * (2 ^ 386 * B2v ^ 5) * ((m : Int) + Sc) =
        (toInt pword * (2 ^ 386 * B2v ^ 5)) * ((q : Int) * ((m : Int) + Sc)) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have e2 : toInt pword * (((m : Int) - Sc) * 2 ^ 100) * (2 ^ 386 * B2v ^ 5) =
        (toInt pword * (2 ^ 386 * B2v ^ 5)) * (((m : Int) - Sc) * 2 ^ 100) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have hf : (0 : Int) ≤ toInt pword * (2 ^ 386 * B2v ^ 5) :=
      Int.mul_nonneg hppos (Int.mul_nonneg (by omega) hB25)
    have h := mul_le_mul_left_nonneg hq1 hf
    omega
  -- step 4: bring in the P bound
  have s4 : toInt pword * (((m : Int) - Sc) * 2 ^ 100) * (2 ^ 386 * B2v ^ 5) *
      (2 ^ 358 * D8v ^ 4) ≤
      PHV * (((m : Int) - Sc) * (2 ^ 486 * B2v ^ 5)) := by
    have e1 : toInt pword * (((m : Int) - Sc) * 2 ^ 100) * (2 ^ 386 * B2v ^ 5) *
        (2 ^ 358 * D8v ^ 4) =
        (toInt pword * 2 ^ 358 * D8v ^ 4) *
          (((m : Int) - Sc) * (2 ^ 100 * 2 ^ 386 * B2v ^ 5)) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have hf : (0 : Int) ≤ ((m : Int) - Sc) * (2 ^ 100 * 2 ^ 386 * B2v ^ 5) :=
      Int.mul_nonneg hApos (Int.mul_nonneg (by omega) hB25)
    have h := mul_le_mul_right_nonneg hPfin hf
    have e2 : PHV * (((m : Int) - Sc) * (2 ^ 100 * 2 ^ 386 * B2v ^ 5)) =
        PHV * (((m : Int) - Sc) * (2 ^ 486 * B2v ^ 5)) := by
      rw [show ((2 : Int) ^ 100 * 2 ^ 386) = 2 ^ 486 from by decide]
    omega
  -- multiplied chain and cancellation
  have hD84pos : (0 : Int) < D8v ^ 4 := by
    rw [hD8e]
    refine pow_pos' (Int.mul_pos (by omega) (Int.mul_pos hBpos hBpos)) 4
  have hMpos : (0 : Int) < ((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4) :=
    Int.mul_pos hBpos (Int.mul_pos (by omega) hD84pos)
  have hMnn : (0 : Int) ≤ ((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4) := by omega
  have k1 : X1v * -QHV * (((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4)) ≤
      X1v * (-toInt qword * 2 ^ 386 * B2v ^ 5) *
        (((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4)) :=
    mul_le_mul_right_nonneg s1 hMnn
  have k2 : X1v * (-toInt qword * 2 ^ 386 * B2v ^ 5) *
      (((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4)) ≤
      toInt pword * (q : Int) * (2 ^ 386 * B2v ^ 5) *
        (((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4)) :=
    mul_le_mul_right_nonneg s2 hMnn
  have k3 : toInt pword * (q : Int) * (2 ^ 386 * B2v ^ 5) *
      (((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4)) =
      toInt pword * (q : Int) * (2 ^ 386 * B2v ^ 5) * ((m : Int) + Sc) *
        (2 ^ 358 * D8v ^ 4) := by
    simp only [Int.mul_assoc]
  have k4 : toInt pword * (q : Int) * (2 ^ 386 * B2v ^ 5) * ((m : Int) + Sc) *
      (2 ^ 358 * D8v ^ 4) ≤
      toInt pword * (((m : Int) - Sc) * 2 ^ 100) * (2 ^ 386 * B2v ^ 5) *
        (2 ^ 358 * D8v ^ 4) :=
    mul_le_mul_right_nonneg s3 (Int.mul_nonneg (by omega) (by omega))
  have k6 : 2 ^ 17 * (((m : Int) - Sc) * ((m : Int) + Sc) * PHV) * 2 ^ 99 *
      (((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4)) =
      PHV * (((m : Int) - Sc) * (2 ^ 486 * B2v ^ 5)) := by
    rw [hD8e, hB2e]
    rw [show ((8 : Int) * (((m : Int) + Sc) * ((m : Int) + Sc))) ^ 4 =
      4096 * (((m : Int) + Sc) * ((m : Int) + Sc)) ^ 4 from by
        rw [Int.mul_pow]
        rw [show ((8 : Int) ^ 4) = 4096 from by decide]]
    rw [show (((m : Int) + Sc) * ((m : Int) + Sc)) ^ 5 =
      (((m : Int) + Sc) * ((m : Int) + Sc)) ^ 4 *
        (((m : Int) + Sc) * ((m : Int) + Sc)) from by
        rw [Int.pow_succ]]
    have hAC : 2 ^ 17 * (((m : Int) - Sc) * ((m : Int) + Sc) * PHV) * 2 ^ 99 *
        (((m : Int) + Sc) * (2 ^ 358 * (4096 * (((m : Int) + Sc) * ((m : Int) + Sc)) ^ 4))) =
        (2 ^ 17 * 2 ^ 99 * 2 ^ 358 * 4096) *
          (PHV * (((m : Int) - Sc) * ((((m : Int) + Sc) * ((m : Int) + Sc)) ^ 4 *
            (((m : Int) + Sc) * ((m : Int) + Sc))))) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [hAC, show ((2 : Int) ^ 17 * 2 ^ 99 * 2 ^ 358 * 4096) = 2 ^ 486 from by decide]
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have key : X1v * -QHV * (((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4)) ≤
      2 ^ 17 * (((m : Int) - Sc) * ((m : Int) + Sc) * PHV) * 2 ^ 99 *
        (((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4)) := by
    rw [k6]
    omega
  exact Int.le_of_mul_le_mul_right key hMpos

/-- The pipeline value sits above the lower certificate rational on the
`m ≥ S` branch: `TN2b(m) · 2^99 ≤ X1 · TD2b(m)`. -/
theorem bracket_ge_lo {m : Nat} (h1 : Sc + 46 ≤ m) (h2 : m < MHI) :
    evalPoly geTN2b (m : Int) * 2 ^ 99 ≤
      toInt (x1W (zWord m)) * evalPoly geTD2b (m : Int) := by
  have hMLO : MLO ≤ m := by
    simp only [MLO]; simp only [Sc] at h1; omega
  have hSle : Sc ≤ m := by simp only [Sc] at h1 ⊢; omega
  obtain ⟨q, hzq, hq1, hq2⟩ := z_bracket_ge hSle h2
  have hzr := zWord_range hMLO h2
  have hwlt : zWord m < 2 ^ 256 := by unfold zWord; exact evmSdiv_lt _ _
  have hx1 : x1W (zWord m) = hAt (toInt (zWord m)) := by
    unfold hAt; rw [ofInt_toInt hwlt]
  obtain ⟨heq, hmul⟩ := hAt_facts (toInt (zWord m)) hzr.1 hzr.2
  have huv : uVal (toInt (zWord m)) = q * q / 2 ^ 104 := by
    unfold uVal
    rw [hzq]
    have e : -(q : Int) * -(q : Int) = ((q * q : Nat) : Int) := by
      rw [Int.neg_mul_neg]
      omega
    rw [e]
    omega
  have hu_le : q * q / 2 ^ 104 ≤ Uc := by
    have := uVal_le (toInt (zWord m)) hzr.1 hzr.2
    rw [huv] at this
    exact this
  have hudm := Nat.div_add_mod (q * q) (2 ^ 104)
  have huml := Nat.mod_lt (q * q) (y := 2 ^ 104) (by omega)
  have hq_ge1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h0 | h
    · exfalso
      subst h0
      have hA46 : (46 : Int) ≤ (m : Int) - Sc := by simp only [Sc] at h1 ⊢; omega
      have hBmax : (m : Int) + Sc ≤ 34624238973196922243142627472244 := by
        simp only [MHI] at h2; simp only [Sc]; omega
      have h46 : (46 : Int) * 2 ^ 100 ≤ ((m : Int) - Sc) * 2 ^ 100 :=
        mul_le_mul_right_nonneg hA46 (by omega)
      omega
    · exact h
  obtain ⟨pw, plo, phi, psl, psh⟩ := pS4_facts hu_le
  obtain ⟨qw, qlo, qhi, qsl, qsh⟩ := qS5_facts hu_le
  rw [huv] at heq hmul
  generalize hw1 : pS4 (q * q / 2 ^ 104) = pword at heq hmul pw plo phi psl psh
  generalize hw2 : qS5 (q * q / 2 ^ 104) = qword at heq qw qlo qhi qsl qsh
  generalize hPP : evalPoly PPc ((q * q / 2 ^ 104 : Nat) : Int) = PPv at psl psh
  generalize hQQ : evalPoly QQc ((q * q / 2 ^ 104 : Nat) : Int) = QQv at qsl qsh
  have hxe : x1W (zWord m) = evmSdiv (evmMul pword (ofInt (toInt (zWord m)))) qword :=
    hx1.trans heq
  have hnum_neg : toInt (evmMul pword (ofInt (toInt (zWord m)))) < 0 := by
    rw [hmul, hzq]
    have h := mul_le_mul_left_nonneg (show (1 : Int) ≤ (q : Int) by omega)
      (show (0 : Int) ≤ toInt pword by omega)
    have e : toInt pword * -(q : Int) = -(toInt pword * (q : Int)) := Int.mul_neg _ _
    omega
  have hpz := pz_bound plo phi hzr.1 hzr.2
  have hX1v : toInt (x1W (zWord m)) =
      (((toInt pword * (q : Int)).toNat / (-toInt qword).toNat : Nat) : Int) := by
    rw [hxe, evmSdiv_neg_neg (evmMul_lt _ _) qw hnum_neg
      (by rw [hmul]; exact hpz.1) (by omega), hmul, hzq]
    have e : -(toInt pword * -(q : Int)) = toInt pword * (q : Int) := by
      rw [Int.mul_neg]
      omega
    rw [e]
  have hpq_pos : (0 : Int) ≤ toInt pword * (q : Int) :=
    Int.mul_nonneg (by omega) (by omega)
  have hX1_nn : (0 : Int) ≤ toInt (x1W (zWord m)) := by
    rw [hX1v]
    exact Int.natCast_nonneg _
  -- LOWER division bracket: pw q < (X1+1)(-qw)
  have hdm2 := Nat.div_add_mod (toInt pword * (q : Int)).toNat (-toInt qword).toNat
  have hml2 := Nat.mod_lt (toInt pword * (q : Int)).toNat
    (y := (-toInt qword).toNat) (by omega)
  have hX1lo : toInt pword * (q : Int) <
      (toInt (x1W (zWord m)) + 1) * (-toInt qword) := by
    rw [hX1v]
    have e : (((toInt pword * (q : Int)).toNat / (-toInt qword).toNat : Nat) : Int) + 1 =
        (((toInt pword * (q : Int)).toNat / (-toInt qword).toNat + 1 : Nat) : Int) := by
      omega
    rw [e]
    have e2 : (((toInt pword * (q : Int)).toNat / (-toInt qword).toNat + 1 : Nat) : Int) *
        (-toInt qword) =
        ((((toInt pword * (q : Int)).toNat / (-toInt qword).toNat + 1) *
          (-toInt qword).toNat : Nat) : Int) := by
      rw [Int.natCast_mul]
      have : ((-toInt qword).toNat : Int) = -toInt qword := by omega
      rw [this]
    rw [e2]
    have hexp : ((toInt pword * (q : Int)).toNat / (-toInt qword).toNat + 1) *
        (-toInt qword).toNat =
        (-toInt qword).toNat * ((toInt pword * (q : Int)).toNat / (-toInt qword).toNat) +
          (-toInt qword).toNat := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    omega
  clear heq hxe hmul hX1v hnum_neg hpz hx1 hzr hwlt hudm huml hzq hw1 hw2 hdm2 hml2
  generalize hXg : toInt (x1W (zWord m)) = X1v at hX1lo hX1_nn ⊢
  -- u-hat brackets in Int form
  have huI1 : ((q * q / 2 ^ 104 : Nat) : Int) * 2 ^ 104 ≤ (q : Int) * q := by
    have hudm := Nat.div_add_mod (q * q) (2 ^ 104)
    have e : (q : Int) * q = ((q * q : Nat) : Int) := by omega
    rw [e]
    omega
  -- orderings
  have hcastA : ((m - Sc : Nat) : Int) = (m : Int) - Sc := by omega
  have hcastB : ((m + Sc : Nat) : Int) = (m : Int) + Sc := by omega
  have hunle := un_le_dsq (d := m - Sc) (q := q) (u := q * q / 2 ^ 104)
    (B := m + Sc) (by omega)
    (by rw [hcastA, hcastB]; exact hq1) huI1
  have hordQ : ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly geB2 (m : Int) ≤
      evalPoly geA96 (m : Int) := by
    rw [evalB2_ge, evalA96_ge]
    rw [hcastA, hcastB] at hunle
    exact hunle
  -- wlo ordering (the Q-argument ordering on this side)
  have huI2 : (q : Int) * q ≤ ((q * q / 2 ^ 104 : Nat) : Int) * 2 ^ 104 + 2 ^ 104 - 1 := by
    have hudm := Nat.div_add_mod (q * q) (2 ^ 104)
    have huml := Nat.mod_lt (q * q) (y := 2 ^ 104) (by omega)
    have e : (q : Int) * q = ((q * q : Nat) : Int) := by omega
    rw [e]
    omega
  have hwloLt := wlo_lt_un (d := m - Sc) (q := q) (u := q * q / 2 ^ 104)
    (B := m + Sc) (by omega)
    (by omega) (by simp only [MHI] at h2; simp only [Sc] at *; omega)
    (by rw [hcastA, hcastB]; exact hq2)
    huI2
  have hordP : evalPoly geWLO (m : Int) ≤
      ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly geD8 (m : Int) := by
    rw [evalWLO_ge, evalD8_ge]
    rw [hcastA, hcastB] at hwloLt
    have e1 : ((q * q / 2 ^ 104 : Nat) : Int) * (8 * (((m : Int) + Sc) * ((m : Int) + Sc))) =
        8 * (((q * q / 2 ^ 104 : Nat) : Int) * (((m : Int) + Sc) * ((m : Int) + Sc))) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have e2 : (((m : Int) - Sc) * ((m : Int) - Sc)) * 2 ^ 99 =
        2 ^ 99 * (((m : Int) - Sc) * ((m : Int) - Sc)) := Int.mul_comm _ _
    omega
  -- box bounds
  have hB2nn : (0 : Int) ≤ evalPoly geB2 (m : Int) := by
    rw [evalB2_ge]
    exact Int.mul_nonneg (by simp only [Sc]; omega) (by simp only [Sc]; omega)
  have hD8nn : (0 : Int) ≤ evalPoly geD8 (m : Int) := by
    rw [evalD8_ge]
    refine Int.mul_nonneg (by omega) (Int.mul_nonneg ?_ ?_) <;>
      simp only [Sc] <;> omega
  have hu_lt_UB : ((q * q / 2 ^ 104 : Nat) : Int) ≤ 2333000000000000000000000000 := by
    simp only [Uc] at hu_le
    omega
  have hb1P : ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly geD8 (m : Int) ≤
      2333000000000000000000000000 * evalPoly geD8 (m : Int) :=
    mul_le_mul_right_nonneg hu_lt_UB hD8nn
  have hb2P : -(2333000000000000000000000000 * evalPoly geD8 (m : Int)) ≤
      evalPoly geWLO (m : Int) := by
    rw [evalWLO_ge, evalD8_ge]
    have hAB : ((m : Int) - Sc) * ((m : Int) + Sc) ≤
        ((m : Int) + Sc) * ((m : Int) + Sc) :=
      mul_le_mul_right_nonneg (by omega) (by simp only [Sc]; omega)
    have hsq : (0 : Int) ≤ (((m : Int) - Sc) * ((m : Int) - Sc)) := by
      refine Int.mul_nonneg ?_ ?_ <;> simp only [Sc] at h1 ⊢ <;> omega
    have hBB : (0 : Int) ≤ ((m : Int) + Sc) * ((m : Int) + Sc) := by
      refine Int.mul_nonneg ?_ ?_ <;> simp only [Sc] <;> omega
    generalize ((m : Int) - Sc) * ((m : Int) - Sc) = AA at *
    generalize ((m : Int) - Sc) * ((m : Int) + Sc) = AB at *
    generalize ((m : Int) + Sc) * ((m : Int) + Sc) = BB at *
    have h99 : (0 : Int) ≤ 2 ^ 99 * AA := Int.mul_nonneg (by omega) hsq
    omega
  have hBpos : (0 : Int) < (m : Int) + Sc := by simp only [Sc]; omega
  have hD8pos : (0 : Int) < evalPoly geD8 (m : Int) := by
    rw [evalD8_ge]
    exact Int.mul_pos (by omega) (Int.mul_pos hBpos hBpos)
  have hB2pos : (0 : Int) < evalPoly geB2 (m : Int) := by
    rw [evalB2_ge]
    exact Int.mul_pos hBpos hBpos
  have hb1Q : evalPoly geA96 (m : Int) ≤
      2333000000000000000000000000 * evalPoly geB2 (m : Int) := by
    have hws := geWS_nonneg (m := (m : Int))
      (by simp only [Sc] at h1; omega) (by simp only [MHI] at h2; omega)
    rw [evalWS_ge] at hws
    rw [evalA96_ge, evalB2_ge]
    omega
  have hb2Q : -(2333000000000000000000000000 * evalPoly geB2 (m : Int)) ≤
      ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly geB2 (m : Int) := by
    have h := Int.mul_nonneg (Int.natCast_nonneg (q * q / 2 ^ 104)) (by omega :
      (0 : Int) ≤ evalPoly geB2 (m : Int))
    have h2' : (0 : Int) ≤ 2333000000000000000000000000 * evalPoly geB2 (m : Int) :=
      Int.mul_nonneg (by omega) (by omega)
    omega
  -- divided-difference monotonicity, with the argument roles of the up-side swapped
  have hPanti := homEvalI_PPc_anti (n1 := evalPoly geA96 (m : Int))
    (n2 := ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly geB2 (m : Int))
    (D := evalPoly geB2 (m : Int)) hB2pos hordQ hb1Q hb2Q
  have hQmono := homEvalI_QQc_mono (n1 := ((q * q / 2 ^ 104 : Nat) : Int) *
      evalPoly geD8 (m : Int)) (n2 := evalPoly geWLO (m : Int))
    (D := evalPoly geD8 (m : Int)) hD8pos hordP hb1P hb2P
  -- collapse instances
  have hcolP : homEvalI PPc (((q * q / 2 ^ 104 : Nat) : Int) *
      evalPoly geB2 (m : Int)) (evalPoly geB2 (m : Int)) =
      evalPoly geB2 (m : Int) ^ 4 * PPv := by
    rw [show PPc = (8203564106909714963200842018493798951984754309521818719427488640634114742013119919947469548416190884842555317059682247072626112599280320512 : Int) :: PP3c from rfl,
      homEvalI_collapse, ← hPP]
    rfl
  have hcolP' : homEvalI PPc (((q * q / 2 ^ 104 : Nat) : Int) *
      evalPoly geB2 (m : Int)) (evalPoly geB2 (m : Int)) =
      PPv * evalPoly geB2 (m : Int) ^ 4 := by
    rw [hcolP]
    exact Int.mul_comm _ _
  have hcolQ : homEvalI QQc (((q * q / 2 ^ 104 : Nat) : Int) *
      evalPoly geD8 (m : Int)) (evalPoly geD8 (m : Int)) =
      evalPoly geD8 (m : Int) ^ 5 * QQv := by
    rw [show QQc = (-(2202127471863542086976841246818343354848349628124454549898853972183438719928614203693782484275214277955754824740140383208045055653095158108464873472 : Int)) :: QQ4c from rfl,
      homEvalI_collapse, ← hQQ]
    rfl
  have hcolQ' : homEvalI QQc (((q * q / 2 ^ 104 : Nat) : Int) *
      evalPoly geD8 (m : Int)) (evalPoly geD8 (m : Int)) =
      QQv * evalPoly geD8 (m : Int) ^ 5 := by
    rw [hcolQ]
    exact Int.mul_comm _ _
  have hB24 : (0 : Int) ≤ evalPoly geB2 (m : Int) ^ 4 := pow_nonneg' (by omega) 4
  have hD5nn : (0 : Int) ≤ evalPoly geD8 (m : Int) ^ 5 := pow_nonneg' (by omega) 5
  -- P upper comparison: PLOP(m) ≤ p-hat 2^358 (B²)^4
  have hPfin : evalPoly gePLOP (m : Int) ≤
      toInt pword * 2 ^ 358 * evalPoly geB2 (m : Int) ^ 4 := by
    rw [evalPLOP_ge]
    have s1P : homEvalI PPc (evalPoly geA96 (m : Int)) (evalPoly geB2 (m : Int)) ≤
        PPv * evalPoly geB2 (m : Int) ^ 4 := by
      rw [← hcolP']
      exact hPanti
    have s2P : (PPv - SLOPPc) * evalPoly geB2 (m : Int) ^ 4 ≤
        toInt pword * 2 ^ 358 * evalPoly geB2 (m : Int) ^ 4 :=
      mul_le_mul_right_nonneg (by omega) hB24
    have e1P : (PPv - SLOPPc) * evalPoly geB2 (m : Int) ^ 4 =
        PPv * evalPoly geB2 (m : Int) ^ 4 - SLOPPc * evalPoly geB2 (m : Int) ^ 4 :=
      Int.sub_mul _ _ _
    generalize hg1 : homEvalI PPc (evalPoly geA96 (m : Int))
      (evalPoly geB2 (m : Int)) = HS at s1P ⊢
    generalize hg2 : evalPoly geB2 (m : Int) ^ 4 = B4 at s1P s2P e1P ⊢
    generalize hg3 : PPv * B4 = PB4 at s1P e1P
    generalize hg4 : SLOPPc * B4 = SB4 at e1P ⊢
    generalize hg5 : (PPv - SLOPPc) * B4 = PSB at s2P e1P
    generalize hg6 : toInt pword * 2 ^ 358 * B4 = PW4 at s2P ⊢
    omega
  -- Q lower comparison: (-q-hat) 2^386 (8B²)^5 ≤ DLO(m)
  have hQfin : -toInt qword * 2 ^ 386 * evalPoly geD8 (m : Int) ^ 5 ≤
      evalPoly geDLO (m : Int) := by
    rw [evalDLO_ge]
    have s1Q : homEvalI QQc (evalPoly geWLO (m : Int)) (evalPoly geD8 (m : Int)) ≤
        QQv * evalPoly geD8 (m : Int) ^ 5 := by
      rw [← hcolQ']
      exact hQmono
    have s2Q : (QQv - SLOPQc) * evalPoly geD8 (m : Int) ^ 5 ≤
        toInt qword * 2 ^ 386 * evalPoly geD8 (m : Int) ^ 5 :=
      mul_le_mul_right_nonneg (by omega) hD5nn
    have e1Q : (QQv - SLOPQc) * evalPoly geD8 (m : Int) ^ 5 =
        QQv * evalPoly geD8 (m : Int) ^ 5 - SLOPQc * evalPoly geD8 (m : Int) ^ 5 :=
      Int.sub_mul _ _ _
    have e2Q : -toInt qword * 2 ^ 386 * evalPoly geD8 (m : Int) ^ 5 =
        -(toInt qword * 2 ^ 386 * evalPoly geD8 (m : Int) ^ 5) := by
      rw [Int.neg_mul, Int.neg_mul]
    generalize hg1 : homEvalI QQc (evalPoly geWLO (m : Int))
      (evalPoly geD8 (m : Int)) = HS at s1Q ⊢
    generalize hg2 : evalPoly geD8 (m : Int) ^ 5 = D5 at s1Q s2Q e1Q e2Q ⊢
    generalize hg3 : QQv * D5 = QD at s1Q e1Q
    generalize hg4 : SLOPQc * D5 = SD at e1Q ⊢
    generalize hg5 : (QQv - SLOPQc) * D5 = QSD at s2Q e1Q
    generalize hg6 : toInt qword * 2 ^ 386 * D5 = QW at s2Q e2Q
    generalize hg7 : -toInt qword * 2 ^ 386 * D5 = QWn at e2Q ⊢
    omega
  -- AZ bounds: 0 ≤ AZ(m) ≤ q (m + S)
  have hAZnn : (0 : Int) ≤ evalPoly geAZ (m : Int) := by
    rw [evalAZ_ge]
    simp only [Sc] at h1 ⊢
    simp only [MHI] at h2
    omega
  have hAZle : evalPoly geAZ (m : Int) ≤ (q : Int) * ((m : Int) + Sc) := by
    rw [evalAZ_ge]
    have hq2' := hq2
    have e : ((q : Int) + 1) * ((m : Int) + Sc) =
        (q : Int) * ((m : Int) + Sc) + ((m : Int) + Sc) := by
      rw [Int.add_mul, Int.one_mul]
    rw [e] at hq2'
    generalize (q : Int) * ((m : Int) + Sc) = QB at hq2' ⊢
    omega
  -- numerator chain: 2^99-free part, PLOP·AZ·B ≤ p-hat q 2^358 (B²)^5
  have hBnn : (0 : Int) ≤ (m : Int) + Sc := by simp only [Sc]; omega
  have hPWnn : (0 : Int) ≤ toInt pword * 2 ^ 358 * evalPoly geB2 (m : Int) ^ 4 :=
    Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) hB24
  have t1 : evalPoly gePLOP (m : Int) * evalPoly geAZ (m : Int) ≤
      toInt pword * 2 ^ 358 * evalPoly geB2 (m : Int) ^ 4 * evalPoly geAZ (m : Int) :=
    mul_le_mul_right_nonneg hPfin hAZnn
  have t1b : evalPoly gePLOP (m : Int) * evalPoly geAZ (m : Int) * ((m : Int) + Sc) ≤
      toInt pword * 2 ^ 358 * evalPoly geB2 (m : Int) ^ 4 * evalPoly geAZ (m : Int) *
        ((m : Int) + Sc) :=
    mul_le_mul_right_nonneg t1 hBnn
  have t2 : toInt pword * 2 ^ 358 * evalPoly geB2 (m : Int) ^ 4 *
      evalPoly geAZ (m : Int) ≤
      toInt pword * 2 ^ 358 * evalPoly geB2 (m : Int) ^ 4 *
        ((q : Int) * ((m : Int) + Sc)) :=
    mul_le_mul_left_nonneg hAZle hPWnn
  have t2b : toInt pword * 2 ^ 358 * evalPoly geB2 (m : Int) ^ 4 *
      evalPoly geAZ (m : Int) * ((m : Int) + Sc) ≤
      toInt pword * 2 ^ 358 * evalPoly geB2 (m : Int) ^ 4 *
        ((q : Int) * ((m : Int) + Sc)) * ((m : Int) + Sc) :=
    mul_le_mul_right_nonneg t2 hBnn
  have t34 : toInt pword * 2 ^ 358 * evalPoly geB2 (m : Int) ^ 4 *
      ((q : Int) * ((m : Int) + Sc)) * ((m : Int) + Sc) =
      toInt pword * (q : Int) * (2 ^ 358 * evalPoly geB2 (m : Int) ^ 5) := by
    rw [show evalPoly geB2 (m : Int) ^ 5 =
      evalPoly geB2 (m : Int) ^ 4 * evalPoly geB2 (m : Int) from by rw [Int.pow_succ]]
    rw [evalB2_ge]
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hTfin : evalPoly gePLOP (m : Int) * evalPoly geAZ (m : Int) * ((m : Int) + Sc) ≤
      toInt pword * (q : Int) * (2 ^ 358 * evalPoly geB2 (m : Int) ^ 5) := by
    refine Int.le_trans t1b ?_
    rw [← t34]
    exact t2b
  -- denominator chain: (p-hat q + 1) 2^442 (8B²)^5 ≤ (X1 + 1) 2^56 DLO
  have hFnn : (0 : Int) ≤ 2 ^ 442 * evalPoly geD8 (m : Int) ^ 5 :=
    Int.mul_nonneg (by omega) hD5nn
  have u2 : toInt pword * (q : Int) + 1 ≤ (X1v + 1) * -toInt qword := by
    have h := hX1lo
    generalize hg1 : toInt pword * (q : Int) = PQt at h ⊢
    generalize hg2 : (X1v + 1) * -toInt qword = XQt at h ⊢
    omega
  have u3 : (toInt pword * (q : Int) + 1) * (2 ^ 442 * evalPoly geD8 (m : Int) ^ 5) ≤
      (X1v + 1) * -toInt qword * (2 ^ 442 * evalPoly geD8 (m : Int) ^ 5) :=
    mul_le_mul_right_nonneg u2 hFnn
  have u4 : (X1v + 1) * -toInt qword * (2 ^ 442 * evalPoly geD8 (m : Int) ^ 5) =
      (X1v + 1) * (2 ^ 56 * (-toInt qword * 2 ^ 386 * evalPoly geD8 (m : Int) ^ 5)) := by
    rw [show (2 : Int) ^ 442 = 2 ^ 56 * 2 ^ 386 from by decide]
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have u1b : 2 ^ 56 * (-toInt qword * 2 ^ 386 * evalPoly geD8 (m : Int) ^ 5) ≤
      2 ^ 56 * evalPoly geDLO (m : Int) :=
    mul_le_mul_left_nonneg hQfin (by omega)
  have hX1p1 : (0 : Int) ≤ X1v + 1 := by omega
  have u5 : (X1v + 1) * (2 ^ 56 * (-toInt qword * 2 ^ 386 *
      evalPoly geD8 (m : Int) ^ 5)) ≤
      (X1v + 1) * (2 ^ 56 * evalPoly geDLO (m : Int)) :=
    mul_le_mul_left_nonneg u1b hX1p1
  have hRfin : (toInt pword * (q : Int) + 1) *
      (2 ^ 442 * evalPoly geD8 (m : Int) ^ 5) ≤
      (X1v + 1) * (2 ^ 56 * evalPoly geDLO (m : Int)) := by
    refine Int.le_trans ?_ u5
    rw [← u4]
    exact u3
  -- scale bridge: 2^442 (8B²)^5 = 2^457 (B²)^5
  have ebr : (2 : Int) ^ 442 * evalPoly geD8 (m : Int) ^ 5 =
      2 ^ 457 * evalPoly geB2 (m : Int) ^ 5 := by
    rw [evalD8_ge, evalB2_ge]
    rw [show ((8 : Int) * (((m : Int) + Sc) * ((m : Int) + Sc))) ^ 5 =
      32768 * ((((m : Int) + Sc) * ((m : Int) + Sc)) ^ 5) from by
        rw [Int.mul_pow]
        rw [show ((8 : Int) ^ 5) = 32768 from by decide]]
    rw [← Int.mul_assoc, show (2 : Int) ^ 442 * 32768 = 2 ^ 457 from by decide]
  have escale : toInt pword * (q : Int) * (2 ^ 442 * evalPoly geD8 (m : Int) ^ 5) =
      2 ^ 99 * (toInt pword * (q : Int) * (2 ^ 358 * evalPoly geB2 (m : Int) ^ 5)) := by
    rw [ebr]
    rw [show (2 : Int) ^ 457 = 2 ^ 99 * 2 ^ 358 from by decide]
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  -- final assembly
  rw [evalTN2b_ge, evalTD2b_ge]
  have egoal : X1v * (2 ^ 99 * (2 ^ 56 * evalPoly geDLO (m : Int))) =
      2 ^ 99 * (X1v * (2 ^ 56 * evalPoly geDLO (m : Int))) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [egoal]
  have edist : (X1v + 1) * (2 ^ 56 * evalPoly geDLO (m : Int)) =
      X1v * (2 ^ 56 * evalPoly geDLO (m : Int)) + 2 ^ 56 * evalPoly geDLO (m : Int) := by
    rw [Int.add_mul, Int.one_mul]
  have edist2 : (toInt pword * (q : Int) + 1) *
      (2 ^ 442 * evalPoly geD8 (m : Int) ^ 5) =
      toInt pword * (q : Int) * (2 ^ 442 * evalPoly geD8 (m : Int) ^ 5) +
        2 ^ 442 * evalPoly geD8 (m : Int) ^ 5 := by
    rw [Int.add_mul, Int.one_mul]
  generalize hgT : evalPoly gePLOP (m : Int) * evalPoly geAZ (m : Int) *
    ((m : Int) + Sc) = T at hTfin ⊢
  generalize hgDLO : evalPoly geDLO (m : Int) = DLO at hRfin edist ⊢
  generalize hgD5 : evalPoly geD8 (m : Int) ^ 5 = D5g at hRfin edist2 escale hD5nn
  generalize hgB5 : evalPoly geB2 (m : Int) ^ 5 = B5g at hTfin escale
  generalize hgPQ : toInt pword * (q : Int) = PQ at hTfin hRfin edist2 escale
  generalize hgPB : PQ * (2 ^ 358 * B5g) = PB at hTfin escale
  generalize hgPQD : PQ * (2 ^ 442 * D5g) = PQD at edist2 escale
  generalize hgRD : (PQ + 1) * (2 ^ 442 * D5g) = RD at hRfin edist2
  generalize hgXW : X1v * (2 ^ 56 * DLO) = XW at edist ⊢
  generalize hgXW1 : (X1v + 1) * (2 ^ 56 * DLO) = XW1 at hRfin edist
  omega

theorem evalA_lt (m : Nat) : evalPoly ltA (m : Int) = (Sc : Int) - m := by
  show (Sc : Int) + (m : Int) * (-1 + (m : Int) * 0) = _
  omega

theorem evalB_lt (m : Nat) : evalPoly ltB (m : Int) = (m : Int) + Sc := by
  show (Sc : Int) + (m : Int) * (1 + (m : Int) * 0) = _
  omega

theorem evalB2_lt (m : Nat) :
    evalPoly ltB2 (m : Int) = ((m : Int) + Sc) * ((m : Int) + Sc) := by
  show evalPoly (polyMul ltB ltB) (m : Int) = _
  rw [evalPoly_polyMul, evalB_lt]

theorem evalA2_lt (m : Nat) :
    evalPoly ltA2 (m : Int) = ((Sc : Int) - m) * ((Sc : Int) - m) := by
  show evalPoly (polyMul ltA ltA) (m : Int) = _
  rw [evalPoly_polyMul, evalA_lt]

theorem evalD8_lt (m : Nat) :
    evalPoly ltD8 (m : Int) = 8 * (((m : Int) + Sc) * ((m : Int) + Sc)) := by
  show evalPoly (polyScale 8 ltB2) (m : Int) = _
  rw [evalPoly_polyScale, evalB2_lt]

theorem evalA96_lt (m : Nat) :
    evalPoly ltA96 (m : Int) = 2 ^ 96 * (((Sc : Int) - m) * ((Sc : Int) - m)) := by
  show evalPoly (polyScale (2 ^ 96) ltA2) (m : Int) = _
  rw [evalPoly_polyScale, evalA2_lt]

theorem evalWLO_lt (m : Nat) :
    evalPoly ltWLO (m : Int) =
      2 ^ 99 * (((Sc : Int) - m) * ((Sc : Int) - m)) -
        ((Sc : Int) - m) * ((m : Int) + Sc) -
        8 * (((m : Int) + Sc) * ((m : Int) + Sc)) := by
  show evalPoly (polyAdd (polyAdd (polyScale (2 ^ 99) ltA2)
    (polyNeg (polyMul ltA ltB))) (polyScale (-8) ltB2)) (m : Int) = _
  rw [evalPoly_polyAdd, evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyNeg,
    evalPoly_polyMul, evalPoly_polyScale, evalA2_lt, evalA_lt, evalB_lt, evalB2_lt]
  omega

theorem evalTN_lt (m : Nat) :
    evalPoly ltTN (m : Int) =
      2 ^ 17 * ((((Sc : Int) - m) * (((m : Int) + Sc))) *
        homEvalI PPc (evalPoly ltWLO (m : Int)) (evalPoly ltD8 (m : Int))) := by
  show evalPoly (polyScale (2 ^ 17) (polyMul (polyMul ltA ltB) ltPPHwlo)) (m : Int) = _
  rw [evalPoly_polyScale, evalPoly_polyMul, evalPoly_polyMul, evalA_lt, evalB_lt]
  have h : evalPoly ltPPHwlo (m : Int) =
      homEvalI PPc (evalPoly ltWLO (m : Int)) (evalPoly ltD8 (m : Int)) := by
    show evalPoly (homPoly PPc ltWLO ltD8) (m : Int) = _
    exact evalPoly_homPoly PPc ltWLO ltD8 (m : Int)
  rw [h]

theorem evalTD_lt (m : Nat) :
    evalPoly ltTD (m : Int) =
      -homEvalI QQc (evalPoly ltA96 (m : Int)) (evalPoly ltB2 (m : Int)) := by
  show evalPoly (polyNeg ltQQHws) (m : Int) = _
  rw [evalPoly_polyNeg]
  have h : evalPoly ltQQHws (m : Int) =
      homEvalI QQc (evalPoly ltA96 (m : Int)) (evalPoly ltB2 (m : Int)) := by
    show evalPoly (homPoly QQc ltA96 ltB2) (m : Int) = _
    exact evalPoly_homPoly QQc ltA96 ltB2 (m : Int)
  rw [h]

theorem evalWS_lt (m : Nat) :
    evalPoly certLtWS (m : Int) =
      2333000000000000000000000000 * (((m : Int) + Sc) * ((m : Int) + Sc)) -
        2 ^ 96 * (((Sc : Int) - m) * ((Sc : Int) - m)) := by
  show evalPoly (polyAdd (polyScale UB ltB2) (polyScale (-(2 ^ 96)) ltA2)) (m : Int) = _
  rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyScale, evalB2_lt, evalA2_lt]
  show UB * _ + _ = _
  rw [show UB = (2333000000000000000000000000 : Int) from rfl]
  omega

theorem evalPLOP_lt (m : Nat) :
    evalPoly ltPLOP (m : Int) =
      homEvalI PPc (evalPoly ltA96 (m : Int)) (evalPoly ltB2 (m : Int)) -
        SLOPPc * evalPoly ltB2 (m : Int) ^ 4 := by
  show evalPoly (polyAdd ltPPHws (polyScale (-SLOPPc) (polyPow ltB2 4))) (m : Int) = _
  rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyPow]
  have h : evalPoly ltPPHws (m : Int) =
      homEvalI PPc (evalPoly ltA96 (m : Int)) (evalPoly ltB2 (m : Int)) := by
    show evalPoly (homPoly PPc ltA96 ltB2) (m : Int) = _
    exact evalPoly_homPoly PPc ltA96 ltB2 (m : Int)
  rw [h, Int.sub_eq_add_neg, Int.neg_mul]

theorem evalDLO_lt (m : Nat) :
    evalPoly ltDLO (m : Int) =
      -homEvalI QQc (evalPoly ltWLO (m : Int)) (evalPoly ltD8 (m : Int)) +
        SLOPQc * evalPoly ltD8 (m : Int) ^ 5 := by
  show evalPoly (polyAdd (polyNeg ltQQHwlo) (polyScale SLOPQc (polyPow ltD8 5))) (m : Int) = _
  rw [evalPoly_polyAdd, evalPoly_polyNeg, evalPoly_polyScale, evalPoly_polyPow]
  have h : evalPoly ltQQHwlo (m : Int) =
      homEvalI QQc (evalPoly ltWLO (m : Int)) (evalPoly ltD8 (m : Int)) := by
    show evalPoly (homPoly QQc ltWLO ltD8) (m : Int) = _
    exact evalPoly_homPoly QQc ltWLO ltD8 (m : Int)
  rw [h]

theorem evalAZ_lt (m : Nat) :
    evalPoly ltAZ (m : Int) = 2 ^ 100 * ((Sc : Int) - m) - ((m : Int) + Sc) := by
  show evalPoly (polyAdd (polyScale (2 ^ 100) ltA) (polyNeg ltB)) (m : Int) = _
  rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyNeg, evalA_lt, evalB_lt]
  have e : (2 : Int) ^ 100 * ((Sc : Int) - m) = 2 ^ 100 * (Sc : Int) - 2 ^ 100 * m := by
    rw [Int.mul_sub]
  omega

theorem evalTN2b_lt (m : Nat) :
    evalPoly ltTN2b (m : Int) =
      2 ^ 99 * (evalPoly ltPLOP (m : Int) * evalPoly ltAZ (m : Int) *
        ((m : Int) + Sc)) - 2 ^ 56 * evalPoly ltDLO (m : Int) := by
  show evalPoly (polyAdd (polyScale (2 ^ 99) ltTN2) (polyNeg ltTD2)) (m : Int) = _
  rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyNeg]
  have h1 : evalPoly ltTN2 (m : Int) =
      evalPoly ltPLOP (m : Int) * evalPoly ltAZ (m : Int) * ((m : Int) + Sc) := by
    show evalPoly (polyMul (polyMul ltPLOP ltAZ) ltB) (m : Int) = _
    rw [evalPoly_polyMul, evalPoly_polyMul, evalB_lt]
  have h2 : evalPoly ltTD2 (m : Int) = 2 ^ 56 * evalPoly ltDLO (m : Int) := by
    show evalPoly (polyScale (2 ^ 56) ltDLO) (m : Int) = _
    rw [evalPoly_polyScale]
  rw [h1, h2, Int.sub_eq_add_neg]

theorem evalTD2b_lt (m : Nat) :
    evalPoly ltTD2b (m : Int) = 2 ^ 99 * (2 ^ 56 * evalPoly ltDLO (m : Int)) := by
  show evalPoly (polyScale (2 ^ 99) ltTD2) (m : Int) = _
  rw [evalPoly_polyScale]
  have h2 : evalPoly ltTD2 (m : Int) = 2 ^ 56 * evalPoly ltDLO (m : Int) := by
    show evalPoly (polyScale (2 ^ 56) ltDLO) (m : Int) = _
    rw [evalPoly_polyScale]
  rw [h2]

/-- The pipeline magnitude sits below the upper certificate rational on the
`m < S` branch: `(-X1) · TD(m) ≤ TN(m) · 2^99`. -/
theorem bracket_lt_up {m : Nat} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) :
    -toInt (x1W (zWord m)) * evalPoly ltTD (m : Int) ≤
      evalPoly ltTN (m : Int) * 2 ^ 99 := by
  have hSge : m ≤ Sc := by simp only [Sc] at h2 ⊢; omega
  have hMHI : m < MHI := by simp only [MHI]; simp only [Sc] at h2; omega
  -- z and its division bracket
  obtain ⟨q, hzq, hq1, hq2⟩ := z_bracket_lt h1 hSge
  have hzr := zWord_range h1 hMHI
  have hwlt : zWord m < 2 ^ 256 := by unfold zWord; exact evmSdiv_lt _ _
  have hx1 : x1W (zWord m) = hAt (toInt (zWord m)) := by
    unfold hAt; rw [ofInt_toInt hwlt]
  obtain ⟨heq, hmul⟩ := hAt_facts (toInt (zWord m)) hzr.1 hzr.2
  -- u-hat and its division bracket
  have huv : uVal (toInt (zWord m)) = q * q / 2 ^ 104 := by
    unfold uVal
    rw [hzq]
    have e : (q : Int) * (q : Int) = ((q * q : Nat) : Int) := by omega
    rw [e]
    omega
  have hu_le : q * q / 2 ^ 104 ≤ Uc := by
    have := uVal_le (toInt (zWord m)) hzr.1 hzr.2
    rw [huv] at this
    exact this
  have hudm := Nat.div_add_mod (q * q) (2 ^ 104)
  have huml := Nat.mod_lt (q * q) (y := 2 ^ 104) (by omega)
  -- the quotient is at least one on this branch
  have hq_ge1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h0 | h
    · exfalso
      subst h0
      have hA46 : (46 : Int) ≤ (Sc : Int) - m := by simp only [Sc] at h2 ⊢; omega
      have hBmax : (m : Int) + Sc ≤ 34624238973196922243142627472244 := by
        simp only [MHI] at hMHI; simp only [Sc]; omega
      have h46 : (46 : Int) * 2 ^ 100 ≤ ((Sc : Int) - m) * 2 ^ 100 :=
        mul_le_mul_right_nonneg hA46 (by omega)
      omega
    · exact h
  -- stage sandwiches at u-hat, with every heavy term made opaque
  obtain ⟨pw, plo, phi, psl, psh⟩ := pS4_facts hu_le
  obtain ⟨qw, qlo, qhi, qsl, qsh⟩ := qS5_facts hu_le
  rw [huv] at heq hmul
  generalize hw1 : pS4 (q * q / 2 ^ 104) = pword at heq hmul pw plo phi psl psh
  generalize hw2 : qS5 (q * q / 2 ^ 104) = qword at heq qw qlo qhi qsl qsh
  generalize hPP : evalPoly PPc ((q * q / 2 ^ 104 : Nat) : Int) = PPv at psl psh
  generalize hQQ : evalPoly QQc ((q * q / 2 ^ 104 : Nat) : Int) = QQv at qsl qsh
  have hxe : x1W (zWord m) = evmSdiv (evmMul pword (ofInt (toInt (zWord m)))) qword :=
    hx1.trans heq
  have hpq_pos : (0 : Int) ≤ toInt pword * (q : Int) :=
    Int.mul_nonneg (by omega) (by omega)
  have hnum_nn : (0 : Int) ≤ toInt (evmMul pword (ofInt (toInt (zWord m)))) := by
    rw [hmul, hzq]
    exact hpq_pos
  have hX1v : toInt (x1W (zWord m)) =
      -((((toInt pword * (q : Int)).toNat / (-toInt qword).toNat : Nat) : Int)) := by
    rw [hxe, evmSdiv_pos_neg (evmMul_lt _ _) qw hnum_nn (by omega), hmul, hzq]
  have hX1neg : -toInt (x1W (zWord m)) =
      (((toInt pword * (q : Int)).toNat / (-toInt qword).toNat : Nat) : Int) := by
    rw [hX1v, Int.neg_neg]
  have hX1_nn : (0 : Int) ≤ -toInt (x1W (zWord m)) := by
    rw [hX1neg]
    exact Int.natCast_nonneg _
  -- the division bracket for the magnitude of X1
  have hdiv := Nat.div_mul_le_self (toInt pword * (q : Int)).toNat (-toInt qword).toNat
  have hX1br : -toInt (x1W (zWord m)) * (-toInt qword) ≤ toInt pword * (q : Int) := by
    rw [hX1neg]
    have e : (((toInt pword * (q : Int)).toNat / (-toInt qword).toNat : Nat) : Int) *
        (-toInt qword) =
        ((((toInt pword * (q : Int)).toNat / (-toInt qword).toNat) *
          (-toInt qword).toNat : Nat) : Int) := by
      rw [Int.natCast_mul]
      have : ((-toInt qword).toNat : Int) = -toInt qword := by omega
      rw [this]
    rw [e]
    omega
  clear heq hxe hmul hX1v hnum_nn hdiv hx1 hzr hwlt hudm huml hzq hw1 hw2 hX1neg
  generalize hXg : -toInt (x1W (zWord m)) = X1v at hX1br hX1_nn ⊢
  -- value abbreviations
  have huI1 : ((q * q / 2 ^ 104 : Nat) : Int) * 2 ^ 104 ≤ (q : Int) * q := by
    have e : (q : Int) * q = ((q * q : Nat) : Int) := by omega
    rw [e]
    omega
  have huI2 : (q : Int) * q ≤ ((q * q / 2 ^ 104 : Nat) : Int) * 2 ^ 104 + 2 ^ 104 - 1 := by
    have e : (q : Int) * q = ((q * q : Nat) : Int) := by omega
    rw [e]
    omega
  -- ordering of the P arguments: WLO ≤ u-hat · D8
  have hcastA : ((Sc - m : Nat) : Int) = (Sc : Int) - m := by omega
  have hcastB : ((m + Sc : Nat) : Int) = (m : Int) + Sc := by omega
  have hwloLt := wlo_lt_un (d := Sc - m) (q := q) (u := q * q / 2 ^ 104)
    (B := m + Sc) (by omega)
    (by simp only [MLO] at h1; omega) (by simp only [Sc] at *; omega)
    (by rw [hcastA, hcastB]; exact hq2)
    huI2
  have hordP : evalPoly ltWLO (m : Int) ≤
      ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly ltD8 (m : Int) := by
    rw [evalWLO_lt, evalD8_lt]
    rw [hcastA, hcastB] at hwloLt
    have e1 : ((q * q / 2 ^ 104 : Nat) : Int) * (8 * (((m : Int) + Sc) * ((m : Int) + Sc))) =
        8 * (((q * q / 2 ^ 104 : Nat) : Int) * (((m : Int) + Sc) * ((m : Int) + Sc))) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have e2 : (((Sc : Int) - m) * ((Sc : Int) - m)) * 2 ^ 99 =
        2 ^ 99 * (((Sc : Int) - m) * ((Sc : Int) - m)) := Int.mul_comm _ _
    omega
  -- ordering of the Q arguments: u-hat · B2 ≤ A96
  have hunle := un_le_dsq (d := Sc - m) (q := q) (u := q * q / 2 ^ 104)
    (B := m + Sc) (by simp only [MLO] at h1; omega)
    (by rw [hcastA, hcastB]; exact hq1) huI1
  have hordQ : ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly ltB2 (m : Int) ≤
      evalPoly ltA96 (m : Int) := by
    rw [evalB2_lt, evalA96_lt]
    rw [hcastA, hcastB] at hunle
    exact hunle
  -- box bounds
  have hB2nn : (0 : Int) ≤ evalPoly ltB2 (m : Int) := by
    rw [evalB2_lt]
    exact Int.mul_nonneg (by simp only [Sc]; omega) (by simp only [Sc]; omega)
  have hD8nn : (0 : Int) ≤ evalPoly ltD8 (m : Int) := by
    rw [evalD8_lt]
    refine Int.mul_nonneg (by omega) (Int.mul_nonneg ?_ ?_) <;>
      simp only [Sc] <;> omega
  have hu_lt_UB : ((q * q / 2 ^ 104 : Nat) : Int) ≤ 2333000000000000000000000000 := by
    simp only [Uc] at hu_le
    omega
  have hb1P : ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly ltD8 (m : Int) ≤
      2333000000000000000000000000 * evalPoly ltD8 (m : Int) :=
    mul_le_mul_right_nonneg hu_lt_UB hD8nn
  have hb2P : -(2333000000000000000000000000 * evalPoly ltD8 (m : Int)) ≤
      evalPoly ltWLO (m : Int) := by
    rw [evalWLO_lt, evalD8_lt]
    have hAB : ((Sc : Int) - m) * ((m : Int) + Sc) ≤
        ((m : Int) + Sc) * ((m : Int) + Sc) :=
      mul_le_mul_right_nonneg (by omega) (by simp only [Sc]; omega)
    have hsq : (0 : Int) ≤ (((Sc : Int) - m) * ((Sc : Int) - m)) := by
      refine Int.mul_nonneg ?_ ?_ <;> simp only [Sc] at h2 ⊢ <;> omega
    have hBB : (0 : Int) ≤ ((m : Int) + Sc) * ((m : Int) + Sc) := by
      refine Int.mul_nonneg ?_ ?_ <;> simp only [Sc] <;> omega
    generalize ((Sc : Int) - m) * ((Sc : Int) - m) = AA at *
    generalize ((Sc : Int) - m) * ((m : Int) + Sc) = AB at *
    generalize ((m : Int) + Sc) * ((m : Int) + Sc) = BB at *
    have h99 : (0 : Int) ≤ 2 ^ 99 * AA := Int.mul_nonneg (by omega) hsq
    omega
  -- P comparison through collapse and monotonicity
  have hcolP : homEvalI PPc (((q * q / 2 ^ 104 : Nat) : Int) *
      evalPoly ltD8 (m : Int)) (evalPoly ltD8 (m : Int)) =
      evalPoly ltD8 (m : Int) ^ 4 * PPv := by
    rw [show PPc = (8203564106909714963200842018493798951984754309521818719427488640634114742013119919947469548416190884842555317059682247072626112599280320512 : Int) :: PP3c from rfl,
      homEvalI_collapse, ← hPP]
    rfl
  have hBpos : (0 : Int) < (m : Int) + Sc := by simp only [Sc]; omega
  have hD8pos : (0 : Int) < evalPoly ltD8 (m : Int) := by
    rw [evalD8_lt]
    exact Int.mul_pos (by omega) (Int.mul_pos hBpos hBpos)
  have hB2pos : (0 : Int) < evalPoly ltB2 (m : Int) := by
    rw [evalB2_lt]
    exact Int.mul_pos hBpos hBpos
  have hPanti := homEvalI_PPc_anti (n1 := ((q * q / 2 ^ 104 : Nat) : Int) *
      evalPoly ltD8 (m : Int)) (n2 := evalPoly ltWLO (m : Int))
    (D := evalPoly ltD8 (m : Int)) hD8pos hordP hb1P hb2P
  have hPfin : toInt pword * 2 ^ 358 * evalPoly ltD8 (m : Int) ^ 4 ≤
      homEvalI PPc (evalPoly ltWLO (m : Int)) (evalPoly ltD8 (m : Int)) := by
    have hD84 : (0 : Int) ≤ evalPoly ltD8 (m : Int) ^ 4 := pow_nonneg' (by omega) 4
    have s1 : toInt pword * 2 ^ 358 * evalPoly ltD8 (m : Int) ^ 4 ≤
        PPv * evalPoly ltD8 (m : Int) ^ 4 :=
      mul_le_mul_right_nonneg psh hD84
    have e1 : PPv * evalPoly ltD8 (m : Int) ^ 4 =
        evalPoly ltD8 (m : Int) ^ 4 * PPv := Int.mul_comm _ _
    generalize hg1 : homEvalI PPc (((q * q / 2 ^ 104 : Nat) : Int) *
      evalPoly ltD8 (m : Int)) (evalPoly ltD8 (m : Int)) = HU at hPanti hcolP
    generalize hg2 : homEvalI PPc (evalPoly ltWLO (m : Int))
      (evalPoly ltD8 (m : Int)) = HW at hPanti ⊢
    generalize hg3 : PPv * evalPoly ltD8 (m : Int) ^ 4 = P1 at s1 e1
    generalize hg4 : evalPoly ltD8 (m : Int) ^ 4 * PPv = P2 at e1 hcolP
    generalize hg5 : toInt pword * 2 ^ 358 * evalPoly ltD8 (m : Int) ^ 4 = P0 at s1 ⊢
    omega
  -- Q comparison
  have hb1Q : evalPoly ltA96 (m : Int) ≤
      2333000000000000000000000000 * evalPoly ltB2 (m : Int) := by
    have hws := ltWS_nonneg (m := (m : Int))
      (by simp only [MLO] at h1; omega) (by simp only [Sc] at h2; omega)
    rw [evalWS_lt] at hws
    rw [evalA96_lt, evalB2_lt]
    omega
  have hb2Q : -(2333000000000000000000000000 * evalPoly ltB2 (m : Int)) ≤
      ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly ltB2 (m : Int) := by
    have h := Int.mul_nonneg (Int.natCast_nonneg (q * q / 2 ^ 104)) (by omega :
      (0 : Int) ≤ evalPoly ltB2 (m : Int))
    have h2' : (0 : Int) ≤ 2333000000000000000000000000 * evalPoly ltB2 (m : Int) :=
      Int.mul_nonneg (by omega) (by omega)
    omega
  have hQmono := homEvalI_QQc_mono (n1 := evalPoly ltA96 (m : Int))
    (n2 := ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly ltB2 (m : Int))
    (D := evalPoly ltB2 (m : Int)) hB2pos hordQ hb1Q hb2Q
  have hcolQ : homEvalI QQc (((q * q / 2 ^ 104 : Nat) : Int) *
      evalPoly ltB2 (m : Int)) (evalPoly ltB2 (m : Int)) =
      evalPoly ltB2 (m : Int) ^ 5 * QQv := by
    rw [show QQc = (-(2202127471863542086976841246818343354848349628124454549898853972183438719928614203693782484275214277955754824740140383208045055653095158108464873472 : Int)) :: QQ4c from rfl,
      homEvalI_collapse, ← hQQ]
    rfl
  have hQfin : -homEvalI QQc (evalPoly ltA96 (m : Int)) (evalPoly ltB2 (m : Int)) ≤
      -toInt qword * 2 ^ 386 * evalPoly ltB2 (m : Int) ^ 5 := by
    have hB25 : (0 : Int) ≤ evalPoly ltB2 (m : Int) ^ 5 := pow_nonneg' (by omega) 5
    have s1 : evalPoly ltB2 (m : Int) ^ 5 * QQv ≤
        homEvalI QQc (evalPoly ltA96 (m : Int)) (evalPoly ltB2 (m : Int)) := by
      rw [← hcolQ]
      exact hQmono
    have s2 : toInt qword * 2 ^ 386 * evalPoly ltB2 (m : Int) ^ 5 ≤
        QQv * evalPoly ltB2 (m : Int) ^ 5 :=
      mul_le_mul_right_nonneg qsh hB25
    have e1 : QQv * evalPoly ltB2 (m : Int) ^ 5 =
        evalPoly ltB2 (m : Int) ^ 5 * QQv := Int.mul_comm _ _
    have e2 : -toInt qword * 2 ^ 386 * evalPoly ltB2 (m : Int) ^ 5 =
        -(toInt qword * 2 ^ 386 * evalPoly ltB2 (m : Int) ^ 5) := by
      rw [Int.neg_mul, Int.neg_mul]
    generalize hg1 : homEvalI QQc (evalPoly ltA96 (m : Int))
      (evalPoly ltB2 (m : Int)) = HW at s1 ⊢
    generalize hg2 : evalPoly ltB2 (m : Int) ^ 5 = B5 at s1 s2 e1 e2 hB25 ⊢
    generalize hg3 : QQv * B5 = Q1 at s2 e1
    generalize hg4 : B5 * QQv = Q2 at e1 s1
    generalize hg5 : toInt qword * 2 ^ 386 * B5 = Q0 at s2 e2
    generalize hg6 : -toInt qword * 2 ^ 386 * B5 = Q0n at e2 ⊢
    omega
  -- final assembly
  rw [evalTD_lt, evalTN_lt]
  generalize hPHV : homEvalI PPc (evalPoly ltWLO (m : Int))
    (evalPoly ltD8 (m : Int)) = PHV at hPfin ⊢
  generalize hQHVg : homEvalI QQc (evalPoly ltA96 (m : Int))
    (evalPoly ltB2 (m : Int)) = QHV at hQfin ⊢
  have hD8e := evalD8_lt m
  have hB2e := evalB2_lt m
  generalize hD8g : evalPoly ltD8 (m : Int) = D8v at hPfin hD8e
  generalize hB2g : evalPoly ltB2 (m : Int) = B2v at hQfin hB2e
  have hqpos : (0 : Int) < -toInt qword := by omega
  have hppos : (0 : Int) ≤ toInt pword := by omega
  have hApos : (0 : Int) ≤ (Sc : Int) - m := by simp only [Sc] at h2 ⊢; omega
  have hB25 : (0 : Int) ≤ B2v ^ 5 := by
    rw [hB2e]
    exact pow_nonneg' (Int.mul_nonneg (by omega) (by omega)) 5
  have hD84 : (0 : Int) ≤ D8v ^ 4 := by
    rw [hD8e]
    refine pow_nonneg' (Int.mul_nonneg (by omega) (Int.mul_nonneg ?_ ?_)) 4 <;>
      simp only [Sc] <;> omega
  -- step 1: X1v (-QHV) ≤ X1v ((-qword) 2^386 B2v^5)
  have s1 : X1v * -QHV ≤ X1v * (-toInt qword * 2 ^ 386 * B2v ^ 5) := by
    have h := mul_le_mul_left_nonneg hQfin hX1_nn
    exact h
  -- step 2: pull the division bracket through
  have s2 : X1v * (-toInt qword * 2 ^ 386 * B2v ^ 5) ≤
      toInt pword * (q : Int) * (2 ^ 386 * B2v ^ 5) := by
    have e1 : X1v * (-toInt qword * 2 ^ 386 * B2v ^ 5) =
        (X1v * -toInt qword) * (2 ^ 386 * B2v ^ 5) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have hf : (0 : Int) ≤ 2 ^ 386 * B2v ^ 5 := Int.mul_nonneg (by omega) hB25
    have h := mul_le_mul_right_nonneg hX1br hf
    omega
  -- step 3: multiply by B and use the z bracket
  have s3 : toInt pword * (q : Int) * (2 ^ 386 * B2v ^ 5) * ((m : Int) + Sc) ≤
      toInt pword * (((Sc : Int) - m) * 2 ^ 100) * (2 ^ 386 * B2v ^ 5) := by
    have e1 : toInt pword * (q : Int) * (2 ^ 386 * B2v ^ 5) * ((m : Int) + Sc) =
        (toInt pword * (2 ^ 386 * B2v ^ 5)) * ((q : Int) * ((m : Int) + Sc)) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have e2 : toInt pword * (((Sc : Int) - m) * 2 ^ 100) * (2 ^ 386 * B2v ^ 5) =
        (toInt pword * (2 ^ 386 * B2v ^ 5)) * (((Sc : Int) - m) * 2 ^ 100) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have hf : (0 : Int) ≤ toInt pword * (2 ^ 386 * B2v ^ 5) :=
      Int.mul_nonneg hppos (Int.mul_nonneg (by omega) hB25)
    have h := mul_le_mul_left_nonneg hq1 hf
    omega
  -- step 4: bring in the P bound
  have s4 : toInt pword * (((Sc : Int) - m) * 2 ^ 100) * (2 ^ 386 * B2v ^ 5) *
      (2 ^ 358 * D8v ^ 4) ≤
      PHV * (((Sc : Int) - m) * (2 ^ 486 * B2v ^ 5)) := by
    have e1 : toInt pword * (((Sc : Int) - m) * 2 ^ 100) * (2 ^ 386 * B2v ^ 5) *
        (2 ^ 358 * D8v ^ 4) =
        (toInt pword * 2 ^ 358 * D8v ^ 4) *
          (((Sc : Int) - m) * (2 ^ 100 * 2 ^ 386 * B2v ^ 5)) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have hf : (0 : Int) ≤ ((Sc : Int) - m) * (2 ^ 100 * 2 ^ 386 * B2v ^ 5) :=
      Int.mul_nonneg hApos (Int.mul_nonneg (by omega) hB25)
    have h := mul_le_mul_right_nonneg hPfin hf
    have e2 : PHV * (((Sc : Int) - m) * (2 ^ 100 * 2 ^ 386 * B2v ^ 5)) =
        PHV * (((Sc : Int) - m) * (2 ^ 486 * B2v ^ 5)) := by
      rw [show ((2 : Int) ^ 100 * 2 ^ 386) = 2 ^ 486 from by decide]
    omega
  -- multiplied chain and cancellation
  have hD84pos : (0 : Int) < D8v ^ 4 := by
    rw [hD8e]
    refine pow_pos' (Int.mul_pos (by omega) (Int.mul_pos hBpos hBpos)) 4
  have hMpos : (0 : Int) < ((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4) :=
    Int.mul_pos hBpos (Int.mul_pos (by omega) hD84pos)
  have hMnn : (0 : Int) ≤ ((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4) := by omega
  have k1 : X1v * -QHV * (((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4)) ≤
      X1v * (-toInt qword * 2 ^ 386 * B2v ^ 5) *
        (((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4)) :=
    mul_le_mul_right_nonneg s1 hMnn
  have k2 : X1v * (-toInt qword * 2 ^ 386 * B2v ^ 5) *
      (((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4)) ≤
      toInt pword * (q : Int) * (2 ^ 386 * B2v ^ 5) *
        (((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4)) :=
    mul_le_mul_right_nonneg s2 hMnn
  have k3 : toInt pword * (q : Int) * (2 ^ 386 * B2v ^ 5) *
      (((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4)) =
      toInt pword * (q : Int) * (2 ^ 386 * B2v ^ 5) * ((m : Int) + Sc) *
        (2 ^ 358 * D8v ^ 4) := by
    simp only [Int.mul_assoc]
  have k4 : toInt pword * (q : Int) * (2 ^ 386 * B2v ^ 5) * ((m : Int) + Sc) *
      (2 ^ 358 * D8v ^ 4) ≤
      toInt pword * (((Sc : Int) - m) * 2 ^ 100) * (2 ^ 386 * B2v ^ 5) *
        (2 ^ 358 * D8v ^ 4) :=
    mul_le_mul_right_nonneg s3 (Int.mul_nonneg (by omega) (by omega))
  have k6 : 2 ^ 17 * (((Sc : Int) - m) * ((m : Int) + Sc) * PHV) * 2 ^ 99 *
      (((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4)) =
      PHV * (((Sc : Int) - m) * (2 ^ 486 * B2v ^ 5)) := by
    rw [hD8e, hB2e]
    rw [show ((8 : Int) * (((m : Int) + Sc) * ((m : Int) + Sc))) ^ 4 =
      4096 * (((m : Int) + Sc) * ((m : Int) + Sc)) ^ 4 from by
        rw [Int.mul_pow]
        rw [show ((8 : Int) ^ 4) = 4096 from by decide]]
    rw [show (((m : Int) + Sc) * ((m : Int) + Sc)) ^ 5 =
      (((m : Int) + Sc) * ((m : Int) + Sc)) ^ 4 *
        (((m : Int) + Sc) * ((m : Int) + Sc)) from by
        rw [Int.pow_succ]]
    have hAC : 2 ^ 17 * (((Sc : Int) - m) * ((m : Int) + Sc) * PHV) * 2 ^ 99 *
        (((m : Int) + Sc) * (2 ^ 358 * (4096 * (((m : Int) + Sc) * ((m : Int) + Sc)) ^ 4))) =
        (2 ^ 17 * 2 ^ 99 * 2 ^ 358 * 4096) *
          (PHV * (((Sc : Int) - m) * ((((m : Int) + Sc) * ((m : Int) + Sc)) ^ 4 *
            (((m : Int) + Sc) * ((m : Int) + Sc))))) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [hAC, show ((2 : Int) ^ 17 * 2 ^ 99 * 2 ^ 358 * 4096) = 2 ^ 486 from by decide]
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have key : X1v * -QHV * (((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4)) ≤
      2 ^ 17 * (((Sc : Int) - m) * ((m : Int) + Sc) * PHV) * 2 ^ 99 *
        (((m : Int) + Sc) * (2 ^ 358 * D8v ^ 4)) := by
    rw [k6]
    omega
  exact Int.le_of_mul_le_mul_right key hMpos

/-- The pipeline magnitude sits above the lower certificate rational on the
`m < S` branch: `TN2b(m) · 2^99 ≤ (-X1) · TD2b(m)`. -/
theorem bracket_lt_lo {m : Nat} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) :
    evalPoly ltTN2b (m : Int) * 2 ^ 99 ≤
      -toInt (x1W (zWord m)) * evalPoly ltTD2b (m : Int) := by
  have hSge : m ≤ Sc := by simp only [Sc] at h2 ⊢; omega
  have hMHI : m < MHI := by simp only [MHI]; simp only [Sc] at h2; omega
  obtain ⟨q, hzq, hq1, hq2⟩ := z_bracket_lt h1 hSge
  have hzr := zWord_range h1 hMHI
  have hwlt : zWord m < 2 ^ 256 := by unfold zWord; exact evmSdiv_lt _ _
  have hx1 : x1W (zWord m) = hAt (toInt (zWord m)) := by
    unfold hAt; rw [ofInt_toInt hwlt]
  obtain ⟨heq, hmul⟩ := hAt_facts (toInt (zWord m)) hzr.1 hzr.2
  have huv : uVal (toInt (zWord m)) = q * q / 2 ^ 104 := by
    unfold uVal
    rw [hzq]
    have e : (q : Int) * (q : Int) = ((q * q : Nat) : Int) := by omega
    rw [e]
    omega
  have hu_le : q * q / 2 ^ 104 ≤ Uc := by
    have := uVal_le (toInt (zWord m)) hzr.1 hzr.2
    rw [huv] at this
    exact this
  have hq_ge1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h0 | h
    · exfalso
      subst h0
      have hA46 : (46 : Int) ≤ (Sc : Int) - m := by simp only [Sc] at h2 ⊢; omega
      have hBmax : (m : Int) + Sc ≤ 34624238973196922243142627472244 := by
        simp only [MHI] at hMHI; simp only [Sc]; omega
      have h46 : (46 : Int) * 2 ^ 100 ≤ ((Sc : Int) - m) * 2 ^ 100 :=
        mul_le_mul_right_nonneg hA46 (by omega)
      omega
    · exact h
  obtain ⟨pw, plo, phi, psl, psh⟩ := pS4_facts hu_le
  obtain ⟨qw, qlo, qhi, qsl, qsh⟩ := qS5_facts hu_le
  rw [huv] at heq hmul
  generalize hw1 : pS4 (q * q / 2 ^ 104) = pword at heq hmul pw plo phi psl psh
  generalize hw2 : qS5 (q * q / 2 ^ 104) = qword at heq qw qlo qhi qsl qsh
  generalize hPP : evalPoly PPc ((q * q / 2 ^ 104 : Nat) : Int) = PPv at psl psh
  generalize hQQ : evalPoly QQc ((q * q / 2 ^ 104 : Nat) : Int) = QQv at qsl qsh
  have hxe : x1W (zWord m) = evmSdiv (evmMul pword (ofInt (toInt (zWord m)))) qword :=
    hx1.trans heq
  have hpq_pos : (0 : Int) ≤ toInt pword * (q : Int) :=
    Int.mul_nonneg (by omega) (by omega)
  have hnum_nn : (0 : Int) ≤ toInt (evmMul pword (ofInt (toInt (zWord m)))) := by
    rw [hmul, hzq]
    exact hpq_pos
  have hX1v : toInt (x1W (zWord m)) =
      -((((toInt pword * (q : Int)).toNat / (-toInt qword).toNat : Nat) : Int)) := by
    rw [hxe, evmSdiv_pos_neg (evmMul_lt _ _) qw hnum_nn (by omega), hmul, hzq]
  have hX1neg : -toInt (x1W (zWord m)) =
      (((toInt pword * (q : Int)).toNat / (-toInt qword).toNat : Nat) : Int) := by
    rw [hX1v, Int.neg_neg]
  have hX1_nn : (0 : Int) ≤ -toInt (x1W (zWord m)) := by
    rw [hX1neg]
    exact Int.natCast_nonneg _
  -- LOWER division bracket: pw q < (-X1 + 1)(-qw)
  have hdm2 := Nat.div_add_mod (toInt pword * (q : Int)).toNat (-toInt qword).toNat
  have hml2 := Nat.mod_lt (toInt pword * (q : Int)).toNat
    (y := (-toInt qword).toNat) (by omega)
  have hX1lo : toInt pword * (q : Int) <
      (-toInt (x1W (zWord m)) + 1) * (-toInt qword) := by
    rw [hX1neg]
    have e : (((toInt pword * (q : Int)).toNat / (-toInt qword).toNat : Nat) : Int) + 1 =
        (((toInt pword * (q : Int)).toNat / (-toInt qword).toNat + 1 : Nat) : Int) := by
      omega
    rw [e]
    have e2 : (((toInt pword * (q : Int)).toNat / (-toInt qword).toNat + 1 : Nat) : Int) *
        (-toInt qword) =
        ((((toInt pword * (q : Int)).toNat / (-toInt qword).toNat + 1) *
          (-toInt qword).toNat : Nat) : Int) := by
      rw [Int.natCast_mul]
      have : ((-toInt qword).toNat : Int) = -toInt qword := by omega
      rw [this]
    rw [e2]
    have hexp : ((toInt pword * (q : Int)).toNat / (-toInt qword).toNat + 1) *
        (-toInt qword).toNat =
        (-toInt qword).toNat * ((toInt pword * (q : Int)).toNat / (-toInt qword).toNat) +
          (-toInt qword).toNat := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    omega
  clear heq hxe hmul hX1v hnum_nn hx1 hzr hwlt hzq hw1 hw2 hdm2 hml2 hX1neg
  generalize hXg : -toInt (x1W (zWord m)) = X1v at hX1lo hX1_nn ⊢
  -- u-hat brackets in Int form
  have huI1 : ((q * q / 2 ^ 104 : Nat) : Int) * 2 ^ 104 ≤ (q : Int) * q := by
    have e : (q : Int) * q = ((q * q : Nat) : Int) := by omega
    rw [e]
    omega
  have huI2 : (q : Int) * q ≤ ((q * q / 2 ^ 104 : Nat) : Int) * 2 ^ 104 + 2 ^ 104 - 1 := by
    have e : (q : Int) * q = ((q * q : Nat) : Int) := by omega
    rw [e]
    omega
  -- orderings
  have hcastA : ((Sc - m : Nat) : Int) = (Sc : Int) - m := by omega
  have hcastB : ((m + Sc : Nat) : Int) = (m : Int) + Sc := by omega
  have hunle := un_le_dsq (d := Sc - m) (q := q) (u := q * q / 2 ^ 104)
    (B := m + Sc) (by simp only [MLO] at h1; omega)
    (by rw [hcastA, hcastB]; exact hq1) huI1
  have hordQ : ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly ltB2 (m : Int) ≤
      evalPoly ltA96 (m : Int) := by
    rw [evalB2_lt, evalA96_lt]
    rw [hcastA, hcastB] at hunle
    exact hunle
  have hwloLt := wlo_lt_un (d := Sc - m) (q := q) (u := q * q / 2 ^ 104)
    (B := m + Sc) (by omega)
    (by simp only [MLO] at h1; omega) (by simp only [Sc] at *; omega)
    (by rw [hcastA, hcastB]; exact hq2)
    huI2
  have hordP : evalPoly ltWLO (m : Int) ≤
      ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly ltD8 (m : Int) := by
    rw [evalWLO_lt, evalD8_lt]
    rw [hcastA, hcastB] at hwloLt
    have e1 : ((q * q / 2 ^ 104 : Nat) : Int) * (8 * (((m : Int) + Sc) * ((m : Int) + Sc))) =
        8 * (((q * q / 2 ^ 104 : Nat) : Int) * (((m : Int) + Sc) * ((m : Int) + Sc))) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have e2 : (((Sc : Int) - m) * ((Sc : Int) - m)) * 2 ^ 99 =
        2 ^ 99 * (((Sc : Int) - m) * ((Sc : Int) - m)) := Int.mul_comm _ _
    omega
  -- box bounds
  have hB2nn : (0 : Int) ≤ evalPoly ltB2 (m : Int) := by
    rw [evalB2_lt]
    exact Int.mul_nonneg (by simp only [Sc]; omega) (by simp only [Sc]; omega)
  have hD8nn : (0 : Int) ≤ evalPoly ltD8 (m : Int) := by
    rw [evalD8_lt]
    refine Int.mul_nonneg (by omega) (Int.mul_nonneg ?_ ?_) <;>
      simp only [Sc] <;> omega
  have hu_lt_UB : ((q * q / 2 ^ 104 : Nat) : Int) ≤ 2333000000000000000000000000 := by
    simp only [Uc] at hu_le
    omega
  have hb1P : ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly ltD8 (m : Int) ≤
      2333000000000000000000000000 * evalPoly ltD8 (m : Int) :=
    mul_le_mul_right_nonneg hu_lt_UB hD8nn
  have hb2P : -(2333000000000000000000000000 * evalPoly ltD8 (m : Int)) ≤
      evalPoly ltWLO (m : Int) := by
    rw [evalWLO_lt, evalD8_lt]
    have hAB : ((Sc : Int) - m) * ((m : Int) + Sc) ≤
        ((m : Int) + Sc) * ((m : Int) + Sc) :=
      mul_le_mul_right_nonneg (by omega) (by simp only [Sc]; omega)
    have hsq : (0 : Int) ≤ (((Sc : Int) - m) * ((Sc : Int) - m)) := by
      refine Int.mul_nonneg ?_ ?_ <;> simp only [Sc] at h2 ⊢ <;> omega
    have hBB : (0 : Int) ≤ ((m : Int) + Sc) * ((m : Int) + Sc) := by
      refine Int.mul_nonneg ?_ ?_ <;> simp only [Sc] <;> omega
    generalize ((Sc : Int) - m) * ((Sc : Int) - m) = AA at *
    generalize ((Sc : Int) - m) * ((m : Int) + Sc) = AB at *
    generalize ((m : Int) + Sc) * ((m : Int) + Sc) = BB at *
    have h99 : (0 : Int) ≤ 2 ^ 99 * AA := Int.mul_nonneg (by omega) hsq
    omega
  have hBpos : (0 : Int) < (m : Int) + Sc := by simp only [Sc]; omega
  have hD8pos : (0 : Int) < evalPoly ltD8 (m : Int) := by
    rw [evalD8_lt]
    exact Int.mul_pos (by omega) (Int.mul_pos hBpos hBpos)
  have hB2pos : (0 : Int) < evalPoly ltB2 (m : Int) := by
    rw [evalB2_lt]
    exact Int.mul_pos hBpos hBpos
  have hb1Q : evalPoly ltA96 (m : Int) ≤
      2333000000000000000000000000 * evalPoly ltB2 (m : Int) := by
    have hws := ltWS_nonneg (m := (m : Int))
      (by simp only [MLO] at h1; omega) (by simp only [Sc] at h2; omega)
    rw [evalWS_lt] at hws
    rw [evalA96_lt, evalB2_lt]
    omega
  have hb2Q : -(2333000000000000000000000000 * evalPoly ltB2 (m : Int)) ≤
      ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly ltB2 (m : Int) := by
    have h := Int.mul_nonneg (Int.natCast_nonneg (q * q / 2 ^ 104)) (by omega :
      (0 : Int) ≤ evalPoly ltB2 (m : Int))
    have h2' : (0 : Int) ≤ 2333000000000000000000000000 * evalPoly ltB2 (m : Int) :=
      Int.mul_nonneg (by omega) (by omega)
    omega
  -- divided-difference monotonicity, with the argument roles of the up-side swapped
  have hPanti := homEvalI_PPc_anti (n1 := evalPoly ltA96 (m : Int))
    (n2 := ((q * q / 2 ^ 104 : Nat) : Int) * evalPoly ltB2 (m : Int))
    (D := evalPoly ltB2 (m : Int)) hB2pos hordQ hb1Q hb2Q
  have hQmono := homEvalI_QQc_mono (n1 := ((q * q / 2 ^ 104 : Nat) : Int) *
      evalPoly ltD8 (m : Int)) (n2 := evalPoly ltWLO (m : Int))
    (D := evalPoly ltD8 (m : Int)) hD8pos hordP hb1P hb2P
  -- collapse instances
  have hcolP : homEvalI PPc (((q * q / 2 ^ 104 : Nat) : Int) *
      evalPoly ltB2 (m : Int)) (evalPoly ltB2 (m : Int)) =
      evalPoly ltB2 (m : Int) ^ 4 * PPv := by
    rw [show PPc = (8203564106909714963200842018493798951984754309521818719427488640634114742013119919947469548416190884842555317059682247072626112599280320512 : Int) :: PP3c from rfl,
      homEvalI_collapse, ← hPP]
    rfl
  have hcolP' : homEvalI PPc (((q * q / 2 ^ 104 : Nat) : Int) *
      evalPoly ltB2 (m : Int)) (evalPoly ltB2 (m : Int)) =
      PPv * evalPoly ltB2 (m : Int) ^ 4 := by
    rw [hcolP]
    exact Int.mul_comm _ _
  have hcolQ : homEvalI QQc (((q * q / 2 ^ 104 : Nat) : Int) *
      evalPoly ltD8 (m : Int)) (evalPoly ltD8 (m : Int)) =
      evalPoly ltD8 (m : Int) ^ 5 * QQv := by
    rw [show QQc = (-(2202127471863542086976841246818343354848349628124454549898853972183438719928614203693782484275214277955754824740140383208045055653095158108464873472 : Int)) :: QQ4c from rfl,
      homEvalI_collapse, ← hQQ]
    rfl
  have hcolQ' : homEvalI QQc (((q * q / 2 ^ 104 : Nat) : Int) *
      evalPoly ltD8 (m : Int)) (evalPoly ltD8 (m : Int)) =
      QQv * evalPoly ltD8 (m : Int) ^ 5 := by
    rw [hcolQ]
    exact Int.mul_comm _ _
  have hB24 : (0 : Int) ≤ evalPoly ltB2 (m : Int) ^ 4 := pow_nonneg' (by omega) 4
  have hD5nn : (0 : Int) ≤ evalPoly ltD8 (m : Int) ^ 5 := pow_nonneg' (by omega) 5
  -- P upper comparison: PLOP(m) ≤ p-hat 2^358 (B²)^4
  have hPfin : evalPoly ltPLOP (m : Int) ≤
      toInt pword * 2 ^ 358 * evalPoly ltB2 (m : Int) ^ 4 := by
    rw [evalPLOP_lt]
    have s1P : homEvalI PPc (evalPoly ltA96 (m : Int)) (evalPoly ltB2 (m : Int)) ≤
        PPv * evalPoly ltB2 (m : Int) ^ 4 := by
      rw [← hcolP']
      exact hPanti
    have s2P : (PPv - SLOPPc) * evalPoly ltB2 (m : Int) ^ 4 ≤
        toInt pword * 2 ^ 358 * evalPoly ltB2 (m : Int) ^ 4 :=
      mul_le_mul_right_nonneg (by omega) hB24
    have e1P : (PPv - SLOPPc) * evalPoly ltB2 (m : Int) ^ 4 =
        PPv * evalPoly ltB2 (m : Int) ^ 4 - SLOPPc * evalPoly ltB2 (m : Int) ^ 4 :=
      Int.sub_mul _ _ _
    generalize hg1 : homEvalI PPc (evalPoly ltA96 (m : Int))
      (evalPoly ltB2 (m : Int)) = HS at s1P ⊢
    generalize hg2 : evalPoly ltB2 (m : Int) ^ 4 = B4 at s1P s2P e1P ⊢
    generalize hg3 : PPv * B4 = PB4 at s1P e1P
    generalize hg4 : SLOPPc * B4 = SB4 at e1P ⊢
    generalize hg5 : (PPv - SLOPPc) * B4 = PSB at s2P e1P
    generalize hg6 : toInt pword * 2 ^ 358 * B4 = PW4 at s2P ⊢
    omega
  -- Q lower comparison: (-q-hat) 2^386 (8B²)^5 ≤ DLO(m)
  have hQfin : -toInt qword * 2 ^ 386 * evalPoly ltD8 (m : Int) ^ 5 ≤
      evalPoly ltDLO (m : Int) := by
    rw [evalDLO_lt]
    have s1Q : homEvalI QQc (evalPoly ltWLO (m : Int)) (evalPoly ltD8 (m : Int)) ≤
        QQv * evalPoly ltD8 (m : Int) ^ 5 := by
      rw [← hcolQ']
      exact hQmono
    have s2Q : (QQv - SLOPQc) * evalPoly ltD8 (m : Int) ^ 5 ≤
        toInt qword * 2 ^ 386 * evalPoly ltD8 (m : Int) ^ 5 :=
      mul_le_mul_right_nonneg (by omega) hD5nn
    have e1Q : (QQv - SLOPQc) * evalPoly ltD8 (m : Int) ^ 5 =
        QQv * evalPoly ltD8 (m : Int) ^ 5 - SLOPQc * evalPoly ltD8 (m : Int) ^ 5 :=
      Int.sub_mul _ _ _
    have e2Q : -toInt qword * 2 ^ 386 * evalPoly ltD8 (m : Int) ^ 5 =
        -(toInt qword * 2 ^ 386 * evalPoly ltD8 (m : Int) ^ 5) := by
      rw [Int.neg_mul, Int.neg_mul]
    generalize hg1 : homEvalI QQc (evalPoly ltWLO (m : Int))
      (evalPoly ltD8 (m : Int)) = HS at s1Q ⊢
    generalize hg2 : evalPoly ltD8 (m : Int) ^ 5 = D5 at s1Q s2Q e1Q e2Q ⊢
    generalize hg3 : QQv * D5 = QD at s1Q e1Q
    generalize hg4 : SLOPQc * D5 = SD at e1Q ⊢
    generalize hg5 : (QQv - SLOPQc) * D5 = QSD at s2Q e1Q
    generalize hg6 : toInt qword * 2 ^ 386 * D5 = QW at s2Q e2Q
    generalize hg7 : -toInt qword * 2 ^ 386 * D5 = QWn at e2Q ⊢
    omega
  -- AZ bounds: 0 ≤ AZ(m) ≤ q (m + S)
  have hAZnn : (0 : Int) ≤ evalPoly ltAZ (m : Int) := by
    rw [evalAZ_lt]
    simp only [Sc] at h2 ⊢
    omega
  have hAZle : evalPoly ltAZ (m : Int) ≤ (q : Int) * ((m : Int) + Sc) := by
    rw [evalAZ_lt]
    have hq2' := hq2
    have e : ((q : Int) + 1) * ((m : Int) + Sc) =
        (q : Int) * ((m : Int) + Sc) + ((m : Int) + Sc) := by
      rw [Int.add_mul, Int.one_mul]
    rw [e] at hq2'
    generalize (q : Int) * ((m : Int) + Sc) = QB at hq2' ⊢
    omega
  -- numerator chain: PLOP·AZ·B ≤ p-hat q 2^358 (B²)^5
  have hBnn : (0 : Int) ≤ (m : Int) + Sc := by simp only [Sc]; omega
  have hPWnn : (0 : Int) ≤ toInt pword * 2 ^ 358 * evalPoly ltB2 (m : Int) ^ 4 :=
    Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) hB24
  have t1 : evalPoly ltPLOP (m : Int) * evalPoly ltAZ (m : Int) ≤
      toInt pword * 2 ^ 358 * evalPoly ltB2 (m : Int) ^ 4 * evalPoly ltAZ (m : Int) :=
    mul_le_mul_right_nonneg hPfin hAZnn
  have t1b : evalPoly ltPLOP (m : Int) * evalPoly ltAZ (m : Int) * ((m : Int) + Sc) ≤
      toInt pword * 2 ^ 358 * evalPoly ltB2 (m : Int) ^ 4 * evalPoly ltAZ (m : Int) *
        ((m : Int) + Sc) :=
    mul_le_mul_right_nonneg t1 hBnn
  have t2 : toInt pword * 2 ^ 358 * evalPoly ltB2 (m : Int) ^ 4 *
      evalPoly ltAZ (m : Int) ≤
      toInt pword * 2 ^ 358 * evalPoly ltB2 (m : Int) ^ 4 *
        ((q : Int) * ((m : Int) + Sc)) :=
    mul_le_mul_left_nonneg hAZle hPWnn
  have t2b : toInt pword * 2 ^ 358 * evalPoly ltB2 (m : Int) ^ 4 *
      evalPoly ltAZ (m : Int) * ((m : Int) + Sc) ≤
      toInt pword * 2 ^ 358 * evalPoly ltB2 (m : Int) ^ 4 *
        ((q : Int) * ((m : Int) + Sc)) * ((m : Int) + Sc) :=
    mul_le_mul_right_nonneg t2 hBnn
  have t34 : toInt pword * 2 ^ 358 * evalPoly ltB2 (m : Int) ^ 4 *
      ((q : Int) * ((m : Int) + Sc)) * ((m : Int) + Sc) =
      toInt pword * (q : Int) * (2 ^ 358 * evalPoly ltB2 (m : Int) ^ 5) := by
    rw [show evalPoly ltB2 (m : Int) ^ 5 =
      evalPoly ltB2 (m : Int) ^ 4 * evalPoly ltB2 (m : Int) from by rw [Int.pow_succ]]
    rw [evalB2_lt]
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hTfin : evalPoly ltPLOP (m : Int) * evalPoly ltAZ (m : Int) * ((m : Int) + Sc) ≤
      toInt pword * (q : Int) * (2 ^ 358 * evalPoly ltB2 (m : Int) ^ 5) := by
    refine Int.le_trans t1b ?_
    rw [← t34]
    exact t2b
  -- denominator chain: (p-hat q + 1) 2^442 (8B²)^5 ≤ (-X1 + 1) 2^56 DLO
  have hFnn : (0 : Int) ≤ 2 ^ 442 * evalPoly ltD8 (m : Int) ^ 5 :=
    Int.mul_nonneg (by omega) hD5nn
  have u2 : toInt pword * (q : Int) + 1 ≤ (X1v + 1) * -toInt qword := by
    have h := hX1lo
    generalize hg1 : toInt pword * (q : Int) = PQt at h ⊢
    generalize hg2 : (X1v + 1) * -toInt qword = XQt at h ⊢
    omega
  have u3 : (toInt pword * (q : Int) + 1) * (2 ^ 442 * evalPoly ltD8 (m : Int) ^ 5) ≤
      (X1v + 1) * -toInt qword * (2 ^ 442 * evalPoly ltD8 (m : Int) ^ 5) :=
    mul_le_mul_right_nonneg u2 hFnn
  have u4 : (X1v + 1) * -toInt qword * (2 ^ 442 * evalPoly ltD8 (m : Int) ^ 5) =
      (X1v + 1) * (2 ^ 56 * (-toInt qword * 2 ^ 386 * evalPoly ltD8 (m : Int) ^ 5)) := by
    rw [show (2 : Int) ^ 442 = 2 ^ 56 * 2 ^ 386 from by decide]
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have u1b : 2 ^ 56 * (-toInt qword * 2 ^ 386 * evalPoly ltD8 (m : Int) ^ 5) ≤
      2 ^ 56 * evalPoly ltDLO (m : Int) :=
    mul_le_mul_left_nonneg hQfin (by omega)
  have hX1p1 : (0 : Int) ≤ X1v + 1 := by omega
  have u5 : (X1v + 1) * (2 ^ 56 * (-toInt qword * 2 ^ 386 *
      evalPoly ltD8 (m : Int) ^ 5)) ≤
      (X1v + 1) * (2 ^ 56 * evalPoly ltDLO (m : Int)) :=
    mul_le_mul_left_nonneg u1b hX1p1
  have hRfin : (toInt pword * (q : Int) + 1) *
      (2 ^ 442 * evalPoly ltD8 (m : Int) ^ 5) ≤
      (X1v + 1) * (2 ^ 56 * evalPoly ltDLO (m : Int)) := by
    refine Int.le_trans ?_ u5
    rw [← u4]
    exact u3
  -- scale bridge: 2^442 (8B²)^5 = 2^457 (B²)^5
  have ebr : (2 : Int) ^ 442 * evalPoly ltD8 (m : Int) ^ 5 =
      2 ^ 457 * evalPoly ltB2 (m : Int) ^ 5 := by
    rw [evalD8_lt, evalB2_lt]
    rw [show ((8 : Int) * (((m : Int) + Sc) * ((m : Int) + Sc))) ^ 5 =
      32768 * ((((m : Int) + Sc) * ((m : Int) + Sc)) ^ 5) from by
        rw [Int.mul_pow]
        rw [show ((8 : Int) ^ 5) = 32768 from by decide]]
    rw [← Int.mul_assoc, show (2 : Int) ^ 442 * 32768 = 2 ^ 457 from by decide]
  have escale : toInt pword * (q : Int) * (2 ^ 442 * evalPoly ltD8 (m : Int) ^ 5) =
      2 ^ 99 * (toInt pword * (q : Int) * (2 ^ 358 * evalPoly ltB2 (m : Int) ^ 5)) := by
    rw [ebr]
    rw [show (2 : Int) ^ 457 = 2 ^ 99 * 2 ^ 358 from by decide]
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  -- final assembly
  rw [evalTN2b_lt, evalTD2b_lt]
  have egoal : X1v * (2 ^ 99 * (2 ^ 56 * evalPoly ltDLO (m : Int))) =
      2 ^ 99 * (X1v * (2 ^ 56 * evalPoly ltDLO (m : Int))) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [egoal]
  have edist : (X1v + 1) * (2 ^ 56 * evalPoly ltDLO (m : Int)) =
      X1v * (2 ^ 56 * evalPoly ltDLO (m : Int)) + 2 ^ 56 * evalPoly ltDLO (m : Int) := by
    rw [Int.add_mul, Int.one_mul]
  have edist2 : (toInt pword * (q : Int) + 1) *
      (2 ^ 442 * evalPoly ltD8 (m : Int) ^ 5) =
      toInt pword * (q : Int) * (2 ^ 442 * evalPoly ltD8 (m : Int) ^ 5) +
        2 ^ 442 * evalPoly ltD8 (m : Int) ^ 5 := by
    rw [Int.add_mul, Int.one_mul]
  generalize hgT : evalPoly ltPLOP (m : Int) * evalPoly ltAZ (m : Int) *
    ((m : Int) + Sc) = T at hTfin ⊢
  generalize hgDLO : evalPoly ltDLO (m : Int) = DLO at hRfin edist ⊢
  generalize hgD5 : evalPoly ltD8 (m : Int) ^ 5 = D5g at hRfin edist2 escale hD5nn
  generalize hgB5 : evalPoly ltB2 (m : Int) ^ 5 = B5g at hTfin escale
  generalize hgPQ : toInt pword * (q : Int) = PQ at hTfin hRfin edist2 escale
  generalize hgPB : PQ * (2 ^ 358 * B5g) = PB at hTfin escale
  generalize hgPQD : PQ * (2 ^ 442 * D5g) = PQD at edist2 escale
  generalize hgRD : (PQ + 1) * (2 ^ 442 * D5g) = RD at hRfin edist2
  generalize hgXW : X1v * (2 ^ 56 * DLO) = XW at edist ⊢
  generalize hgXW1 : (X1v + 1) * (2 ^ 56 * DLO) = XW1 at hRfin edist
  omega

end LnFloorCert
