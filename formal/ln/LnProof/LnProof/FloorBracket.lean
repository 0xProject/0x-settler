import LnProof.ZOctave
import LnProof.FloorCertDefs

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

end LnFloorCert
