import LnProof.Floor.CarryIndependent.Bounds

open FormalYul FormalYul.Preservation

namespace LnFloorCarry

open LnYul Common.Poly

set_option maxRecDepth 8192

noncomputable section

def pErrorNum (u : Nat) : Int :=
  2 ^ 274 + 2 ^ 187 * (u : Int) + 2 ^ 90 * (u : Int) ^ 2 + (u : Int) ^ 3

def dErrorNum (u : Nat) : Int :=
  2 ^ 273 + 2 ^ 178 * (u : Int) + 2 ^ 90 * (u : Int) ^ 2 + (u : Int) ^ 3

theorem pError_eq (u : Nat) :
    pError u = (pErrorNum u : Real) / 2 ^ 274 := by
  norm_num [pError, pErrorNum]
  ring

theorem dError_eq (u : Nat) :
    dError u = (dErrorNum u : Real) / 2 ^ 273 := by
  norm_num [dError, dErrorNum]
  ring

theorem pError_eq_scaled (u : Nat) :
    pError u = ((pErrorNum u * 2 ^ 84 : Int) : Real) / pScale := by
  rw [pError_eq]
  norm_num [pScale]
  ring

theorem dError_eq_scaled (u : Nat) :
    dError u = ((dErrorNum u * 2 ^ 113 : Int) : Real) / qScale := by
  rw [dError_eq]
  norm_num [qScale]
  ring

theorem pError_nonneg (u : Nat) : 0 ≤ pError u := by
  unfold pError
  positivity

theorem dError_nonneg (u : Nat) : 0 ≤ dError u := by
  unfold dError
  positivity

private theorem scaled_error_step {ideal runtime shifted u scale radix error : Int}
    (herror : ideal - runtime * scale ≤ error)
    (hu0 : 0 ≤ u) (hscale : 0 ≤ scale)
    (hshift : runtime * u < shifted * radix + radix) :
    ideal * u - shifted * (scale * radix) ≤
      error * u + scale * radix := by
  have hresidue : runtime * u - shifted * radix ≤ radix := by omega
  calc
    ideal * u - shifted * (scale * radix) =
        (ideal - runtime * scale) * u +
          scale * (runtime * u - shifted * radix) := by ring
    _ ≤ error * u + scale * radix :=
      add_le_add (mul_le_mul_of_nonneg_right herror hu0)
        (mul_le_mul_of_nonneg_left hresidue hscale)

private theorem pS1_error {u : Nat} (hu : u ≤ Uc) :
    evalPoly PP1c (u : Int) - int256 (pS1 u) * 2 ^ 84 ≤ 2 ^ 84 := by
  have h := (pS1_facts hu).2.2.2.1
  simp only [SLOPP1] at h
  omega

private theorem pS2_error {u : Nat} (hu : u ≤ Uc) :
    evalPoly PP2c (u : Int) - int256 (pS2 u) * 2 ^ 174 ≤
      2 ^ 84 * ((u : Int) + 2 ^ 90) := by
  obtain ⟨hw, hlo, hhi, _, _⟩ := pS1_facts hu
  have htu : int256 u = (u : Int) := toInt_u hu
  have hu256 : u < 2 ^ 256 := hu.trans_lt (by norm_num [Uc])
  have hu0 : (0 : Int) ≤ (u : Int) := Int.ofNat_zero_le u
  have huU : (u : Int) ≤ Uc := by exact_mod_cast hu
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : int256 (evmMul (pS1 u) u) = int256 (pS1 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255, Uc] at hrange ⊢ <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_90 (evmMul_lt (pS1 u) u)
  rw [hmT] at hs1 hs2
  have hshiftRange :
      (-(541794612910710781063899171 : Int)) ≤
          int256 (evmSar 90 (evmMul (pS1 u) u)) ∧
        int256 (evmSar 90 (evmMul (pS1 u) u)) ≤ 0 := by
    simp only [Uc] at huU hrange
    clear hw hlo hhi hu htu hu256 hmT hwm
    generalize hmul : int256 (evmMul (pS1 u) u) = mul at hs1 hs2 hrange
    generalize hshift : int256 (evmSar 90 (evmMul (pS1 u) u)) = shift at hs1 hs2 ⊢
    omega
  have hcT : int256 P2c = (75095323053466847604974837616 : Int) :=
    toInt_of_lt (by norm_num [P2c])
  have hT : int256 (pS2 u) =
      int256 (evmSar 90 (evmMul (pS1 u) u)) +
        (75095323053466847604974837616 : Int) := by
    unfold pS2
    rw [← hcT]
    refine evmAdd_transport hwm (by norm_num [P2c]) ?_ ?_
    · rw [hcT]
      calc
        -(2 ^ 255 : Int) ≤
            -541794612910710781063899171 + 75095323053466847604974837616 := by norm_num
        _ ≤ int256 (evmSar 90 (evmMul (pS1 u) u)) +
            75095323053466847604974837616 :=
          add_le_add_right hshiftRange.1 _
    · rw [hcT]
      exact (add_le_add_right hshiftRange.2 75095323053466847604974837616).trans_lt
        (by norm_num)
  have heval : evalPoly PP2c (u : Int) =
      (1798175745614395766239082622521528960720477616324792863638563111730471590055378944 : Int) +
        evalPoly PP1c (u : Int) * (u : Int) := by
    show (1798175745614395766239082622521528960720477616324792863638563111730471590055378944 : Int) +
      (u : Int) * evalPoly PP1c (u : Int) = _
    rw [Int.mul_comm]
  have hstep := scaled_error_step (pS1_error hu) hu0 (by norm_num : (0 : Int) ≤ 2 ^ 84) hs2
  rw [hT, heval]
  generalize hshift : int256 (evmSar 90 (evmMul (pS1 u) u)) = shift at hstep ⊢
  norm_num at hstep ⊢
  linarith

private theorem pS3_error {u : Nat} (hu : u ≤ Uc) :
    evalPoly PP3c (u : Int) - int256 (pS3 u) * 2 ^ 271 ≤
      2 ^ 84 * (((u : Int) + 2 ^ 90) * (u : Int) + 2 ^ 187) := by
  obtain ⟨hw, hlo, hhi, _, _⟩ := pS2_facts hu
  have htu : int256 u = (u : Int) := toInt_u hu
  have hu256 : u < 2 ^ 256 := hu.trans_lt (by norm_num [Uc])
  have hu0 : (0 : Int) ≤ (u : Int) := Int.ofNat_zero_le u
  have huU : (u : Int) ≤ Uc := by exact_mod_cast hu
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : int256 (evmMul (pS2 u) u) = int256 (pS2 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255, Uc] at hrange ⊢ <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_97 (evmMul_lt (pS2 u) u)
  rw [hmT] at hs1 hs2
  have hshiftRange :
      (0 : Int) ≤ int256 (evmSar 97 (evmMul (pS2 u) u)) ∧
        int256 (evmSar 97 (evmMul (pS2 u) u)) ≤
          1105299956457643323759552745 := by
    simp only [Uc] at huU hrange
    clear hw hlo hhi hu htu hu256 hmT hwm
    generalize hmul : int256 (evmMul (pS2 u) u) = mul at hs1 hs2 hrange
    generalize hshift : int256 (evmSar 97 (evmMul (pS2 u) u)) = shift at hs1 hs2 ⊢
    omega
  have hcT : int256 P1c = (55801080067338082314461576444 : Int) :=
    toInt_of_lt (by norm_num [P1c])
  have hT : int256 (pS3 u) =
      int256 (evmSar 97 (evmMul (pS2 u) u)) -
        (55801080067338082314461576444 : Int) := by
    unfold pS3
    rw [← hcT]
    refine evmSub_transport hwm (by norm_num [P1c]) ?_ ?_
    · rw [hcT]
      calc
        -(2 ^ 255 : Int) ≤ 0 - 55801080067338082314461576444 := by norm_num
        _ ≤ int256 (evmSar 97 (evmMul (pS2 u) u)) -
            55801080067338082314461576444 :=
          sub_le_sub_right hshiftRange.1 _
    · rw [hcT]
      exact (sub_le_sub_right hshiftRange.2 55801080067338082314461576444).trans_lt
        (by norm_num)
  have heval : evalPoly PP3c (u : Int) =
      (-(211724653123857194763950383720687822670307458715746667734762451892717657012841722322962591250252321890880192512 : Int)) +
        evalPoly PP2c (u : Int) * (u : Int) := by
    show (-(211724653123857194763950383720687822670307458715746667734762451892717657012841722322962591250252321890880192512 : Int)) +
      (u : Int) * evalPoly PP2c (u : Int) = _
    rw [Int.mul_comm]
  have hstep := scaled_error_step (pS2_error hu) hu0 (by norm_num : (0 : Int) ≤ 2 ^ 174) hs2
  rw [hT, heval]
  generalize hshift : int256 (evmSar 97 (evmMul (pS2 u) u)) = shift at hstep ⊢
  norm_num at hstep ⊢
  linarith

private theorem pS4_error {u : Nat} (hu : u ≤ Uc) :
    evalPoly PPc (u : Int) - int256 (pS4 u) * pScale ≤
      pErrorNum u * 2 ^ 84 := by
  obtain ⟨hw, hlo, hhi, _, _⟩ := pS3_facts hu
  have htu : int256 u = (u : Int) := toInt_u hu
  have hu256 : u < 2 ^ 256 := hu.trans_lt (by norm_num [Uc])
  have hu0 : (0 : Int) ≤ (u : Int) := Int.ofNat_zero_le u
  have huU : (u : Int) ≤ Uc := by exact_mod_cast hu
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : int256 (evmMul (pS3 u) u) = int256 (pS3 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255, Uc] at hrange ⊢ <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_87 (evmMul_lt (pS3 u) u)
  rw [hmT] at hs1 hs2
  have hshiftRange :
      (-(841026779744997415277863435595 : Int)) ≤
          int256 (evmSar 87 (evmMul (pS3 u) u)) ∧
        int256 (evmSar 87 (evmMul (pS3 u) u)) ≤ 0 := by
    simp only [Uc] at huU hrange
    clear hw hlo hhi hu htu hu256 hmT hwm
    generalize hmul : int256 (evmMul (pS3 u) u) = mul at hs1 hs2 hrange
    generalize hshift : int256 (evmSar 87 (evmMul (pS3 u) u)) = shift at hs1 hs2 ⊢
    omega
  have hcT : int256 C0c = (13972178604861559108982341686387 : Int) :=
    toInt_of_lt (by norm_num [C0c])
  have hT : int256 (pS4 u) =
      int256 (evmSar 87 (evmMul (pS3 u) u)) +
        (13972178604861559108982341686387 : Int) := by
    unfold pS4
    rw [← hcT]
    refine evmAdd_transport hwm (by norm_num [C0c]) ?_ ?_
    · rw [hcT]
      calc
        -(2 ^ 255 : Int) ≤
            -841026779744997415277863435595 + 13972178604861559108982341686387 := by norm_num
        _ ≤ int256 (evmSar 87 (evmMul (pS3 u) u)) +
            13972178604861559108982341686387 :=
          add_le_add_right hshiftRange.1 _
    · rw [hcT]
      exact (add_le_add_right hshiftRange.2 13972178604861559108982341686387).trans_lt
        (by norm_num)
  have heval : evalPoly PPc (u : Int) =
      (8203564106909714963200842018502018851024462725819431901516251320229929630934299039494945066816553616430456446611805193566972803059892092928 : Int) +
        evalPoly PP3c (u : Int) * (u : Int) := by
    show (8203564106909714963200842018502018851024462725819431901516251320229929630934299039494945066816553616430456446611805193566972803059892092928 : Int) +
      (u : Int) * evalPoly PP3c (u : Int) = _
    rw [Int.mul_comm]
  have hstep := scaled_error_step (pS3_error hu) hu0 (by norm_num : (0 : Int) ≤ 2 ^ 271) hs2
  rw [hT, heval]
  generalize hshift : int256 (evmSar 87 (evmMul (pS3 u) u)) = shift at hstep ⊢
  norm_num [pScale, pErrorNum] at hstep ⊢
  nlinarith

private theorem qS1_error {u : Nat} (hu : u ≤ Uc) :
    evalPoly QQ1c (u : Int) - int256 (qS1 u) * (1 : Int) ≤ 0 := by
  have h := (qS1_facts hu).2.2.2.1
  simp only [SLOPQ1, sub_zero] at h
  omega

private theorem qS2_error {u : Nat} (hu : u ≤ Uc) :
    evalPoly QQ2c (u : Int) - int256 (qS2 u) * 2 ^ 113 ≤ 2 ^ 113 := by
  obtain ⟨hw, hlo, hhi, _, _⟩ := qS1_facts hu
  have htu : int256 u = (u : Int) := toInt_u hu
  have hu256 : u < 2 ^ 256 := hu.trans_lt (by norm_num [Uc])
  have hu0 : (0 : Int) ≤ (u : Int) := Int.ofNat_zero_le u
  have huU : (u : Int) ≤ Uc := by exact_mod_cast hu
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : int256 (evmMul (qS1 u) u) = int256 (qS1 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255, Uc] at hrange ⊢ <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_113 (evmMul_lt (qS1 u) u)
  rw [hmT] at hs1 hs2
  have hshiftRange :
      (-(965694431563962025332668 : Int)) ≤
          int256 (evmSar 113 (evmMul (qS1 u) u)) ∧
        int256 (evmSar 113 (evmMul (qS1 u) u)) ≤ 0 := by
    simp only [Uc] at huU hrange
    clear hw hlo hhi hu htu hu256 hmT hwm
    generalize hmul : int256 (evmMul (qS1 u) u) = mul at hs1 hs2 hrange
    generalize hshift : int256 (evmSar 113 (evmMul (qS1 u) u)) = shift at hs1 hs2 ⊢
    omega
  have hcT : int256 Q3c = (281702237671157106654810095 : Int) :=
    toInt_of_lt (by norm_num [Q3c])
  have hT : int256 (qS2 u) =
      int256 (evmSar 113 (evmMul (qS1 u) u)) +
        (281702237671157106654810095 : Int) := by
    unfold qS2
    rw [← hcT]
    refine evmAdd_transport hwm (by norm_num [Q3c]) ?_ ?_
    · rw [hcT]
      calc
        -(2 ^ 255 : Int) ≤
            -965694431563962025332668 + 281702237671157106654810095 := by norm_num
        _ ≤ int256 (evmSar 113 (evmMul (qS1 u) u)) +
            281702237671157106654810095 := add_le_add_right hshiftRange.1 _
    · rw [hcT]
      exact (add_le_add_right hshiftRange.2 281702237671157106654810095).trans_lt
        (by norm_num)
  have heval : evalPoly QQ2c (u : Int) =
      (2925363287404360843667081098480704995728827760271876675338240 : Int) +
        evalPoly QQ1c (u : Int) * (u : Int) := by
    show (2925363287404360843667081098480704995728827760271876675338240 : Int) +
      (u : Int) * evalPoly QQ1c (u : Int) = _
    rw [Int.mul_comm]
  have hprevious := qS1_error hu
  have hscale : (0 : Int) ≤ 1 := zero_le_one
  generalize hruntime : int256 (qS1 u) = runtime at hprevious hs2
  generalize hshift : int256 (evmSar 113 (evmMul (qS1 u) u)) = shift at hs2
  have hstep := scaled_error_step hprevious hu0 hscale hs2
  rw [hT, heval]
  rw [hshift]
  norm_num at hstep ⊢
  linarith

private theorem qS3_error {u : Nat} (hu : u ≤ Uc) :
    evalPoly QQ3c (u : Int) - int256 (qS3 u) * 2 ^ 203 ≤
      2 ^ 113 * ((u : Int) + 2 ^ 90) := by
  obtain ⟨hw, hlo, hhi, _, _⟩ := qS2_facts hu
  have htu : int256 u = (u : Int) := toInt_u hu
  have hu256 : u < 2 ^ 256 := hu.trans_lt (by norm_num [Uc])
  have hu0 : (0 : Int) ≤ (u : Int) := Int.ofNat_zero_le u
  have huU : (u : Int) ≤ Uc := by exact_mod_cast hu
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : int256 (evmMul (qS2 u) u) = int256 (qS2 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255, Uc] at hrange ⊢ <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_90 (evmMul_lt (qS2 u) u)
  rw [hmT] at hs1 hs2
  have hshiftRange :
      (0 : Int) ≤ int256 (evmSar 90 (evmMul (qS2 u) u)) ∧
        int256 (evmSar 90 (evmMul (qS2 u) u)) ≤ 530722535992203150542952384 := by
    simp only [Uc] at huU hrange
    clear hw hlo hhi hu htu hu256 hmT hwm
    generalize hmul : int256 (evmMul (qS2 u) u) = mul at hs1 hs2 hrange
    generalize hshift : int256 (evmSar 90 (evmMul (qS2 u) u)) = shift at hs1 hs2 ⊢
    omega
  have hcT : int256 Q2c = (53722296096946541673620529149 : Int) :=
    toInt_of_lt (by norm_num [Q2c])
  have hT : int256 (qS3 u) =
      int256 (evmSar 90 (evmMul (qS2 u) u)) -
        (53722296096946541673620529149 : Int) := by
    unfold qS3
    rw [← hcT]
    refine evmSub_transport hwm (by norm_num [Q2c]) ?_ ?_
    · rw [hcT]
      calc
        -(2 ^ 255 : Int) ≤ 0 - 53722296096946541673620529149 := by norm_num
        _ ≤ int256 (evmSar 90 (evmMul (qS2 u) u)) -
            53722296096946541673620529149 := sub_le_sub_right hshiftRange.1 _
    · rw [hcT]
      exact (sub_le_sub_right hshiftRange.2 53722296096946541673620529149).trans_lt
        (by norm_num)
  have heval : evalPoly QQ3c (u : Int) =
      (-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int)) +
        evalPoly QQ2c (u : Int) * (u : Int) := by
    show (-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int)) +
      (u : Int) * evalPoly QQ2c (u : Int) = _
    rw [Int.mul_comm]
  have hprevious := qS2_error hu
  have hscale : (0 : Int) ≤ 2 ^ 113 := by norm_num
  generalize hruntime : int256 (qS2 u) = runtime at hprevious hs2
  generalize hshift : int256 (evmSar 90 (evmMul (qS2 u) u)) = shift at hs2
  have hstep := scaled_error_step hprevious hu0 hscale hs2
  rw [hT, heval]
  rw [hshift]
  norm_num at hstep ⊢
  linarith

private theorem qS4_error {u : Nat} (hu : u ≤ Uc) :
    evalPoly QQ4c (u : Int) - int256 (qS4 u) * 2 ^ 291 ≤
      2 ^ 113 * (((u : Int) + 2 ^ 90) * (u : Int) + 2 ^ 178) := by
  obtain ⟨hw, hlo, hhi, _, _⟩ := qS3_facts hu
  have htu : int256 u = (u : Int) := toInt_u hu
  have hu256 : u < 2 ^ 256 := hu.trans_lt (by norm_num [Uc])
  have hu0 : (0 : Int) ≤ (u : Int) := Int.ofNat_zero_le u
  have huU : (u : Int) ≤ Uc := by exact_mod_cast hu
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : int256 (evmMul (qS3 u) u) = int256 (qS3 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255, Uc] at hrange ⊢ <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_88 (evmMul_lt (qS3 u) u)
  rw [hmT] at hs1 hs2
  have hshiftRange :
      (-(404847806103384053046409292281 : Int)) ≤
          int256 (evmSar 88 (evmMul (qS3 u) u)) ∧
        int256 (evmSar 88 (evmMul (qS3 u) u)) ≤ 0 := by
    simp only [Uc] at huU hrange
    clear hw hlo hhi hu htu hu256 hmT hwm
    generalize hmul : int256 (evmMul (qS3 u) u) = mul at hs1 hs2 hrange
    generalize hshift : int256 (evmSar 88 (evmMul (qS3 u) u)) = shift at hs1 hs2 ⊢
    omega
  have hcT : int256 Q1c = (16613772931382142257332678212554 : Int) :=
    toInt_of_lt (by norm_num [Q1c])
  have hT : int256 (qS4 u) =
      int256 (evmSar 88 (evmMul (qS3 u) u)) +
        (16613772931382142257332678212554 : Int) := by
    unfold qS4
    rw [← hcT]
    refine evmAdd_transport hwm (by norm_num [Q1c]) ?_ ?_
    · rw [hcT]
      calc
        -(2 ^ 255 : Int) ≤
            -404847806103384053046409292281 + 16613772931382142257332678212554 := by norm_num
        _ ≤ int256 (evmSar 88 (evmMul (qS3 u) u)) +
            16613772931382142257332678212554 := add_le_add_right hshiftRange.1 _
    · rw [hcT]
      exact (add_le_add_right hshiftRange.2 16613772931382142257332678212554).trans_lt
        (by norm_num)
  have heval : evalPoly QQ4c (u : Int) =
      (66099322585698201304896817119133314370855648754593283446756353822335972946493244703677923116935407234039976856169480192 : Int) +
        evalPoly QQ3c (u : Int) * (u : Int) := by
    show (66099322585698201304896817119133314370855648754593283446756353822335972946493244703677923116935407234039976856169480192 : Int) +
      (u : Int) * evalPoly QQ3c (u : Int) = _
    rw [Int.mul_comm]
  have hprevious := qS3_error hu
  have hscale : (0 : Int) ≤ 2 ^ 203 := by norm_num
  generalize hruntime : int256 (qS3 u) = runtime at hprevious hs2
  generalize hshift : int256 (evmSar 88 (evmMul (qS3 u) u)) = shift at hs2
  have hstep := scaled_error_step hprevious hu0 hscale hs2
  rw [hT, heval]
  rw [hshift]
  norm_num at hstep ⊢
  linarith

theorem qS5_error {u : Nat} (hu : u ≤ Uc) :
    evalPoly QQc (u : Int) - int256 (qS5 u) * qScale ≤
      dErrorNum u * 2 ^ 113 := by
  obtain ⟨hw, hlo, hhi, _, _⟩ := qS4_facts hu
  have htu : int256 u = (u : Int) := toInt_u hu
  have hu256 : u < 2 ^ 256 := hu.trans_lt (by norm_num [Uc])
  have hu0 : (0 : Int) ≤ (u : Int) := Int.ofNat_zero_le u
  have huU : (u : Int) ≤ Uc := by exact_mod_cast hu
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : int256 (evmMul (qS4 u) u) = int256 (qS4 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255, Uc] at hrange ⊢ <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_95 (evmMul_lt (qS4 u) u)
  rw [hmT] at hs1 hs2
  have hshiftRange :
      (0 : Int) ≤ int256 (evmSar 95 (evmMul (qS4 u) u)) ∧
        int256 (evmSar 95 (evmMul (qS4 u) u)) ≤ 978127625049538968174347910714 := by
    simp only [Uc] at huU hrange
    clear hw hlo hhi hu htu hu256 hmT hwm
    generalize hmul : int256 (evmMul (qS4 u) u) = mul at hs1 hs2 hrange
    generalize hshift : int256 (evmSar 95 (evmMul (qS4 u) u)) = shift at hs1 hs2 ⊢
    omega
  have hcT : int256 C0c = (13972178604861559108982341686387 : Int) :=
    toInt_of_lt (by norm_num [C0c])
  have hT : int256 (qS5 u) =
      int256 (evmSar 95 (evmMul (qS4 u) u)) -
        (13972178604861559108982341686387 : Int) := by
    unfold qS5
    rw [← hcT]
    refine evmSub_transport hwm (by norm_num [C0c]) ?_ ?_
    · rw [hcT]
      calc
        -(2 ^ 255 : Int) ≤ 0 - 13972178604861559108982341686387 := by norm_num
        _ ≤ int256 (evmSar 95 (evmMul (qS4 u) u)) -
            13972178604861559108982341686387 := sub_le_sub_right hshiftRange.1 _
    · rw [hcT]
      exact (sub_le_sub_right hshiftRange.2 13972178604861559108982341686387).trans_lt
        (by norm_num)
  have heval : evalPoly QQc (u : Int) =
      (-(2202127471863542086976841246820549867195347718960342176144462014556523185327760268707187588705852038374958668534379582118318610928980329275922055168 : Int)) +
        evalPoly QQ4c (u : Int) * (u : Int) := by
    show (-(2202127471863542086976841246820549867195347718960342176144462014556523185327760268707187588705852038374958668534379582118318610928980329275922055168 : Int)) +
      (u : Int) * evalPoly QQ4c (u : Int) = _
    rw [Int.mul_comm]
  have hprevious := qS4_error hu
  have hscale : (0 : Int) ≤ 2 ^ 291 := by norm_num
  generalize hruntime : int256 (qS4 u) = runtime at hprevious hs2
  generalize hshift : int256 (evmSar 95 (evmMul (qS4 u) u)) = shift at hs2
  have hstep := scaled_error_step hprevious hu0 hscale hs2
  rw [hT, heval]
  rw [hshift]
  norm_num [qScale, dErrorNum] at hstep ⊢
  nlinarith

theorem pS4_error_bound {u : Nat} (hu : u ≤ Uc) :
    evalPoly PPc (u : Int) - int256 (pS4 u) * pScale ≤
      pErrorNum u * 2 ^ 84 :=
  pS4_error hu

end

end LnFloorCarry
