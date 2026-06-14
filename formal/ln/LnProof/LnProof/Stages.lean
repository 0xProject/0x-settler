import LnProof.BridgeDiv
import LnProof.Poly

/-!
# Horner stage lemmas

Each Horner stage of the model's `p`/`q` evaluation is sandwiched against an
exact integer polynomial (`PPc` at scale `2^358`, `QQc` at scale `2^386`,
coefficients low-order first) with a one-sided truncation slop: the
renormalizing shifts only ever round down. Stage value intervals are concrete
literals checked by `omega` as the chain is built, so a wrong literal fails
the build. All scale factors are spelled as numerals (the kernel must not
unfold `Int` powers of this size).
-/

namespace LnGeneratedModel

open LnPoly

def Sc : Nat := 14341829369545251819195376186229
def P4c : Nat := 4542704643877621417440
def P3c : Nat := 287579185854221620442209346
def P2c : Nat := 75095323053466847604974837616
def P1c : Nat := 14285076497238549072502163569605
def C0c : Nat := 13972178604861559108982341686373
def Q4c : Nat := 4299840983308505679614339668442
def Q3c : Nat := 72115772843816219303631384287
def Q2c : Nat := 53722296096946541673620529149
def Q1c : Nat := 16613772931382142257332678212540
def Kc : Nat := 7450580596923828125
def LN2c : Nat := 3273295013171879848905889459134067659407864468560
def BIASc : Nat := 143060321855302967919159136223863753677754092301269

/-- Largest |z| over the mantissa domain. -/
def Zc : Nat := 217494458298375249691265569570

theorem Zc_def : Zc = ((Sc - 2 ^ 103) * 2 ^ 100) / (2 ^ 103 + Sc) := by decide

/-- Largest `u`. -/
def Uc : Nat := 2332259347626381040680638252

theorem Uc_def : Uc = Zc * Zc / 2 ^ 104 := by decide

def SLOPP1 : Int := 19342813113834066795298815
def SLOPP2 : Int := 69057699520159162110141648894228821086113826043390164
def SLOPP3 : Int := 175881852653841527465731299025290925982211563058490275341424550836308597972865136
def SLOPPc : Int := 997337740623226022763231126257526602143516768691287840071060348738876110879097835502646319520435285356766016
def SLOPQ1 : Int := 0
def SLOPQ2 : Int := 40564819207303340847894502572032
def SLOPQ3 : Int := 12950112032852929585362618207496571604840551141446660046979072
def SLOPQ4 : Int := 34181605732708413891107132501972221452642750611817606987286165092915319399309220450926592
def SLOPQc : Int := 237328394272566608543184577042992631102137769183554805465838453830626805665679633215510949390003272039043519320424448

/-! ## Pipeline words -/

def zWord (m : Nat) : Nat := evmSdiv (evmShl 100 (evmSub Sc m)) (evmAdd m Sc)

def uWord (z : Nat) : Nat := evmShr 104 (evmMul z z)

def pS1 (u : Nat) : Nat := evmSub (evmShr 84 (evmMul P4c u)) P3c
def pS2 (u : Nat) : Nat := evmAdd (evmSar 90 (evmMul (pS1 u) u)) P2c
def pS3 (u : Nat) : Nat := evmSub (evmSar 89 (evmMul (pS2 u) u)) P1c
def pS4 (u : Nat) : Nat := evmAdd (evmSar 95 (evmMul (pS3 u) u)) C0c

def qS1 (u : Nat) : Nat := evmSub u Q4c
def qS2 (u : Nat) : Nat := evmAdd (evmSar 105 (evmMul (qS1 u) u)) Q3c
def qS3 (u : Nat) : Nat := evmSub (evmSar 98 (evmMul (qS2 u) u)) Q2c
def qS4 (u : Nat) : Nat := evmAdd (evmSar 88 (evmMul (qS3 u) u)) Q1c
def qS5 (u : Nat) : Nat := evmSub (evmSar 95 (evmMul (qS4 u) u)) C0c

/-! ## Suffix polynomials (numeral coefficients) -/

def PP1c : List Int := [(-(5562590447406762316237749022682109217671325297934336 : Int) : Int), (4542704643877621417440 : Int)]
def PP2c : List Int := (1798175745614395766239082622521528960720477616324792863638563111730471590055378944 : Int) :: PP1c
def PP3c : List Int := (-(211724653123857194763950383719813360812387246807907859655976840812609762088646804783336607575824561935839395840 : Int) : Int) :: PP2c
def PPc : List Int := (8203564106909714963200842018493798951984754309521818719427488640634114742013119919947469548416190884842555317059682247072626112599280320512 : Int) :: PP3c

def QQ1c : List Int := [(-(4299840983308505679614339668442 : Int) : Int), (1 : Int)]
def QQ2c : List Int := (2925363287404360843667081097142065961887817512291358090461184 : Int) :: QQ1c
def QQ3c : List Int := (-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int) : Int) :: QQ2c
def QQ4c : List Int := (66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) :: QQ3c
def QQc : List Int := (-(2202127471863542086976841246818343354848349628124454549898853972183438719928614203693782484275214277955754824740140383208045055653095158108464873472 : Int) : Int) :: QQ4c

/-! ## Generic step helpers -/

/-- Transfers a scaled sandwich through one multiplication by `u`. -/
theorem scaled_mul_step {sv uv E SS slop U : Int}
    (h1 : SS - slop ≤ sv * E) (h2 : sv * E ≤ SS)
    (hu0 : 0 ≤ uv) (huU : uv ≤ U) (hslop : 0 ≤ slop) :
    SS * uv - slop * U ≤ sv * uv * E ∧ sv * uv * E ≤ SS * uv := by
  have e1 : sv * uv * E = sv * E * uv := by
    rw [Int.mul_assoc, Int.mul_comm uv E, ← Int.mul_assoc]
  have low : (SS - slop) * uv ≤ sv * E * uv := mul_le_mul_right_nonneg h1 hu0
  have high : sv * E * uv ≤ SS * uv := mul_le_mul_right_nonneg h2 hu0
  have expand : (SS - slop) * uv = SS * uv - slop * uv := by
    rw [Int.sub_mul]
  have slopmul : slop * uv ≤ slop * U := mul_le_mul_left_nonneg huU hslop
  omega

/-- Range of a product from ranges of the factors (second factor nonnegative). -/
theorem mul_range {s u lo hi U : Int} (h1 : lo ≤ s) (h2 : s ≤ hi) (h3 : 0 ≤ u)
    (h4 : u ≤ U) : min (lo * U) 0 ≤ s * u ∧ s * u ≤ max (hi * U) 0 := by
  have hU : 0 ≤ U := by omega
  constructor
  · rcases Int.le_total 0 s with hs | hs
    · have : 0 ≤ s * u := Int.mul_nonneg hs h3
      omega
    · have a1 : s * U ≤ s * u := mul_le_mul_left_nonpos h4 hs
      have a2 : lo * U ≤ s * U := mul_le_mul_right_nonneg h1 hU
      omega
  · rcases Int.le_total 0 s with hs | hs
    · have a1 : s * u ≤ s * U := mul_le_mul_left_nonneg h4 hs
      have a2 : s * U ≤ hi * U := mul_le_mul_right_nonneg h2 hU
      omega
    · have a1 : s * u ≤ 0 * u := mul_le_mul_right_nonneg hs h3
      rw [Int.zero_mul] at a1
      omega

theorem toInt_u {u : Nat} (h : u ≤ Uc) : toInt u = (u : Int) := by
  refine toInt_of_lt ?_
  simp only [Uc] at h
  omega

/-! ## q-chain stage 1 (exact) -/

theorem qS1_facts {u : Nat} (hu : u ≤ Uc) :
    qS1 u < 2 ^ 256 ∧
    (-(4299840983308505679614339668442 : Int)) ≤ toInt (qS1 u) ∧
    toInt (qS1 u) ≤ (-(4297508723960879298573659030190 : Int)) ∧
    evalPoly QQ1c (u : Int) - SLOPQ1 ≤ toInt (qS1 u) * 1 ∧
    toInt (qS1 u) * 1 ≤ evalPoly QQ1c (u : Int) := by
  have htu : toInt u = (u : Int) := toInt_u hu
  simp only [Uc] at hu
  have hu256 : u < 2 ^ 256 := by omega
  have hT : toInt (qS1 u) = (u : Int) - (4299840983308505679614339668442 : Int) := by
    unfold qS1
    have h2 : toInt Q4c = (4299840983308505679614339668442 : Int) := toInt_of_lt (by simp only [Q4c]; omega)
    rw [← htu, ← h2]
    refine evmSub_transport hu256 (by simp only [Q4c]; omega) ?_ ?_ <;>
      rw [htu, h2] <;> simp only [ipow255] <;> omega
  refine ⟨evmSub_lt _ _, ?_, ?_, ?_, ?_⟩
  · rw [hT]; omega
  · rw [hT]; omega
  · rw [hT]
    simp only [QQ1c, evalPoly, SLOPQ1]
    omega
  · rw [hT]
    simp only [QQ1c, evalPoly]
    omega

/-! ## p-chain stage 1 -/

theorem pS1_facts {u : Nat} (hu : u ≤ Uc) :
    pS1 u < 2 ^ 256 ∧
    (-(287579185854221620442209346 : Int)) ≤ toInt (pS1 u) ∧
    toInt (pS1 u) ≤ (-(287031449322475267106929263 : Int)) ∧
    evalPoly PP1c (u : Int) - SLOPP1 ≤ toInt (pS1 u) * 19342813113834066795298816 ∧
    toInt (pS1 u) * 19342813113834066795298816 ≤ evalPoly PP1c (u : Int) := by
  simp only [Uc] at hu
  have hm1 : evmMul P4c u = P4c * u := by
    unfold evmMul u256
    simp only [word_mod_eq, P4c]
    omega
  have hm1lt : P4c * u < 2 ^ 256 := by simp only [P4c]; omega
  have hd1 : evmShr 84 (evmMul P4c u) = P4c * u / 2 ^ 84 := by
    rw [hm1]; exact evmShr_eq_div_84 hm1lt
  have hT : toInt (pS1 u) = ((P4c * u / 2 ^ 84 : Nat) : Int) - (287579185854221620442209346 : Int) := by
    unfold pS1
    rw [hd1]
    have h1 : toInt (P4c * u / 2 ^ 84 : Nat) = ((P4c * u / 2 ^ 84 : Nat) : Int) :=
      toInt_of_lt (by simp only [P4c]; omega)
    have h2 : toInt P3c = (287579185854221620442209346 : Int) := toInt_of_lt (by simp only [P3c]; omega)
    rw [← h1, ← h2]
    refine evmSub_transport (by simp only [P4c]; omega) (by simp only [P3c]; omega) ?_ ?_ <;>
      rw [h1, h2] <;> simp only [P4c, ipow255] <;> omega
  refine ⟨evmSub_lt _ _, ?_, ?_, ?_, ?_⟩
  · rw [hT]; simp only [P4c]; omega
  · rw [hT]; simp only [P4c]; omega
  · rw [hT]
    simp only [PP1c, evalPoly, SLOPP1, P4c]
    omega
  · rw [hT]
    simp only [PP1c, evalPoly, P4c]
    omega

theorem pS2_facts {u : Nat} (hu : u ≤ Uc) :
    pS2 u < 2 ^ 256 ∧
    (74553528440556136823910938445 : Int) ≤ toInt (pS2 u) ∧
    toInt (pS2 u) ≤ (75095323053466847604974837616 : Int) ∧
    evalPoly PP2c (u : Int) - SLOPP2 ≤ toInt (pS2 u) * 23945242826029513411849172299223580994042798784118784 ∧
    toInt (pS2 u) * 23945242826029513411849172299223580994042798784118784 ≤ evalPoly PP2c (u : Int) := by
  obtain ⟨hw, hlo, hhi, hsl, hsh⟩ := pS1_facts hu
  have htu : toInt u = (u : Int) := toInt_u hu
  simp only [Uc] at hu
  have hu256 : u < 2 ^ 256 := by omega
  have hu0 : (0 : Int) ≤ (u : Int) := by omega
  have huU : (u : Int) ≤ 2332259347626381040680638252 := by omega
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : toInt (evmMul (pS1 u) u) = toInt (pS1 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255] <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_90 (evmMul_lt (pS1 u) u)
  rw [hmT] at hs1 hs2
  have hdb : (-(541794612910710781063899171 : Int)) ≤ toInt (evmSar 90 (evmMul (pS1 u) u)) ∧
      toInt (evmSar 90 (evmMul (pS1 u) u)) ≤ (0 : Int) := by
    clear hsl hsh hmT hw htu hu256 hu
    generalize hB : toInt (pS1 u) * (u : Int) = B at hs1 hs2 hrange
    generalize hD : toInt (evmSar 90 (evmMul (pS1 u) u)) = D at hs1 hs2 ⊢
    omega
  have hcT : toInt P2c = (75095323053466847604974837616 : Int) := toInt_of_lt (by simp only [P2c]; omega)
  have hT : toInt (pS2 u) =
      toInt (evmSar 90 (evmMul (pS1 u) u)) + (75095323053466847604974837616 : Int) := by
    unfold pS2
    rw [← hcT]
    refine evmAdd_transport hwm (by simp only [P2c]; omega) ?_ ?_
    · clear hsl hsh hrange hs1 hs2 hmT
      rw [hcT]
      simp only [ipow255]
      omega
    · clear hsl hsh hrange hs1 hs2 hmT
      rw [hcT]
      simp only [ipow255]
      omega
  have hstep := scaled_mul_step hsl hsh hu0 huU (by simp only [SLOPP1]; omega)
  have ec : evalPoly PP2c (u : Int) =
      (1798175745614395766239082622521528960720477616324792863638563111730471590055378944 : Int) + evalPoly PP1c (u : Int) * (u : Int) := by
    show (1798175745614395766239082622521528960720477616324792863638563111730471590055378944 : Int) + (u : Int) * evalPoly PP1c (u : Int) = _
    rw [Int.mul_comm]
  refine ⟨evmAdd_lt _ _, ?_, ?_, ?_, ?_⟩
  · rw [hT]
    clear hsl hsh hrange hs1 hs2 hstep ec hmT
    omega
  · rw [hT]
    clear hsl hsh hrange hs1 hs2 hstep ec hmT
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPP1] at hstep
    simp only [SLOPP2]
    generalize hB : toInt (pS1 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly PP1c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : toInt (evmSar 90 (evmMul (pS1 u) u)) = D at hs1 hs2 ⊢
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPP1] at hstep
    generalize hB : toInt (pS1 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly PP1c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : toInt (evmSar 90 (evmMul (pS1 u) u)) = D at hs1 hs2 ⊢
    omega

theorem pS3_facts {u : Nat} (hu : u ≤ Uc) :
    pS3 u < 2 ^ 256 ∧
    (-(14285076497238549072502163569605 : Int)) ≤ toInt (pS3 u) ∧
    toInt (pS3 u) ≤ (-(14002119708385392381619718066850 : Int)) ∧
    evalPoly PP3c (u : Int) - SLOPP3 ≤ toInt (pS3 u) * 14821387422376473014217086081112052205218558037201992197050570753012880593911808 ∧
    toInt (pS3 u) * 14821387422376473014217086081112052205218558037201992197050570753012880593911808 ≤ evalPoly PP3c (u : Int) := by
  obtain ⟨hw, hlo, hhi, hsl, hsh⟩ := pS2_facts hu
  have htu : toInt u = (u : Int) := toInt_u hu
  simp only [Uc] at hu
  have hu256 : u < 2 ^ 256 := by omega
  have hu0 : (0 : Int) ≤ (u : Int) := by omega
  have huU : (u : Int) ≤ 2332259347626381040680638252 := by omega
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : toInt (evmMul (pS2 u) u) = toInt (pS2 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255] <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_89 (evmMul_lt (pS2 u) u)
  rw [hmT] at hs1 hs2
  have hdb : (0 : Int) ≤ toInt (evmSar 89 (evmMul (pS2 u) u)) ∧
      toInt (evmSar 89 (evmMul (pS2 u) u)) ≤ (282956788853156690882445502755 : Int) := by
    clear hsl hsh hmT hw htu hu256 hu
    generalize hB : toInt (pS2 u) * (u : Int) = B at hs1 hs2 hrange
    generalize hD : toInt (evmSar 89 (evmMul (pS2 u) u)) = D at hs1 hs2 ⊢
    omega
  have hcT : toInt P1c = (14285076497238549072502163569605 : Int) := toInt_of_lt (by simp only [P1c]; omega)
  have hT : toInt (pS3 u) =
      toInt (evmSar 89 (evmMul (pS2 u) u)) - (14285076497238549072502163569605 : Int) := by
    unfold pS3
    rw [← hcT]
    refine evmSub_transport hwm (by simp only [P1c]; omega) ?_ ?_
    · clear hsl hsh hrange hs1 hs2 hmT
      rw [hcT]
      simp only [ipow255]
      omega
    · clear hsl hsh hrange hs1 hs2 hmT
      rw [hcT]
      simp only [ipow255]
      omega
  have hstep := scaled_mul_step hsl hsh hu0 huU (by simp only [SLOPP2]; omega)
  have ec : evalPoly PP3c (u : Int) =
      (-(211724653123857194763950383719813360812387246807907859655976840812609762088646804783336607575824561935839395840 : Int)) + evalPoly PP2c (u : Int) * (u : Int) := by
    show (-(211724653123857194763950383719813360812387246807907859655976840812609762088646804783336607575824561935839395840 : Int)) + (u : Int) * evalPoly PP2c (u : Int) = _
    rw [Int.mul_comm]
  refine ⟨evmSub_lt _ _, ?_, ?_, ?_, ?_⟩
  · rw [hT]
    clear hsl hsh hrange hs1 hs2 hstep ec hmT
    omega
  · rw [hT]
    clear hsl hsh hrange hs1 hs2 hstep ec hmT
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPP2] at hstep
    simp only [SLOPP3]
    generalize hB : toInt (pS2 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly PP2c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : toInt (evmSar 89 (evmMul (pS2 u) u)) = D at hs1 hs2 ⊢
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPP2] at hstep
    generalize hB : toInt (pS2 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly PP2c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : toInt (evmSar 89 (evmMul (pS2 u) u)) = D at hs1 hs2 ⊢
    omega

theorem pS4_facts {u : Nat} (hu : u ≤ Uc) :
    pS4 u < 2 ^ 256 ∧
    (13131151825116561693704478250782 : Int) ≤ toInt (pS4 u) ∧
    toInt (pS4 u) ≤ (13972178604861559108982341686373 : Int) ∧
    evalPoly PPc (u : Int) - SLOPPc ≤ toInt (pS4 u) * 587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744 ∧
    toInt (pS4 u) * 587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744 ≤ evalPoly PPc (u : Int) := by
  obtain ⟨hw, hlo, hhi, hsl, hsh⟩ := pS3_facts hu
  have htu : toInt u = (u : Int) := toInt_u hu
  simp only [Uc] at hu
  have hu256 : u < 2 ^ 256 := by omega
  have hu0 : (0 : Int) ≤ (u : Int) := by omega
  have huU : (u : Int) ≤ 2332259347626381040680638252 := by omega
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : toInt (evmMul (pS3 u) u) = toInt (pS3 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255] <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_95 (evmMul_lt (pS3 u) u)
  rw [hmT] at hs1 hs2
  have hdb : (-(841026779744997415277863435591 : Int)) ≤ toInt (evmSar 95 (evmMul (pS3 u) u)) ∧
      toInt (evmSar 95 (evmMul (pS3 u) u)) ≤ (0 : Int) := by
    clear hsl hsh hmT hw htu hu256 hu
    generalize hB : toInt (pS3 u) * (u : Int) = B at hs1 hs2 hrange
    generalize hD : toInt (evmSar 95 (evmMul (pS3 u) u)) = D at hs1 hs2 ⊢
    omega
  have hcT : toInt C0c = (13972178604861559108982341686373 : Int) := toInt_of_lt (by simp only [C0c]; omega)
  have hT : toInt (pS4 u) =
      toInt (evmSar 95 (evmMul (pS3 u) u)) + (13972178604861559108982341686373 : Int) := by
    unfold pS4
    rw [← hcT]
    refine evmAdd_transport hwm (by simp only [C0c]; omega) ?_ ?_
    · clear hsl hsh hrange hs1 hs2 hmT
      rw [hcT]
      simp only [ipow255]
      omega
    · clear hsl hsh hrange hs1 hs2 hmT
      rw [hcT]
      simp only [ipow255]
      omega
  have hstep := scaled_mul_step hsl hsh hu0 huU (by simp only [SLOPP3]; omega)
  have ec : evalPoly PPc (u : Int) =
      (8203564106909714963200842018493798951984754309521818719427488640634114742013119919947469548416190884842555317059682247072626112599280320512 : Int) + evalPoly PP3c (u : Int) * (u : Int) := by
    show (8203564106909714963200842018493798951984754309521818719427488640634114742013119919947469548416190884842555317059682247072626112599280320512 : Int) + (u : Int) * evalPoly PP3c (u : Int) = _
    rw [Int.mul_comm]
  refine ⟨evmAdd_lt _ _, ?_, ?_, ?_, ?_⟩
  · rw [hT]
    clear hsl hsh hrange hs1 hs2 hstep ec hmT
    omega
  · rw [hT]
    clear hsl hsh hrange hs1 hs2 hstep ec hmT
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPP3] at hstep
    simp only [SLOPPc]
    generalize hB : toInt (pS3 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly PP3c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : toInt (evmSar 95 (evmMul (pS3 u) u)) = D at hs1 hs2 ⊢
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPP3] at hstep
    generalize hB : toInt (pS3 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly PP3c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : toInt (evmSar 95 (evmMul (pS3 u) u)) = D at hs1 hs2 ⊢
    omega

theorem qS2_facts {u : Nat} (hu : u ≤ Uc) :
    qS2 u < 2 ^ 256 ∧
    (71868555069335845025146221382 : Int) ≤ toInt (qS2 u) ∧
    toInt (qS2 u) ≤ (72115772843816219303631384287 : Int) ∧
    evalPoly QQ2c (u : Int) - SLOPQ2 ≤ toInt (qS2 u) * 40564819207303340847894502572032 ∧
    toInt (qS2 u) * 40564819207303340847894502572032 ≤ evalPoly QQ2c (u : Int) := by
  obtain ⟨hw, hlo, hhi, hsl, hsh⟩ := qS1_facts hu
  have htu : toInt u = (u : Int) := toInt_u hu
  simp only [Uc] at hu
  have hu256 : u < 2 ^ 256 := by omega
  have hu0 : (0 : Int) ≤ (u : Int) := by omega
  have huU : (u : Int) ≤ 2332259347626381040680638252 := by omega
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : toInt (evmMul (qS1 u) u) = toInt (qS1 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255] <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_105 (evmMul_lt (qS1 u) u)
  rw [hmT] at hs1 hs2
  have hdb : (-(247217774480374278485162905 : Int)) ≤ toInt (evmSar 105 (evmMul (qS1 u) u)) ∧
      toInt (evmSar 105 (evmMul (qS1 u) u)) ≤ (0 : Int) := by
    clear hsl hsh hmT hw htu hu256 hu
    generalize hB : toInt (qS1 u) * (u : Int) = B at hs1 hs2 hrange
    generalize hD : toInt (evmSar 105 (evmMul (qS1 u) u)) = D at hs1 hs2 ⊢
    omega
  have hcT : toInt Q3c = (72115772843816219303631384287 : Int) := toInt_of_lt (by simp only [Q3c]; omega)
  have hT : toInt (qS2 u) =
      toInt (evmSar 105 (evmMul (qS1 u) u)) + (72115772843816219303631384287 : Int) := by
    unfold qS2
    rw [← hcT]
    refine evmAdd_transport hwm (by simp only [Q3c]; omega) ?_ ?_
    · clear hsl hsh hrange hs1 hs2 hmT
      rw [hcT]
      simp only [ipow255]
      omega
    · clear hsl hsh hrange hs1 hs2 hmT
      rw [hcT]
      simp only [ipow255]
      omega
  have hstep := scaled_mul_step hsl hsh hu0 huU (by simp only [SLOPQ1]; omega)
  have ec : evalPoly QQ2c (u : Int) =
      (2925363287404360843667081097142065961887817512291358090461184 : Int) + evalPoly QQ1c (u : Int) * (u : Int) := by
    show (2925363287404360843667081097142065961887817512291358090461184 : Int) + (u : Int) * evalPoly QQ1c (u : Int) = _
    rw [Int.mul_comm]
  refine ⟨evmAdd_lt _ _, ?_, ?_, ?_, ?_⟩
  · rw [hT]
    clear hsl hsh hrange hs1 hs2 hstep ec hmT
    omega
  · rw [hT]
    clear hsl hsh hrange hs1 hs2 hstep ec hmT
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPQ1] at hstep
    simp only [SLOPQ2]
    generalize hB : toInt (qS1 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly QQ1c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : toInt (evmSar 105 (evmMul (qS1 u) u)) = D at hs1 hs2 ⊢
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPQ1] at hstep
    generalize hB : toInt (qS1 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly QQ1c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : toInt (evmSar 105 (evmMul (qS1 u) u)) = D at hs1 hs2 ⊢
    omega

theorem qS3_facts {u : Nat} (hu : u ≤ Uc) :
    qS3 u < 2 ^ 256 ∧
    (-(53722296096946541673620529149 : Int)) ≤ toInt (qS3 u) ∧
    toInt (qS3 u) ≤ (-(53191573560954338523077576765 : Int)) ∧
    evalPoly QQ3c (u : Int) - SLOPQ3 ≤ toInt (qS3 u) * 12855504354071922204335696738729300820177623950262342682411008 ∧
    toInt (qS3 u) * 12855504354071922204335696738729300820177623950262342682411008 ≤ evalPoly QQ3c (u : Int) := by
  obtain ⟨hw, hlo, hhi, hsl, hsh⟩ := qS2_facts hu
  have htu : toInt u = (u : Int) := toInt_u hu
  simp only [Uc] at hu
  have hu256 : u < 2 ^ 256 := by omega
  have hu0 : (0 : Int) ≤ (u : Int) := by omega
  have huU : (u : Int) ≤ 2332259347626381040680638252 := by omega
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : toInt (evmMul (qS2 u) u) = toInt (qS2 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255] <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_98 (evmMul_lt (qS2 u) u)
  rw [hmT] at hs1 hs2
  have hdb : (0 : Int) ≤ toInt (evmSar 98 (evmMul (qS2 u) u)) ∧
      toInt (evmSar 98 (evmMul (qS2 u) u)) ≤ (530722535992203150542952384 : Int) := by
    clear hsl hsh hmT hw htu hu256 hu
    generalize hB : toInt (qS2 u) * (u : Int) = B at hs1 hs2 hrange
    generalize hD : toInt (evmSar 98 (evmMul (qS2 u) u)) = D at hs1 hs2 ⊢
    omega
  have hcT : toInt Q2c = (53722296096946541673620529149 : Int) := toInt_of_lt (by simp only [Q2c]; omega)
  have hT : toInt (qS3 u) =
      toInt (evmSar 98 (evmMul (qS2 u) u)) - (53722296096946541673620529149 : Int) := by
    unfold qS3
    rw [← hcT]
    refine evmSub_transport hwm (by simp only [Q2c]; omega) ?_ ?_
    · clear hsl hsh hrange hs1 hs2 hmT
      rw [hcT]
      simp only [ipow255]
      omega
    · clear hsl hsh hrange hs1 hs2 hmT
      rw [hcT]
      simp only [ipow255]
      omega
  have hstep := scaled_mul_step hsl hsh hu0 huU (by simp only [SLOPQ2]; omega)
  have ec : evalPoly QQ3c (u : Int) =
      (-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int)) + evalPoly QQ2c (u : Int) * (u : Int) := by
    show (-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int)) + (u : Int) * evalPoly QQ2c (u : Int) = _
    rw [Int.mul_comm]
  refine ⟨evmSub_lt _ _, ?_, ?_, ?_, ?_⟩
  · rw [hT]
    clear hsl hsh hrange hs1 hs2 hstep ec hmT
    omega
  · rw [hT]
    clear hsl hsh hrange hs1 hs2 hstep ec hmT
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPQ2] at hstep
    simp only [SLOPQ3]
    generalize hB : toInt (qS2 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly QQ2c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : toInt (evmSar 98 (evmMul (qS2 u) u)) = D at hs1 hs2 ⊢
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPQ2] at hstep
    generalize hB : toInt (qS2 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly QQ2c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : toInt (evmSar 98 (evmMul (qS2 u) u)) = D at hs1 hs2 ⊢
    omega

theorem qS4_facts {u : Nat} (hu : u ≤ Uc) :
    qS4 u < 2 ^ 256 ∧
    (16208925125278758204286268920259 : Int) ≤ toInt (qS4 u) ∧
    toInt (qS4 u) ≤ (16613772931382142257332678212540 : Int) ∧
    evalPoly QQ4c (u : Int) - SLOPQ4 ≤ toInt (qS4 u) * 3978585891278293137243057985174566720803649206378781739523711815145275976100267004264448 ∧
    toInt (qS4 u) * 3978585891278293137243057985174566720803649206378781739523711815145275976100267004264448 ≤ evalPoly QQ4c (u : Int) := by
  obtain ⟨hw, hlo, hhi, hsl, hsh⟩ := qS3_facts hu
  have htu : toInt u = (u : Int) := toInt_u hu
  simp only [Uc] at hu
  have hu256 : u < 2 ^ 256 := by omega
  have hu0 : (0 : Int) ≤ (u : Int) := by omega
  have huU : (u : Int) ≤ 2332259347626381040680638252 := by omega
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : toInt (evmMul (qS3 u) u) = toInt (qS3 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255] <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_88 (evmMul_lt (qS3 u) u)
  rw [hmT] at hs1 hs2
  have hdb : (-(404847806103384053046409292281 : Int)) ≤ toInt (evmSar 88 (evmMul (qS3 u) u)) ∧
      toInt (evmSar 88 (evmMul (qS3 u) u)) ≤ (0 : Int) := by
    clear hsl hsh hmT hw htu hu256 hu
    generalize hB : toInt (qS3 u) * (u : Int) = B at hs1 hs2 hrange
    generalize hD : toInt (evmSar 88 (evmMul (qS3 u) u)) = D at hs1 hs2 ⊢
    omega
  have hcT : toInt Q1c = (16613772931382142257332678212540 : Int) := toInt_of_lt (by simp only [Q1c]; omega)
  have hT : toInt (qS4 u) =
      toInt (evmSar 88 (evmMul (qS3 u) u)) + (16613772931382142257332678212540 : Int) := by
    unfold qS4
    rw [← hcT]
    refine evmAdd_transport hwm (by simp only [Q1c]; omega) ?_ ?_
    · clear hsl hsh hrange hs1 hs2 hmT
      rw [hcT]
      simp only [ipow255]
      omega
    · clear hsl hsh hrange hs1 hs2 hmT
      rw [hcT]
      simp only [ipow255]
      omega
  have hstep := scaled_mul_step hsl hsh hu0 huU (by simp only [SLOPQ3]; omega)
  have ec : evalPoly QQ4c (u : Int) =
      (66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) + evalPoly QQ3c (u : Int) * (u : Int) := by
    show (66099322585698201304896817119077614168377752650671880634963909888244721857603941759324591151523373370374573118109777920 : Int) + (u : Int) * evalPoly QQ3c (u : Int) = _
    rw [Int.mul_comm]
  refine ⟨evmAdd_lt _ _, ?_, ?_, ?_, ?_⟩
  · rw [hT]
    clear hsl hsh hrange hs1 hs2 hstep ec hmT
    omega
  · rw [hT]
    clear hsl hsh hrange hs1 hs2 hstep ec hmT
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPQ3] at hstep
    simp only [SLOPQ4]
    generalize hB : toInt (qS3 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly QQ3c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : toInt (evmSar 88 (evmMul (qS3 u) u)) = D at hs1 hs2 ⊢
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPQ3] at hstep
    generalize hB : toInt (qS3 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly QQ3c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : toInt (evmSar 88 (evmMul (qS3 u) u)) = D at hs1 hs2 ⊢
    omega

theorem qS5_facts {u : Nat} (hu : u ≤ Uc) :
    qS5 u < 2 ^ 256 ∧
    (-(13972178604861559108982341686373 : Int)) ≤ toInt (qS5 u) ∧
    toInt (qS5 u) ≤ (-(12994050979812020140807993775660 : Int)) ∧
    evalPoly QQc (u : Int) - SLOPQc ≤ toInt (qS5 u) * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264 ∧
    toInt (qS5 u) * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264 ≤ evalPoly QQc (u : Int) := by
  obtain ⟨hw, hlo, hhi, hsl, hsh⟩ := qS4_facts hu
  have htu : toInt u = (u : Int) := toInt_u hu
  simp only [Uc] at hu
  have hu256 : u < 2 ^ 256 := by omega
  have hu0 : (0 : Int) ≤ (u : Int) := by omega
  have huU : (u : Int) ≤ 2332259347626381040680638252 := by omega
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : toInt (evmMul (qS4 u) u) = toInt (qS4 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255] <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_95 (evmMul_lt (qS4 u) u)
  rw [hmT] at hs1 hs2
  have hdb : (0 : Int) ≤ toInt (evmSar 95 (evmMul (qS4 u) u)) ∧
      toInt (evmSar 95 (evmMul (qS4 u) u)) ≤ (978127625049538968174347910713 : Int) := by
    clear hsl hsh hmT hw htu hu256 hu
    generalize hB : toInt (qS4 u) * (u : Int) = B at hs1 hs2 hrange
    generalize hD : toInt (evmSar 95 (evmMul (qS4 u) u)) = D at hs1 hs2 ⊢
    omega
  have hcT : toInt C0c = (13972178604861559108982341686373 : Int) := toInt_of_lt (by simp only [C0c]; omega)
  have hT : toInt (qS5 u) =
      toInt (evmSar 95 (evmMul (qS4 u) u)) - (13972178604861559108982341686373 : Int) := by
    unfold qS5
    rw [← hcT]
    refine evmSub_transport hwm (by simp only [C0c]; omega) ?_ ?_
    · clear hsl hsh hrange hs1 hs2 hmT
      rw [hcT]
      simp only [ipow255]
      omega
    · clear hsl hsh hrange hs1 hs2 hmT
      rw [hcT]
      simp only [ipow255]
      omega
  have hstep := scaled_mul_step hsl hsh hu0 huU (by simp only [SLOPQ4]; omega)
  have ec : evalPoly QQc (u : Int) =
      (-(2202127471863542086976841246818343354848349628124454549898853972183438719928614203693782484275214277955754824740140383208045055653095158108464873472 : Int)) + evalPoly QQ4c (u : Int) * (u : Int) := by
    show (-(2202127471863542086976841246818343354848349628124454549898853972183438719928614203693782484275214277955754824740140383208045055653095158108464873472 : Int)) + (u : Int) * evalPoly QQ4c (u : Int) = _
    rw [Int.mul_comm]
  refine ⟨evmSub_lt _ _, ?_, ?_, ?_, ?_⟩
  · rw [hT]
    clear hsl hsh hrange hs1 hs2 hstep ec hmT
    omega
  · rw [hT]
    clear hsl hsh hrange hs1 hs2 hstep ec hmT
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPQ4] at hstep
    simp only [SLOPQc]
    generalize hB : toInt (qS4 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly QQ4c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : toInt (evmSar 95 (evmMul (qS4 u) u)) = D at hs1 hs2 ⊢
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPQ4] at hstep
    generalize hB : toInt (qS4 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly QQ4c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : toInt (evmSar 95 (evmMul (qS4 u) u)) = D at hs1 hs2 ⊢
    omega

def pWordD (u : Nat) : Nat := pS4 u
def qWordD (u : Nat) : Nat := qS5 u

end LnGeneratedModel
