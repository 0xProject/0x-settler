import LnProof.BridgeDiv
import LnProof.Poly

open FormalYul
open FormalYul.Preservation

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

namespace LnYul

open LnPoly

def Sc : Nat := 56022770974786139918731938227
def P4c : Nat := 4542704643877621417440
def P3c : Nat := 287579185854221620442209346
def P2c : Nat := 75095323053466847604974837616
def P1c : Nat := 55801080067338082314461576444
def C0c : Nat := 13972178604861559108982341686387
def Q4c : Nat := 4299840983308505679614339668444
def Q3c : Nat := 281702237671157106654810095
def Q2c : Nat := 53722296096946541673620529149
def Q1c : Nat := 16613772931382142257332678212554
def Kc : Nat := 7450580596923828125
def LN2c : Nat := 3273295013171879848905889459134067659407864468560
def BIASc : Nat := 116873961749927929127912020551516284764321243411868

/-- Largest |z| over the mantissa domain. -/
def Zc : Nat := 217494458298375249691265569565

theorem Zc_def : Zc = ((Sc - 2 ^ 95) * 2 ^ 100) / (2 ^ 95 + Sc) := by decide

/-- Largest `u`. -/
def Uc : Nat := 2332259347626381040680638252

theorem Uc_def : Uc = Zc * Zc / 2 ^ 104 := by decide

def SLOPP1 : Int := 19342813113834066795298815
def SLOPP2 : Int := 69057699520159162110141648894228821086113826043390164
def SLOPP3 : Int := 3955335645359842146091088249708864238312943862544998285589320092854593149420376176
def SLOPPc : Int := 9812004177583774588419572070418085567299104489606785913494676545320496277998160323177880419302954869373068096
def SLOPQ1 : Int := 0
def SLOPQ2 : Int := 10384593717069655257060992658440192
def SLOPQ3 : Int := 37075070122009811747227592743150621693886984893447588011835392
def SLOPQ4 : Int := 90447264747239228016757156189751796048865736349899133297194457280325857683859743526879232
def SLOPQc : Int := 368554503459564650655355223502937602070057924280391756343149979867298567572166014505521622720564112305091187444809728

/-! ## Pipeline words -/

def zWord (m : Nat) : Nat := evmSdiv (evmShl 100 (evmSub Sc m)) (evmAdd m Sc)

def uWord (z : Nat) : Nat := evmShr 104 (evmMul z z)

def pS1 (u : Nat) : Nat := evmSub (evmShr 84 (evmMul P4c u)) P3c
def pS2 (u : Nat) : Nat := evmAdd (evmSar 90 (evmMul (pS1 u) u)) P2c
def pS3 (u : Nat) : Nat := evmSub (evmSar 97 (evmMul (pS2 u) u)) P1c
def pS4 (u : Nat) : Nat := evmAdd (evmSar 87 (evmMul (pS3 u) u)) C0c

def qS1 (u : Nat) : Nat := evmSub u Q4c
def qS2 (u : Nat) : Nat := evmAdd (evmSar 113 (evmMul (qS1 u) u)) Q3c
def qS3 (u : Nat) : Nat := evmSub (evmSar 90 (evmMul (qS2 u) u)) Q2c
def qS4 (u : Nat) : Nat := evmAdd (evmSar 88 (evmMul (qS3 u) u)) Q1c
def qS5 (u : Nat) : Nat := evmSub (evmSar 95 (evmMul (qS4 u) u)) C0c

def lnWadToRayBody (x : Nat) : Nat :=
  let c := evmClz x
  let k := evmSub 160 c
  let m := evmShr 160 (evmShl c x)
  let z := zWord m
  let u := uWord z
  let p := pS4 u
  let q := qS5 u
  let r0 := evmSdiv (evmMul p z) q
  let r1 := evmMul Kc r0
  let r2 := evmAdd (evmMul LN2c k) r1
  let r3 := evmAdd BIASc r2
  let r4 := evmSar 72 r3
  evmAdd (evmIszero (evmNot r4)) r4

def lnWadBody (x : Nat) : Nat :=
  let r := lnWadToRayBody x
  evmSdiv (evmSub r (evmMul 999999999 (evmSgt 0 r))) 1000000000

/-! ## Suffix polynomials (numeral coefficients) -/

def PP1c : List Int := [(-(5562590447406762316237749022682109217671325297934336 : Int) : Int), (4542704643877621417440 : Int)]
def PP2c : List Int := (1798175745614395766239082622521528960720477616324792863638563111730471590055378944 : Int) :: PP1c
def PP3c : List Int := (-(211724653123857194763950383720687822670307458715746667734762451892717657012841722322962591250252321890880192512 : Int) : Int) :: PP2c
def PPc : List Int := (8203564106909714963200842018502018851024462725819431901516251320229929630934299039494945066816553616430456446611805193566972803059892092928 : Int) :: PP3c

def QQ1c : List Int := [(-(4299840983308505679614339668444 : Int) : Int), (1 : Int)]
def QQ2c : List Int := (2925363287404360843667081098480704995728827760271876675338240 : Int) :: QQ1c
def QQ3c : List Int := (-(690627211385037298547738551962892852267586075469791719173459072596031701017399264062472192 : Int) : Int) :: QQ2c
def QQ4c : List Int := (66099322585698201304896817119133314370855648754593283446756353822335972946493244703677923116935407234039976856169480192 : Int) :: QQ3c
def QQc : List Int := (-(2202127471863542086976841246820549867195347718960342176144462014556523185327760268707187588705852038374958668534379582118318610928980329275922055168 : Int) : Int) :: QQ4c

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

theorem toInt_u {u : Nat} (h : u ≤ Uc) : int256 u = (u : Int) := by
  refine toInt_of_lt ?_
  simp only [Uc] at h
  omega

/-! ## q-chain exact first stage -/

theorem qS1_facts {u : Nat} (hu : u ≤ Uc) :
    qS1 u < 2 ^ 256 ∧
    (-(4299840983308505679614339668444 : Int)) ≤ int256 (qS1 u) ∧
    int256 (qS1 u) ≤ (-(4297508723960879298573659030192 : Int)) ∧
    evalPoly QQ1c (u : Int) - SLOPQ1 ≤ int256 (qS1 u) * 1 ∧
    int256 (qS1 u) * 1 ≤ evalPoly QQ1c (u : Int) := by
  have htu : int256 u = (u : Int) := toInt_u hu
  simp only [Uc] at hu
  have hu256 : u < 2 ^ 256 := by omega
  have hT : int256 (qS1 u) = (u : Int) - (4299840983308505679614339668444 : Int) := by
    unfold qS1
    have h2 : int256 Q4c = (4299840983308505679614339668444 : Int) := toInt_of_lt (by simp only [Q4c]; omega)
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

/-! ## p-chain first stage -/

theorem pS1_facts {u : Nat} (hu : u ≤ Uc) :
    pS1 u < 2 ^ 256 ∧
    (-(287579185854221620442209346 : Int)) ≤ int256 (pS1 u) ∧
    int256 (pS1 u) ≤ (-(287031449322475267106929263 : Int)) ∧
    evalPoly PP1c (u : Int) - SLOPP1 ≤ int256 (pS1 u) * 19342813113834066795298816 ∧
    int256 (pS1 u) * 19342813113834066795298816 ≤ evalPoly PP1c (u : Int) := by
  simp only [Uc] at hu
  have hm1 : evmMul P4c u = P4c * u := by
    unfold evmMul u256
    simp only [word_mod_eq, P4c]
    omega
  have hm1lt : P4c * u < 2 ^ 256 := by simp only [P4c]; omega
  have hd1 : evmShr 84 (evmMul P4c u) = P4c * u / 2 ^ 84 := by
    rw [hm1]; exact evmShr_eq_div_84 hm1lt
  have hT : int256 (pS1 u) = ((P4c * u / 2 ^ 84 : Nat) : Int) - (287579185854221620442209346 : Int) := by
    unfold pS1
    rw [hd1]
    have h1 : int256 (P4c * u / 2 ^ 84 : Nat) = ((P4c * u / 2 ^ 84 : Nat) : Int) :=
      toInt_of_lt (by simp only [P4c]; omega)
    have h2 : int256 P3c = (287579185854221620442209346 : Int) := toInt_of_lt (by simp only [P3c]; omega)
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
    (74553528440556136823910938445 : Int) ≤ int256 (pS2 u) ∧
    int256 (pS2 u) ≤ (75095323053466847604974837616 : Int) ∧
    evalPoly PP2c (u : Int) - SLOPP2 ≤ int256 (pS2 u) * 23945242826029513411849172299223580994042798784118784 ∧
    int256 (pS2 u) * 23945242826029513411849172299223580994042798784118784 ≤ evalPoly PP2c (u : Int) := by
  obtain ⟨hw, hlo, hhi, hsl, hsh⟩ := pS1_facts hu
  have htu : int256 u = (u : Int) := toInt_u hu
  simp only [Uc] at hu
  have hu256 : u < 2 ^ 256 := by omega
  have hu0 : (0 : Int) ≤ (u : Int) := by omega
  have huU : (u : Int) ≤ 2332259347626381040680638252 := by omega
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : int256 (evmMul (pS1 u) u) = int256 (pS1 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255] <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_90 (evmMul_lt (pS1 u) u)
  rw [hmT] at hs1 hs2
  have hdb : (-(541794612910710781063899171 : Int)) ≤ int256 (evmSar 90 (evmMul (pS1 u) u)) ∧
      int256 (evmSar 90 (evmMul (pS1 u) u)) ≤ (0 : Int) := by
    clear hsl hsh hmT hw htu hu256 hu
    generalize hB : int256 (pS1 u) * (u : Int) = B at hs1 hs2 hrange
    generalize hD : int256 (evmSar 90 (evmMul (pS1 u) u)) = D at hs1 hs2 ⊢
    omega
  have hcT : int256 P2c = (75095323053466847604974837616 : Int) := toInt_of_lt (by simp only [P2c]; omega)
  have hT : int256 (pS2 u) =
      int256 (evmSar 90 (evmMul (pS1 u) u)) + (75095323053466847604974837616 : Int) := by
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
    generalize hB : int256 (pS1 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly PP1c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : int256 (evmSar 90 (evmMul (pS1 u) u)) = D at hs1 hs2 ⊢
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPP1] at hstep
    generalize hB : int256 (pS1 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly PP1c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : int256 (evmSar 90 (evmMul (pS1 u) u)) = D at hs1 hs2 ⊢
    omega

theorem pS3_facts {u : Nat} (hu : u ≤ Uc) :
    pS3 u < 2 ^ 256 ∧
    (-(55801080067338082314461576444 : Int)) ≤ int256 (pS3 u) ∧
    int256 (pS3 u) ≤ (-(54695780110880438990702023699 : Int)) ∧
    evalPoly PP3c (u : Int) - SLOPP3 ≤ int256 (pS3 u) * 3794275180128377091639574036764685364535950857523710002444946112771297432041422848 ∧
    int256 (pS3 u) * 3794275180128377091639574036764685364535950857523710002444946112771297432041422848 ≤ evalPoly PP3c (u : Int) := by
  obtain ⟨hw, hlo, hhi, hsl, hsh⟩ := pS2_facts hu
  have htu : int256 u = (u : Int) := toInt_u hu
  simp only [Uc] at hu
  have hu256 : u < 2 ^ 256 := by omega
  have hu0 : (0 : Int) ≤ (u : Int) := by omega
  have huU : (u : Int) ≤ 2332259347626381040680638252 := by omega
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : int256 (evmMul (pS2 u) u) = int256 (pS2 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255] <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_97 (evmMul_lt (pS2 u) u)
  rw [hmT] at hs1 hs2
  have hdb : (0 : Int) ≤ int256 (evmSar 97 (evmMul (pS2 u) u)) ∧
      int256 (evmSar 97 (evmMul (pS2 u) u)) ≤ (1105299956457643323759552745 : Int) := by
    clear hsl hsh hmT hw htu hu256 hu
    generalize hB : int256 (pS2 u) * (u : Int) = B at hs1 hs2 hrange
    generalize hD : int256 (evmSar 97 (evmMul (pS2 u) u)) = D at hs1 hs2 ⊢
    omega
  have hcT : int256 P1c = (55801080067338082314461576444 : Int) := toInt_of_lt (by simp only [P1c]; omega)
  have hT : int256 (pS3 u) =
      int256 (evmSar 97 (evmMul (pS2 u) u)) - (55801080067338082314461576444 : Int) := by
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
      (-(211724653123857194763950383720687822670307458715746667734762451892717657012841722322962591250252321890880192512 : Int)) + evalPoly PP2c (u : Int) * (u : Int) := by
    show (-(211724653123857194763950383720687822670307458715746667734762451892717657012841722322962591250252321890880192512 : Int)) + (u : Int) * evalPoly PP2c (u : Int) = _
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
    generalize hB : int256 (pS2 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly PP2c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : int256 (evmSar 97 (evmMul (pS2 u) u)) = D at hs1 hs2 ⊢
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPP2] at hstep
    generalize hB : int256 (pS2 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly PP2c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : int256 (evmSar 97 (evmMul (pS2 u) u)) = D at hs1 hs2 ⊢
    omega

theorem pS4_facts {u : Nat} (hu : u ≤ Uc) :
    pS4 u < 2 ^ 256 ∧
    (13131151825116561693704478250792 : Int) ≤ int256 (pS4 u) ∧
    int256 (pS4 u) ≤ (13972178604861559108982341686387 : Int) ∧
    evalPoly PPc (u : Int) - SLOPPc ≤ int256 (pS4 u) * 587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744 ∧
    int256 (pS4 u) * 587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744 ≤ evalPoly PPc (u : Int) := by
  obtain ⟨hw, hlo, hhi, hsl, hsh⟩ := pS3_facts hu
  have htu : int256 u = (u : Int) := toInt_u hu
  simp only [Uc] at hu
  have hu256 : u < 2 ^ 256 := by omega
  have hu0 : (0 : Int) ≤ (u : Int) := by omega
  have huU : (u : Int) ≤ 2332259347626381040680638252 := by omega
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : int256 (evmMul (pS3 u) u) = int256 (pS3 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255] <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_87 (evmMul_lt (pS3 u) u)
  rw [hmT] at hs1 hs2
  have hdb : (-(841026779744997415277863435595 : Int)) ≤ int256 (evmSar 87 (evmMul (pS3 u) u)) ∧
      int256 (evmSar 87 (evmMul (pS3 u) u)) ≤ (0 : Int) := by
    clear hsl hsh hmT hw htu hu256 hu
    generalize hB : int256 (pS3 u) * (u : Int) = B at hs1 hs2 hrange
    generalize hD : int256 (evmSar 87 (evmMul (pS3 u) u)) = D at hs1 hs2 ⊢
    omega
  have hcT : int256 C0c = (13972178604861559108982341686387 : Int) := toInt_of_lt (by simp only [C0c]; omega)
  have hT : int256 (pS4 u) =
      int256 (evmSar 87 (evmMul (pS3 u) u)) + (13972178604861559108982341686387 : Int) := by
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
      (8203564106909714963200842018502018851024462725819431901516251320229929630934299039494945066816553616430456446611805193566972803059892092928 : Int) + evalPoly PP3c (u : Int) * (u : Int) := by
    show (8203564106909714963200842018502018851024462725819431901516251320229929630934299039494945066816553616430456446611805193566972803059892092928 : Int) + (u : Int) * evalPoly PP3c (u : Int) = _
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
    generalize hB : int256 (pS3 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly PP3c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : int256 (evmSar 87 (evmMul (pS3 u) u)) = D at hs1 hs2 ⊢
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPP3] at hstep
    generalize hB : int256 (pS3 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly PP3c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : int256 (evmSar 87 (evmMul (pS3 u) u)) = D at hs1 hs2 ⊢
    omega

theorem qS2_facts {u : Nat} (hu : u ≤ Uc) :
    qS2 u < 2 ^ 256 ∧
    (280736543239593144629477427 : Int) ≤ int256 (qS2 u) ∧
    int256 (qS2 u) ≤ (281702237671157106654810095 : Int) ∧
    evalPoly QQ2c (u : Int) - SLOPQ2 ≤ int256 (qS2 u) * 10384593717069655257060992658440192 ∧
    int256 (qS2 u) * 10384593717069655257060992658440192 ≤ evalPoly QQ2c (u : Int) := by
  obtain ⟨hw, hlo, hhi, hsl, hsh⟩ := qS1_facts hu
  have htu : int256 u = (u : Int) := toInt_u hu
  simp only [Uc] at hu
  have hu256 : u < 2 ^ 256 := by omega
  have hu0 : (0 : Int) ≤ (u : Int) := by omega
  have huU : (u : Int) ≤ 2332259347626381040680638252 := by omega
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : int256 (evmMul (qS1 u) u) = int256 (qS1 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255] <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_113 (evmMul_lt (qS1 u) u)
  rw [hmT] at hs1 hs2
  have hdb : (-(965694431563962025332668 : Int)) ≤ int256 (evmSar 113 (evmMul (qS1 u) u)) ∧
      int256 (evmSar 113 (evmMul (qS1 u) u)) ≤ (0 : Int) := by
    clear hsl hsh hmT hw htu hu256 hu
    generalize hB : int256 (qS1 u) * (u : Int) = B at hs1 hs2 hrange
    generalize hD : int256 (evmSar 113 (evmMul (qS1 u) u)) = D at hs1 hs2 ⊢
    omega
  have hcT : int256 Q3c = (281702237671157106654810095 : Int) := toInt_of_lt (by simp only [Q3c]; omega)
  have hT : int256 (qS2 u) =
      int256 (evmSar 113 (evmMul (qS1 u) u)) + (281702237671157106654810095 : Int) := by
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
      (2925363287404360843667081098480704995728827760271876675338240 : Int) + evalPoly QQ1c (u : Int) * (u : Int) := by
    show (2925363287404360843667081098480704995728827760271876675338240 : Int) + (u : Int) * evalPoly QQ1c (u : Int) = _
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
    generalize hB : int256 (qS1 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly QQ1c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : int256 (evmSar 113 (evmMul (qS1 u) u)) = D at hs1 hs2 ⊢
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPQ1] at hstep
    generalize hB : int256 (qS1 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly QQ1c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : int256 (evmSar 113 (evmMul (qS1 u) u)) = D at hs1 hs2 ⊢
    omega

theorem qS3_facts {u : Nat} (hu : u ≤ Uc) :
    qS3 u < 2 ^ 256 ∧
    (-(53722296096946541673620529149 : Int)) ≤ int256 (qS3 u) ∧
    int256 (qS3 u) ≤ (-(53191573560954338523077576765 : Int)) ∧
    evalPoly QQ3c (u : Int) - SLOPQ3 ≤ int256 (qS3 u) * 12855504354071922204335696738729300820177623950262342682411008 ∧
    int256 (qS3 u) * 12855504354071922204335696738729300820177623950262342682411008 ≤ evalPoly QQ3c (u : Int) := by
  obtain ⟨hw, hlo, hhi, hsl, hsh⟩ := qS2_facts hu
  have htu : int256 u = (u : Int) := toInt_u hu
  simp only [Uc] at hu
  have hu256 : u < 2 ^ 256 := by omega
  have hu0 : (0 : Int) ≤ (u : Int) := by omega
  have huU : (u : Int) ≤ 2332259347626381040680638252 := by omega
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : int256 (evmMul (qS2 u) u) = int256 (qS2 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255] <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_90 (evmMul_lt (qS2 u) u)
  rw [hmT] at hs1 hs2
  have hdb : (0 : Int) ≤ int256 (evmSar 90 (evmMul (qS2 u) u)) ∧
      int256 (evmSar 90 (evmMul (qS2 u) u)) ≤ (530722535992203150542952384 : Int) := by
    clear hsl hsh hmT hw htu hu256 hu
    generalize hB : int256 (qS2 u) * (u : Int) = B at hs1 hs2 hrange
    generalize hD : int256 (evmSar 90 (evmMul (qS2 u) u)) = D at hs1 hs2 ⊢
    omega
  have hcT : int256 Q2c = (53722296096946541673620529149 : Int) := toInt_of_lt (by simp only [Q2c]; omega)
  have hT : int256 (qS3 u) =
      int256 (evmSar 90 (evmMul (qS2 u) u)) - (53722296096946541673620529149 : Int) := by
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
    generalize hB : int256 (qS2 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly QQ2c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : int256 (evmSar 90 (evmMul (qS2 u) u)) = D at hs1 hs2 ⊢
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPQ2] at hstep
    generalize hB : int256 (qS2 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly QQ2c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : int256 (evmSar 90 (evmMul (qS2 u) u)) = D at hs1 hs2 ⊢
    omega

theorem qS4_facts {u : Nat} (hu : u ≤ Uc) :
    qS4 u < 2 ^ 256 ∧
    (16208925125278758204286268920273 : Int) ≤ int256 (qS4 u) ∧
    int256 (qS4 u) ≤ (16613772931382142257332678212554 : Int) ∧
    evalPoly QQ4c (u : Int) - SLOPQ4 ≤ int256 (qS4 u) * 3978585891278293137243057985174566720803649206378781739523711815145275976100267004264448 ∧
    int256 (qS4 u) * 3978585891278293137243057985174566720803649206378781739523711815145275976100267004264448 ≤ evalPoly QQ4c (u : Int) := by
  obtain ⟨hw, hlo, hhi, hsl, hsh⟩ := qS3_facts hu
  have htu : int256 u = (u : Int) := toInt_u hu
  simp only [Uc] at hu
  have hu256 : u < 2 ^ 256 := by omega
  have hu0 : (0 : Int) ≤ (u : Int) := by omega
  have huU : (u : Int) ≤ 2332259347626381040680638252 := by omega
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : int256 (evmMul (qS3 u) u) = int256 (qS3 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255] <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_88 (evmMul_lt (qS3 u) u)
  rw [hmT] at hs1 hs2
  have hdb : (-(404847806103384053046409292281 : Int)) ≤ int256 (evmSar 88 (evmMul (qS3 u) u)) ∧
      int256 (evmSar 88 (evmMul (qS3 u) u)) ≤ (0 : Int) := by
    clear hsl hsh hmT hw htu hu256 hu
    generalize hB : int256 (qS3 u) * (u : Int) = B at hs1 hs2 hrange
    generalize hD : int256 (evmSar 88 (evmMul (qS3 u) u)) = D at hs1 hs2 ⊢
    omega
  have hcT : int256 Q1c = (16613772931382142257332678212554 : Int) := toInt_of_lt (by simp only [Q1c]; omega)
  have hT : int256 (qS4 u) =
      int256 (evmSar 88 (evmMul (qS3 u) u)) + (16613772931382142257332678212554 : Int) := by
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
      (66099322585698201304896817119133314370855648754593283446756353822335972946493244703677923116935407234039976856169480192 : Int) + evalPoly QQ3c (u : Int) * (u : Int) := by
    show (66099322585698201304896817119133314370855648754593283446756353822335972946493244703677923116935407234039976856169480192 : Int) + (u : Int) * evalPoly QQ3c (u : Int) = _
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
    generalize hB : int256 (qS3 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly QQ3c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : int256 (evmSar 88 (evmMul (qS3 u) u)) = D at hs1 hs2 ⊢
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPQ3] at hstep
    generalize hB : int256 (qS3 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly QQ3c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : int256 (evmSar 88 (evmMul (qS3 u) u)) = D at hs1 hs2 ⊢
    omega

theorem qS5_facts {u : Nat} (hu : u ≤ Uc) :
    qS5 u < 2 ^ 256 ∧
    (-(13972178604861559108982341686387 : Int)) ≤ int256 (qS5 u) ∧
    int256 (qS5 u) ≤ (-(12994050979812020140807993775673 : Int)) ∧
    evalPoly QQc (u : Int) - SLOPQc ≤ int256 (qS5 u) * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264 ∧
    int256 (qS5 u) * 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264 ≤ evalPoly QQc (u : Int) := by
  obtain ⟨hw, hlo, hhi, hsl, hsh⟩ := qS4_facts hu
  have htu : int256 u = (u : Int) := toInt_u hu
  simp only [Uc] at hu
  have hu256 : u < 2 ^ 256 := by omega
  have hu0 : (0 : Int) ≤ (u : Int) := by omega
  have huU : (u : Int) ≤ 2332259347626381040680638252 := by omega
  have hrange := mul_range hlo hhi hu0 huU
  have hmT : int256 (evmMul (qS4 u) u) = int256 (qS4 u) * (u : Int) := by
    rw [← htu]
    refine evmMul_transport hw hu256 ?_ ?_ <;> rw [htu] <;>
      simp only [ipow255] <;> omega
  obtain ⟨hwm, hs1, hs2⟩ := evmSar_sandwich_95 (evmMul_lt (qS4 u) u)
  rw [hmT] at hs1 hs2
  have hdb : (0 : Int) ≤ int256 (evmSar 95 (evmMul (qS4 u) u)) ∧
      int256 (evmSar 95 (evmMul (qS4 u) u)) ≤ (978127625049538968174347910714 : Int) := by
    clear hsl hsh hmT hw htu hu256 hu
    generalize hB : int256 (qS4 u) * (u : Int) = B at hs1 hs2 hrange
    generalize hD : int256 (evmSar 95 (evmMul (qS4 u) u)) = D at hs1 hs2 ⊢
    omega
  have hcT : int256 C0c = (13972178604861559108982341686387 : Int) := toInt_of_lt (by simp only [C0c]; omega)
  have hT : int256 (qS5 u) =
      int256 (evmSar 95 (evmMul (qS4 u) u)) - (13972178604861559108982341686387 : Int) := by
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
      (-(2202127471863542086976841246820549867195347718960342176144462014556523185327760268707187588705852038374958668534379582118318610928980329275922055168 : Int)) + evalPoly QQ4c (u : Int) * (u : Int) := by
    show (-(2202127471863542086976841246820549867195347718960342176144462014556523185327760268707187588705852038374958668534379582118318610928980329275922055168 : Int)) + (u : Int) * evalPoly QQ4c (u : Int) = _
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
    generalize hB : int256 (qS4 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly QQ4c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : int256 (evmSar 95 (evmMul (qS4 u) u)) = D at hs1 hs2 ⊢
    omega
  · rw [hT, ec]
    clear hrange hdb hsl hsh hmT hwm hw htu hu256 hcT hu hlo hhi
    simp only [SLOPQ4] at hstep
    generalize hB : int256 (qS4 u) * (u : Int) = B at hs1 hs2 hstep
    generalize hE : evalPoly QQ4c (u : Int) * (u : Int) = E at hstep ⊢
    generalize hD : int256 (evmSar 95 (evmMul (qS4 u) u)) = D at hs1 hs2 ⊢
    omega

def pWordD (u : Nat) : Nat := pS4 u
def qWordD (u : Nat) : Nat := qS5 u

end LnYul
