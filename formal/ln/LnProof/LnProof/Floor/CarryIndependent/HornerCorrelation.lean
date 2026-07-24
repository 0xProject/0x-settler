import LnProof.Cert.HornerCorrelation
import LnProof.Floor.CarryIndependent.ApproximationReal
import LnProof.Floor.CarryIndependent.Horner
import LnProof.Floor.CarryIndependent.WordRuntime

open FormalYul FormalYul.Preservation

namespace LnFloorCarry

open LnYul Common.Poly

set_option maxRecDepth 8192

noncomputable section

theorem hornerCorrelationPErrorNum_eval (u : Nat) :
    evalPoly hornerCorrelationPErrorNum (u : Int) = pErrorNum u := by
  simp only [hornerCorrelationPErrorNum, pErrorNum, evalPoly]
  ring

theorem hornerCorrelationDErrorNum_eval (u : Nat) :
    evalPoly hornerCorrelationDErrorNum (u : Int) = dErrorNum u := by
  simp only [hornerCorrelationDErrorNum, dErrorNum, evalPoly]
  ring

theorem hornerCorrelationDNum_eval (u : Nat) :
    evalPoly hornerCorrelationDNum (u : Int) = -evalPoly QQc (u : Int) := by
  simp only [hornerCorrelationDNum, evalPoly_polyNeg]

theorem hornerCorrelationNum_eval (u : Nat) :
    evalPoly hornerCorrelationNum (u : Int) =
      2 ^ 112 *
        (2 ^ 29 * evalPoly PPc (u : Int) * dErrorNum u +
          pErrorNum u * (-evalPoly QQc (u : Int))) := by
  simp only [hornerCorrelationNum, evalPoly_polyScale, evalPoly_polyAdd,
    evalPoly_polyMul, hornerCorrelationPErrorNum_eval,
    hornerCorrelationDErrorNum_eval, hornerCorrelationDNum_eval]
  ring

theorem hornerCorrelationDen_eval (u : Nat) :
    evalPoly hornerCorrelationDen (u : Int) =
      (-evalPoly QQc (u : Int)) *
        (-evalPoly QQc (u : Int) + 2 ^ 113 * dErrorNum u) := by
  simp only [hornerCorrelationDen, evalPoly_polyMul, evalPoly_polyAdd,
    evalPoly_polyScale, hornerCorrelationDNum_eval,
    hornerCorrelationDErrorNum_eval]

theorem dErrorNum_nonneg (u : Nat) : 0 ≤ dErrorNum u := by
  unfold dErrorNum
  positivity

theorem hornerCorrelationDNum_pos {u : Nat} (hu : u ≤ Uc) :
    0 < evalPoly hornerCorrelationDNum (u : Int) := by
  have h := approximationRationalDen_pos
    (show u ≤ approximationMaxU by simpa [approximationMaxU] using hu)
  simpa only [approximationRationalDen, hornerCorrelationDNum] using h

theorem hornerCorrelationDen_pos {u : Nat} (hu : u ≤ Uc) :
    0 < evalPoly hornerCorrelationDen (u : Int) := by
  rw [hornerCorrelationDen_eval]
  have hD := hornerCorrelationDNum_pos hu
  rw [hornerCorrelationDNum_eval] at hD
  exact mul_pos hD (add_pos_of_pos_of_nonneg hD
    (mul_nonneg (by norm_num) (dErrorNum_nonneg u)))

theorem ratio_gap_eq (u : Nat) (hu : u ≤ Uc) :
    exactRatio u - shadowRatio u =
      (exactP u * dError u + pError u * exactD u) /
        (exactD u * (exactD u + dError u)) := by
  obtain ⟨_, _, _, _, hD, _⟩ := final_stage_sandwich_of_u hu
  have hDE : 0 < exactD u + dError u :=
    add_pos_of_pos_of_nonneg hD (dError_nonneg u)
  unfold exactRatio shadowRatio
  field_simp [hD.ne', hDE.ne']
  ring

theorem hornerCorrelation_fraction_eq (u : Nat) (hu : u ≤ Uc) :
    (evalPoly hornerCorrelationNum (u : Int) : Real) /
        evalPoly hornerCorrelationDen (u : Int) =
      (exactP u * dError u + pError u * exactD u) /
        (exactD u * (exactD u + dError u)) := by
  have hD := hornerCorrelationDNum_pos hu
  have hF : (0 : Int) ≤ dErrorNum u := dErrorNum_nonneg u
  have hDF : (0 : Int) <
      evalPoly hornerCorrelationDNum (u : Int) + 2 ^ 113 * dErrorNum u :=
    add_pos_of_pos_of_nonneg hD (mul_nonneg (by norm_num) hF)
  rw [hornerCorrelationNum_eval, hornerCorrelationDen_eval,
    pError_eq, dError_eq]
  unfold exactP exactD
  have hpScale : (pScale : Real) = 2 ^ 358 := by norm_num [pScale]
  have hqScale : (qScale : Real) = 2 ^ 386 := by norm_num [qScale]
  rw [hpScale, hqScale]
  push_cast
  rw [hornerCorrelationDNum_eval] at hD hDF
  let A : Real := evalPoly PPc (u : Int)
  let B : Real := -evalPoly QQc (u : Int)
  let E : Real := pErrorNum u
  let F : Real := dErrorNum u
  have hBR : 0 < B := by
    dsimp [B]
    exact_mod_cast hD
  have hBFR : 0 < B + 2 ^ 113 * F := by
    dsimp [B, F]
    exact_mod_cast hDF
  change
    5192296858534827628530496329220096 *
          (536870912 * A * F + E * B) /
        (B * (B + 10384593717069655257060992658440192 * F)) =
      (A / 2 ^ 358 * (F / 2 ^ 273) +
          E / 2 ^ 274 * (B / 2 ^ 386)) /
        (B / 2 ^ 386 * (B / 2 ^ 386 + F / 2 ^ 273))
  field_simp [hBR.ne', hBFR.ne']
  ring

theorem hornerCorrelation_gap_eq (u : Nat) (hu : u ≤ Uc) :
    exactRatio u - shadowRatio u =
      (evalPoly hornerCorrelationNum (u : Int) : Real) /
        evalPoly hornerCorrelationDen (u : Int) := by
  rw [ratio_gap_eq u hu, hornerCorrelation_fraction_eq u hu]

theorem hornerCorrelation_gap_le_endpoint {u : Nat} (hu : u ≤ Uc) :
    exactRatio u - shadowRatio u ≤
      exactRatio Uc - shadowRatio Uc := by
  have hcross := hornerCorrelation_nonneg (u := (u : Int))
    (Int.ofNat_zero_le u) (by exact_mod_cast hu)
  rw [hornerCorrelationCert_eval] at hcross
  have hratio := ratio_le_endpoint_of_cross_nonneg
    (num := hornerCorrelationNum) (den := hornerCorrelationDen)
    (u := (u : Int)) (endpoint := (Uc : Int))
    (hornerCorrelationDen_pos hu) (hornerCorrelationDen_pos (u := Uc) le_rfl)
    (by simpa only [endpointNum, endpointDen] using hcross)
  rw [hornerCorrelation_gap_eq u hu,
    hornerCorrelation_gap_eq Uc le_rfl]
  exact hratio

theorem endpoint_gap_nonneg :
    0 ≤ exactRatio Uc - shadowRatio Uc := by
  rw [ratio_gap_eq Uc le_rfl]
  obtain ⟨_, hpHi, _, _, hD, _⟩ := final_stage_sandwich_of_u (u := Uc) le_rfl
  have hpRuntime : (0 : Real) ≤ int256 (pS4 Uc) := by
    exact_mod_cast
      ((by norm_num : (0 : Int) ≤ 13131151825116561693704478250792).trans
        (pS4_facts (u := Uc) le_rfl).2.1)
  have hP : 0 ≤ exactP Uc := hpRuntime.trans hpHi
  have hpError := pError_nonneg Uc
  have hdError := dError_nonneg Uc
  exact div_nonneg
    (add_nonneg (mul_nonneg hP hdError) (mul_nonneg hpError hD.le))
    (mul_nonneg hD.le (add_nonneg hD.le hdError))

theorem lowHornerTerm_le_budget {m : Nat}
    (hmlo : 2 ^ 95 ≤ m) (hmsc : m < Sc) :
    hornerTerm m ≤ hornerBudget := by
  obtain ⟨hz0, hzEnd, _, _⟩ := low_endpoint_bounds hmlo hmsc
  have hu := (low_u_facts hmlo hmsc).1
  have hterm := hornerTerm_le_of_gap_le hz0 hzEnd endpoint_gap_nonneg
    (hornerCorrelation_gap_le_endpoint hu)
  rw [ratio_gap_eq Uc le_rfl] at hterm
  calc
    hornerTerm m ≤
        2 * rayScale * endpointZ *
          ((exactP Uc * dError Uc + pError Uc * exactD Uc) /
            (exactD Uc * (exactD Uc + dError Uc))) := hterm
    _ = hornerBudget := by
      simp only [hornerBudget, endpointUWord, Uc]
      ring

end

end LnFloorCarry
