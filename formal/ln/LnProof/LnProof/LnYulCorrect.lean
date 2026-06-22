import LnProof.LnYulProof
import LnProof.LnEvmMath
import LnProof.LnRealSpec
import LnProof.LnRealBridge

/-!
# Public ln runtime proof surface

This module is the tracked entry point for statements about the generated
`LnWrapper` runtime. The generated `LnYulRuntime` and `LnYulProof` modules are
ignored artifacts rebuilt from `forge inspect`; the predicates below state the
public correctness obligations against the `Real.log` fixed-point spec.
-/

namespace LnYul

open FormalYul

noncomputable section

def signedPositiveInput (x : Nat) : Prop :=
  0 < toInt (u256 x)

def signedNonpositiveInput (x : Nat) : Prop :=
  toInt (u256 x) ≤ 0

def signedResult (result : Nat) : Int :=
  toInt (u256 result)

def runLnWadToRaySigned (x : Nat) : Except String Int :=
  match run_ln_wad_to_ray_evm x with
  | .ok result => .ok (signedResult result)
  | .error err => .error err

def runLnWadSigned (x : Nat) : Except String Int :=
  match run_ln_wad_evm x with
  | .ok result => .ok (signedResult result)
  | .error err => .error err

def LnWadToRayRuntimeCorrect (x : Nat) : Prop :=
  signedPositiveInput x →
    ∃ r, runLnWadToRaySigned x = .ok r ∧ LnRealSpec.LnWadToRaySpec x r

def LnWadRuntimeCorrect (x : Nat) : Prop :=
  signedPositiveInput x →
    ∃ w, runLnWadSigned x = .ok w ∧ LnRealSpec.LnWadSpec x w

def LnWadToRayRuntimeRevertsNonpositive (x : Nat) : Prop :=
  signedNonpositiveInput x → run_ln_wad_to_ray_evm x = .error "revert"

def LnWadRuntimeRevertsNonpositive (x : Nat) : Prop :=
  signedNonpositiveInput x → run_ln_wad_evm x = .error "revert"

def LnWadToRayRuntimeCutCorrect (x : Nat) : Prop :=
  signedPositiveInput x →
    ∃ r, runLnWadToRaySigned x = .ok r ∧ LnRealBridge.CutLnWadRayBracket r x

def LnWadRuntimeCutCorrect (x : Nat) : Prop :=
  signedPositiveInput x →
    ∃ ray w, runLnWadToRaySigned x = .ok ray ∧ runLnWadSigned x = .ok w ∧
      LnRealBridge.CutLnWadSpec ray w x

theorem run_ln_wad_to_ray_evm_eq_callWord (x : Nat) :
    run_ln_wad_to_ray_evm x = FormalYul.callWord yulContract selector_lnWadToRay [x] := rfl

theorem run_ln_wad_evm_eq_callWord (x : Nat) :
    run_ln_wad_evm x = FormalYul.callWord yulContract selector_lnWad [x] := rfl

theorem runLnWadToRaySigned_ok_iff {x : Nat} {r : Int} :
    runLnWadToRaySigned x = .ok r ↔
      ∃ result, run_ln_wad_to_ray_evm x = .ok result ∧ signedResult result = r := by
  unfold runLnWadToRaySigned
  cases h : run_ln_wad_to_ray_evm x <;> simp

theorem runLnWadSigned_ok_iff {x : Nat} {w : Int} :
    runLnWadSigned x = .ok w ↔
      ∃ result, run_ln_wad_evm x = .ok result ∧ signedResult result = w := by
  unfold runLnWadSigned
  cases h : run_ln_wad_evm x <;> simp

theorem nat_pos_of_signedPositiveInput {x : Nat} (h : signedPositiveInput x) : 0 < x := by
  by_contra hx
  have hx0 : x = 0 := Nat.eq_zero_of_not_pos hx
  subst hx0
  norm_num [signedPositiveInput, toInt, u256_eq]
    at h

theorem runLnWadToRaySigned_real_of_cut {x : Nat} {r : Int}
    (hx : 0 < x) (_hrun : runLnWadToRaySigned x = .ok r)
    (hcut : LnRealBridge.CutLnWadRayBracket r x) :
    LnRealSpec.LnWadToRaySpec x r :=
  LnRealBridge.cutLnWadRayBracket_real hx hcut

theorem runLnWadSigned_real_of_cut {x : Nat} {ray wad : Int}
    (hx : 0 < x) (_hrunRay : runLnWadToRaySigned x = .ok ray)
    (_hrunWad : runLnWadSigned x = .ok wad)
    (hcut : LnRealBridge.CutLnWadSpec ray wad x) :
    LnRealSpec.LnWadSpec x wad :=
  LnRealBridge.cutLnWadSpec_real hx hcut

theorem lnWadToRayRuntimeCorrect_of_cutCorrect {x : Nat}
    (hcut : LnWadToRayRuntimeCutCorrect x) :
    LnWadToRayRuntimeCorrect x := by
  intro hxSigned
  obtain ⟨r, hrun, hcert⟩ := hcut hxSigned
  exact ⟨r, hrun, runLnWadToRaySigned_real_of_cut
    (nat_pos_of_signedPositiveInput hxSigned) hrun hcert⟩

theorem lnWadRuntimeCorrect_of_cutCorrect {x : Nat}
    (hcut : LnWadRuntimeCutCorrect x) :
    LnWadRuntimeCorrect x := by
  intro hxSigned
  obtain ⟨ray, w, hrunRay, hrunWad, hcert⟩ := hcut hxSigned
  exact ⟨w, hrunWad, runLnWadSigned_real_of_cut
    (nat_pos_of_signedPositiveInput hxSigned) hrunRay hrunWad hcert⟩

end

end LnYul
