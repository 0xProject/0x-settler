import LnProof.LnYulProof
import FormalYul.Preservation
import LnProof.LnRealSpec
import LnProof.LnRealBridge
import LnProof.LnYulBody
import LnProof.ExpLogCutSpec

/-!
# Public ln runtime proof surface

This module is the tracked entry point for statements about the generated
`LnWrapper` runtime. The generated `LnYulRuntime` and `LnYulProof` modules are
ignored artifacts rebuilt from `forge inspect`; the predicates below state the
public correctness obligations against the `Real.log` fixed-point spec.
-/

namespace LnYul

open FormalYul
open FormalYul.Preservation

noncomputable section

def signedPositiveInput (x : Nat) : Prop :=
  0 < int256 (u256 x)

def signedNonpositiveInput (x : Nat) : Prop :=
  int256 (u256 x) ≤ 0

def signedResult (result : Nat) : Int :=
  int256 (u256 result)

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
    ∃ r, runLnWadToRaySigned x = .ok r ∧ LnFloorCert.CutLnWadRayBracket r x

def LnWadRuntimeCutCorrect (x : Nat) : Prop :=
  signedPositiveInput x →
    ∃ ray w, runLnWadToRaySigned x = .ok ray ∧ runLnWadSigned x = .ok w ∧
      LnFloorCert.CutLnWadSpec ray w x

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
  norm_num [signedPositiveInput, int256, u256, WORD_MOD]
    at h

theorem runLnWadToRaySigned_real_of_cut {x : Nat} {r : Int}
    (hx : 0 < x) (_hrun : runLnWadToRaySigned x = .ok r)
    (hcut : LnFloorCert.CutLnWadRayBracket r x) :
    LnRealSpec.LnWadToRaySpec x r :=
  LnRealBridge.cutLnWadRayBracket_real hx hcut

theorem runLnWadSigned_real_of_cut {x : Nat} {ray wad : Int}
    (hx : 0 < x) (_hrunRay : runLnWadToRaySigned x = .ok ray)
    (_hrunWad : runLnWadSigned x = .ok wad)
    (hcut : LnFloorCert.CutLnWadSpec ray wad x) :
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

/-- The compiled `lnWadToRay` runtime satisfies the explicit cut bracket for
every 256-bit input. The wrapper's ABI argument is always a 256-bit word, so
`x < 2 ^ 256` is the full natural domain; the runtime depends only on `u256 x`,
which equals `x` on that domain. -/
theorem lnWadToRayRuntimeCutCorrect_holds (x : Nat) (hx : x < 2 ^ 256) :
    LnWadToRayRuntimeCutCorrect x := by
  intro hxSigned
  obtain ⟨hpos, hpos2⟩ := u256_pos_bounds hxSigned
  have hux : u256 x = x := u256_eq_of_lt x (by simpa [WORD_MOD] using hx)
  have hrun := run_ln_wad_to_ray_evm_eq_body x hpos hpos2
  rw [hux] at hpos hpos2 hrun
  refine ⟨int256 (lnWadToRayBody x), ?_, ?_⟩
  · rw [runLnWadToRaySigned_ok_iff]
    refine ⟨lnWadToRayBody x, hrun, ?_⟩
    show int256 (u256 (lnWadToRayBody x)) = int256 (lnWadToRayBody x)
    rw [u256_eq_of_lt _ (by simpa [WORD_MOD] using lnWadToRayBody_lt hx)]
  · exact LnFloorCert.lnWadToRayBody_cut_spec hpos hpos2

/-- C1 discharged unconditionally for `lnWadToRay`: the compiled runtime is
correct against the `Real.log` fixed-point spec for every 256-bit input. -/
theorem lnWadToRayRuntimeCorrect (x : Nat) (hx : x < 2 ^ 256) :
    LnWadToRayRuntimeCorrect x :=
  lnWadToRayRuntimeCorrect_of_cutCorrect (lnWadToRayRuntimeCutCorrect_holds x hx)

/-- The compiled `lnWad` runtime satisfies the explicit cut spec (ray + wad
brackets) for every 256-bit input, using both the ray and wad runtime
equalities. -/
theorem lnWadRuntimeCutCorrect_holds (x : Nat) (hx : x < 2 ^ 256) :
    LnWadRuntimeCutCorrect x := by
  intro hxSigned
  obtain ⟨hpos, hpos2⟩ := u256_pos_bounds hxSigned
  have hux : u256 x = x := u256_eq_of_lt x (by simpa [WORD_MOD] using hx)
  have hrunRay := run_ln_wad_to_ray_evm_eq_body x hpos hpos2
  have hrunWad := run_ln_wad_evm_eq_body x hpos hpos2
  rw [hux] at hpos hpos2 hrunRay hrunWad
  refine ⟨int256 (lnWadToRayBody x), int256 (lnWadBody x), ?_, ?_, ?_⟩
  · rw [runLnWadToRaySigned_ok_iff]
    refine ⟨lnWadToRayBody x, hrunRay, ?_⟩
    show int256 (u256 (lnWadToRayBody x)) = int256 (lnWadToRayBody x)
    rw [u256_eq_of_lt _ (by simpa [WORD_MOD] using lnWadToRayBody_lt hx)]
  · rw [runLnWadSigned_ok_iff]
    refine ⟨lnWadBody x, hrunWad, ?_⟩
    show int256 (u256 (lnWadBody x)) = int256 (lnWadBody x)
    rw [u256_eq_of_lt _ (by simpa [WORD_MOD] using to_wad_lt hx)]
  · exact LnFloorCert.lnWadBody_cut_spec hpos hpos2

/-- C1 discharged unconditionally for `lnWad`: the compiled runtime is correct
against the `Real.log` fixed-point spec for every 256-bit input. -/
theorem lnWadRuntimeCorrect (x : Nat) (hx : x < 2 ^ 256) :
    LnWadRuntimeCorrect x :=
  lnWadRuntimeCorrect_of_cutCorrect (lnWadRuntimeCutCorrect_holds x hx)

end

end LnYul
