import LnProof.LnYulProof
import FormalYul.Preservation
import LnProof.Spec.Real
import LnProof.Seam.RealLog
import LnProof.Seam.RuntimeModel
import LnProof.Floor.CutEquiv

/-!
# Public ln runtime proof surface

This module is the entry point for statements about the generated
`LnWrapper` runtime. The generated `LnYulRuntime` and `LnYulProof` modules are
ignored artifacts rebuilt from `forge inspect`; the predicates below state the
public correctness properties against the `Real.log` fixed-point spec.
-/

namespace LnYul

open FormalYul
open FormalYul.Preservation
open Common.Word

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

/-- The compiled `lnWadToRay` runtime is correct against the `Real.log`
fixed-point spec for every 256-bit input. -/
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

/-- The compiled `lnWad` runtime is correct against the `Real.log` fixed-point
spec for every 256-bit input. -/
theorem lnWadRuntimeCorrect (x : Nat) (hx : x < 2 ^ 256) :
    LnWadRuntimeCorrect x :=
  lnWadRuntimeCorrect_of_cutCorrect (lnWadRuntimeCutCorrect_holds x hx)

/-! ## Runtime-level transports of the model properties -/

/-- At the wad scale-point the compiled `lnWadToRay` runtime returns `0`
(`ln(1) = 0`). -/
theorem run_ln_wad_to_ray_evm_zero_at_wad :
    run_ln_wad_to_ray_evm (10 ^ 18) = .ok 0 := by
  have hlt : (10 : Nat) ^ 18 < 2 ^ 256 := by norm_num
  have hux : u256 (10 ^ 18) = 10 ^ 18 := u256_eq_of_lt _ (by simp [WORD_MOD])
  have hpos : 1 ≤ u256 (10 ^ 18) := by rw [hux]; norm_num
  have hpos2 : u256 (10 ^ 18) < 2 ^ 255 := by rw [hux]; norm_num
  have h := run_ln_wad_to_ray_evm_eq_body (10 ^ 18) hpos hpos2
  rwa [hux, lnWadToRayBody_one_wad] at h

/-- At the wad scale-point the compiled `lnWad` runtime returns `0`
(`ln(1) = 0`). -/
theorem run_ln_wad_evm_zero_at_wad :
    run_ln_wad_evm (10 ^ 18) = .ok 0 := by
  have hux : u256 (10 ^ 18) = 10 ^ 18 := u256_eq_of_lt _ (by simp [WORD_MOD])
  have hpos : 1 ≤ u256 (10 ^ 18) := by rw [hux]; norm_num
  have hpos2 : u256 (10 ^ 18) < 2 ^ 255 := by rw [hux]; norm_num
  have h := run_ln_wad_evm_eq_body (10 ^ 18) hpos hpos2
  rwa [hux, lnWadBody_one_wad] at h

/-- The compiled `lnWadToRay` runtime result is signed-negative iff the input is
below the wad scale-point (`ln(x) < 0 ↔ x < 1`). -/
theorem lnWadToRayRuntimeNegativeIff (x : Nat) (hx : x < 2 ^ 256) :
    signedPositiveInput x →
      ∃ r, runLnWadToRaySigned x = .ok r ∧ (r < 0 ↔ u256 x < 10 ^ 18) := by
  intro hxSigned
  obtain ⟨hpos, hpos2⟩ := u256_pos_bounds hxSigned
  have hux : u256 x = x := u256_eq_of_lt x (by simpa [WORD_MOD] using hx)
  have hrun := run_ln_wad_to_ray_evm_eq_body x hpos hpos2
  rw [hux] at hpos hpos2 hrun ⊢
  refine ⟨int256 (lnWadToRayBody x), ?_, ?_⟩
  · rw [runLnWadToRaySigned_ok_iff]
    refine ⟨lnWadToRayBody x, hrun, ?_⟩
    show int256 (u256 (lnWadToRayBody x)) = int256 (lnWadToRayBody x)
    rw [u256_eq_of_lt _ (by simpa [WORD_MOD] using lnWadToRayBody_lt hx)]
  · exact LnFloorCert.lnWadToRayBody_negative_iff hpos hpos2

/-- The compiled `lnWad` runtime result is signed-negative iff the input is
below the wad scale-point (`ln(x) < 0 ↔ x < 1`). -/
theorem lnWadRuntimeNegativeIff (x : Nat) (hx : x < 2 ^ 256) :
    signedPositiveInput x →
      ∃ w, runLnWadSigned x = .ok w ∧ (w < 0 ↔ u256 x < 10 ^ 18) := by
  intro hxSigned
  obtain ⟨hpos, hpos2⟩ := u256_pos_bounds hxSigned
  have hux : u256 x = x := u256_eq_of_lt x (by simpa [WORD_MOD] using hx)
  have hrun := run_ln_wad_evm_eq_body x hpos hpos2
  rw [hux] at hpos hpos2 hrun ⊢
  refine ⟨int256 (lnWadBody x), ?_, ?_⟩
  · rw [runLnWadSigned_ok_iff]
    refine ⟨lnWadBody x, hrun, ?_⟩
    show int256 (u256 (lnWadBody x)) = int256 (lnWadBody x)
    rw [u256_eq_of_lt _ (by simpa [WORD_MOD] using to_wad_lt hx)]
  · exact LnFloorCert.lnWadBody_negative_iff hpos hpos2

/-- Runtime monotonicity: the compiled `lnWadToRay` signed results are
`≤`-ordered for ordered positive inputs (`x ≤ y < 2^255`). -/
theorem lnWadToRayRuntimeMono (x y : Nat) (hx : 0 < x) (hxy : x ≤ y) (hy : y < 2 ^ 255) :
    ∃ rx ry, runLnWadToRaySigned x = .ok rx ∧ runLnWadToRaySigned y = .ok ry ∧ rx ≤ ry := by
  have hpow : (2 : Nat) ^ 256 = 2 * 2 ^ 255 := by rw [pow_succ]; ring
  have hpp : 0 < (2 : Nat) ^ 255 := by positivity
  have hx256 : x < 2 ^ 256 := by omega
  have hy256 : y < 2 ^ 256 := by omega
  have huxx : u256 x = x := u256_eq_of_lt x (by simpa [WORD_MOD] using hx256)
  have huyy : u256 y = y := u256_eq_of_lt y (by simpa [WORD_MOD] using hy256)
  have hposx : 1 ≤ u256 x := by rw [huxx]; omega
  have hpos2x : u256 x < 2 ^ 255 := by rw [huxx]; omega
  have hposy : 1 ≤ u256 y := by rw [huyy]; omega
  have hpos2y : u256 y < 2 ^ 255 := by rw [huyy]; omega
  have hrunx := run_ln_wad_to_ray_evm_eq_body x hposx hpos2x
  have hruny := run_ln_wad_to_ray_evm_eq_body y hposy hpos2y
  rw [huxx] at hrunx
  rw [huyy] at hruny
  refine ⟨int256 (lnWadToRayBody x), int256 (lnWadToRayBody y), ?_, ?_, ?_⟩
  · rw [runLnWadToRaySigned_ok_iff]
    refine ⟨lnWadToRayBody x, hrunx, ?_⟩
    show int256 (u256 (lnWadToRayBody x)) = int256 (lnWadToRayBody x)
    rw [u256_eq_of_lt _ (by simpa [WORD_MOD] using lnWadToRayBody_lt hx256)]
  · rw [runLnWadToRaySigned_ok_iff]
    refine ⟨lnWadToRayBody y, hruny, ?_⟩
    show int256 (u256 (lnWadToRayBody y)) = int256 (lnWadToRayBody y)
    rw [u256_eq_of_lt _ (by simpa [WORD_MOD] using lnWadToRayBody_lt hy256)]
  · exact toInt_of_sle (lnWadToRayBody_lt hx256) (lnWadToRayBody_lt hy256)
      (lnWadToRayBody_mono hx hxy hy)

/-- Runtime monotonicity: the compiled `lnWad` signed results are `≤`-ordered
for ordered positive inputs (`x ≤ y < 2^255`). -/
theorem lnWadRuntimeMono (x y : Nat) (hx : 0 < x) (hxy : x ≤ y) (hy : y < 2 ^ 255) :
    ∃ wx wy, runLnWadSigned x = .ok wx ∧ runLnWadSigned y = .ok wy ∧ wx ≤ wy := by
  have hpow : (2 : Nat) ^ 256 = 2 * 2 ^ 255 := by rw [pow_succ]; ring
  have hpp : 0 < (2 : Nat) ^ 255 := by positivity
  have hx256 : x < 2 ^ 256 := by omega
  have hy256 : y < 2 ^ 256 := by omega
  have huxx : u256 x = x := u256_eq_of_lt x (by simpa [WORD_MOD] using hx256)
  have huyy : u256 y = y := u256_eq_of_lt y (by simpa [WORD_MOD] using hy256)
  have hposx : 1 ≤ u256 x := by rw [huxx]; omega
  have hpos2x : u256 x < 2 ^ 255 := by rw [huxx]; omega
  have hposy : 1 ≤ u256 y := by rw [huyy]; omega
  have hpos2y : u256 y < 2 ^ 255 := by rw [huyy]; omega
  have hrunx := run_ln_wad_evm_eq_body x hposx hpos2x
  have hruny := run_ln_wad_evm_eq_body y hposy hpos2y
  rw [huxx] at hrunx
  rw [huyy] at hruny
  refine ⟨int256 (lnWadBody x), int256 (lnWadBody y), ?_, ?_, ?_⟩
  · rw [runLnWadSigned_ok_iff]
    refine ⟨lnWadBody x, hrunx, ?_⟩
    show int256 (u256 (lnWadBody x)) = int256 (lnWadBody x)
    rw [u256_eq_of_lt _ (by simpa [WORD_MOD] using to_wad_lt hx256)]
  · rw [runLnWadSigned_ok_iff]
    refine ⟨lnWadBody y, hruny, ?_⟩
    show int256 (u256 (lnWadBody y)) = int256 (lnWadBody y)
    rw [u256_eq_of_lt _ (by simpa [WORD_MOD] using to_wad_lt hy256)]
  · exact toInt_of_sle (to_wad_lt hx256) (to_wad_lt hy256)
      (lnWadBody_mono hx hxy hy)

/-! ## Nonpositive input reverts -/

/-- The compiled `lnWadToRay` runtime reverts on every nonpositive signed input. -/
theorem lnWadToRayRuntimeRevertsNonpositive_holds (x : Nat) :
    LnWadToRayRuntimeRevertsNonpositive x := fun h => run_ln_wad_to_ray_evm_revert x h

/-- The compiled `lnWad` runtime reverts on every nonpositive signed input. -/
theorem lnWadRuntimeRevertsNonpositive_holds (x : Nat) :
    LnWadRuntimeRevertsNonpositive x := fun h => run_ln_wad_evm_revert x h

end

end LnYul
