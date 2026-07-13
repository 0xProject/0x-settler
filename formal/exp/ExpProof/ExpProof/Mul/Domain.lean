import ExpProof.Mono.MulTree
import ExpProof.Mul.WordBridge

/-!
# `mulExpRay` value and panic domains

The runtime guard partitions canonical calldata into a value path and a `Panic(17)` path. Every
multiplier takes the same guard: the magnitude bound, the unconditional upper fence at the first
octave past the deficit envelope, and the accuracy test on the closing shift. Each predicate mirrors
one comparison of the compiled guard; `int256 (mulShiftTree y x) < 2` is exactly the runtime's
`slt(shift, 2)`.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- A canonical EVM word for an `int128` value. -/
def Int128Word (w : Nat) : Prop :=
  w < 2 ^ 256 ∧
    EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word w) = FormalYul.word w

theorem int128Word_zero : Int128Word 0 := by
  unfold Int128Word
  decide

theorem int128Word_scaleMax : Int128Word scaleMax := by
  unfold Int128Word
  decide

theorem int128Word_min : Int128Word (2 ^ 256 - 2 ^ 127) := by
  unfold Int128Word
  decide

/-- ABI words transported into this proof layer. -/
def MulExpRayCanonical (y x : Nat) : Prop :=
  Int128Word y ∧ x < 2 ^ 256

/-- The exact successful-input domain induced by the implementation guard. -/
def MulExpRayValueDomain (y x : Nat) : Prop :=
  MulExpRayCanonical y x ∧
    scaleShiftTree (absTree y) ≤ 127 ∧
      int256 x < int256 mulExpRayHi ∧ 2 ≤ int256 (mulShiftTree y x)

/-- The exact panic domain induced by the implementation guard. -/
def MulExpRayPanicDomain (y x : Nat) : Prop :=
  MulExpRayCanonical y x ∧
    (127 < scaleShiftTree (absTree y) ∨
      int256 mulExpRayHi ≤ int256 x ∨
        int256 (mulShiftTree y x) < 2)

/-- Canonical inputs are either accepted by the value guard or rejected by the panic guard. -/
theorem mulExpRay_value_or_panic_of_canonical {y x : Nat} (hcanon : MulExpRayCanonical y x) :
    MulExpRayValueDomain y x ∨ MulExpRayPanicDomain y x := by
  by_cases hscale : scaleShiftTree (absTree y) ≤ 127
  · by_cases hxhi : int256 x < int256 mulExpRayHi
    · by_cases hshift : 2 ≤ int256 (mulShiftTree y x)
      · exact Or.inl ⟨hcanon, hscale, hxhi, hshift⟩
      · exact Or.inr ⟨hcanon, Or.inr (Or.inr (by omega))⟩
    · exact Or.inr ⟨hcanon, Or.inr (Or.inl (by omega))⟩
  · exact Or.inr ⟨hcanon, Or.inl (by omega)⟩

/-- The accepted and rejected guard domains are disjoint. -/
theorem mulExpRay_value_not_panic {y x : Nat} :
    MulExpRayValueDomain y x → ¬ MulExpRayPanicDomain y x := by
  intro hv hp
  obtain ⟨_, hscale, hxhi, hlive⟩ := hv
  obtain ⟨_, hbadScale | hbadHi | hbadShift⟩ := hp
  · omega
  · omega
  · omega

/-- Canonical inputs are accepted exactly when they are not in the panic domain. -/
theorem mulExpRay_value_iff_not_panic {y x : Nat} (hcanon : MulExpRayCanonical y x) :
    MulExpRayValueDomain y x ↔ ¬ MulExpRayPanicDomain y x := by
  constructor
  · exact mulExpRay_value_not_panic
  · intro hnot
    rcases mulExpRay_value_or_panic_of_canonical hcanon with hval | hpanic
    · exact hval
    · exact False.elim (hnot hpanic)


/-! ## The guard word as a decidable predicate -/

/-- The guard word is the `if`-encoding of the exact panic condition. -/
theorem mulExpGuardTree_eq_ite {y x : Nat} (hx : x < 2 ^ 256) :
    mulExpGuardTree y x =
      if 127 < scaleShiftTree (absTree y) ∨ int256 mulExpRayHi ≤ int256 x ∨
          int256 (mulShiftTree y x) < 2 then 1 else 0 := by
  have hux : u256 x = x := u256_of_lt_pow256 hx
  have hs : u256 (scaleShiftTree (absTree y)) = scaleShiftTree (absTree y) :=
    u256_of_lt_pow256 (scaleShiftTree_lt _)
  have hsh : u256 (mulShiftTree y x) = mulShiftTree y x :=
    u256_of_lt_pow256 (mulShiftTree_lt y x)
  have hhim1 : evmSub mulExpRayHi 1 = mulExpRayHi - 1 := by
    unfold evmSub mulExpRayHi u256 WORD_MOD
    norm_num
  have hhim1w : evmSub mulExpRayHi 1 < 2 ^ 256 := evmSub_lt _ _
  have hhim1u : u256 (evmSub mulExpRayHi 1) = evmSub mulExpRayHi 1 :=
    u256_of_lt_pow256 hhim1w
  have h127 : u256 127 = 127 := u256_of_lt_pow256 (by norm_num)
  have h2 : u256 2 = 2 := u256_of_lt_pow256 (by norm_num)
  have hint2 : int256 (u256 2) = 2 := by rw [h2]; unfold int256; norm_num
  have hhi : int256 (evmSub mulExpRayHi 1) = int256 mulExpRayHi - 1 := by
    rw [hhim1, int256_mulExpRayHi]
    unfold mulExpRayHi int256
    norm_num
  have hscaleCmp : evmGt (scaleShiftTree (absTree y)) 127 =
      if 127 < scaleShiftTree (absTree y) then 1 else 0 := by
    rw [evmGt_eq_ite, hs, h127]
  have hxCmp : evmSgt x (evmSub mulExpRayHi 1) =
      if int256 mulExpRayHi ≤ int256 x then 1 else 0 := by
    rw [evmSgt_eq_evmSlt_swap, evmSlt_eq_ite, hhim1u, hux, hhi]
    split_ifs <;> omega
  have hshiftCmp : evmSlt (mulShiftTree y x) 2 =
      if int256 (mulShiftTree y x) < 2 then 1 else 0 := by
    rw [evmSlt_eq_ite, hsh, hint2]
  unfold mulExpGuardTree
  rw [hscaleCmp, hxCmp, evmOr_ite, hshiftCmp, evmOr_ite]
  simp only [or_assoc]

/-- The guard word is zero exactly on the accepted inputs. -/
theorem mulExpGuardTree_eq_zero_iff {y x : Nat} (hx : x < 2 ^ 256) :
    mulExpGuardTree y x = 0 ↔
      scaleShiftTree (absTree y) ≤ 127 ∧ int256 x < int256 mulExpRayHi ∧
        2 ≤ int256 (mulShiftTree y x) := by
  rw [mulExpGuardTree_eq_ite hx, ite_one_zero_eq_zero_iff]
  push_neg
  omega

/-- The guard word is one exactly on the rejected inputs. -/
theorem mulExpGuardTree_eq_one_iff {y x : Nat} (hx : x < 2 ^ 256) :
    mulExpGuardTree y x = 1 ↔
      127 < scaleShiftTree (absTree y) ∨ int256 mulExpRayHi ≤ int256 x ∨
        int256 (mulShiftTree y x) < 2 := by
  rw [mulExpGuardTree_eq_ite hx, ite_one_zero_eq_one_iff]

/-- The value domain is exactly the guard word being zero. -/
theorem valueDomain_iff_guard_eq_zero {y x : Nat} (hcanon : MulExpRayCanonical y x) :
    MulExpRayValueDomain y x ↔ mulExpGuardTree y x = 0 := by
  rw [mulExpGuardTree_eq_zero_iff hcanon.2]
  unfold MulExpRayValueDomain
  exact ⟨fun h => h.2, fun h => ⟨hcanon, h⟩⟩

/-- The panic domain is exactly the guard word being one. -/
theorem panicDomain_iff_guard_eq_one {y x : Nat} (hcanon : MulExpRayCanonical y x) :
    MulExpRayPanicDomain y x ↔ mulExpGuardTree y x = 1 := by
  rw [mulExpGuardTree_eq_one_iff hcanon.2]
  unfold MulExpRayPanicDomain
  exact ⟨fun h => h.2, fun h => ⟨hcanon, h⟩⟩

end ExpYul
