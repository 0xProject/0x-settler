import ExpProof.Mono.Tree
import ExpProof.Seam.Value

/-!
# Bridge from the run-level value tree to `expTree`

`run_exp_ray_to_wad_evm_eq_tree` returns the inline `let`-shared `evm*` tree; `expTree` is the
same value organised into thin layers. They are definitionally equal (each layer unfolds to one
piece of the inline tree), so the run returns `expTree x` on the supported domain.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- `expTree x` is the inline value tree. -/
theorem run_exp_ray_to_wad_evm_eq_expTree
    (x : Nat)
    (hval : FormalYul.u256 x < 0x92b2f16cc66c5a4ae96e80d4 ∨ 2 ^ 255 ≤ FormalYul.u256 x)
    (hresultClean :
      EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word (expTree x)) =
        FormalYul.word (expTree x)) :
    run_exp_ray_to_wad_evm x = .ok (expTree x) := by
  have hcleanTree := hresultClean
  unfold expTree r1Tree r0Tree todTree odTree evTree vTree tTree kTree at hcleanTree
  unfold Cmask kRoundShift kHalfShift cInvQ192 k27Q235 ln2Q235 tArgShift squareShift at hcleanTree
  unfold ev0 ev1 ev2 ev3 ev4 evShift1 evShift2 evShift3 evShift4 at hcleanTree
  unfold od0 od1 od2 od3 od4 odShift1 odShift2 odShift3 odShift4 at hcleanTree
  unfold todShift foldShift scaleQ67 marginWord at hcleanTree
  rw [run_exp_ray_to_wad_evm_eq_tree x hval hcleanTree]
  unfold expTree r1Tree r0Tree todTree odTree evTree vTree tTree kTree
  unfold Cmask kRoundShift kHalfShift cInvQ192 k27Q235 ln2Q235 tArgShift squareShift
  unfold ev0 ev1 ev2 ev3 ev4 evShift1 evShift2 evShift3 evShift4
  unfold od0 od1 od2 od3 od4 odShift1 odShift2 odShift3 odShift4
  unfold todShift foldShift scaleQ67 marginWord
  rfl

end ExpYul
