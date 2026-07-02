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
    (hval : FormalYul.u256 x < 0x8e383a2cdfa1b74a9422d2e1 ∨ 2 ^ 255 ≤ FormalYul.u256 x) :
    run_exp_ray_to_wad_evm x = .ok (expTree x) := by
  rw [run_exp_ray_to_wad_evm_eq_tree x hval]
  unfold expTree r1Tree r0Tree todTree odTree evTree vTree tTree kTree
  unfold Cmask kRoundShift kHalfShift cInvQ200 k27Q235 ln2Q235 tArgShift squareShift
  unfold ev0 ev1 ev2 ev3 ev4 evShift1 evShift2 evShift3 evShift4
  unfold od0 od1 od2 od3 od4 odShift1 odShift2 odShift3 odShift4
  unfold todShift expQShift wadWord marginWord
  rfl

end ExpYul
