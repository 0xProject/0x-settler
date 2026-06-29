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
  rfl

end ExpYul
