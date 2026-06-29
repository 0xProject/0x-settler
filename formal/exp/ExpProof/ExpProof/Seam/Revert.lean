import ExpProof.ExpYulProof
import ExpProof.Seam.RuntimeShared
import ExpProof.Seam.Guard
import FormalYul.Preservation

/-!
# Revert reduction for the overflow guard

`fun_expRayToWad_70` takes the overflow-guard branch for inputs at/above the threshold and calls
`fun_panic_8`, which does `mstore;mstore;revert(0x1c,0x24)`. These per-function "direct" lemmas
step the interpreter through that branch; mirrors the `ln` revert path.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- A Yul `revert(a, b)` primitive call halts with `.error .Revert`. -/
private theorem primCall_revert_yul (fuel : Nat) (s : EvmYul.Yul.State)
    (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s
        (EvmYul.Operation.System EvmYul.Operation.SOp.REVERT : EvmYul.Operation .Yul) [a, b] =
      .error EvmYul.Yul.Exception.Revert := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, List.not_mem_nil, EvmYul.Operation.System.injEq,
    Bool.not_eq_true, reduceCtorEq, or_self, and_false, if_false,
    EvmYul.step.eq_def]
  rfl

/-- The `zero_value_for_split_t_int256()` helper returns the word `0`. -/
private theorem call_zero_value_for_split_t_int256_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [] (.some "zero_value_for_split_t_int256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_zero_value_for_split_t_int256]
  simp only [yulFunction_zero_value_for_split_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

set_option maxHeartbeats 8000000 in
/-- `fun_panic_8(code)` reverts: its body is `mstore(0,…); mstore(0x20,code); revert(0x1c,0x24)`. -/
theorem call_fun_panic_8_revert_direct
    (code fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 600) [FormalYul.word code] (.some "fun_panic_8")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .error EvmYul.Yul.Exception.Revert := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_panic_8]
  simp only [yulFunction_fun_panic_8,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, primCall_revert_yul]

end ExpYul
