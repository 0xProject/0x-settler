import ExpProof.ExpYulProof
import ExpProof.Seam.RuntimeShared
import ExpProof.Seam.Guard
import ExpProof.Seam.Helpers
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

set_option maxHeartbeats 8000000 in
/-- `fun_panic_8(code)` reverts: its body is `mstore(0,…); mstore(0x20,code); revert(0x1c,0x24)`. -/
theorem call_fun_panic_8_revert_direct
    (code fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 600)) [FormalYul.word code] (.some "fun_panic_8")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .error EvmYul.Yul.Exception.Revert := by
  rw [show fuel + (extra + 600) = (fuel + extra) + 600 by omega]
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

set_option maxHeartbeats 8000000 in
/-- For inputs at/above the overflow threshold, `fun_expRayToWad_70` takes the guard branch and
reverts via `fun_panic_8(ARITHMETIC_OVERFLOW)`. -/
theorem call_fun_expRayToWad_70_revert_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (h1 : (0x8e383a2cdfa1b74a9422d2e1 : Nat) ≤ FormalYul.u256 x)
    (h2 : FormalYul.u256 x < 2 ^ 255) :
    EvmYul.Yul.call (fuel + 1000) [FormalYul.word x] (.some "fun_expRayToWad_70")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .error EvmYul.Yul.Exception.Revert := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_expRayToWad_70]
  simp only [yulFunction_fun_expRayToWad_70,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hconv44 :=
    call_convert_44_to_int256_direct (v := 0x8e383a2cdfa1b74a9422d2e1) (fuel := fuel) (extra := 867)
      (shared := shared) (hlookup := hlookup)
  have hcleanup :=
    call_cleanup_t_int256_direct (v := x) (fuel := fuel) (extra := 965)
      (shared := shared) (hlookup := hlookup)
  have hconvu :=
    call_convert_uint8_to_uint256_17_direct (fuel := fuel) (extra := 865)
      (shared := shared) (hlookup := hlookup)
  have hpanic :=
    call_fun_panic_8_revert_direct (code := 0x11) (fuel := fuel) (extra := 384)
      (shared := shared) (hlookup := hlookup)
  simp only [Nat.reduceAdd, FormalYul.word] at hconv44 hcleanup hconvu hpanic
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    slt_thresh_ge h1 h2,
    call_zero_value_for_split_t_int256_direct (fuel := fuel) (extra := 976)
      (shared := shared) (hlookup := hlookup),
    call_constant_ARITHMETIC_OVERFLOW_17_direct (fuel := fuel) (extra := 826)
      (shared := shared) (hlookup := hlookup),
    hcleanup, hconv44, hconvu, hpanic]

end ExpYul
