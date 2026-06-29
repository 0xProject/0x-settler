import ExpProof.ExpYulProof
import ExpProof.Seam.RuntimeShared
import ExpProof.Seam.Helpers
import ExpProof.Seam.Dispatcher
import FormalYul.Preservation

/-!
# Value-path reductions for `expRayToWad`

The non-reverting branch. This file establishes the scale-point input `x = 0`, where the
kernel collapses to concrete arithmetic and the `iszero(x)` fix-up lands the result exactly at the
wad unit `10^18`.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
/-- The kernel `fun__expRayToWad_80` at the scale point `x = 0`: every `mul` by `x` vanishes, so
`k = t = v = 0`, the rational form evaluates to `2^126`, and the final `iszero(0) = 1` fix-up makes
the result exactly `10^18`. -/
theorem call_fun__expRayToWad_80_zero_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 700)) [FormalYul.word 0] (.some "fun__expRayToWad_80")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 1000000000000000000]) := by
  rw [show fuel + (extra + 700) = (fuel + extra) + 700 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun__expRayToWad_80]
  simp only [yulFunction_fun__expRayToWad_80,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    call_zero_value_for_split_t_int256_direct (fuel := fuel + extra) (extra := 676)
      (shared := shared) (hlookup := hlookup)]

set_option maxHeartbeats 8000000 in
/-- `fun_expRayToWad_70` at `x = 0`: the overflow guard `iszero(slt(0, threshold)) = 0` is false, so
the panic branch is skipped and the kernel result `10^18` is forwarded. -/
theorem call_fun_expRayToWad_70_zero_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 900)) [FormalYul.word 0] (.some "fun_expRayToWad_70")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 1000000000000000000]) := by
  rw [show fuel + (extra + 900) = (fuel + extra) + 900 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_expRayToWad_70]
  simp only [yulFunction_fun_expRayToWad_70,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hconv44 :=
    call_convert_44_to_int256_direct (v := 0x8e383a2cdfa1b74a9422d2e1) (fuel := fuel + extra) (extra := 767)
      (shared := shared) (hlookup := hlookup)
  have hcleanup :=
    call_cleanup_t_int256_direct (v := 0) (fuel := fuel + extra) (extra := 865)
      (shared := shared) (hlookup := hlookup)
  have hkernel :=
    call_fun__expRayToWad_80_zero_direct (fuel := fuel + extra) (extra := 187)
      (shared := shared) (hlookup := hlookup)
  simp only [Nat.reduceAdd, FormalYul.word] at hconv44 hcleanup hkernel
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    call_zero_value_for_split_t_int256_direct (fuel := fuel + extra) (extra := 876)
      (shared := shared) (hlookup := hlookup),
    hcleanup, hconv44, hkernel]

set_option maxHeartbeats 8000000 in
/-- `fun_wrap_expRayToWad_99` at `x = 0` forwards to `fun_expRayToWad_70`, giving `10^18`. -/
theorem call_fun_wrap_expRayToWad_zero_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 1100)) [FormalYul.word 0] (.some "fun_wrap_expRayToWad_99")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 1000000000000000000]) := by
  rw [show fuel + (extra + 1100) = (fuel + extra) + 1100 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_wrap_expRayToWad]
  simp only [yulFunction_fun_wrap_expRayToWad, yulFunction_fun_wrap_expRayToWad_99,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have h70 :=
    call_fun_expRayToWad_70_zero_direct (fuel := fuel + extra) (extra := 191)
      (shared := shared) (hlookup := hlookup)
  simp only [Nat.reduceAdd, FormalYul.word] at h70
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    call_zero_value_for_split_t_int256_direct (fuel := fuel + extra) (extra := 1076)
      (shared := shared) (hlookup := hlookup),
    h70]

end ExpYul
