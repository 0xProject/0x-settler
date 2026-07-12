import ExpProof.ExpYulProof
import Common.Word
import ExpProof.Mono.MulTree
import FormalYul.Preservation

/-!
# Per-function "direct" reductions for the trivial solc ABI/cleanup helpers

These functions (`cleanup_*`, `identity`, `convert_*`, the constant accessors, `zero_value_*`)
are the solc-emitted plumbing called from the guards and panic-code paths of `fun_expRayToWad`
and `fun_mulExpRay`. Each is a one-liner; the directs step the interpreter through them. They are
branch-agnostic — the value paths also evaluate the guards (to decide *not* to revert) — so they
live here, shared by `Seam/Revert.lean` and the value-path seams.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word

set_option maxRecDepth 100000
set_option Elab.async false

/-- `zero_value_for_split_t_int256()` returns the word `0`. -/
theorem call_zero_value_for_split_t_int256_direct
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

/-- `zero_value_for_split_t_uint256()` returns the word `0`. -/
theorem call_zero_value_for_split_t_uint256_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [] (.some "zero_value_for_split_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_zero_value_for_split_t_uint256]
  simp only [yulFunction_zero_value_for_split_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

/-- A one-line identity helper `f(value) -> out { out := value }` returns its argument. The proof
recipe is shared by `cleanup_t_int256`, `identity`, `cleanup_t_rational_*`, `cleanup_t_uint256`. -/
theorem call_cleanup_t_int256_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [FormalYul.word v] (.some "cleanup_t_int256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_cleanup_t_int256]
  simp only [yulFunction_cleanup_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

/-- A Yul `signextend(a, b)` primitive call returns the sign-extended word. -/
theorem primCall_signextend_yul (fuel : Nat) (s : EvmYul.Yul.State)
    (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s
        (EvmYul.Operation.StopArith EvmYul.Operation.SAOp.SIGNEXTEND : EvmYul.Operation .Yul)
        [a, b] =
      .ok (s, [EvmYul.UInt256.signextend a b]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, List.not_mem_nil, Bool.not_eq_true, reduceCtorEq, or_self, and_false, if_false,
    EvmYul.step.eq_def]
  rfl

/-- `cleanup_t_int128(value) -> cleaned { cleaned := signextend(15, value) }`. -/
theorem call_cleanup_t_int128_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [FormalYul.word v] (.some "cleanup_t_int128")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word v)]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_cleanup_t_int128]
  simp only [yulFunction_cleanup_t_int128,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hsign := primCall_signextend_yul (fuel + extra + 16)
    (EvmYul.Yul.State.Ok shared
      (Finmap.insert "value" (FormalYul.word v) (Inhabited.default : EvmYul.Yul.VarStore)))
    (FormalYul.word 15) (FormalYul.word v)
  simp only [FormalYul.word] at hsign
  simp +decide [EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hsign]

theorem call_identity_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [FormalYul.word v] (.some "identity")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_identity]
  simp only [yulFunction_identity,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

theorem call_cleanup_t_rational_44_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [FormalYul.word v]
      (.some "cleanup_t_rational_45401140326676417766828703956_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_cleanup_t_rational_45401140326676417766828703956_by_1]
  simp only [yulFunction_cleanup_t_rational_45401140326676417766828703956_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

theorem call_cleanup_t_rational_17_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [FormalYul.word v]
      (.some "cleanup_t_rational_17_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_cleanup_t_rational_17_by_1]
  simp only [yulFunction_cleanup_t_rational_17_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

theorem call_cleanup_t_rational_67_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [FormalYul.word v]
      (.some "cleanup_t_rational_67_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_cleanup_t_rational_67_by_1]
  simp only [yulFunction_cleanup_t_rational_67_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

theorem call_cleanup_t_rational_WAD_SCALE_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [FormalYul.word v]
      (.some "cleanup_t_rational_147573952589676412928000000000000000000_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_cleanup_t_rational_147573952589676412928000000000000000000_by_1]
  simp only [yulFunction_cleanup_t_rational_147573952589676412928000000000000000000_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

theorem call_cleanup_t_rational_WAD_ZERO_MAX_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [FormalYul.word v]
      (.some "cleanup_t_rational_minus_41446531673892822312323846185_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_cleanup_t_rational_minus_41446531673892822312323846185_by_1]
  simp only [yulFunction_cleanup_t_rational_minus_41446531673892822312323846185_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

theorem call_cleanup_t_uint256_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [FormalYul.word v] (.some "cleanup_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_cleanup_t_uint256]
  simp only [yulFunction_cleanup_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

/-- `convert_t_rational_44…_to_t_int256(value) -> converted` is
`cleanup_t_int256(identity(cleanup_t_rational_44…(value)))` — three identity calls, so it returns
its argument. Used to evaluate the overflow-guard comparison's right-hand side. -/
theorem call_convert_44_to_int256_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120)) [FormalYul.word v]
      (.some "convert_t_rational_45401140326676417766828703956_by_1_to_t_int256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_convert_t_rational_45401140326676417766828703956_by_1_to_t_int256]
  simp only [yulFunction_convert_t_rational_45401140326676417766828703956_by_1_to_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have h1 :=
    call_cleanup_t_rational_44_direct (v := v) (fuel := fuel + extra) (extra := 92) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word v) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h2 :=
    call_identity_direct (v := v) (fuel := fuel + extra) (extra := 94) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word v) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h3 :=
    call_cleanup_t_int256_direct (v := v) (fuel := fuel + extra) (extra := 96) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word v) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word] at h1 h2 h3
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, h1, h2, h3]

theorem call_constant__EXP_RAY_TO_WAD_HI_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 160)) [] (.some yulName_constant__EXP_RAY_TO_WAD_HI)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0x92b2f16cc66c5a4ae96e80d4]) := by
  rw [show fuel + (extra + 160) = (fuel + extra) + 160 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_constant__EXP_RAY_TO_WAD_HI]
  simp only [yulFunctionBody_constant__EXP_RAY_TO_WAD_HI,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hconv :=
    call_convert_44_to_int256_direct (v := 0x92b2f16cc66c5a4ae96e80d4)
      (fuel := fuel + extra + 35) (extra := 0) (shared := shared)
      (store := Finmap.insert "expr_131" (FormalYul.word 0x92b2f16cc66c5a4ae96e80d4)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word] at hconv
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hconv]

theorem call_convert_67_to_int256_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120)) [FormalYul.word 0x43]
      (.some "convert_t_rational_67_by_1_to_t_int256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0x43]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_convert_t_rational_67_by_1_to_t_int256]
  simp only [yulFunction_convert_t_rational_67_by_1_to_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have h1 :=
    call_cleanup_t_rational_67_direct (v := 0x43) (fuel := fuel + extra) (extra := 92)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0x43) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h2 :=
    call_identity_direct (v := 0x43) (fuel := fuel + extra) (extra := 94) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0x43) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h3 :=
    call_cleanup_t_int256_direct (v := 0x43) (fuel := fuel + extra) (extra := 96) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0x43) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word] at h1 h2 h3
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, h1, h2, h3]

theorem call_convert_WAD_SCALE_to_uint256_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120))
      [FormalYul.word 0x6f05b59d3b2000000000000000000000]
      (.some "convert_t_rational_147573952589676412928000000000000000000_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word 0x6f05b59d3b2000000000000000000000]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_convert_t_rational_147573952589676412928000000000000000000_by_1_to_t_uint256]
  simp only [yulFunction_convert_t_rational_147573952589676412928000000000000000000_by_1_to_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have h1 :=
    call_cleanup_t_rational_WAD_SCALE_direct
      (v := 0x6f05b59d3b2000000000000000000000) (fuel := fuel + extra) (extra := 92)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0x6f05b59d3b2000000000000000000000)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h2 :=
    call_identity_direct (v := 0x6f05b59d3b2000000000000000000000)
      (fuel := fuel + extra) (extra := 94) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0x6f05b59d3b2000000000000000000000)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h3 :=
    call_cleanup_t_uint256_direct (v := 0x6f05b59d3b2000000000000000000000)
      (fuel := fuel + extra) (extra := 96) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0x6f05b59d3b2000000000000000000000)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word] at h1 h2 h3
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, h1, h2, h3]

theorem call_convert_WAD_ZERO_MAX_to_int256_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120))
      [FormalYul.word 0xffffffffffffffffffffffffffffffffffffffff7a143b87dbdabf5ee0a0efd7]
      (.some "convert_t_rational_minus_41446531673892822312323846185_by_1_to_t_int256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word 0xffffffffffffffffffffffffffffffffffffffff7a143b87dbdabf5ee0a0efd7]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_convert_t_rational_minus_41446531673892822312323846185_by_1_to_t_int256]
  simp only [yulFunction_convert_t_rational_minus_41446531673892822312323846185_by_1_to_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have h1 :=
    call_cleanup_t_rational_WAD_ZERO_MAX_direct
      (v := 0xffffffffffffffffffffffffffffffffffffffff7a143b87dbdabf5ee0a0efd7)
      (fuel := fuel + extra) (extra := 92) (shared := shared)
      (store := Finmap.insert "value"
        (FormalYul.word 0xffffffffffffffffffffffffffffffffffffffff7a143b87dbdabf5ee0a0efd7)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h2 :=
    call_identity_direct (v := 0xffffffffffffffffffffffffffffffffffffffff7a143b87dbdabf5ee0a0efd7)
      (fuel := fuel + extra) (extra := 94) (shared := shared)
      (store := Finmap.insert "value"
        (FormalYul.word 0xffffffffffffffffffffffffffffffffffffffff7a143b87dbdabf5ee0a0efd7)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h3 :=
    call_cleanup_t_int256_direct
      (v := 0xffffffffffffffffffffffffffffffffffffffff7a143b87dbdabf5ee0a0efd7)
      (fuel := fuel + extra) (extra := 96) (shared := shared)
      (store := Finmap.insert "value"
        (FormalYul.word 0xffffffffffffffffffffffffffffffffffffffff7a143b87dbdabf5ee0a0efd7)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word] at h1 h2 h3
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, h1, h2, h3]

theorem call_constant__WAD_SCALE_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 160)) [] (.some yulName_constant__WAD_SCALE)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word 0x6f05b59d3b2000000000000000000000]) := by
  rw [show fuel + (extra + 160) = (fuel + extra) + 160 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_constant__WAD_SCALE]
  simp only [yulFunctionBody_constant__WAD_SCALE,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hconv :=
    call_convert_WAD_SCALE_to_uint256_direct (fuel := fuel + extra + 35) (extra := 0)
      (shared := shared)
      (store := Finmap.insert "expr_128"
        (FormalYul.word 0x6f05b59d3b2000000000000000000000)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word] at hconv
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hconv]

theorem call_constant__WAD_ZERO_MAX_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 160)) [] (.some yulName_constant__WAD_ZERO_MAX)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word 0xffffffffffffffffffffffffffffffffffffffff7a143b87dbdabf5ee0a0efd7]) := by
  rw [show fuel + (extra + 160) = (fuel + extra) + 160 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_constant__WAD_ZERO_MAX]
  simp only [yulFunctionBody_constant__WAD_ZERO_MAX,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hconv :=
    call_convert_WAD_ZERO_MAX_to_int256_direct (fuel := fuel + extra + 35) (extra := 0)
      (shared := shared)
      (store := Finmap.insert "expr_135"
        (FormalYul.word 0xffffffffffffffffffffffffffffffffffffffff7a143b87dbdabf5ee0a0efd7)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word] at hconv
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hconv]

theorem call_wrapping_sub_t_int256_direct
    (x y fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 80)) [FormalYul.word x, FormalYul.word y]
      (.some "wrapping_sub_t_int256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmSub x y)]) := by
  rw [show fuel + (extra + 80) = (fuel + extra) + 80 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_wrapping_sub_t_int256]
  simp only [yulFunction_wrapping_sub_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcleanup :=
    call_cleanup_t_int256_direct (v := evmSub x y) (fuel := fuel + extra) (extra := 56)
      (shared := shared)
      (store := Finmap.insert "x" (FormalYul.word x)
        (Finmap.insert "y" (FormalYul.word y) (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup)
  simp [FormalYul.word] at hcleanup
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    FormalYul.Preservation.uint256_ofNat_sub_eq_word_evmSub, hcleanup]

theorem call_convert_int256_to_uint256_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120)) [FormalYul.word v]
      (.some "convert_t_int256_to_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_convert_t_int256_to_t_uint256]
  simp only [yulFunction_convert_t_int256_to_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have h1 :=
    call_cleanup_t_int256_direct (v := v) (fuel := fuel + extra) (extra := 92) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word v) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h2 :=
    call_identity_direct (v := v) (fuel := fuel + extra) (extra := 94) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word v) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h3 :=
    call_cleanup_t_uint256_direct (v := v) (fuel := fuel + extra) (extra := 96) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word v) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word] at h1 h2 h3
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, h1, h2, h3]

theorem call_convert_uint256_to_int256_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120)) [FormalYul.word v]
      (.some "convert_t_uint256_to_t_int256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_convert_t_uint256_to_t_int256]
  simp only [yulFunction_convert_t_uint256_to_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have h1 :=
    call_cleanup_t_uint256_direct (v := v) (fuel := fuel + extra) (extra := 92) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word v) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h2 :=
    call_identity_direct (v := v) (fuel := fuel + extra) (extra := 94) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word v) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h3 :=
    call_cleanup_t_int256_direct (v := v) (fuel := fuel + extra) (extra := 96) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word v) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word] at h1 h2 h3
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, h1, h2, h3]

theorem call_fun__octave_direct
    (x fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120)) [FormalYul.word x] (.some yulName_fun__octave)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word
        (evmSar 0xc0 (evmAdd (evmShl 0xbf 1) (evmMul 0x724d54edbacbebbb95c52a0f60 x)))]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun__octave]
  simp only [yulFunctionBody_fun__octave,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    call_zero_value_for_split_t_int256_direct (fuel := fuel + extra) (extra := 96)
      (shared := shared) (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [wordNat_sar,
    FormalYul.Preservation.wordNat_shiftLeft, FormalYul.Preservation.wordNat_add,
    FormalYul.Preservation.wordNat_mul, FormalYul.Preservation.wordNat_ofNat]
  simp only [FormalYul.Preservation.evmMul_u256_left,
    FormalYul.Preservation.evmMul_u256_right,
    FormalYul.Preservation.evmShl_u256_left, FormalYul.Preservation.evmShl_u256_right,
    evmSar_u256_left]
  have hsar :
      evmSar 192 (evmAdd (evmShl 191 1) (evmMul 9055943544797870567083544809312 x)) <
        2 ^ 256 :=
    (evmSar_sandwich (s := 192) (by norm_num)
      (FormalYul.Preservation.evmAdd_lt_pow256 _ _)).1
  exact (FormalYul.Preservation.u256_eq_of_lt _ (by simpa [FormalYul.WORD_MOD] using hsar)).symm

/-- `cleanup_t_uint8(value) -> cleaned { cleaned := and(value, 0xff) }`. Specialized to the panic
code `0x11`, where `and(0x11, 0xff) = 0x11`. -/
theorem call_cleanup_t_uint8_17_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [FormalYul.word 0x11] (.some "cleanup_t_uint8")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0x11]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_cleanup_t_uint8]
  simp only [yulFunction_cleanup_t_uint8,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

/-- `convert_t_rational_17_by_1_to_t_uint8(0x11) = 0x11` (= `cleanup_t_uint8(identity(cleanup_…(0x11)))`). -/
theorem call_convert_17_to_uint8_17_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 120) [FormalYul.word 0x11]
      (.some "convert_t_rational_17_by_1_to_t_uint8")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0x11]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_convert_t_rational_17_by_1_to_t_uint8]
  simp only [yulFunction_convert_t_rational_17_by_1_to_t_uint8,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have h1 :=
    call_cleanup_t_rational_17_direct (v := 0x11) (fuel := fuel) (extra := 92) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0x11) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h2 :=
    call_identity_direct (v := 0x11) (fuel := fuel) (extra := 94) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0x11) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h3 :=
    call_cleanup_t_uint8_17_direct (fuel := fuel + 96) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0x11) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word] at h1 h2 h3
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, h1, h2, h3]

/-- The solc panic-code accessor for arithmetic overflow returns `0x11`.
overflow (`0x11`). -/
theorem call_constant_ARITHMETIC_OVERFLOW_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 160)) [] (.some yulName_constant_ARITHMETIC_OVERFLOW)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0x11]) := by
  rw [show fuel + (extra + 160) = (fuel + extra) + 160 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_constant_ARITHMETIC_OVERFLOW]
  simp only [yulFunctionBody_constant_ARITHMETIC_OVERFLOW,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hconv :=
    call_convert_17_to_uint8_17_direct (fuel := fuel + extra + 35) (shared := shared)
      (store := Finmap.insert "expr_61" (FormalYul.word 0x11) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word] at hconv
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hconv]

/-- `convert_t_uint8_to_t_uint256(0x11) = 0x11` (= `cleanup_t_uint256(identity(cleanup_t_uint8(0x11)))`). -/
theorem call_convert_uint8_to_uint256_17_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120)) [FormalYul.word 0x11] (.some "convert_t_uint8_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0x11]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_convert_t_uint8_to_t_uint256]
  simp only [yulFunction_convert_t_uint8_to_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have h1 :=
    call_cleanup_t_uint8_17_direct (fuel := fuel + extra + 92) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0x11) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h2 :=
    call_identity_direct (v := 0x11) (fuel := fuel + extra) (extra := 94) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0x11) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h3 :=
    call_cleanup_t_uint256_direct (v := 0x11) (fuel := fuel + extra) (extra := 96) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0x11) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word] at h1 h2 h3
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, h1, h2, h3]

theorem call_zero_value_for_split_t_bool_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [] (.some "zero_value_for_split_t_bool")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_zero_value_for_split_t_bool]
  simp only [yulFunction_zero_value_for_split_t_bool,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

theorem call_cleanup_t_rational_1_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [FormalYul.word v]
      (.some "cleanup_t_rational_1_by_1") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_cleanup_t_rational_1_by_1]
  simp only [yulFunction_cleanup_t_rational_1_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

theorem call_cleanup_t_rational_2_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [FormalYul.word v]
      (.some "cleanup_t_rational_2_by_1") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_cleanup_t_rational_2_by_1]
  simp only [yulFunction_cleanup_t_rational_2_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

theorem call_cleanup_t_rational_127_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [FormalYul.word v]
      (.some "cleanup_t_rational_127_by_1") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_cleanup_t_rational_127_by_1]
  simp only [yulFunction_cleanup_t_rational_127_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

theorem call_cleanup_t_rational_129_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [FormalYul.word v]
      (.some "cleanup_t_rational_129_by_1") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_cleanup_t_rational_129_by_1]
  simp only [yulFunction_cleanup_t_rational_129_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

theorem call_cleanup_t_rational_MUL_EXP_RAY_HI_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [FormalYul.word v]
      (.some "cleanup_t_rational_86989971160273136331862631244_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_cleanup_t_rational_86989971160273136331862631244_by_1]
  simp only [yulFunction_cleanup_t_rational_86989971160273136331862631244_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

theorem call_cleanup_t_rational_MUL_EXP_RAY_ZERO_MAX_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [FormalYul.word v]
      (.some "cleanup_t_rational_minus_88376265521393026950697095485_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_cleanup_t_rational_minus_88376265521393026950697095485_by_1]
  simp only [yulFunction_cleanup_t_rational_minus_88376265521393026950697095485_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

theorem call_convert_2_to_int256_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120)) [FormalYul.word 2]
      (.some "convert_t_rational_2_by_1_to_t_int256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 2]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_convert_t_rational_2_by_1_to_t_int256]
  simp only [yulFunction_convert_t_rational_2_by_1_to_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have h1 :=
    call_cleanup_t_rational_2_direct (v := 2) (fuel := fuel + extra) (extra := 92)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 2) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h2 :=
    call_identity_direct (v := 2) (fuel := fuel + extra) (extra := 94) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 2) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h3 :=
    call_cleanup_t_int256_direct (v := 2) (fuel := fuel + extra) (extra := 96) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 2) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word] at h1 h2 h3
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, h1, h2, h3]

theorem call_convert_1_to_int256_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120)) [FormalYul.word 1]
      (.some "convert_t_rational_1_by_1_to_t_int256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 1]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_convert_t_rational_1_by_1_to_t_int256]
  simp only [yulFunction_convert_t_rational_1_by_1_to_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have h1 :=
    call_cleanup_t_rational_1_direct (v := 1) (fuel := fuel + extra) (extra := 92)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 1) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h2 :=
    call_identity_direct (v := 1) (fuel := fuel + extra) (extra := 94) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 1) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h3 :=
    call_cleanup_t_int256_direct (v := 1) (fuel := fuel + extra) (extra := 96) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 1) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word] at h1 h2 h3
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, h1, h2, h3]

theorem call_convert_127_to_uint256_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120)) [FormalYul.word 0x7f]
      (.some "convert_t_rational_127_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0x7f]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_convert_t_rational_127_by_1_to_t_uint256]
  simp only [yulFunction_convert_t_rational_127_by_1_to_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have h1 :=
    call_cleanup_t_rational_127_direct (v := 0x7f) (fuel := fuel + extra) (extra := 92)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0x7f) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h2 :=
    call_identity_direct (v := 0x7f) (fuel := fuel + extra) (extra := 94) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0x7f) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h3 :=
    call_cleanup_t_uint256_direct (v := 0x7f) (fuel := fuel + extra) (extra := 96)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0x7f) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word] at h1 h2 h3
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, h1, h2, h3]

theorem call_convert_129_to_uint256_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120)) [FormalYul.word 0x81]
      (.some "convert_t_rational_129_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0x81]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_convert_t_rational_129_by_1_to_t_uint256]
  simp only [yulFunction_convert_t_rational_129_by_1_to_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have h1 :=
    call_cleanup_t_rational_129_direct (v := 0x81) (fuel := fuel + extra) (extra := 92)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0x81) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h2 :=
    call_identity_direct (v := 0x81) (fuel := fuel + extra) (extra := 94) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0x81) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h3 :=
    call_cleanup_t_uint256_direct (v := 0x81) (fuel := fuel + extra) (extra := 96) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0x81) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word] at h1 h2 h3
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, h1, h2, h3]

theorem call_convert_MUL_EXP_RAY_HI_to_int256_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120)) [FormalYul.word mulExpRayHi]
      (.some "convert_t_rational_86989971160273136331862631244_by_1_to_t_int256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word mulExpRayHi]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_convert_t_rational_86989971160273136331862631244_by_1_to_t_int256]
  simp only [yulFunction_convert_t_rational_86989971160273136331862631244_by_1_to_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have h1 :=
    call_cleanup_t_rational_MUL_EXP_RAY_HI_direct (v := mulExpRayHi) (fuel := fuel + extra) (extra := 92)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word mulExpRayHi)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h2 :=
    call_identity_direct (v := mulExpRayHi) (fuel := fuel + extra) (extra := 94) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word mulExpRayHi)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h3 :=
    call_cleanup_t_int256_direct (v := mulExpRayHi) (fuel := fuel + extra) (extra := 96)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word mulExpRayHi)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word, mulExpRayHi] at h1 h2 h3
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, mulExpRayHi, h1, h2, h3]

theorem call_convert_MUL_EXP_RAY_ZERO_MAX_to_int256_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120)) [FormalYul.word mulExpRayZeroMax]
      (.some "convert_t_rational_minus_88376265521393026950697095485_by_1_to_t_int256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word mulExpRayZeroMax]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_convert_t_rational_minus_88376265521393026950697095485_by_1_to_t_int256]
  simp only [yulFunction_convert_t_rational_minus_88376265521393026950697095485_by_1_to_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have h1 :=
    call_cleanup_t_rational_MUL_EXP_RAY_ZERO_MAX_direct (v := mulExpRayZeroMax) (fuel := fuel + extra)
      (extra := 92) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word mulExpRayZeroMax)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h2 :=
    call_identity_direct (v := mulExpRayZeroMax) (fuel := fuel + extra) (extra := 94)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word mulExpRayZeroMax)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h3 :=
    call_cleanup_t_int256_direct (v := mulExpRayZeroMax) (fuel := fuel + extra) (extra := 96)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word mulExpRayZeroMax)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word, mulExpRayZeroMax] at h1 h2 h3
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, mulExpRayZeroMax, h1, h2, h3]

theorem call_constant__MUL_EXP_RAY_HI_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 160)) [] (.some yulName_constant__MUL_EXP_RAY_HI)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word mulExpRayHi]) := by
  rw [show fuel + (extra + 160) = (fuel + extra) + 160 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_constant__MUL_EXP_RAY_HI]
  simp only [yulFunctionBody_constant__MUL_EXP_RAY_HI,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hconv :=
    call_convert_MUL_EXP_RAY_HI_to_int256_direct (fuel := fuel + extra + 35) (extra := 0)
      (shared := shared)
      (store := Finmap.insert "expr_138" (FormalYul.word mulExpRayHi)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word, mulExpRayHi] at hconv
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, mulExpRayHi, hconv]

theorem call_constant__MUL_EXP_RAY_ZERO_MAX_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 160)) [] (.some yulName_constant__MUL_EXP_RAY_ZERO_MAX)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word mulExpRayZeroMax]) := by
  rw [show fuel + (extra + 160) = (fuel + extra) + 160 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_constant__MUL_EXP_RAY_ZERO_MAX]
  simp only [yulFunctionBody_constant__MUL_EXP_RAY_ZERO_MAX,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hconv :=
    call_convert_MUL_EXP_RAY_ZERO_MAX_to_int256_direct (fuel := fuel + extra + 35) (extra := 0)
      (shared := shared)
      (store := Finmap.insert "expr_142" (FormalYul.word mulExpRayZeroMax)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word, mulExpRayZeroMax] at hconv
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, mulExpRayZeroMax, hconv]

theorem call_constant__SCALE_MAX_CLZ_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 160)) [] (.some yulName_constant__SCALE_MAX_CLZ)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word scaleMaxClz]) := by
  rw [show fuel + (extra + 160) = (fuel + extra) + 160 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_constant__SCALE_MAX_CLZ]
  simp only [yulFunctionBody_constant__SCALE_MAX_CLZ,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hconv :=
    call_convert_129_to_uint256_direct (fuel := fuel + extra + 35) (extra := 0)
      (shared := shared)
      (store := Finmap.insert "expr_125" (FormalYul.word scaleMaxClz)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word, scaleMaxClz] at hconv
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, scaleMaxClz, hconv]

theorem call_wrapping_sub_t_uint256_direct
    (x y fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 80)) [FormalYul.word x, FormalYul.word y]
      (.some "wrapping_sub_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmSub x y)]) := by
  rw [show fuel + (extra + 80) = (fuel + extra) + 80 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_wrapping_sub_t_uint256]
  simp only [yulFunction_wrapping_sub_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcleanup :=
    call_cleanup_t_uint256_direct (v := evmSub x y) (fuel := fuel + extra) (extra := 56)
      (shared := shared)
      (store := Finmap.insert "x" (FormalYul.word x)
        (Finmap.insert "y" (FormalYul.word y) (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup)
  simp [FormalYul.word] at hcleanup
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    FormalYul.Preservation.uint256_ofNat_sub_eq_word_evmSub, hcleanup]

theorem call_fun_clz_direct
    (x fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 80)) [FormalYul.word x] (.some yulName_fun_clz)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmClz x)]) := by
  rw [show fuel + (extra + 80) = (fuel + extra) + 80 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_clz]
  simp only [yulFunctionBody_fun_clz,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    FormalYul.Preservation.uint256_ofNat_clz_eq_word_evmClz,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel + extra) (extra := 56)
      (shared := shared) (hlookup := hlookup)]

theorem call_shift_left_dynamic_direct
    (bits value fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 40)) [FormalYul.word bits, FormalYul.word value]
      (.some "shift_left_dynamic") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmShl bits value)]) := by
  rw [show fuel + (extra + 40) = (fuel + extra) + 40 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_shift_left_dynamic]
  simp only [yulFunction_shift_left_dynamic,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    FormalYul.Preservation.uint256_ofNat_shiftLeft_eq_word_evmShl]

theorem call_shift_left_t_uint256_t_uint256_direct
    (value bits fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 180)) [FormalYul.word value, FormalYul.word bits]
      (.some "shift_left_t_uint256_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmShl bits value)]) := by
  rw [show fuel + (extra + 180) = (fuel + extra) + 180 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_shift_left_t_uint256_t_uint256]
  simp only [yulFunction_shift_left_t_uint256_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hbits :=
    call_cleanup_t_uint256_direct (v := bits) (fuel := fuel + extra) (extra := 156)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word value)
        (Finmap.insert "bits" (FormalYul.word bits) (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup)
  have hvalue :=
    call_cleanup_t_uint256_direct (v := value) (fuel := fuel + extra) (extra := 151)
      (shared := shared)
      (store := Finmap.insert "bits" (FormalYul.word bits)
        (Finmap.insert "value" (FormalYul.word value)
          (Finmap.insert "bits" (FormalYul.word bits) (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup)
  have hshift :=
    call_shift_left_dynamic_direct (bits := bits) (value := value) (fuel := fuel + extra)
      (extra := 133) (shared := shared)
      (store := Finmap.insert "bits" (FormalYul.word bits)
        (Finmap.insert "value" (FormalYul.word value)
          (Finmap.insert "bits" (FormalYul.word bits) (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup)
  have hcleanup :=
    call_cleanup_t_uint256_direct (v := evmShl bits value) (fuel := fuel + extra) (extra := 155)
      (shared := shared)
      (store := Finmap.insert "bits" (FormalYul.word bits)
        (Finmap.insert "value" (FormalYul.word value)
          (Finmap.insert "bits" (FormalYul.word bits) (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup)
  simp [FormalYul.word] at hbits hvalue hshift hcleanup
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hbits, hvalue, hshift, hcleanup]

theorem call_fun_or_direct
    (a b fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 80)) [FormalYul.word a, FormalYul.word b] (.some yulName_fun_or)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmOr a b)]) := by
  rw [show fuel + (extra + 80) = (fuel + extra) + 80 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_or]
  simp only [yulFunctionBody_fun_or,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    FormalYul.Preservation.uint256_ofNat_or_eq_word_evmOr,
    call_zero_value_for_split_t_bool_direct (fuel := fuel + extra) (extra := 56)
      (shared := shared) (hlookup := hlookup)]

theorem uint256_ofNat_sgt_eq_word_evmSgt (a b : Nat) :
    EvmYul.UInt256.sgt (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b) =
      FormalYul.word (evmSgt a b) := by
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [wordNat_sgt, FormalYul.Preservation.wordNat_ofNat,
    FormalYul.Preservation.wordNat_word]
  simp [evmSgt_u256_left, evmSgt_u256_right, u256_evmSgt]

theorem uint256_ofNat_slt_eq_word_evmSlt (a b : Nat) :
    EvmYul.UInt256.slt (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b) =
      FormalYul.word (evmSlt a b) := by
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [wordNat_slt, FormalYul.Preservation.wordNat_ofNat,
    FormalYul.Preservation.wordNat_word]
  have hclosed : u256 (evmSlt a b) = evmSlt a b := by
    unfold evmSlt
    split <;> simp [u256, WORD_MOD]
  simp [evmSlt_u256_left, evmSlt_u256_right, hclosed]

theorem uint256_ofNat_iszero_eq_word_evmIszero (a : Nat) :
    EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat a) =
      FormalYul.word (evmIszero a) := by
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_iszero, FormalYul.Preservation.wordNat_ofNat,
    FormalYul.Preservation.wordNat_word]
  simp [FormalYul.Preservation.evmIszero_u256]

end ExpYul
