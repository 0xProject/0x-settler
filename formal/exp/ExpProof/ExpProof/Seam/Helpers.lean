import ExpProof.ExpYulProof
import Common.Word
import ExpProof.Mono.MulTree
import FormalYul.Preservation

/-!
# Per-function "direct" reductions for the trivial solc ABI/cleanup helpers

These functions (`cleanup_*`, `identity`, `convert_*`, the constant accessor, `zero_value_*`) are
the solc-emitted plumbing called from `fun_expRayToWad`'s overflow guard and panic-code path.
Each is a one-liner; the directs step the interpreter through them. They are branch-agnostic —
the value path also evaluates the guard (to decide *not* to revert) — so they live here, shared by
both `Seam/Revert.lean` and the value-path seam.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word

set_option maxRecDepth 100000

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

theorem call_cleanup_t_rational_SCALE_MAX_direct
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
  simp only [yulFunction_constant__EXP_RAY_TO_WAD_HI, yulFunction_constant__EXP_RAY_TO_WAD_HI_132,
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

theorem call_convert_SCALE_MAX_to_uint256_direct
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
    call_cleanup_t_rational_SCALE_MAX_direct
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

theorem call_constant__SCALE_MAX_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 160)) [] (.some yulName_constant__SCALE_MAX)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word 0x6f05b59d3b2000000000000000000000]) := by
  rw [show fuel + (extra + 160) = (fuel + extra) + 160 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_constant__SCALE_MAX]
  simp only [yulFunction_constant__SCALE_MAX, yulFunction_constant__SCALE_MAX_126,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hconv :=
    call_convert_SCALE_MAX_to_uint256_direct (fuel := fuel + extra + 35) (extra := 0)
      (shared := shared)
      (store := Finmap.insert "expr_125"
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
  simp only [yulFunction_constant__WAD_ZERO_MAX, yulFunction_constant__WAD_ZERO_MAX_136,
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
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
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
  simp only [yulFunction_fun__octave, yulFunction_fun__octave_337,
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
  simp only [FormalYul.Preservation.evmAdd_u256_left,
    FormalYul.Preservation.evmMul_u256_left, FormalYul.Preservation.evmMul_u256_right,
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
  simp only [yulFunction_constant_ARITHMETIC_OVERFLOW, yulFunction_constant_ARITHMETIC_OVERFLOW_62,
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

theorem call_cleanup_t_rational_0_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [FormalYul.word v]
      (.some "cleanup_t_rational_0_by_1") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_cleanup_t_rational_0_by_1]
  simp only [yulFunction_cleanup_t_rational_0_by_1,
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

theorem call_cleanup_t_rational_X_HI_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [FormalYul.word v]
      (.some "cleanup_t_rational_86296823979713191022445399122_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_cleanup_t_rational_86296823979713191022445399122_by_1]
  simp only [yulFunction_cleanup_t_rational_86296823979713191022445399122_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

theorem call_cleanup_t_rational_X_LO_ZERO_direct
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

theorem call_convert_0_to_int256_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120)) [FormalYul.word 0]
      (.some "convert_t_rational_0_by_1_to_t_int256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_convert_t_rational_0_by_1_to_t_int256]
  simp only [yulFunction_convert_t_rational_0_by_1_to_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have h1 :=
    call_cleanup_t_rational_0_direct (v := 0) (fuel := fuel + extra) (extra := 92)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h2 :=
    call_identity_direct (v := 0) (fuel := fuel + extra) (extra := 94) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h3 :=
    call_cleanup_t_int256_direct (v := 0) (fuel := fuel + extra) (extra := 96) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word 0) (Inhabited.default : EvmYul.Yul.VarStore))
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

theorem call_convert_X_HI_to_int256_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120)) [FormalYul.word xHiMulExpRay]
      (.some "convert_t_rational_86296823979713191022445399122_by_1_to_t_int256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word xHiMulExpRay]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_convert_t_rational_86296823979713191022445399122_by_1_to_t_int256]
  simp only [yulFunction_convert_t_rational_86296823979713191022445399122_by_1_to_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have h1 :=
    call_cleanup_t_rational_X_HI_direct (v := xHiMulExpRay) (fuel := fuel + extra) (extra := 92)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word xHiMulExpRay)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h2 :=
    call_identity_direct (v := xHiMulExpRay) (fuel := fuel + extra) (extra := 94) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word xHiMulExpRay)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h3 :=
    call_cleanup_t_int256_direct (v := xHiMulExpRay) (fuel := fuel + extra) (extra := 96)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word xHiMulExpRay)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word, xHiMulExpRay] at h1 h2 h3
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, xHiMulExpRay, h1, h2, h3]

theorem call_convert_X_LO_ZERO_to_int256_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120)) [FormalYul.word xLoZeroMulExpRay]
      (.some "convert_t_rational_minus_88376265521393026950697095485_by_1_to_t_int256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word xLoZeroMulExpRay]) := by
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
    call_cleanup_t_rational_X_LO_ZERO_direct (v := xLoZeroMulExpRay) (fuel := fuel + extra)
      (extra := 92) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word xLoZeroMulExpRay)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h2 :=
    call_identity_direct (v := xLoZeroMulExpRay) (fuel := fuel + extra) (extra := 94)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word xLoZeroMulExpRay)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have h3 :=
    call_cleanup_t_int256_direct (v := xLoZeroMulExpRay) (fuel := fuel + extra) (extra := 96)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word xLoZeroMulExpRay)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word, xLoZeroMulExpRay] at h1 h2 h3
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, xLoZeroMulExpRay, h1, h2, h3]

theorem call_constant__X_HI_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 160)) [] (.some "constant__X_HI_139")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word xHiMulExpRay]) := by
  rw [show fuel + (extra + 160) = (fuel + extra) + 160 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_constant__X_HI_139]
  simp only [yulFunction_constant__X_HI_139,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hconv :=
    call_convert_X_HI_to_int256_direct (fuel := fuel + extra + 35) (extra := 0)
      (shared := shared)
      (store := Finmap.insert "expr_138" (FormalYul.word xHiMulExpRay)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word, xHiMulExpRay] at hconv
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, xHiMulExpRay, hconv]

theorem call_constant__X_LO_ZERO_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 160)) [] (.some "constant__X_LO_ZERO_143")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word xLoZeroMulExpRay]) := by
  rw [show fuel + (extra + 160) = (fuel + extra) + 160 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_constant__X_LO_ZERO_143]
  simp only [yulFunction_constant__X_LO_ZERO_143,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hconv :=
    call_convert_X_LO_ZERO_to_int256_direct (fuel := fuel + extra + 35) (extra := 0)
      (shared := shared)
      (store := Finmap.insert "expr_142" (FormalYul.word xLoZeroMulExpRay)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word, xLoZeroMulExpRay] at hconv
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, xLoZeroMulExpRay, hconv]

theorem call_constant__SCALE_MAX_CLZ_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 160)) [] (.some "constant__SCALE_MAX_CLZ_129")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word scaleMaxClz]) := by
  rw [show fuel + (extra + 160) = (fuel + extra) + 160 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_constant__SCALE_MAX_CLZ_129]
  simp only [yulFunction_constant__SCALE_MAX_CLZ_129,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hconv :=
    call_convert_129_to_uint256_direct (fuel := fuel + extra + 35) (extra := 0)
      (shared := shared)
      (store := Finmap.insert "expr_128" (FormalYul.word scaleMaxClz)
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
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
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
  simp only [yulFunction_fun_clz, yulFunction_fun_clz_96,
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
    Finmap.lookup_insert, FormalYul.word,
    FormalYul.Preservation.uint256_ofNat_clz_eq_word_evmClz,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel + extra) (extra := 56)
      (shared := shared) (hlookup := hlookup)]

theorem call_fun__absSign_direct
    (y fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 200)) [FormalYul.word y] (.some yulName_fun__absSign)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (absTree y), FormalYul.word (signTree y)]) := by
  rw [show fuel + (extra + 200) = (fuel + extra) + 200 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun__absSign]
  simp only [yulFunction_fun__absSign, yulFunction_fun__absSign_305,
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
    Finmap.lookup_insert, FormalYul.word, signTree, absTree,
    uint256_ofNat_sar_eq_word_evmSar,
    uint256_ofNat_xor_eq_word_evmXor,
    FormalYul.Preservation.uint256_ofNat_sub_eq_word_evmSub,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel + extra) (extra := 176)
      (shared := shared) (hlookup := hlookup),
    call_zero_value_for_split_t_uint256_direct (fuel := fuel + extra) (extra := 174)
      (shared := shared) (hlookup := hlookup)]

theorem call_fun__scaleShift_direct
    (ay fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 700)) [FormalYul.word ay]
      (.some yulName_fun__scaleShift) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (scaleShiftTree ay)]) := by
  rw [show fuel + (extra + 700) = (fuel + extra) + 700 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun__scaleShift]
  simp only [yulFunction_fun__scaleShift, yulFunction_fun__scaleShift_328,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let s := evmSub (evmClz ay) scaleMaxClz
  let initStore :=
    Finmap.insert "var_ay_307" (FormalYul.word ay)
      (Inhabited.default : EvmYul.Yul.VarStore)
  let zeroStore := Finmap.insert "zero_t_uint256_42" (FormalYul.word 0) initStore
  let baseStore := Finmap.insert "var_s_310" (FormalYul.word 0) zeroStore
  let beforeClzStore :=
    Finmap.insert "expr_315" (FormalYul.word ay)
      (Finmap.insert "_43" (FormalYul.word ay)
        (Finmap.insert "expr_313_address" (FormalYul.word 0) baseStore))
  let afterClzStore := Finmap.insert "expr_316" (FormalYul.word (evmClz ay)) beforeClzStore
  let afterClzConstStore := Finmap.insert "expr_317" (FormalYul.word scaleMaxClz) afterClzStore
  let afterSubStore := Finmap.insert "expr_318" (FormalYul.word s) afterClzConstStore
  let beforeScaleStore :=
    Finmap.insert "expr_319" (FormalYul.word s)
      (Finmap.insert "var_s_310" (FormalYul.word s) afterSubStore)
  have hzero :=
    call_zero_value_for_split_t_uint256_direct (fuel := fuel + extra) (extra := 676)
      (shared := shared) (hlookup := hlookup)
      (store := initStore)
  have hclz :=
    call_fun_clz_direct (x := ay) (fuel := fuel + extra) (extra := 611)
      (shared := shared) (store := beforeClzStore) (hlookup := hlookup)
  have hclzConst :=
    call_constant__SCALE_MAX_CLZ_direct (fuel := fuel + extra) (extra := 530)
      (shared := shared) (store := afterClzStore) (hlookup := hlookup)
  have hsub :=
    call_wrapping_sub_t_uint256_direct (x := evmClz ay) (y := scaleMaxClz)
      (fuel := fuel + extra) (extra := 609)
      (shared := shared) (store := afterClzConstStore) (hlookup := hlookup)
  have hscale :=
    call_constant__SCALE_MAX_direct (fuel := fuel + extra) (extra := 526)
      (shared := shared) (store := beforeScaleStore) (hlookup := hlookup)
  simp only [Nat.reduceAdd, FormalYul.word, initStore, zeroStore, baseStore,
    beforeClzStore, afterClzStore, afterClzConstStore, afterSubStore, beforeScaleStore]
    at hzero hclz hclzConst hsub hscale
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, scaleShiftTree, s,
    initStore, zeroStore, baseStore, beforeClzStore, afterClzStore, afterClzConstStore,
    afterSubStore, beforeScaleStore,
    FormalYul.Preservation.uint256_ofNat_sub_eq_word_evmSub,
    FormalYul.Preservation.uint256_ofNat_shiftLeft_eq_word_evmShl,
    FormalYul.Preservation.uint256_ofNat_gt_eq_word_evmGt,
    hzero, hclz, hclzConst, hsub, hscale]

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
  simp only [yulFunction_fun_or, yulFunction_fun_or_12,
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
    Finmap.lookup_insert, FormalYul.word,
    FormalYul.Preservation.uint256_ofNat_or_eq_word_evmOr,
    call_zero_value_for_split_t_bool_direct (fuel := fuel + extra) (extra := 56)
      (shared := shared) (hlookup := hlookup)]

theorem call_fun_and_direct
    (a b fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 80)) [FormalYul.word a, FormalYul.word b] (.some yulName_fun_and)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmAnd a b)]) := by
  rw [show fuel + (extra + 80) = (fuel + extra) + 80 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_and]
  simp only [yulFunction_fun_and, yulFunction_fun_and_23,
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
    Finmap.lookup_insert, FormalYul.word,
    FormalYul.Preservation.uint256_ofNat_and_eq_word_evmAnd,
    call_zero_value_for_split_t_bool_direct (fuel := fuel + extra) (extra := 56)
      (shared := shared) (hlookup := hlookup)]

end ExpYul
