import ExpProof.ExpYulProof
import Common.Word
import FormalYul.Preservation

/-!
# Per-function "direct" reductions for the trivial solc ABI/cleanup helpers

These functions (`cleanup_*`, `identity`, `convert_*`, the constant accessor, `zero_value_*`) are
the solc-emitted plumbing called from `fun_expRayToWad_70`'s overflow guard and panic-code path.
Each is a one-liner; the directs step the interpreter through them. They are branch-agnostic —
the value path also evaluates the guard (to decide *not* to revert) — so they live here, shared by
both `Seam/Revert.lean` and the value-path seam.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

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
      (.some "cleanup_t_rational_44014845965556527147994239713_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_cleanup_t_rational_44014845965556527147994239713_by_1]
  simp only [yulFunction_cleanup_t_rational_44014845965556527147994239713_by_1,
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
      (.some "convert_t_rational_44014845965556527147994239713_by_1_to_t_int256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word v]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_convert_t_rational_44014845965556527147994239713_by_1_to_t_int256]
  simp only [yulFunction_convert_t_rational_44014845965556527147994239713_by_1_to_t_int256,
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
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, h1, h2, h3]

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
  simp +decide [EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
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
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, h1, h2, h3]

/-- `constant_ARITHMETIC_OVERFLOW_17() = 0x11` — the solc panic-code accessor for arithmetic
overflow (`0x11`). -/
theorem call_constant_ARITHMETIC_OVERFLOW_17_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 160)) [] (.some "constant_ARITHMETIC_OVERFLOW_17")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0x11]) := by
  rw [show fuel + (extra + 160) = (fuel + extra) + 160 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_constant_ARITHMETIC_OVERFLOW_17]
  simp only [yulFunction_constant_ARITHMETIC_OVERFLOW_17,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hconv :=
    call_convert_17_to_uint8_17_direct (fuel := fuel + extra + 35) (shared := shared)
      (store := Finmap.insert "expr_16" (FormalYul.word 0x11) (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [FormalYul.word] at hconv
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
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
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, h1, h2, h3]

end ExpYul
