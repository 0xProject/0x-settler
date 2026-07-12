import ExpProof.ExpYulProof
import Common.Word
import ExpProof.Seam.Helpers
import FormalYul.Preservation

/-!
# Branch-agnostic dispatcher / calldata seam for `ExpYul`

The free-pointer setup, ABI calldata decode, selector extraction, switch-case selection, and the
contract-polymorphic `runContract` packaging are independent of which way `expRayToWad` resolves
(revert vs value), so they live here, shared by `Seam/Revert.lean` and the value path. Mirrors the
`ln` dispatcher seam.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- Shared state after the dispatcher's `mstore(64,128)` free-pointer init, for the
`expRayToWad` calldata. -/
def expSharedAfterFreePtr (x : Nat) : EvmYul.SharedState .Yul :=
  let shared := FormalYul.sharedFor yulContract (selector_expRayToWad ++ FormalYul.encodeWords [x])
  { shared with toMachineState := shared.toMachineState.mstore (FormalYul.word 64) (FormalYul.word 128) }

@[simp]
theorem expSharedAfterFreePtr_lookup (x : Nat) :
    (expSharedAfterFreePtr x).accountMap.find?
        (expSharedAfterFreePtr x).executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract) := by
  simp [expSharedAfterFreePtr]

@[simp]
theorem expSharedAfterFreePtr_calldata (x : Nat) :
    (expSharedAfterFreePtr x).executionEnv.calldata =
      selector_expRayToWad ++ FormalYul.encodeWords [x] := by
  simp [expSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
theorem expSharedAfterFreePtr_weiValue (x : Nat) :
    (expSharedAfterFreePtr x).executionEnv.weiValue = ({ val := 0 } : EvmYul.UInt256) := by
  simp [expSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
theorem expSharedAfterFreePtr_mload64 (x : Nat) :
    ((expSharedAfterFreePtr x).mload (FormalYul.word 64)).1 = FormalYul.word 128 :=
  FormalYul.Preservation.sharedFor_mload_freePtr_after_mstore yulContract
    (selector_expRayToWad ++ FormalYul.encodeWords [x])

@[simp]
theorem expRayToWad_calldata_size (x : Nat) :
    (selector_expRayToWad ++ FormalYul.encodeWords [x]).size = 36 := by
  simp [selector_expRayToWad, FormalYul.encodeWords,
    FormalYul.bytes, ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
    FormalYul.Preservation.encodeWord_size]

/-- Shared state after the dispatcher's `mstore(64,128)` free-pointer init, for the
`mulExpRay` calldata. -/
def mulExpSharedAfterFreePtr (y x : Nat) : EvmYul.SharedState .Yul :=
  let shared := FormalYul.sharedFor yulContract (selector_mulExpRay ++ FormalYul.encodeWords [y, x])
  { shared with toMachineState := shared.toMachineState.mstore (FormalYul.word 64) (FormalYul.word 128) }

@[simp]
theorem mulExpSharedAfterFreePtr_lookup (y x : Nat) :
    (mulExpSharedAfterFreePtr y x).accountMap.find?
        (mulExpSharedAfterFreePtr y x).executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract) := by
  simp [mulExpSharedAfterFreePtr]

@[simp]
theorem mulExpSharedAfterFreePtr_calldata (y x : Nat) :
    (mulExpSharedAfterFreePtr y x).executionEnv.calldata =
      selector_mulExpRay ++ FormalYul.encodeWords [y, x] := by
  simp [mulExpSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
theorem mulExpSharedAfterFreePtr_weiValue (y x : Nat) :
    (mulExpSharedAfterFreePtr y x).executionEnv.weiValue = ({ val := 0 } : EvmYul.UInt256) := by
  simp [mulExpSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
theorem mulExpSharedAfterFreePtr_mload64 (y x : Nat) :
    ((mulExpSharedAfterFreePtr y x).mload (FormalYul.word 64)).1 = FormalYul.word 128 :=
  FormalYul.Preservation.sharedFor_mload_freePtr_after_mstore yulContract
    (selector_mulExpRay ++ FormalYul.encodeWords [y, x])

@[simp]
theorem mulExpRay_calldata_size (y x : Nat) :
    (selector_mulExpRay ++ FormalYul.encodeWords [y, x]).size = 68 := by
  simp [selector_mulExpRay, FormalYul.encodeWords,
    FormalYul.bytes, ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
    FormalYul.Preservation.encodeWord_size]

@[simp]
theorem calldataload_expRayToWad_arg_of_calldata
    (x : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hdata : shared.executionEnv.calldata = selector_expRayToWad ++ FormalYul.encodeWords [x]) :
    EvmYul.State.calldataload
      (EvmYul.Yul.State.Ok shared store).toState (FormalYul.word 4) =
      FormalYul.word x := by
  simp [EvmYul.State.calldataload, EvmYul.Yul.State.toState, hdata,
    selector_expRayToWad, FormalYul.encodeWords]

@[simp]
theorem calldataload_mulExpRay_arg0_of_calldata
    (y x : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hdata : shared.executionEnv.calldata = selector_mulExpRay ++ FormalYul.encodeWords [y, x]) :
    EvmYul.State.calldataload
      (EvmYul.Yul.State.Ok shared store).toState (FormalYul.word 4) =
      FormalYul.word y := by
  exact FormalYul.Preservation.calldataload_two_args_first_of_calldata
    0x0d 0xbb 0x6b 0xb9 y x shared store (by simpa [selector_mulExpRay] using hdata)

@[simp]
theorem calldataload_mulExpRay_arg1_of_calldata
    (y x : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hdata : shared.executionEnv.calldata = selector_mulExpRay ++ FormalYul.encodeWords [y, x]) :
    EvmYul.State.calldataload
      (EvmYul.Yul.State.Ok shared store).toState (FormalYul.word 36) =
      FormalYul.word x := by
  exact FormalYul.Preservation.calldataload_two_args_second_of_calldata
    0x0d 0xbb 0x6b 0xb9 y x shared store (by simpa [selector_mulExpRay] using hdata)

/-- `validator_revert_t_int256(value)` does `if iszero(eq(value, cleanup_t_int256(value))) {revert}`;
since `cleanup_t_int256` is the identity the equality always holds, so it never reverts. -/
theorem call_validator_revert_t_int256_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 80)) [FormalYul.word v] (.some "validator_revert_t_int256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, []) := by
  rw [show fuel + (extra + 80) = (fuel + extra) + 80 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_validator_revert_t_int256]
  simp only [yulFunction_validator_revert_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcleanup :=
    call_cleanup_t_int256_direct (v := v) (fuel := fuel + extra) (extra := 51)
      (shared := shared) (hlookup := hlookup)
  simp only [Nat.reduceAdd, FormalYul.word] at hcleanup
  simp +decide [EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    FormalYul.word, hcleanup]

/-- `validator_revert_t_int128(value)` accepts exactly the words unchanged by
`cleanup_t_int128`. -/
theorem call_validator_revert_t_int128_direct
    (v fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hclean : EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word v) =
      FormalYul.word v) :
    EvmYul.Yul.call (fuel + (extra + 80)) [FormalYul.word v] (.some "validator_revert_t_int128")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, []) := by
  rw [show fuel + (extra + 80) = (fuel + extra) + 80 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_validator_revert_t_int128]
  simp only [yulFunction_validator_revert_t_int128,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcleanup :=
    call_cleanup_t_int128_direct (v := v) (fuel := fuel + extra) (extra := 51)
      (shared := shared) (hlookup := hlookup)
  simp only [Nat.reduceAdd, FormalYul.word] at hcleanup
  simp only [FormalYul.word] at hclean
  simp +decide [EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    FormalYul.word, hcleanup, hclean]

/-- `abi_decode_t_int256(offset, end) := calldataload(offset); validator(value)` — for the
`expRayToWad` calldata at offset 4 it reads `x` and validates (no revert). -/
theorem call_abi_decode_t_int256_of_calldata
    (x fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_expRayToWad ++ FormalYul.encodeWords [x]) :
    EvmYul.Yul.call (fuel + (extra + 200)) [FormalYul.word 4, FormalYul.word 36]
      (.some "abi_decode_t_int256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word x]) := by
  rw [show fuel + (extra + 200) = (fuel + extra) + 200 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_abi_decode_t_int256]
  simp only [yulFunction_abi_decode_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hvalidator :=
    call_validator_revert_t_int256_direct (v := x) (fuel := fuel + extra) (extra := 115)
      (shared := shared) (hlookup := hlookup)
  simp only [Nat.reduceAdd, FormalYul.word] at hvalidator
  have hload :=
    calldataload_expRayToWad_arg_of_calldata x shared
      (Finmap.insert "offset" (FormalYul.word 4)
        (Finmap.insert "end" (FormalYul.word 36) (Inhabited.default : EvmYul.Yul.VarStore)))
      hdata
  simp [FormalYul.word] at hload
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hload, hvalidator]

/-- `abi_decode_tuple_t_int256(headStart, dataEnd)` decodes the single `int256` argument `x`. -/
theorem call_abi_decode_tuple_t_int256_of_calldata
    (x fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_expRayToWad ++ FormalYul.encodeWords [x]) :
    EvmYul.Yul.call (fuel + (extra + 320)) [FormalYul.word 4, FormalYul.word 36]
      (.some "abi_decode_tuple_t_int256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word x]) := by
  rw [show fuel + (extra + 320) = (fuel + extra) + 320 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_abi_decode_tuple_t_int256]
  simp only [yulFunction_abi_decode_tuple_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hdecode :=
    call_abi_decode_t_int256_of_calldata (x := x) (fuel := fuel + extra) (extra := 113)
      (shared := shared) (hlookup := hlookup) (hdata := hdata)
  simp only [Nat.reduceAdd, FormalYul.word] at hdecode
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hdecode]

theorem call_abi_decode_t_int128_mul_arg0_of_calldata
    (y x fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_mulExpRay ++ FormalYul.encodeWords [y, x])
    (hclean : EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word y) =
      FormalYul.word y) :
    EvmYul.Yul.call (fuel + (extra + 200)) [FormalYul.word 4, FormalYul.word 68]
      (.some "abi_decode_t_int128") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word y]) := by
  rw [show fuel + (extra + 200) = (fuel + extra) + 200 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_abi_decode_t_int128]
  simp only [yulFunction_abi_decode_t_int128,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hvalidator :=
    call_validator_revert_t_int128_direct (v := y) (fuel := fuel + extra) (extra := 115)
      (shared := shared) (hlookup := hlookup) (hclean := hclean)
  simp only [Nat.reduceAdd, FormalYul.word] at hvalidator
  have hload :=
    calldataload_mulExpRay_arg0_of_calldata y x shared
      (Finmap.insert "offset" (FormalYul.word 4)
        (Finmap.insert "end" (FormalYul.word 68) (Inhabited.default : EvmYul.Yul.VarStore)))
      hdata
  simp [FormalYul.word] at hload
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hload, hvalidator]

theorem call_abi_decode_t_int256_mul_arg1_of_calldata
    (y x fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_mulExpRay ++ FormalYul.encodeWords [y, x]) :
    EvmYul.Yul.call (fuel + (extra + 200)) [FormalYul.word 36, FormalYul.word 68]
      (.some "abi_decode_t_int256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word x]) := by
  rw [show fuel + (extra + 200) = (fuel + extra) + 200 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_abi_decode_t_int256]
  simp only [yulFunction_abi_decode_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hvalidator :=
    call_validator_revert_t_int256_direct (v := x) (fuel := fuel + extra) (extra := 115)
      (shared := shared) (hlookup := hlookup)
  simp only [Nat.reduceAdd, FormalYul.word] at hvalidator
  have hload :=
    calldataload_mulExpRay_arg1_of_calldata y x shared
      (Finmap.insert "offset" (FormalYul.word 36)
        (Finmap.insert "end" (FormalYul.word 68) (Inhabited.default : EvmYul.Yul.VarStore)))
      hdata
  simp [FormalYul.word] at hload
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hload, hvalidator]

/-- `abi_decode_tuple_t_int128t_int256(headStart, dataEnd)` decodes `(y, x)`. -/
theorem call_abi_decode_tuple_t_int128t_int256_of_mul_calldata
    (y x fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_mulExpRay ++ FormalYul.encodeWords [y, x])
    (hclean : EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word y) =
      FormalYul.word y) :
    EvmYul.Yul.call (fuel + (extra + 520)) [FormalYul.word 4, FormalYul.word 68]
      (.some "abi_decode_tuple_t_int128t_int256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word y, FormalYul.word x]) := by
  rw [show fuel + (extra + 520) = (fuel + extra) + 520 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_abi_decode_tuple_t_int128t_int256]
  simp only [yulFunction_abi_decode_tuple_t_int128t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hdecode0 :=
    call_abi_decode_t_int128_mul_arg0_of_calldata (y := y) (x := x)
      (fuel := fuel + extra) (extra := 313)
      (shared := shared)
      (store := Finmap.insert "offset" (FormalYul.word 0)
        (Finmap.insert "headStart" (FormalYul.word 4)
          (Finmap.insert "dataEnd" (FormalYul.word 68)
            (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup) (hdata := hdata) (hclean := hclean)
  have hdecode1 :=
    call_abi_decode_t_int256_mul_arg1_of_calldata (y := y) (x := x)
      (fuel := fuel + extra) (extra := 312)
      (shared := shared)
      (store := Finmap.insert "offset" (FormalYul.word 32)
        (Finmap.insert "value0" (FormalYul.word y)
          (Finmap.insert "offset" (FormalYul.word 0)
            (Finmap.insert "headStart" (FormalYul.word 4)
              (Finmap.insert "dataEnd" (FormalYul.word 68)
                (Inhabited.default : EvmYul.Yul.VarStore))))))
      (hlookup := hlookup) (hdata := hdata)
  simp only [Nat.reduceAdd, FormalYul.word] at hdecode0 hdecode1
  have h436 : EvmYul.UInt256.ofNat 4 + EvmYul.UInt256.ofNat 32 = EvmYul.UInt256.ofNat 36 := by
    decide
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, h436, hdecode0, hdecode1]

/-- `allocate_unbounded() := mload(64)` — returns the current free pointer. -/
theorem call_allocate_unbounded_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [] (.some "allocate_unbounded") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok
      ((EvmYul.Yul.State.Ok shared store).setMachineState
        (((EvmYul.Yul.State.Ok shared store).toMachineState.mload (FormalYul.word 64)).2),
        [((EvmYul.Yul.State.Ok shared store).toMachineState.mload (FormalYul.word 64)).1]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_allocate_unbounded]
  simp only [yulFunction_allocate_unbounded,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

/-- `abi_encode_t_int256_to_t_int256_fromStack(value, pos) := mstore(pos, cleanup(value))`,
specialized to a literal `value = word v` (the only shape the return path needs). -/
theorem call_abi_encode_t_int256_to_t_int256_fromStack_direct
    (v : Nat) (pos : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 90) [FormalYul.word v, pos]
      (.some "abi_encode_t_int256_to_t_int256_fromStack")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok ((EvmYul.Yul.State.Ok shared store).setMachineState
      ((EvmYul.Yul.State.Ok shared store).toMachineState.mstore pos (FormalYul.word v)), []) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_abi_encode_t_int256_to_t_int256_fromStack]
  simp only [yulFunction_abi_encode_t_int256_to_t_int256_fromStack,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcleanup :=
    call_cleanup_t_int256_direct (v := v) (fuel := fuel) (extra := 64) (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word v)
        (Finmap.insert "pos" pos (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup)
  simp only [Nat.reduceAdd, FormalYul.word] at hcleanup
  simp +decide [EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    FormalYul.word, hcleanup]

/-- `abi_encode_tuple_t_int256__to_t_int256__fromStack(headStart, value)` encodes a single `int256`
return value (`value = word v`) and returns the tail pointer `headStart + 32`. -/
theorem call_abi_encode_tuple_t_int256__to_t_int256__fromStack_direct
    (headStart : EvmYul.UInt256) (v : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 150) [headStart, FormalYul.word v]
      (.some "abi_encode_tuple_t_int256__to_t_int256__fromStack")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok ((EvmYul.Yul.State.Ok shared store).setMachineState
      ((EvmYul.Yul.State.Ok shared store).toMachineState.mstore headStart (FormalYul.word v)),
      [headStart + FormalYul.word 32]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_abi_encode_tuple_t_int256__to_t_int256__fromStack]
  simp only [yulFunction_abi_encode_tuple_t_int256__to_t_int256__fromStack,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hencode :=
    call_abi_encode_t_int256_to_t_int256_fromStack_direct
      (v := v) (pos := headStart + FormalYul.word 0) (fuel := fuel + 55)
      (shared := shared)
      (store := Finmap.insert "tail" (headStart + FormalYul.word 32)
        (Finmap.insert "headStart" headStart
          (Finmap.insert "value0" (FormalYul.word v) (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup)
  simp [FormalYul.word] at hencode
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hencode]

/-- `shift_right_224_unsigned(value) := shr(224, value)`. -/
theorem call_shift_right_224_unsigned_direct
    (v : EvmYul.UInt256) (fuel : Nat)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v] (.some "shift_right_224_unsigned")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [EvmYul.UInt256.shiftRight v (FormalYul.word 224)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_shift_right_224_unsigned]
  simp only [yulFunction_shift_right_224_unsigned,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

theorem sharedFor_inherited_mstore_mk_eq_expSharedAfterFreePtr (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_expRayToWad ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_expRayToWad ++ FormalYul.encodeWords [x])).mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      expSharedAfterFreePtr x := rfl

theorem sharedFor_inherited_mstore_mk_eq_expSharedAfterFreePtr_raw (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_expRayToWad ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_expRayToWad ++ FormalYul.encodeWords [x])).mstore
          (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128))) =
      expSharedAfterFreePtr x := by
  simpa [FormalYul.word] using sharedFor_inherited_mstore_mk_eq_expSharedAfterFreePtr x

@[simp]
theorem sharedFor_expRayToWad_calldata_size (x : Nat) :
    (FormalYul.sharedFor yulContract
      (selector_expRayToWad ++ FormalYul.encodeWords [x])).executionEnv.calldata.size = 36 := by
  simp [FormalYul.sharedFor, FormalYul.envFor, expRayToWad_calldata_size]

theorem expRayToWad_selector_afterFreePtr (x : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok (expSharedAfterFreePtr x)
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 1099384363 := by
  have hselector :=
    FormalYul.Preservation.shiftRight_calldataload_selector_single_arg_of_calldata
      (shared := expSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (a := 0x41) (b := 0x87) (c := 0x46) (d := 0x2b) (x := x)
      (by simp [selector_expRayToWad])
  simpa [EvmYul.fromBytesBigEndian, EvmYul.fromBytes', FormalYul.word] using hselector

@[simp]
theorem expRayToWad_selector_sharedFor_mk (x : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_expRayToWad ++ FormalYul.encodeWords [x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_expRayToWad ++ FormalYul.encodeWords [x])).mstore
                (FormalYul.word 64) (FormalYul.word 128)))
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 1099384363 := by
  rw [sharedFor_inherited_mstore_mk_eq_expSharedAfterFreePtr]
  exact expRayToWad_selector_afterFreePtr x

@[simp]
theorem selectSwitchCase_expRayToWad_sharedFor_mk (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (EvmYul.SharedState.mk
              (FormalYul.sharedFor yulContract
                (selector_expRayToWad ++ FormalYul.encodeWords [x])).toState
              ((FormalYul.sharedFor yulContract
                (selector_expRayToWad ++ FormalYul.encodeWords [x])).mstore
                  (FormalYul.word 64) (FormalYul.word 128)))
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (FormalYul.word 0))
      (FormalYul.word 224))
      [(FormalYul.word 230386617,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_mulExpRay) [])]),
        (FormalYul.word 1099384363,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_expRayToWad) [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_expRayToWad) [])] := by
  rw [expRayToWad_selector_sharedFor_mk]
  rfl

theorem selectSwitchCase_expRayToWad_sharedFor_mk_raw (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (EvmYul.SharedState.mk
              (FormalYul.sharedFor yulContract
                (selector_expRayToWad ++ FormalYul.encodeWords [x])).toState
              ((FormalYul.sharedFor yulContract
                (selector_expRayToWad ++ FormalYul.encodeWords [x])).mstore
                  (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (EvmYul.UInt256.ofNat 0))
      (EvmYul.UInt256.ofNat 224))
      [(EvmYul.UInt256.ofNat 230386617,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_mulExpRay) [])]),
        (EvmYul.UInt256.ofNat 1099384363,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_expRayToWad) [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_expRayToWad) [])] := by
  simpa [FormalYul.word] using selectSwitchCase_expRayToWad_sharedFor_mk x

theorem sharedFor_inherited_mstore_mk_eq_mulExpSharedAfterFreePtr (y x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_mulExpRay ++ FormalYul.encodeWords [y, x])).toState
        ((FormalYul.sharedFor yulContract (selector_mulExpRay ++ FormalYul.encodeWords [y, x])).mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      mulExpSharedAfterFreePtr y x := rfl

theorem sharedFor_inherited_mstore_mk_eq_mulExpSharedAfterFreePtr_raw (y x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_mulExpRay ++ FormalYul.encodeWords [y, x])).toState
        ((FormalYul.sharedFor yulContract (selector_mulExpRay ++ FormalYul.encodeWords [y, x])).mstore
          (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128))) =
      mulExpSharedAfterFreePtr y x := by
  simpa [FormalYul.word] using sharedFor_inherited_mstore_mk_eq_mulExpSharedAfterFreePtr y x

@[simp]
theorem sharedFor_mulExpRay_calldata_size (y x : Nat) :
    (FormalYul.sharedFor yulContract
      (selector_mulExpRay ++ FormalYul.encodeWords [y, x])).executionEnv.calldata.size = 68 := by
  simp [FormalYul.sharedFor, FormalYul.envFor, mulExpRay_calldata_size]

theorem mulExpRay_selector_afterFreePtr (y x : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok (mulExpSharedAfterFreePtr y x)
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 230386617 := by
  have hselector :=
    FormalYul.Preservation.shiftRight_calldataload_selector_two_args_of_calldata
      (shared := mulExpSharedAfterFreePtr y x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (a := 0x0d) (b := 0xbb) (c := 0x6b) (d := 0xb9) (x := y) (y := x)
      (by simp [selector_mulExpRay])
  simpa [EvmYul.fromBytesBigEndian, EvmYul.fromBytes', FormalYul.word] using hselector

@[simp]
theorem mulExpRay_selector_sharedFor_mk (y x : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_mulExpRay ++ FormalYul.encodeWords [y, x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_mulExpRay ++ FormalYul.encodeWords [y, x])).mstore
                (FormalYul.word 64) (FormalYul.word 128)))
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 230386617 := by
  rw [sharedFor_inherited_mstore_mk_eq_mulExpSharedAfterFreePtr]
  exact mulExpRay_selector_afterFreePtr y x

@[simp]
theorem selectSwitchCase_mulExpRay_sharedFor_mk (y x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (EvmYul.SharedState.mk
              (FormalYul.sharedFor yulContract
                (selector_mulExpRay ++ FormalYul.encodeWords [y, x])).toState
              ((FormalYul.sharedFor yulContract
                (selector_mulExpRay ++ FormalYul.encodeWords [y, x])).mstore
                  (FormalYul.word 64) (FormalYul.word 128)))
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (FormalYul.word 0))
      (FormalYul.word 224))
      [(FormalYul.word 230386617,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_mulExpRay) [])]),
        (FormalYul.word 1099384363,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_expRayToWad) [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_mulExpRay) [])] := by
  rw [mulExpRay_selector_sharedFor_mk]
  rfl

theorem selectSwitchCase_mulExpRay_sharedFor_mk_raw (y x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (EvmYul.SharedState.mk
              (FormalYul.sharedFor yulContract
                (selector_mulExpRay ++ FormalYul.encodeWords [y, x])).toState
              ((FormalYul.sharedFor yulContract
                (selector_mulExpRay ++ FormalYul.encodeWords [y, x])).mstore
                  (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (EvmYul.UInt256.ofNat 0))
      (EvmYul.UInt256.ofNat 224))
      [(EvmYul.UInt256.ofNat 230386617,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_mulExpRay) [])]),
        (EvmYul.UInt256.ofNat 1099384363,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_expRayToWad) [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_mulExpRay) [])] := by
  simpa [FormalYul.word] using selectSwitchCase_mulExpRay_sharedFor_mk y x

/-- Revert-analogue of `Preservation.runContract_ok_of_dispatcherReturn`: if the bare dispatcher
`exec` on `stateFor` reverts, the wrapped `runContract` returns `.error "revert"`. Contract
polymorphic; mirrors `ln`'s lemma verbatim. -/
theorem runContract_revert_of_exec_revert
    {contract : YulContract} {input : ByteArray} {execFuel : Nat}
    (h : EvmYul.Yul.exec execFuel contract.dispatcher (.some contract)
          (stateFor contract input) = .error EvmYul.Yul.Exception.Revert) :
    runContract contract input (Nat.succ (Nat.succ execFuel)) = .error "revert" := by
  unfold runContract
  rw [EvmYul.Yul.callDispatcher.eq_def]
  simp only [stateFor, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.executionEnv, sharedFor, envFor, accountMapFor, accountFor,
    EvmYul.Yul.State.multifill, EvmYul.Yul.State.setStore, List.zip_nil_left, List.foldr_nil,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def]
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  have hdisp' :
      EvmYul.Yul.exec execFuel contract.dispatcher (.some contract)
        (EvmYul.Yul.State.Ok
          { (Inhabited.default : EvmYul.SharedState .Yul) with
            accountMap := accountMapFor contract
            executionEnv := envFor contract input
            gasAvailable := .ofNat 1000000000 }
          (Inhabited.default : EvmYul.Yul.VarStore)) =
        .error EvmYul.Yul.Exception.Revert := by
    simpa [stateFor, sharedFor] using h
  have hdisp'' :
      EvmYul.Yul.exec execFuel contract.dispatcher (.some contract)
        (EvmYul.Yul.State.Ok
          { accountMap := accountMapFor contract,
            σ₀ := (Inhabited.default : EvmYul.SharedState .Yul).σ₀,
            totalGasUsedInBlock := (Inhabited.default : EvmYul.SharedState .Yul).totalGasUsedInBlock,
            transactionReceipts := (Inhabited.default : EvmYul.SharedState .Yul).transactionReceipts,
            substate := (Inhabited.default : EvmYul.SharedState .Yul).substate,
            executionEnv := envFor contract input,
            blocks := (Inhabited.default : EvmYul.SharedState .Yul).blocks,
            genesisBlockHeader := (Inhabited.default : EvmYul.SharedState .Yul).genesisBlockHeader,
            createdAccounts := (Inhabited.default : EvmYul.SharedState .Yul).createdAccounts,
            gasAvailable := EvmYul.UInt256.ofNat 1000000000,
            activeWords := (Inhabited.default : EvmYul.SharedState .Yul).activeWords,
            memory := (Inhabited.default : EvmYul.SharedState .Yul).memory,
            returnData := (Inhabited.default : EvmYul.SharedState .Yul).returnData,
            H_return := (Inhabited.default : EvmYul.SharedState .Yul).H_return }
          (Inhabited.default : EvmYul.Yul.VarStore)) =
        .error EvmYul.Yul.Exception.Revert := by
    simpa using hdisp'
  have hdisp''' :
      EvmYul.Yul.exec execFuel contract.dispatcher (.some contract)
        (EvmYul.Yul.State.Ok
          { accountMap := Batteries.RBMap.insert ∅ contractOwner
              { (Inhabited.default : EvmYul.Account .Yul) with code := contract },
            σ₀ := (Inhabited.default : EvmYul.SharedState .Yul).σ₀,
            totalGasUsedInBlock := (Inhabited.default : EvmYul.SharedState .Yul).totalGasUsedInBlock,
            transactionReceipts := (Inhabited.default : EvmYul.SharedState .Yul).transactionReceipts,
            substate := (Inhabited.default : EvmYul.SharedState .Yul).substate,
            executionEnv := { (Inhabited.default : EvmYul.ExecutionEnv .Yul) with
              calldata := input
              code := contract
              codeOwner := contractOwner
              weiValue := ⟨0⟩
              perm := true },
            blocks := (Inhabited.default : EvmYul.SharedState .Yul).blocks,
            genesisBlockHeader := (Inhabited.default : EvmYul.SharedState .Yul).genesisBlockHeader,
            createdAccounts := (Inhabited.default : EvmYul.SharedState .Yul).createdAccounts,
            gasAvailable := EvmYul.UInt256.ofNat 1000000000,
            activeWords := (Inhabited.default : EvmYul.SharedState .Yul).activeWords,
            memory := (Inhabited.default : EvmYul.SharedState .Yul).memory,
            returnData := (Inhabited.default : EvmYul.SharedState .Yul).returnData,
            H_return := (Inhabited.default : EvmYul.SharedState .Yul).H_return }
          (Inhabited.default : EvmYul.Yul.VarStore)) =
        .error EvmYul.Yul.Exception.Revert := by
    simpa [accountMapFor, accountFor, envFor] using hdisp''
  rw [hdisp''']

end ExpYul
