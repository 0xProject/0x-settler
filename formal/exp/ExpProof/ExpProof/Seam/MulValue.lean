import ExpProof.ExpYulProof
import Common.Word
import ExpProof.Seam.Helpers
import ExpProof.Seam.Dispatcher
import FormalYul.Preservation

/-!
# Value-path reductions for `mulExpRay`

This file discharges the concrete zero-magnitude path, which returns before the dynamic scale,
octave, range guard, and kernel.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
/-- `fun_mulExpRay(0, x)` returns `0` before evaluating scale, octave, range, or kernel code. -/
theorem call_fun_mulExpRay_zero_direct
    (x fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 500)) [FormalYul.word 0, FormalYul.word x]
      (.some yulName_fun_mulExpRay) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  rw [show fuel + (extra + 500) = (fuel + extra) + 500 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_mulExpRay]
  simp only [yulFunction_fun_mulExpRay, yulFunction_fun_mulExpRay_294,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hzeroInit :=
    call_zero_value_for_split_t_int256_direct (fuel := fuel + extra) (extra := 476)
      (shared := shared) (hlookup := hlookup)
  have hcleanupY :=
    call_cleanup_t_int256_direct (v := 0) (fuel := fuel + extra) (extra := 467)
      (shared := shared) (hlookup := hlookup)
  have hconvertCmp :=
    call_convert_0_to_int256_direct (fuel := fuel + extra) (extra := 369)
      (shared := shared) (hlookup := hlookup)
  have hconvertRet :=
    call_convert_0_to_int256_direct (fuel := fuel + extra) (extra := 367)
      (shared := shared) (hlookup := hlookup)
  simp only [Nat.reduceAdd, FormalYul.word] at hzeroInit hcleanupY hconvertCmp hconvertRet
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    FormalYul.Preservation.call_on_checkpoint,
    Finmap.lookup_insert, FormalYul.word,
    hzeroInit, hcleanupY, hconvertCmp, hconvertRet]

set_option maxHeartbeats 4000000 in
/-- `fun_wrap_mulExpRay(0, x)` forwards to `fun_mulExpRay`, giving `0`. -/
theorem call_fun_wrap_mulExpRay_zero_direct
    (x fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 1100)) [FormalYul.word 0, FormalYul.word x]
      (.some yulName_fun_wrap_mulExpRay) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  rw [show fuel + (extra + 1100) = (fuel + extra) + 1100 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_wrap_mulExpRay]
  simp only [yulFunction_fun_wrap_mulExpRay, yulFunction_fun_wrap_mulExpRay_390,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hinner :=
    call_fun_mulExpRay_zero_direct (x := x) (fuel := fuel + extra) (extra := 589)
      (shared := shared) (hlookup := hlookup)
  simp only [Nat.reduceAdd, FormalYul.word] at hinner
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    call_zero_value_for_split_t_int256_direct (fuel := fuel + extra) (extra := 1076)
      (shared := shared) (hlookup := hlookup),
    hinner]

set_option maxHeartbeats 12000000 in
/-- The external `mulExpRay` entrypoint at `y = 0` ABI-encodes and returns `0`. -/
theorem external_fun_wrap_mulExpRay_zero_calldata_result
    (x : Nat) (store : EvmYul.Yul.VarStore) :
    ((match
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_mulExpRay) (.some yulContract)
        (EvmYul.Yul.State.Ok (mulExpSharedAfterFreePtr 0 x) store)
    with
    | .error (.YulHalt state _) => FormalYul.resultWord (FormalYul.returnOf state)
    | .error .Revert => .error "revert"
    | .error err => .error (reprStr err)
    | .ok (state, _) => FormalYul.resultWord (FormalYul.returnOf state)) :
      Except String Nat) =
      .ok 0 := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [mulExpSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_mulExpRay]
  simp only [yulFunction_external_fun_wrap_mulExpRay, yulFunction_external_fun_wrap_mulExpRay_390,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word 0)
      (Finmap.insert "param_0" (FormalYul.word 0)
        (Finmap.insert "param_1" (FormalYul.word x)
          (Inhabited.default : EvmYul.Yul.VarStore)))
  let memPos :=
    ((EvmYul.Yul.State.Ok (mulExpSharedAfterFreePtr 0 x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { mulExpSharedAfterFreePtr 0 x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (mulExpSharedAfterFreePtr 0 x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_int256t_int256_of_mul_calldata (y := 0) (x := x)
      (fuel := 0) (extra := 999464)
      (shared := mulExpSharedAfterFreePtr 0 x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := mulExpSharedAfterFreePtr_lookup 0 x)
      (hdata := mulExpSharedAfterFreePtr_calldata 0 x)
  simp only [Nat.reduceAdd, FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_mulExpRay_zero_direct (x := x) (fuel := 0) (extra := 998883)
      (shared := mulExpSharedAfterFreePtr 0 x)
      (store := Finmap.insert "param_0" (FormalYul.word 0)
        (Finmap.insert "param_1" (FormalYul.word x)
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := mulExpSharedAfterFreePtr_lookup 0 x)
  simp only [Nat.reduceAdd, FormalYul.word] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := mulExpSharedAfterFreePtr 0 x)
      (store := baseStore) (hlookup := mulExpSharedAfterFreePtr_lookup 0 x)
  simp only [FormalYul.word, baseStore] at halloc
  have hencode :=
    call_abi_encode_tuple_t_int256__to_t_int256__fromStack_direct
      (headStart := memPos) (v := 0) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by simp [memShared, mulExpSharedAfterFreePtr_lookup 0 x])
  simp [FormalYul.word, memShared, encStore, memPos, baseStore] at hencode
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,
    mulExpSharedAfterFreePtr_weiValue, mulExpSharedAfterFreePtr_calldata, mulExpRay_calldata_size,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    EvmYul.Yul.State.toMachineState, FormalYul.returnOf,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    hdecode, hwrap, halloc, hencode]
  have hmload :
      ((mulExpSharedAfterFreePtr 0 x).mload (EvmYul.UInt256.ofNat 64)).1 =
        EvmYul.UInt256.ofNat 128 := by
    simpa [FormalYul.word] using mulExpSharedAfterFreePtr_mload64 0 x
  rw [hmload]
  have hretLen :
      EvmYul.UInt256.ofNat 128 + EvmYul.UInt256.ofNat 32 - EvmYul.UInt256.ofNat 128 =
        FormalYul.word 32 := by decide
  rw [hretLen]
  rw [FormalYul.Preservation.resultWord_evmReturn_mstore_word]
  rfl

set_option maxHeartbeats 12000000 in
/-- The external `mulExpRay` entrypoint at `y = 0` halts (returns). -/
theorem external_fun_wrap_mulExpRay_zero_calldata_halts
    (x : Nat) (store : EvmYul.Yul.VarStore) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_mulExpRay) (.some yulContract)
        (EvmYul.Yul.State.Ok (mulExpSharedAfterFreePtr 0 x) store) =
        .error (.YulHalt state value) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [mulExpSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_mulExpRay]
  simp only [yulFunction_external_fun_wrap_mulExpRay, yulFunction_external_fun_wrap_mulExpRay_390,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word 0)
      (Finmap.insert "param_0" (FormalYul.word 0)
        (Finmap.insert "param_1" (FormalYul.word x)
          (Inhabited.default : EvmYul.Yul.VarStore)))
  let memPos :=
    ((EvmYul.Yul.State.Ok (mulExpSharedAfterFreePtr 0 x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { mulExpSharedAfterFreePtr 0 x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (mulExpSharedAfterFreePtr 0 x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_int256t_int256_of_mul_calldata (y := 0) (x := x)
      (fuel := 0) (extra := 999464)
      (shared := mulExpSharedAfterFreePtr 0 x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := mulExpSharedAfterFreePtr_lookup 0 x)
      (hdata := mulExpSharedAfterFreePtr_calldata 0 x)
  simp only [Nat.reduceAdd, FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_mulExpRay_zero_direct (x := x) (fuel := 0) (extra := 998883)
      (shared := mulExpSharedAfterFreePtr 0 x)
      (store := Finmap.insert "param_0" (FormalYul.word 0)
        (Finmap.insert "param_1" (FormalYul.word x)
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := mulExpSharedAfterFreePtr_lookup 0 x)
  simp only [Nat.reduceAdd, FormalYul.word] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := mulExpSharedAfterFreePtr 0 x)
      (store := baseStore) (hlookup := mulExpSharedAfterFreePtr_lookup 0 x)
  simp only [FormalYul.word, baseStore] at halloc
  have hencode :=
    call_abi_encode_tuple_t_int256__to_t_int256__fromStack_direct
      (headStart := memPos) (v := 0) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by simp [memShared, mulExpSharedAfterFreePtr_lookup 0 x])
  simp [FormalYul.word, memShared, encStore, memPos, baseStore] at hencode
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,
    mulExpSharedAfterFreePtr_weiValue, mulExpSharedAfterFreePtr_calldata, mulExpRay_calldata_size,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    EvmYul.Yul.State.toMachineState,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    hdecode, hwrap, halloc, hencode]

set_option maxHeartbeats 12000000 in
/-- Result, starting from the exact state the dispatcher hands the external `mulExpRay` function. -/
theorem external_fun_wrap_mulExpRay_zero_dispatcher_state_result (x : Nat) :
    ((match
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_mulExpRay) (.some yulContract)
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_mulExpRay ++ FormalYul.encodeWords [0, x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_mulExpRay ++ FormalYul.encodeWords [0, x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
          (Finmap.insert "selector"
            (EvmYul.UInt256.shiftRight
              (EvmYul.State.calldataload
                (EvmYul.Yul.State.Ok
                  (EvmYul.SharedState.mk
                    (FormalYul.sharedFor yulContract
                      (selector_mulExpRay ++ FormalYul.encodeWords [0, x])).toState
                    ((FormalYul.sharedFor yulContract
                      (selector_mulExpRay ++ FormalYul.encodeWords [0, x])).mstore
                        (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
                  (Inhabited.default : EvmYul.Yul.VarStore)).toState
                (EvmYul.UInt256.ofNat 0))
              (EvmYul.UInt256.ofNat 224))
            (Inhabited.default : EvmYul.Yul.VarStore)))
    with
    | .error (.YulHalt state _) => FormalYul.resultWord (FormalYul.returnOf state)
    | .error .Revert => .error "revert"
    | .error err => .error (reprStr err)
    | .ok (state, _) => FormalYul.resultWord (FormalYul.returnOf state)) :
      Except String Nat) =
      .ok 0 := by
  rw [sharedFor_inherited_mstore_mk_eq_mulExpSharedAfterFreePtr_raw]
  exact external_fun_wrap_mulExpRay_zero_calldata_result x
    (store := Finmap.insert "selector"
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok (mulExpSharedAfterFreePtr 0 x)
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224))
      (Inhabited.default : EvmYul.Yul.VarStore))

set_option maxHeartbeats 12000000 in
/-- Halt, starting from the exact state the dispatcher hands the external `mulExpRay` function. -/
theorem external_fun_wrap_mulExpRay_zero_dispatcher_state_halts (x : Nat) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_mulExpRay) (.some yulContract)
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_mulExpRay ++ FormalYul.encodeWords [0, x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_mulExpRay ++ FormalYul.encodeWords [0, x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
          (Finmap.insert "selector"
            (EvmYul.UInt256.shiftRight
              (EvmYul.State.calldataload
                (EvmYul.Yul.State.Ok
                  (EvmYul.SharedState.mk
                    (FormalYul.sharedFor yulContract
                      (selector_mulExpRay ++ FormalYul.encodeWords [0, x])).toState
                    ((FormalYul.sharedFor yulContract
                      (selector_mulExpRay ++ FormalYul.encodeWords [0, x])).mstore
                        (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
                  (Inhabited.default : EvmYul.Yul.VarStore)).toState
                (EvmYul.UInt256.ofNat 0))
              (EvmYul.UInt256.ofNat 224))
            (Inhabited.default : EvmYul.Yul.VarStore))) =
        .error (.YulHalt state value) := by
  rw [sharedFor_inherited_mstore_mk_eq_mulExpSharedAfterFreePtr_raw]
  exact external_fun_wrap_mulExpRay_zero_calldata_halts x
    (store := Finmap.insert "selector"
        (EvmYul.UInt256.shiftRight
          (EvmYul.State.calldataload
            (EvmYul.Yul.State.Ok (mulExpSharedAfterFreePtr 0 x)
              (Inhabited.default : EvmYul.Yul.VarStore)).toState
            (EvmYul.UInt256.ofNat 0))
          (EvmYul.UInt256.ofNat 224))
        (Inhabited.default : EvmYul.Yul.VarStore))

set_option maxHeartbeats 12000000 in
/-- **Zero-magnitude exactness.** `mulExpRay(0, x)` returns `0` for every exponent word. -/
theorem run_mul_exp_ray_evm_zero (x : Nat) :
    run_mul_exp_ray_evm 0 x = .ok 0 := by
  obtain ⟨haltState, _haltValue, hhalt⟩ :=
    external_fun_wrap_mulExpRay_zero_dispatcher_state_halts x
  have hresult := external_fun_wrap_mulExpRay_zero_dispatcher_state_result x
  rw [hhalt] at hresult
  have hReturn :
      FormalYul.Preservation.DispatcherReturn yulContract
        (FormalYul.calldata selector_mulExpRay [0, x]) 999998 (FormalYul.returnOf haltState) := by
    apply FormalYul.Preservation.dispatcherReturn_of_exec_halt
      (hdispatcher := yulContract_dispatcher)
    refine ⟨haltState, _haltValue, ?_, rfl⟩
    simp +decide [FormalYul.calldata, FormalYul.stateFor,
      yulDispatcher, EvmYul.Yul.execCall.eq_def,
      EvmYul.Yul.execPrimCall.eq_def,
      EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
      EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
      EvmYul.Yul.State.insert,
      EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.lookup!,
      EvmYul.Yul.State.executionEnv,
      EvmYul.Yul.State.toMachineState,
      GetElem?.getElem!, decidableGetElem?,
      EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
      EvmYul.Yul.State.store, Finmap.lookup_insert,
      FormalYul.word,
      call_shift_right_224_unsigned_direct]
    rw [selectSwitchCase_mulExpRay_sharedFor_mk_raw 0 x]
    simp +decide [hhalt, EvmYul.Yul.exec.eq_def,
      EvmYul.Yul.execCall.eq_def,
      EvmYul.Yul.reverse', EvmYul.Yul.multifill']
  unfold run_mul_exp_ray_evm
  exact FormalYul.Preservation.callWord_ok_of_dispatcherReturn_result_1000000
    (contract := yulContract) (selector := selector_mulExpRay) (args := [0, x])
    (hReturn := hReturn) (by simpa using hresult)

end ExpYul
