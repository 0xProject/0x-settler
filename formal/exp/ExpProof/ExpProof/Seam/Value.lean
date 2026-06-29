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

set_option maxHeartbeats 12000000 in
/-- The external entrypoint at `x = 0` ABI-encodes and returns `10^18`. -/
theorem external_fun_wrap_expRayToWad_zero_calldata_result
    (store : EvmYul.Yul.VarStore) :
    ((match
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_expRayToWad) (.some yulContract)
        (EvmYul.Yul.State.Ok (expSharedAfterFreePtr 0) store)
    with
    | .error (.YulHalt state _) => FormalYul.resultWord (FormalYul.returnOf state)
    | .error .Revert => .error "revert"
    | .error err => .error (reprStr err)
    | .ok (state, _) => FormalYul.resultWord (FormalYul.returnOf state)) :
      Except String Nat) =
      .ok 1000000000000000000 := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [expSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_expRayToWad]
  simp only [yulFunction_external_fun_wrap_expRayToWad, yulFunction_external_fun_wrap_expRayToWad_99,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word 1000000000000000000)
      (Finmap.insert "param_0" (FormalYul.word 0) (Inhabited.default : EvmYul.Yul.VarStore))
  let memPos :=
    ((EvmYul.Yul.State.Ok (expSharedAfterFreePtr 0) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { expSharedAfterFreePtr 0 with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (expSharedAfterFreePtr 0) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_int256_of_calldata (x := 0) (fuel := 0) (extra := 999664)
      (shared := expSharedAfterFreePtr 0)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := expSharedAfterFreePtr_lookup 0)
      (hdata := expSharedAfterFreePtr_calldata 0)
  simp only [Nat.reduceAdd, FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_expRayToWad_zero_direct (fuel := 0) (extra := 998883)
      (shared := expSharedAfterFreePtr 0)
      (store := Finmap.insert "param_0" (FormalYul.word 0)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := expSharedAfterFreePtr_lookup 0)
  simp only [Nat.reduceAdd, FormalYul.word] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := expSharedAfterFreePtr 0)
      (store := baseStore) (hlookup := expSharedAfterFreePtr_lookup 0)
  simp only [FormalYul.word, baseStore] at halloc
  have hencode :=
    call_abi_encode_tuple_t_int256__to_t_int256__fromStack_direct
      (headStart := memPos) (v := 1000000000000000000) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by simp [memShared, expSharedAfterFreePtr_lookup 0])
  simp [FormalYul.word, memShared, encStore, memPos, baseStore] at hencode
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,
    expSharedAfterFreePtr_weiValue, expSharedAfterFreePtr_calldata, expRayToWad_calldata_size,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    EvmYul.Yul.State.toMachineState, FormalYul.returnOf,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    hdecode, hwrap, halloc, hencode, baseStore, memPos, memShared, encStore]
  have hmload :
      ((expSharedAfterFreePtr 0).mload (EvmYul.UInt256.ofNat 64)).1 =
        EvmYul.UInt256.ofNat 128 := by
    simpa [FormalYul.word] using expSharedAfterFreePtr_mload64 0
  rw [hmload]
  have hretLen :
      EvmYul.UInt256.ofNat 128 + EvmYul.UInt256.ofNat 32 - EvmYul.UInt256.ofNat 128 =
        FormalYul.word 32 := by decide
  rw [hretLen]
  rw [FormalYul.Preservation.resultWord_evmReturn_mstore_word]
  have hnat :
      (EvmYul.UInt256.ofNat 1000000000000000000).toNat = 1000000000000000000 := by
    change FormalYul.wordNat (EvmYul.UInt256.ofNat 1000000000000000000) = 1000000000000000000
    exact (FormalYul.Preservation.wordNat_ofNat 1000000000000000000).trans
      (FormalYul.Preservation.u256_eq_of_lt _ (by decide))
  rw [hnat]

set_option maxHeartbeats 12000000 in
/-- The external entrypoint at `x = 0` halts (returns), as opposed to reverting. -/
theorem external_fun_wrap_expRayToWad_zero_calldata_halts
    (store : EvmYul.Yul.VarStore) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_expRayToWad) (.some yulContract)
        (EvmYul.Yul.State.Ok (expSharedAfterFreePtr 0) store) =
        .error (.YulHalt state value) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [expSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_expRayToWad]
  simp only [yulFunction_external_fun_wrap_expRayToWad, yulFunction_external_fun_wrap_expRayToWad_99,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word 1000000000000000000)
      (Finmap.insert "param_0" (FormalYul.word 0) (Inhabited.default : EvmYul.Yul.VarStore))
  let memPos :=
    ((EvmYul.Yul.State.Ok (expSharedAfterFreePtr 0) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { expSharedAfterFreePtr 0 with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (expSharedAfterFreePtr 0) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_int256_of_calldata (x := 0) (fuel := 0) (extra := 999664)
      (shared := expSharedAfterFreePtr 0)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := expSharedAfterFreePtr_lookup 0)
      (hdata := expSharedAfterFreePtr_calldata 0)
  simp only [Nat.reduceAdd, FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_expRayToWad_zero_direct (fuel := 0) (extra := 998883)
      (shared := expSharedAfterFreePtr 0)
      (store := Finmap.insert "param_0" (FormalYul.word 0)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := expSharedAfterFreePtr_lookup 0)
  simp only [Nat.reduceAdd, FormalYul.word] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := expSharedAfterFreePtr 0)
      (store := baseStore) (hlookup := expSharedAfterFreePtr_lookup 0)
  simp only [FormalYul.word, baseStore] at halloc
  have hencode :=
    call_abi_encode_tuple_t_int256__to_t_int256__fromStack_direct
      (headStart := memPos) (v := 1000000000000000000) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by simp [memShared, expSharedAfterFreePtr_lookup 0])
  simp [FormalYul.word, memShared, encStore, memPos, baseStore] at hencode
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,
    expSharedAfterFreePtr_weiValue, expSharedAfterFreePtr_calldata, expRayToWad_calldata_size,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    EvmYul.Yul.State.toMachineState, FormalYul.returnOf,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    hdecode, hwrap, halloc, hencode, baseStore, memPos, memShared, encStore]

set_option maxHeartbeats 12000000 in
/-- Result, starting from the exact state the dispatcher hands the external function. -/
theorem external_fun_wrap_expRayToWad_zero_dispatcher_state_result :
    ((match
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_expRayToWad) (.some yulContract)
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_expRayToWad ++ FormalYul.encodeWords [0])).toState
            ((FormalYul.sharedFor yulContract
              (selector_expRayToWad ++ FormalYul.encodeWords [0])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
          (Finmap.insert "selector"
            (EvmYul.UInt256.shiftRight
              (EvmYul.State.calldataload
                (EvmYul.Yul.State.Ok
                  (EvmYul.SharedState.mk
                    (FormalYul.sharedFor yulContract
                      (selector_expRayToWad ++ FormalYul.encodeWords [0])).toState
                    ((FormalYul.sharedFor yulContract
                      (selector_expRayToWad ++ FormalYul.encodeWords [0])).mstore
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
      .ok 1000000000000000000 := by
  rw [sharedFor_inherited_mstore_mk_eq_expSharedAfterFreePtr_raw]
  exact external_fun_wrap_expRayToWad_zero_calldata_result
    (store := Finmap.insert "selector"
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok (expSharedAfterFreePtr 0)
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224))
      (Inhabited.default : EvmYul.Yul.VarStore))

set_option maxHeartbeats 12000000 in
/-- Halt, starting from the exact state the dispatcher hands the external function. -/
theorem external_fun_wrap_expRayToWad_zero_dispatcher_state_halts :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_expRayToWad) (.some yulContract)
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_expRayToWad ++ FormalYul.encodeWords [0])).toState
            ((FormalYul.sharedFor yulContract
              (selector_expRayToWad ++ FormalYul.encodeWords [0])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
          (Finmap.insert "selector"
            (EvmYul.UInt256.shiftRight
              (EvmYul.State.calldataload
                (EvmYul.Yul.State.Ok
                  (EvmYul.SharedState.mk
                    (FormalYul.sharedFor yulContract
                      (selector_expRayToWad ++ FormalYul.encodeWords [0])).toState
                    ((FormalYul.sharedFor yulContract
                      (selector_expRayToWad ++ FormalYul.encodeWords [0])).mstore
                        (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
                  (Inhabited.default : EvmYul.Yul.VarStore)).toState
                (EvmYul.UInt256.ofNat 0))
              (EvmYul.UInt256.ofNat 224))
            (Inhabited.default : EvmYul.Yul.VarStore))) =
        .error (.YulHalt state value) := by
  rw [sharedFor_inherited_mstore_mk_eq_expSharedAfterFreePtr_raw]
  exact external_fun_wrap_expRayToWad_zero_calldata_halts
    (store := Finmap.insert "selector"
        (EvmYul.UInt256.shiftRight
          (EvmYul.State.calldataload
            (EvmYul.Yul.State.Ok (expSharedAfterFreePtr 0)
              (Inhabited.default : EvmYul.Yul.VarStore)).toState
            (EvmYul.UInt256.ofNat 0))
          (EvmYul.UInt256.ofNat 224))
        (Inhabited.default : EvmYul.Yul.VarStore))

set_option maxHeartbeats 12000000 in
/-- **Zero-input exactness.** `expRayToWad(0)` returns the wad unit `10^18`: the EVM run of the `ExpWrapper`
on input `0` yields `.ok 10^18`. -/
theorem run_exp_ray_to_wad_evm_zero :
    run_exp_ray_to_wad_evm 0 = .ok 1000000000000000000 := by
  obtain ⟨haltState, _haltValue, hhalt⟩ :=
    external_fun_wrap_expRayToWad_zero_dispatcher_state_halts
  have hresult := external_fun_wrap_expRayToWad_zero_dispatcher_state_result
  rw [hhalt] at hresult
  have hReturn :
      FormalYul.Preservation.DispatcherReturn yulContract
        (FormalYul.calldata selector_expRayToWad [0]) 999998 (FormalYul.returnOf haltState) := by
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
    rw [selectSwitchCase_expRayToWad_sharedFor_mk_raw 0]
    simp +decide [hhalt, EvmYul.Yul.exec.eq_def,
      EvmYul.Yul.execCall.eq_def,
      EvmYul.Yul.reverse', EvmYul.Yul.multifill']
  unfold run_exp_ray_to_wad_evm
  exact FormalYul.Preservation.callWord_ok_of_dispatcherReturn_result_1000000
    (contract := yulContract) (selector := selector_expRayToWad) (args := [0])
    (hReturn := hReturn) (by simpa using hresult)

end ExpYul
