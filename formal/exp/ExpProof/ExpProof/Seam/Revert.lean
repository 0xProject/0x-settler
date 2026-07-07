import ExpProof.ExpYulProof
import Common.Word
import ExpProof.Seam.Guard
import ExpProof.Seam.Helpers
import ExpProof.Seam.Dispatcher
import FormalYul.Preservation

/-!
# Revert reduction for the overflow guard

`fun_expRayToWad_68` takes the overflow-guard branch for inputs at/above the threshold and calls
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
  simp +decide [
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.setStore,
    FormalYul.word, primCall_revert_yul]

set_option maxHeartbeats 8000000 in
/-- For inputs at/above the overflow threshold, `fun_expRayToWad_68` takes the guard branch and
reverts via `fun_panic_8(ARITHMETIC_OVERFLOW)`. -/
theorem call_fun_expRayToWad_68_revert_direct
    (x fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (h1 : (0x92b2f16cc66c5a4ae96e80d4 : Nat) ≤ FormalYul.u256 x)
    (h2 : FormalYul.u256 x < 2 ^ 255) :
    EvmYul.Yul.call (fuel + (extra + 1000)) [FormalYul.word x] (.some "fun_expRayToWad_68")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .error EvmYul.Yul.Exception.Revert := by
  rw [show fuel + (extra + 1000) = (fuel + extra) + 1000 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_expRayToWad_68]
  simp only [yulFunction_fun_expRayToWad_68,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hconv44 :=
    call_convert_44_to_int256_direct (v := 0x92b2f16cc66c5a4ae96e80d4) (fuel := fuel + extra) (extra := 867)
      (shared := shared) (hlookup := hlookup)
  have hcleanup :=
    call_cleanup_t_int256_direct (v := x) (fuel := fuel + extra) (extra := 965)
      (shared := shared) (hlookup := hlookup)
  have hconvu :=
    call_convert_uint8_to_uint256_17_direct (fuel := fuel + extra) (extra := 865)
      (shared := shared) (hlookup := hlookup)
  have hpanic :=
    call_fun_panic_8_revert_direct (code := 0x11) (fuel := fuel + extra) (extra := 384)
      (shared := shared) (hlookup := hlookup)
  simp only [Nat.reduceAdd, FormalYul.word] at hconv44 hcleanup hconvu hpanic
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.setStore,
    FormalYul.word,
    slt_thresh_ge h1 h2,
    call_zero_value_for_split_t_int256_direct (fuel := fuel + extra) (extra := 976)
      (shared := shared) (hlookup := hlookup),
    call_constant_ARITHMETIC_OVERFLOW_17_direct (fuel := fuel + extra) (extra := 826)
      (shared := shared) (hlookup := hlookup),
    hcleanup, hconv44, hconvu, hpanic]

set_option maxHeartbeats 8000000 in
/-- The thin wrapper `fun_wrap_expRayToWad_97` just forwards to `fun_expRayToWad_68`, so it reverts
on the same out-of-range inputs. -/
theorem call_fun_wrap_expRayToWad_revert_direct
    (x fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (h1 : (0x92b2f16cc66c5a4ae96e80d4 : Nat) ≤ FormalYul.u256 x)
    (h2 : FormalYul.u256 x < 2 ^ 255) :
    EvmYul.Yul.call (fuel + (extra + 1200)) [FormalYul.word x] (.some "fun_wrap_expRayToWad_97")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .error EvmYul.Yul.Exception.Revert := by
  rw [show fuel + (extra + 1200) = (fuel + extra) + 1200 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_wrap_expRayToWad]
  simp only [yulFunction_fun_wrap_expRayToWad, yulFunction_fun_wrap_expRayToWad_97,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have h70 :=
    call_fun_expRayToWad_68_revert_direct (x := x) (fuel := fuel + extra) (extra := 191)
      (shared := shared) (h1 := h1) (h2 := h2) (hlookup := hlookup)
  simp only [Nat.reduceAdd, FormalYul.word] at h70
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.setStore,
    FormalYul.word,
    call_zero_value_for_split_t_int256_direct (fuel := fuel + extra) (extra := 1176)
      (shared := shared) (hlookup := hlookup),
    h70]

set_option maxHeartbeats 8000000 in
/-- The external entrypoint `external_fun_wrap_expRayToWad_97` decodes the calldata argument `x`
(`callvalue` is 0, so the value guard is skipped) and forwards to `fun_wrap_expRayToWad_97`, which
reverts for out-of-range `x`. -/
theorem external_fun_wrap_expRayToWad_calldata_revert
    (x : Nat) (store : EvmYul.Yul.VarStore)
    (h1 : (0x92b2f16cc66c5a4ae96e80d4 : Nat) ≤ FormalYul.u256 x)
    (h2 : FormalYul.u256 x < 2 ^ 255) :
    EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_expRayToWad) (.some yulContract)
        (EvmYul.Yul.State.Ok (expSharedAfterFreePtr x) store) =
      .error EvmYul.Yul.Exception.Revert := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [expSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_expRayToWad]
  simp only [yulFunction_external_fun_wrap_expRayToWad, yulFunction_external_fun_wrap_expRayToWad_97,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hdecode :=
    call_abi_decode_tuple_t_int256_of_calldata (x := x) (fuel := 0) (extra := 999664)
      (shared := expSharedAfterFreePtr x)
      (hlookup := expSharedAfterFreePtr_lookup x)
      (hdata := expSharedAfterFreePtr_calldata x)
  simp only [Nat.reduceAdd, FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_expRayToWad_revert_direct (x := x) (fuel := 0) (extra := 998783)
      (shared := expSharedAfterFreePtr x)
      (hlookup := expSharedAfterFreePtr_lookup x) (h1 := h1) (h2 := h2)
  simp only [Nat.reduceAdd, FormalYul.word] at hwrap
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,
    expSharedAfterFreePtr_weiValue, expSharedAfterFreePtr_calldata, expRayToWad_calldata_size,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    Finmap.lookup_insert,
    hdecode, hwrap]

set_option maxHeartbeats 8000000 in
/-- The same revert, but starting from the exact state the dispatcher hands the external function
(free-pointer `mstore` baked into a `SharedState.mk`, with the extracted `selector` in the store). -/
theorem external_fun_wrap_expRayToWad_dispatcher_state_revert
    (x : Nat)
    (h1 : (0x92b2f16cc66c5a4ae96e80d4 : Nat) ≤ FormalYul.u256 x)
    (h2 : FormalYul.u256 x < 2 ^ 255) :
    EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_expRayToWad) (.some yulContract)
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_expRayToWad ++ FormalYul.encodeWords [x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_expRayToWad ++ FormalYul.encodeWords [x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
          (Finmap.insert "selector"
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
            (Inhabited.default : EvmYul.Yul.VarStore))) =
        .error EvmYul.Yul.Exception.Revert := by
  rw [sharedFor_inherited_mstore_mk_eq_expSharedAfterFreePtr_raw]
  exact external_fun_wrap_expRayToWad_calldata_revert (x := x)
    (store := Finmap.insert "selector"
        (EvmYul.UInt256.shiftRight
          (EvmYul.State.calldataload
            (EvmYul.Yul.State.Ok (expSharedAfterFreePtr x)
              (Inhabited.default : EvmYul.Yul.VarStore)).toState
            (EvmYul.UInt256.ofNat 0))
          (EvmYul.UInt256.ofNat 224))
        (Inhabited.default : EvmYul.Yul.VarStore)) h1 h2

set_option maxHeartbeats 8000000 in
/-- **Supported-range revert.** For any input at or above the supported-range threshold (and below `2^255`),
`expRayToWad` reverts: the EVM run of the `ExpWrapper` returns `.error "revert"`. -/
theorem run_exp_ray_to_wad_evm_revert
    (x : Nat)
    (h1 : (0x92b2f16cc66c5a4ae96e80d4 : Nat) ≤ FormalYul.u256 x)
    (h2 : FormalYul.u256 x < 2 ^ 255) :
    run_exp_ray_to_wad_evm x = .error "revert" := by
  have hexec :
      EvmYul.Yul.exec 999998 yulContract.dispatcher (.some yulContract)
        (stateFor yulContract (FormalYul.calldata selector_expRayToWad [x])) =
        .error EvmYul.Yul.Exception.Revert := by
    rw [yulContract_dispatcher]
    simp +decide [FormalYul.calldata, stateFor, yulDispatcher,
      EvmYul.Yul.execCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
      EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
      EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
      EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.toMachineState,
      FormalYul.word, call_shift_right_224_unsigned_direct]
    rw [selectSwitchCase_expRayToWad_sharedFor_mk_raw x]
    simp +decide [external_fun_wrap_expRayToWad_dispatcher_state_revert x h1 h2,
      EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def,
      EvmYul.Yul.reverse', EvmYul.Yul.multifill']
  have hrun :
      runContract yulContract (FormalYul.calldata selector_expRayToWad [x]) 1000000 =
        .error "revert" :=
    runContract_revert_of_exec_revert hexec
  unfold run_exp_ray_to_wad_evm FormalYul.callWord FormalYul.call
  rw [hrun]
  rfl

end ExpYul
