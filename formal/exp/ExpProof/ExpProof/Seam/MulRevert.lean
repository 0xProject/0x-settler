import ExpProof.ExpYulProof
import Common.Word
import ExpProof.Seam.Helpers
import ExpProof.Seam.Dispatcher
import ExpProof.Seam.Revert
import ExpProof.Mono.MulTree
import FormalYul.Preservation

/-!
# Revert reduction for the `mulExpRay` guard

When the guard word is one, `fun_mulExpRay` takes the panic branch and reverts via
`fun_panic(ARITHMETIC_OVERFLOW)`. The prefix of the trace (headroom, octave, shift, and the
guard atoms) is shared with the value path; only the branch outcome differs.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word

set_option maxRecDepth 100000

set_option maxHeartbeats 12000000 in
/-- `fun_mulExpRay(y, x)` reverts when the guard word is one. -/
theorem call_fun_mulExpRay_revert_direct
    (y x fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hclean : EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word y) =
      FormalYul.word y)
    (hguard : mulExpGuardTree y x = 1) :
    EvmYul.Yul.call (fuel + (extra + 2200)) [FormalYul.word y, FormalYul.word x]
      (.some yulName_fun_mulExpRay) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .error EvmYul.Yul.Exception.Revert := by
  rw [show fuel + (extra + 2200) = (fuel + extra) + 2200 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_mulExpRay]
  simp only [yulFunctionBody_fun_mulExpRay,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp only [FormalYul.word] at hclean
  let sign := signTree y
  let ay := absTree y
  let s := scaleShiftTree ay
  let k := kTree x
  let shift := evmSub s k
  have hconvertY1 :=
    call_convert_int128_to_int256_direct (v := y) (fuel := fuel + extra) (extra := 2072)
      (shared := shared) (hlookup := hlookup) (hclean := hclean)
  have hconvert255 :=
    call_convert_255_to_uint8_direct (fuel := fuel + extra) (extra := 2070)
      (shared := shared) (hlookup := hlookup)
  have hshiftSign :=
    call_shift_right_t_int256_t_uint8_255_direct (value := y)
      (fuel := fuel + extra) (extra := 2009) (shared := shared) (hlookup := hlookup)
  have hsignAsUint :=
    call_convert_int256_to_uint256_direct (v := evmSar 255 y)
      (fuel := fuel + extra) (extra := 2068) (shared := shared) (hlookup := hlookup)
  have hconvertY2 :=
    call_convert_int128_to_int256_direct (v := y) (fuel := fuel + extra) (extra := 2064)
      (shared := shared) (hlookup := hlookup) (hclean := hclean)
  have hayAsUint :=
    call_convert_int256_to_uint256_direct (v := y) (fuel := fuel + extra) (extra := 2063)
      (shared := shared) (hlookup := hlookup)
  have hwrapAy :=
    call_wrapping_sub_t_uint256_direct (x := evmXor y (evmSar 255 y)) (y := evmSar 255 y)
      (fuel := fuel + extra) (extra := 2096) (shared := shared) (hlookup := hlookup)
  have hzeroInit :=
    call_zero_value_for_split_t_int128_direct (fuel := fuel + extra) (extra := 2176)
      (shared := shared) (hlookup := hlookup)
  have hclz :=
    call_fun_clz_direct (x := ay) (fuel := fuel + extra) (extra := 2091)
      (shared := shared) (hlookup := hlookup)
  have hscaleClzBias :=
    call_convert_129_to_uint256_direct (fuel := fuel + extra) (extra := 2047)
      (shared := shared) (hlookup := hlookup)
  have hwrapS :=
    call_wrapping_sub_t_uint256_direct (x := evmClz ay) (y := scaleClzBias)
      (fuel := fuel + extra) (extra := 2089) (shared := shared) (hlookup := hlookup)
  have hconvert127 :=
    call_convert_127_to_uint8_direct (fuel := fuel + extra) (extra := 2045)
      (shared := shared) (hlookup := hlookup)
  have hshrAy :=
    call_shift_right_t_uint256_t_uint8_127_direct (value := ay)
      (fuel := fuel + extra) (extra := 1984) (shared := shared) (hlookup := hlookup)
  have hwrapAdd :=
    call_wrapping_add_t_uint256_direct
      (x := evmSub (evmClz ay) scaleClzBias) (y := evmShr 127 ay)
      (fuel := fuel + extra) (extra := 2082) (shared := shared) (hlookup := hlookup)
  have hoctave :=
    call_fun__octave_direct (x := x) (fuel := fuel + extra) (extra := 2038)
      (shared := shared) (hlookup := hlookup)
  have hconvertS :=
    call_convert_uint256_to_int256_direct (v := s) (fuel := fuel + extra) (extra := 2034)
      (shared := shared) (hlookup := hlookup)
  have hwrapShift :=
    call_wrapping_sub_t_int256_direct (x := s) (y := k) (fuel := fuel + extra) (extra := 2071)
      (shared := shared) (hlookup := hlookup)
  have hHi :=
    call_convert_MUL_EXP_RAY_HI_MINUS_ONE_to_int256_direct
      (fuel := fuel + extra) (extra := 2024)
      (shared := shared) (hlookup := hlookup)
  have hcleanupXForHi :=
    call_cleanup_t_int256_direct (v := x) (fuel := fuel + extra) (extra := 2122)
      (shared := shared) (hlookup := hlookup)
  have hconvertTwo :=
    call_convert_2_to_int256_direct (fuel := fuel + extra) (extra := 2018)
      (shared := shared) (hlookup := hlookup)
  have hcleanupShift :=
    call_cleanup_t_int256_direct (v := shift) (fuel := fuel + extra) (extra := 2116)
      (shared := shared) (hlookup := hlookup)
  have hOrGuard :=
    call_fun_or_direct
      (a := evmSgt x 86989971160273136331862631243)
      (b := evmSlt shift 2)
      (fuel := fuel + extra) (extra := 2059) (shared := shared) (hlookup := hlookup)
  have hoverflow :=
    call_constant_ARITHMETIC_OVERFLOW_direct (fuel := fuel + extra) (extra := 1974)
      (shared := shared) (hlookup := hlookup)
  have hconvu :=
    call_convert_uint8_to_uint256_17_direct (fuel := fuel + extra) (extra := 2013)
      (shared := shared) (hlookup := hlookup)
  have hpanic :=
    call_fun_panic_revert_direct (code := 0x11) (fuel := fuel + extra) (extra := 1532)
      (shared := shared) (hlookup := hlookup)
  simp only [Nat.reduceAdd, FormalYul.word] at hconvertY1 hconvert255 hshiftSign hsignAsUint hconvertY2 hayAsUint hwrapAy hzeroInit
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun_clz, ay, absTree, signTree] at hclz
  simp only [Nat.reduceAdd, FormalYul.word] at hscaleClzBias
  simp only [Nat.reduceAdd, FormalYul.word, ay, absTree, signTree, scaleClzBias] at hwrapS
  simp only [Nat.reduceAdd, FormalYul.word] at hconvert127
  simp only [Nat.reduceAdd, FormalYul.word, ay, absTree, signTree] at hshrAy
  simp only [Nat.reduceAdd, FormalYul.word, ay, absTree, signTree, scaleClzBias] at hwrapAdd
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun__octave] at hoctave
  simp only [Nat.reduceAdd, FormalYul.word, s, ay, absTree, signTree, scaleShiftTree,
    scaleClzBias] at hconvertS
  simp only [Nat.reduceAdd, FormalYul.word, k, kTree, s, ay, absTree, signTree,
    scaleShiftTree, scaleClzBias]
    at hwrapShift
  simp only [Nat.reduceAdd, FormalYul.word] at hHi
  simp only [Nat.reduceAdd, FormalYul.word] at hcleanupXForHi
  simp only [Nat.reduceAdd, FormalYul.word] at hconvertTwo
  simp only [Nat.reduceAdd, FormalYul.word, shift, k, kTree, s, ay, absTree, signTree,
    scaleShiftTree, scaleClzBias] at hcleanupShift
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun_or, k, kTree, shift, s, ay, absTree,
    signTree, scaleShiftTree, scaleClzBias] at hOrGuard
  simp only [Nat.reduceAdd, FormalYul.word, yulName_constant_ARITHMETIC_OVERFLOW] at hoverflow
  simp only [Nat.reduceAdd, FormalYul.word] at hconvu
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun_panic] at hpanic
  have hhiMinusOne : evmSub mulExpRayHi 1 = 86989971160273136331862631243 := by
    norm_num [evmSub, mulExpRayHi, u256, WORD_MOD]
  have hguardUnfold :
      evmOr
        (evmSgt x 86989971160273136331862631243)
        (evmSlt
          (evmSub
            (evmAdd
              (evmSub (evmClz (evmSub (evmXor y (evmSar 255 y)) (evmSar 255 y))) 129)
              (evmShr 127 (evmSub (evmXor y (evmSar 255 y)) (evmSar 255 y))))
            (evmSar kRoundShift (evmAdd (evmShl kHalfShift 1) (evmMul cInvQ192 x))))
          2) = 1 := by
    simpa [mulExpGuardTree, mulShiftTree, scaleShiftTree, absTree, signTree, kTree,
      scaleClzBias, hhiMinusOne] using hguard
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.setStore,
    FormalYul.word,
    hconvertY1, hconvert255, hshiftSign, hsignAsUint, hconvertY2, hayAsUint, hwrapAy,
    hguardUnfold,
    hzeroInit, hclz, hscaleClzBias, hwrapS,
    hconvert127, hshrAy, hwrapAdd, hoctave, hconvertS, hwrapShift,
    hHi, hcleanupXForHi,
    hconvertTwo, hcleanupShift, hOrGuard,
    hoverflow, hconvu, hpanic,
    Common.Word.uint256_ofNat_xor_eq_word_evmXor,
    uint256_ofNat_slt_eq_word_evmSlt,
    uint256_ofNat_sgt_eq_word_evmSgt]

set_option maxHeartbeats 12000000 in
/-- `fun_wrap_mulExpRay` forwards the revert. -/
theorem call_fun_wrap_mulExpRay_revert_direct
    (y x fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hclean : EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word y) =
      FormalYul.word y)
    (hguard : mulExpGuardTree y x = 1) :
    EvmYul.Yul.call (fuel + (extra + 2300)) [FormalYul.word y, FormalYul.word x]
      (.some yulName_fun_wrap_mulExpRay) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .error EvmYul.Yul.Exception.Revert := by
  rw [show fuel + (extra + 2300) = (fuel + extra) + 2300 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_wrap_mulExpRay]
  simp only [yulFunctionBody_fun_wrap_mulExpRay,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hinner :=
    call_fun_mulExpRay_revert_direct (y := y) (x := x) (fuel := fuel + extra) (extra := 89)
      (shared := shared) (hlookup := hlookup) (hclean := hclean) (hguard := hguard)
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun_mulExpRay] at hinner
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.setStore,
    FormalYul.word,
    call_zero_value_for_split_t_int128_direct (fuel := fuel + extra) (extra := 2276)
      (shared := shared) (hlookup := hlookup),
    hinner]

set_option maxHeartbeats 12000000 in
/-- The external `mulExpRay` entrypoint forwards the revert. -/
theorem external_fun_wrap_mulExpRay_calldata_revert
    (y x : Nat) (store : EvmYul.Yul.VarStore)
    (hclean : EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word y) =
      FormalYul.word y)
    (hguard : mulExpGuardTree y x = 1) :
    EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_mulExpRay) (.some yulContract)
        (EvmYul.Yul.State.Ok (mulExpSharedAfterFreePtr y x) store) =
      .error EvmYul.Yul.Exception.Revert := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [mulExpSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_mulExpRay]
  simp only [yulFunctionBody_external_fun_wrap_mulExpRay,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hdecode :=
    call_abi_decode_tuple_t_int128t_int256_of_mul_calldata (y := y) (x := x)
      (fuel := 0) (extra := 999464)
      (shared := mulExpSharedAfterFreePtr y x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := mulExpSharedAfterFreePtr_lookup y x)
      (hdata := mulExpSharedAfterFreePtr_calldata y x) (hclean := hclean)
  simp only [Nat.reduceAdd, FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_mulExpRay_revert_direct (y := y) (x := x) (fuel := 0) (extra := 997683)
      (shared := mulExpSharedAfterFreePtr y x)
      (store := Finmap.insert "param_0" (FormalYul.word y)
        (Finmap.insert "param_1" (FormalYul.word x)
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := mulExpSharedAfterFreePtr_lookup y x) (hclean := hclean) (hguard := hguard)
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun_wrap_mulExpRay] at hwrap
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,
    mulExpSharedAfterFreePtr_weiValue, mulExpSharedAfterFreePtr_calldata, mulExpRay_calldata_size,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    Finmap.lookup_insert,
    hdecode, hwrap]

set_option maxHeartbeats 12000000 in
/-- The revert from the exact dispatcher-handed state. -/
theorem external_fun_wrap_mulExpRay_dispatcher_state_revert
    (y x : Nat)
    (hclean : EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word y) =
      FormalYul.word y)
    (hguard : mulExpGuardTree y x = 1) :
    EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_mulExpRay) (.some yulContract)
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_mulExpRay ++ FormalYul.encodeWords [y, x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_mulExpRay ++ FormalYul.encodeWords [y, x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
          (Finmap.insert "selector"
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
            (Inhabited.default : EvmYul.Yul.VarStore))) =
        .error EvmYul.Yul.Exception.Revert := by
  rw [sharedFor_inherited_mstore_mk_eq_mulExpSharedAfterFreePtr_raw]
  exact external_fun_wrap_mulExpRay_calldata_revert y x
    (store := Finmap.insert "selector"
        (EvmYul.UInt256.shiftRight
          (EvmYul.State.calldataload
            (EvmYul.Yul.State.Ok (mulExpSharedAfterFreePtr y x)
              (Inhabited.default : EvmYul.Yul.VarStore)).toState
            (EvmYul.UInt256.ofNat 0))
          (EvmYul.UInt256.ofNat 224))
        (Inhabited.default : EvmYul.Yul.VarStore))
    hclean hguard

set_option maxHeartbeats 12000000 in
/-- **Guard revert.** When the guard word is one, the compiled runtime reverts. -/
theorem run_mul_exp_ray_evm_revert_of_guard (y x : Nat)
    (hclean : EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word y) =
      FormalYul.word y)
    (hguard : mulExpGuardTree y x = 1) :
    run_mul_exp_ray_evm y x = .error "revert" := by
  have hexec :
      EvmYul.Yul.exec 999998 yulContract.dispatcher (.some yulContract)
        (stateFor yulContract (FormalYul.calldata selector_mulExpRay [y, x])) =
        .error EvmYul.Yul.Exception.Revert := by
    rw [yulContract_dispatcher]
    simp +decide [FormalYul.calldata, stateFor, yulDispatcher,
      EvmYul.Yul.execCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
      EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
      EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
      EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.toMachineState,
      FormalYul.word, call_shift_right_224_unsigned_direct]
    rw [selectSwitchCase_mulExpRay_sharedFor_mk_raw y x]
    simp +decide [external_fun_wrap_mulExpRay_dispatcher_state_revert y x hclean hguard,
      EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def,
      EvmYul.Yul.reverse', EvmYul.Yul.multifill']
  have hrun :
      runContract yulContract (FormalYul.calldata selector_mulExpRay [y, x]) 1000000 =
        .error "revert" :=
    runContract_revert_of_exec_revert hexec
  unfold run_mul_exp_ray_evm FormalYul.callWord FormalYul.call
  rw [hrun]
  rfl

end ExpYul
