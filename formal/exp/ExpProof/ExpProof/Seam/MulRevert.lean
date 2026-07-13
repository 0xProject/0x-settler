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
  let s := evmSub (evmClz ay) scaleMaxClz
  let k := kTree x
  let shift := evmSub s k
  have hzeroInit :=
    call_zero_value_for_split_t_int128_direct (fuel := fuel + extra) (extra := 2176)
      (shared := shared) (hlookup := hlookup)
  have hzeroUint1 :=
    call_zero_value_for_split_t_uint256_direct (fuel := fuel + extra) (extra := 2173)
      (shared := shared) (hlookup := hlookup)
  have hzeroUint2 :=
    call_zero_value_for_split_t_uint256_direct (fuel := fuel + extra) (extra := 2170)
      (shared := shared) (hlookup := hlookup)
  have hclz :=
    call_fun_clz_direct (x := ay) (fuel := fuel + extra) (extra := 2104)
      (shared := shared) (hlookup := hlookup)
  have hscaleMaxClz :=
    call_constant__SCALE_MAX_CLZ_direct (fuel := fuel + extra) (extra := 2023)
      (shared := shared) (hlookup := hlookup)
  have hwrapS :=
    call_wrapping_sub_t_uint256_direct (x := evmClz ay) (y := scaleMaxClz)
      (fuel := fuel + extra) (extra := 2102) (shared := shared) (hlookup := hlookup)
  have hoctave :=
    call_fun__octave_direct (x := x) (fuel := fuel + extra) (extra := 2058)
      (shared := shared) (hlookup := hlookup)
  have hconvertS :=
    call_convert_uint256_to_int256_direct (v := s) (fuel := fuel + extra) (extra := 2054)
      (shared := shared) (hlookup := hlookup)
  have hwrapShift :=
    call_wrapping_sub_t_int256_direct (x := s) (y := k) (fuel := fuel + extra) (extra := 2091)
      (shared := shared) (hlookup := hlookup)
  have hconvert127 :=
    call_convert_127_to_uint256_direct (fuel := fuel + extra) (extra := 2044)
      (shared := shared) (hlookup := hlookup)
  have hcleanupSGuard :=
    call_cleanup_t_uint256_direct (v := s) (fuel := fuel + extra) (extra := 2142)
      (shared := shared) (hlookup := hlookup)
  have hHi :=
    call_constant__MUL_EXP_RAY_HI_direct (fuel := fuel + extra) (extra := 2001)
      (shared := shared) (hlookup := hlookup)
  have hconvertOne :=
    call_convert_1_to_int256_direct (fuel := fuel + extra) (extra := 2037)
      (shared := shared) (hlookup := hlookup)
  have hsubHi :=
    call_wrapping_sub_t_int256_direct (x := mulExpRayHi) (y := 1)
      (fuel := fuel + extra) (extra := 2079) (shared := shared) (hlookup := hlookup)
  have hcleanupHiMinusOne :=
    call_cleanup_t_int256_direct (v := evmSub mulExpRayHi 1)
      (fuel := fuel + extra) (extra := 2136) (shared := shared) (hlookup := hlookup)
  have hcleanupXForHi :=
    call_cleanup_t_int256_direct (v := x) (fuel := fuel + extra) (extra := 2134)
      (shared := shared) (hlookup := hlookup)
  have hOrOut :=
    call_fun_or_direct (a := evmGt s 127) (b := evmSgt x (evmSub mulExpRayHi 1))
      (fuel := fuel + extra) (extra := 2077) (shared := shared) (hlookup := hlookup)
  have hconvertTwo :=
    call_convert_2_to_int256_direct (fuel := fuel + extra) (extra := 2030)
      (shared := shared) (hlookup := hlookup)
  have hcleanupShift :=
    call_cleanup_t_int256_direct (v := shift) (fuel := fuel + extra) (extra := 2128)
      (shared := shared) (hlookup := hlookup)
  have hOrGuard :=
    call_fun_or_direct
      (a := evmOr (evmGt s 127) (evmSgt x (evmSub mulExpRayHi 1)))
      (b := evmSlt shift 2)
      (fuel := fuel + extra) (extra := 2071) (shared := shared) (hlookup := hlookup)
  have hoverflow :=
    call_constant_ARITHMETIC_OVERFLOW_direct (fuel := fuel + extra) (extra := 1986)
      (shared := shared) (hlookup := hlookup)
  have hconvu :=
    call_convert_uint8_to_uint256_17_direct (fuel := fuel + extra) (extra := 2025)
      (shared := shared) (hlookup := hlookup)
  have hpanic :=
    call_fun_panic_revert_direct (code := 0x11) (fuel := fuel + extra) (extra := 1544)
      (shared := shared) (hlookup := hlookup)
  simp only [Nat.reduceAdd, FormalYul.word] at hzeroInit hzeroUint1 hzeroUint2
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun_clz, ay, absTree, signTree] at hclz
  simp only [Nat.reduceAdd, FormalYul.word, yulName_constant__SCALE_MAX_CLZ] at hscaleMaxClz
  simp only [Nat.reduceAdd, FormalYul.word, ay, absTree, signTree, scaleMaxClz] at hwrapS
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun__octave] at hoctave
  simp only [Nat.reduceAdd, FormalYul.word, s, ay, absTree, signTree, scaleMaxClz] at hconvertS
  simp only [Nat.reduceAdd, FormalYul.word, k, kTree, s, ay, absTree, signTree, scaleMaxClz]
    at hwrapShift
  simp only [Nat.reduceAdd, FormalYul.word] at hconvert127
  simp only [Nat.reduceAdd, FormalYul.word, s, ay, absTree, signTree, scaleMaxClz]
    at hcleanupSGuard
  simp only [Nat.reduceAdd, FormalYul.word, yulName_constant__MUL_EXP_RAY_HI,
    mulExpRayHi] at hHi
  simp only [Nat.reduceAdd, FormalYul.word] at hconvertOne
  simp only [Nat.reduceAdd, FormalYul.word, mulExpRayHi] at hsubHi hcleanupHiMinusOne
  simp only [Nat.reduceAdd, FormalYul.word] at hcleanupXForHi
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun_or, s, ay, absTree, signTree,
    scaleMaxClz, mulExpRayHi] at hOrOut
  simp only [Nat.reduceAdd, FormalYul.word] at hconvertTwo
  simp only [Nat.reduceAdd, FormalYul.word, shift, k, kTree, s, ay, absTree, signTree,
    scaleMaxClz] at hcleanupShift
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun_or, k, kTree, shift, s, ay, absTree,
    signTree, scaleMaxClz, mulExpRayHi] at hOrGuard
  simp only [Nat.reduceAdd, FormalYul.word, yulName_constant_ARITHMETIC_OVERFLOW] at hoverflow
  simp only [Nat.reduceAdd, FormalYul.word] at hconvu
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun_panic] at hpanic
  have hguardUnfold :
      evmOr
        (evmOr
          (evmGt
            (evmSub (evmClz (evmSub (evmXor y (evmSar 255 y)) (evmSar 255 y))) 129)
            127)
          (evmSgt x (evmSub 86989971160273136331862631244 1)))
          (evmSlt
            (evmSub
              (evmSub (evmClz (evmSub (evmXor y (evmSar 255 y)) (evmSar 255 y))) 129)
              (evmSar kRoundShift (evmAdd (evmShl kHalfShift 1) (evmMul cInvQ192 x))))
            2) = 1 := by
    simpa [mulExpGuardTree, mulShiftTree, scaleShiftTree, absTree, signTree, kTree,
      scaleMaxClz, mulExpRayHi] using hguard
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.setStore,
    FormalYul.word, primCall_signextend_yul,
    hguardUnfold,
    hzeroInit, hzeroUint1, hzeroUint2, hclz, hscaleMaxClz, hwrapS,
    hoctave, hconvertS, hwrapShift, hconvert127, hcleanupSGuard,
    hHi, hconvertOne, hsubHi, hcleanupHiMinusOne, hcleanupXForHi, hOrOut,
    hconvertTwo, hcleanupShift, hOrGuard,
    hoverflow, hconvu, hpanic,
    FormalYul.Preservation.uint256_ofNat_gt_eq_word_evmGt,
    FormalYul.Preservation.uint256_ofNat_sub_eq_word_evmSub,
    Common.Word.uint256_ofNat_xor_eq_word_evmXor,
    Common.Word.uint256_ofNat_sar_eq_word_evmSar,
    uint256_ofNat_slt_eq_word_evmSlt,
    uint256_ofNat_sgt_eq_word_evmSgt,
    scaleMaxClz, hclean]

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
