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
  let sign := signTree y
  let ay := absTree y
  let s0 := evmSub (evmClz ay) scaleMaxClz
  let s := evmSub s0 (evmGt (evmShl s0 ay) scaleQ67)
  let k := kTree x
  let shift := evmSub s k
  have hzeroInit :=
    call_zero_value_for_split_t_int256_direct (fuel := fuel + extra) (extra := 2176)
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
  have hwrapS0 :=
    call_wrapping_sub_t_uint256_direct (x := evmClz ay) (y := scaleMaxClz)
      (fuel := fuel + extra) (extra := 2102) (shared := shared) (hlookup := hlookup)
  have hscaleMax1 :=
    call_constant__SCALE_MAX_direct (fuel := fuel + extra) (extra := 2020)
      (shared := shared) (hlookup := hlookup)
  have hoctave :=
    call_fun__octave_direct (x := x) (fuel := fuel + extra) (extra := 2055)
      (shared := shared) (hlookup := hlookup)
  have hconvertS :=
    call_convert_uint256_to_int256_direct (v := s) (fuel := fuel + extra) (extra := 2051)
      (shared := shared) (hlookup := hlookup)
  have hwrapShift :=
    call_wrapping_sub_t_int256_direct (x := s) (y := k) (fuel := fuel + extra) (extra := 2088)
      (shared := shared) (hlookup := hlookup)
  have hscaleMax2 :=
    call_constant__SCALE_MAX_direct (fuel := fuel + extra) (extra := 2004)
      (shared := shared) (hlookup := hlookup)
  have hcleanupScaleMax :=
    call_cleanup_t_uint256_direct (v := scaleQ67) (fuel := fuel + extra) (extra := 2141)
      (shared := shared) (hlookup := hlookup)
  have hcleanupAyGuard :=
    call_cleanup_t_uint256_direct (v := ay) (fuel := fuel + extra) (extra := 2139)
      (shared := shared) (hlookup := hlookup)
  have hHi :=
    call_constant__MUL_EXP_RAY_HI_direct (fuel := fuel + extra) (extra := 1998)
      (shared := shared) (hlookup := hlookup)
  have hcleanupHi :=
    call_cleanup_t_int256_direct (v := mulExpRayHi) (fuel := fuel + extra) (extra := 2133)
      (shared := shared) (hlookup := hlookup)
  have hcleanupXForHi :=
    call_cleanup_t_int256_direct (v := x) (fuel := fuel + extra) (extra := 2131)
      (shared := shared) (hlookup := hlookup)
  have hOrOut :=
    call_fun_or_direct (a := evmGt ay scaleQ67) (b := evmIszero (evmSlt x mulExpRayHi))
      (fuel := fuel + extra) (extra := 2076) (shared := shared) (hlookup := hlookup)
  have hconvertZeroEq :=
    call_convert_0_to_int256_direct (fuel := fuel + extra) (extra := 2027)
      (shared := shared) (hlookup := hlookup)
  have hcleanupXEq :=
    call_cleanup_t_int256_direct (v := x) (fuel := fuel + extra) (extra := 2125)
      (shared := shared) (hlookup := hlookup)
  have hZM1 :=
    call_constant__MUL_EXP_RAY_ZERO_MAX_direct (fuel := fuel + extra) (extra := 1986)
      (shared := shared) (hlookup := hlookup)
  have hcleanupZM :=
    call_cleanup_t_int256_direct (v := mulExpRayZeroMax) (fuel := fuel + extra) (extra := 2123)
      (shared := shared) (hlookup := hlookup)
  have hcleanupXForLo :=
    call_cleanup_t_int256_direct (v := x) (fuel := fuel + extra) (extra := 2121)
      (shared := shared) (hlookup := hlookup)
  have hAndLo :=
    call_fun_and_direct (a := evmIszero (evmEq x 0)) (b := evmSgt x mulExpRayZeroMax)
      (fuel := fuel + extra) (extra := 2064) (shared := shared) (hlookup := hlookup)
  have hconvertTwo :=
    call_convert_2_to_int256_direct (fuel := fuel + extra) (extra := 2017)
      (shared := shared) (hlookup := hlookup)
  have hcleanupShift :=
    call_cleanup_t_int256_direct (v := shift) (fuel := fuel + extra) (extra := 2115)
      (shared := shared) (hlookup := hlookup)
  have hAndAccuracy :=
    call_fun_and_direct
      (a := evmAnd (evmIszero (evmEq x 0)) (evmSgt x mulExpRayZeroMax))
      (b := evmSlt shift 2) (fuel := fuel + extra) (extra := 2058)
      (shared := shared) (hlookup := hlookup)
  have hOrGuard :=
    call_fun_or_direct
      (a := evmOr (evmGt ay scaleQ67) (evmIszero (evmSlt x mulExpRayHi)))
      (b := evmAnd (evmAnd (evmIszero (evmEq x 0)) (evmSgt x mulExpRayZeroMax))
        (evmSlt shift 2))
      (fuel := fuel + extra) (extra := 2057) (shared := shared) (hlookup := hlookup)
  have hoverflow :=
    call_constant_ARITHMETIC_OVERFLOW_direct (fuel := fuel + extra) (extra := 1972)
      (shared := shared) (hlookup := hlookup)
  have hconvu :=
    call_convert_uint8_to_uint256_17_direct (fuel := fuel + extra) (extra := 2011)
      (shared := shared) (hlookup := hlookup)
  have hpanic :=
    call_fun_panic_revert_direct (code := 0x11) (fuel := fuel + extra) (extra := 1530)
      (shared := shared) (hlookup := hlookup)
  simp only [Nat.reduceAdd, FormalYul.word] at hzeroInit hzeroUint1 hzeroUint2
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun_clz, ay, absTree, signTree] at hclz
  simp only [Nat.reduceAdd, FormalYul.word, yulName_constant__SCALE_MAX_CLZ] at hscaleMaxClz
  simp only [Nat.reduceAdd, FormalYul.word, ay, absTree, signTree, scaleMaxClz] at hwrapS0
  simp only [Nat.reduceAdd, FormalYul.word] at hscaleMax1 hscaleMax2
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun__octave] at hoctave
  simp only [Nat.reduceAdd, FormalYul.word, s, s0, ay, absTree, signTree, scaleMaxClz,
    scaleQ67] at hconvertS
  simp only [Nat.reduceAdd, FormalYul.word, k, kTree, s, s0, ay, absTree, signTree, scaleMaxClz,
    scaleQ67] at hwrapShift
  simp only [Nat.reduceAdd, FormalYul.word, ay, absTree, signTree,
    scaleQ67] at hcleanupScaleMax hcleanupAyGuard
  simp only [Nat.reduceAdd, FormalYul.word, yulName_constant__MUL_EXP_RAY_HI,
    mulExpRayHi] at hHi
  simp only [Nat.reduceAdd, FormalYul.word, mulExpRayHi] at hcleanupHi
  simp only [Nat.reduceAdd, FormalYul.word] at hcleanupXForHi
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun_or, ay, absTree, signTree, scaleQ67,
    mulExpRayHi] at hOrOut
  simp only [Nat.reduceAdd, FormalYul.word] at hconvertZeroEq hcleanupXEq
  simp only [Nat.reduceAdd, FormalYul.word, yulName_constant__MUL_EXP_RAY_ZERO_MAX,
    mulExpRayZeroMax] at hZM1
  simp only [Nat.reduceAdd, FormalYul.word, mulExpRayZeroMax] at hcleanupZM
  simp only [Nat.reduceAdd, FormalYul.word] at hcleanupXForLo
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun_and,
    mulExpRayZeroMax] at hAndLo
  simp only [Nat.reduceAdd, FormalYul.word] at hconvertTwo
  simp only [Nat.reduceAdd, FormalYul.word, shift, k, kTree, s, s0, ay, absTree, signTree,
    scaleMaxClz, scaleQ67] at hcleanupShift
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun_and, k, kTree, shift, s, s0, ay, absTree,
    signTree, scaleMaxClz, scaleQ67, mulExpRayZeroMax] at hAndAccuracy
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun_or, k, kTree, shift, s, s0, ay, absTree,
    signTree, scaleMaxClz, scaleQ67, mulExpRayHi, mulExpRayZeroMax] at hOrGuard
  simp only [Nat.reduceAdd, FormalYul.word, yulName_constant_ARITHMETIC_OVERFLOW] at hoverflow
  simp only [Nat.reduceAdd, FormalYul.word] at hconvu
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun_panic] at hpanic
  have hguardUnfold :
      evmOr
        (evmOr
          (evmGt (evmSub (evmXor y (evmSar 255 y)) (evmSar 255 y))
            147573952589676412928000000000000000000)
          (evmIszero (evmSlt x 86989971160273136331862631244)))
        (evmAnd
          (evmAnd (evmIszero (evmEq x 0))
            (evmSgt x 115792089237316195423570985008687907853269984665552187773936190980962432544451))
          (evmSlt
            (evmSub
              (evmSub (evmSub (evmClz (evmSub (evmXor y (evmSar 255 y)) (evmSar 255 y))) 129)
                (evmGt
                  (evmShl (evmSub (evmClz (evmSub (evmXor y (evmSar 255 y)) (evmSar 255 y))) 129)
                    (evmSub (evmXor y (evmSar 255 y)) (evmSar 255 y)))
                  147573952589676412928000000000000000000))
              (evmSar kRoundShift (evmAdd (evmShl kHalfShift 1) (evmMul cInvQ192 x))))
            2)) = 1 := by
    simpa [mulExpGuardTree, mulShiftTree, scaleShiftTree, absTree, signTree, kTree, scaleQ67,
      scaleMaxClz, mulExpRayHi, mulExpRayZeroMax] using hguard
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    hguard, hguardUnfold,
    hzeroInit, hzeroUint1, hzeroUint2, hclz, hscaleMaxClz, hwrapS0,
    hscaleMax1, hoctave, hconvertS, hwrapShift, hscaleMax2, hcleanupScaleMax, hcleanupAyGuard,
    hHi, hcleanupHi, hcleanupXForHi, hOrOut, hconvertZeroEq, hcleanupXEq, hZM1, hcleanupZM,
    hcleanupXForLo, hAndLo, hconvertTwo, hcleanupShift, hAndAccuracy, hOrGuard,
    hoverflow, hconvu, hpanic,
    FormalYul.Preservation.uint256_ofNat_eq_eq_word_evmEq,
    FormalYul.Preservation.uint256_ofNat_gt_eq_word_evmGt,
    FormalYul.Preservation.uint256_ofNat_sub_eq_word_evmSub,
    FormalYul.Preservation.uint256_ofNat_shiftLeft_eq_word_evmShl,
    Common.Word.uint256_ofNat_xor_eq_word_evmXor,
    Common.Word.uint256_ofNat_sar_eq_word_evmSar,
    uint256_ofNat_slt_eq_word_evmSlt,
    uint256_ofNat_sgt_eq_word_evmSgt,
    uint256_ofNat_iszero_eq_word_evmIszero,
    mulExpGuardTree, mulShiftTree, kTree, scaleShiftTree, absTree, signTree,
    scaleQ67, scaleMaxClz, mulExpRayHi, mulExpRayZeroMax,
    sign, ay, s0, s, k, shift]

set_option maxHeartbeats 12000000 in
/-- `fun_wrap_mulExpRay` forwards the revert. -/
theorem call_fun_wrap_mulExpRay_revert_direct
    (y x fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
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
      (shared := shared) (hlookup := hlookup) (hguard := hguard)
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun_mulExpRay] at hinner
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.setStore,
    FormalYul.word,
    call_zero_value_for_split_t_int256_direct (fuel := fuel + extra) (extra := 2276)
      (shared := shared) (hlookup := hlookup),
    hinner]

set_option maxHeartbeats 12000000 in
/-- The external `mulExpRay` entrypoint forwards the revert. -/
theorem external_fun_wrap_mulExpRay_calldata_revert
    (y x : Nat) (store : EvmYul.Yul.VarStore)
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
    call_abi_decode_tuple_t_int256t_int256_of_mul_calldata (y := y) (x := x)
      (fuel := 0) (extra := 999464)
      (shared := mulExpSharedAfterFreePtr y x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := mulExpSharedAfterFreePtr_lookup y x)
      (hdata := mulExpSharedAfterFreePtr_calldata y x)
  simp only [Nat.reduceAdd, FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_mulExpRay_revert_direct (y := y) (x := x) (fuel := 0) (extra := 997683)
      (shared := mulExpSharedAfterFreePtr y x)
      (store := Finmap.insert "param_0" (FormalYul.word y)
        (Finmap.insert "param_1" (FormalYul.word x)
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := mulExpSharedAfterFreePtr_lookup y x) (hguard := hguard)
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
    hguard

set_option maxHeartbeats 12000000 in
/-- **Guard revert.** When the guard word is one, the compiled runtime reverts. -/
theorem run_mul_exp_ray_evm_revert_of_guard (y x : Nat)
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
    simp +decide [external_fun_wrap_mulExpRay_dispatcher_state_revert y x hguard,
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
