import ExpProof.ExpYulProof
import Common.Word
import ExpProof.Seam.Helpers
import ExpProof.Seam.Dispatcher
import ExpProof.Seam.Value
import FormalYul.Preservation
import Mathlib.Data.Nat.Bitwise

/-!
# Value-path reductions for `mulExpRay`

Every multiplier takes the same straight-line path: headroom, octave, closing shift, the guard
word, the shared kernel, and the closing `sgn(y)` multiply. One reduction covers all inputs whose
guard word is zero; a zero multiplier needs no separate path because `sgn(0) = 0` collapses the
kernel output at the tree level.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word

set_option maxRecDepth 100000

set_option maxHeartbeats 12000000 in
/-- `fun_mulExpRay(y, x)` on the value path returns the signed dynamic-scale tree. -/
theorem call_fun_mulExpRay_direct
    (y x fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hclean : EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word y) =
      FormalYul.word y)
    (hresultClean :
      EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word (mulExpTree y x)) =
        FormalYul.word (mulExpTree y x))
    (hguard : mulExpGuardTree y x = 0) :
    EvmYul.Yul.call (fuel + (extra + 2200)) [FormalYul.word y, FormalYul.word x]
      (.some yulName_fun_mulExpRay) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (mulExpTree y x)]) := by
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
  let scale := evmShl s ay
  let result :=
    evmMul (evmOr (evmLt 0 (absTree y)) (signTree y)) (mulMagnitudeTree y x)
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
  have hscaleShift :=
    call_shift_left_t_uint256_t_uint256_direct (value := ay) (bits := s)
      (fuel := fuel + extra) (extra := 1949) (shared := shared) (hlookup := hlookup)
  have hconvertShiftOut :=
    call_convert_int256_to_uint256_direct (v := shift) (fuel := fuel + extra) (extra := 2006)
      (shared := shared) (hlookup := hlookup)
  have hZM :=
    call_convert_MUL_EXP_RAY_ZERO_MAX_to_int256_direct
      (fuel := fuel + extra) (extra := 2004)
      (shared := shared) (hlookup := hlookup)
  have hkernel :=
    call_fun__expRayKernel_direct (x := x) (k := k) (scale := scale) (shift := shift)
      (zeroCutoff := mulExpRayZeroMax) (fuel := fuel + extra) (extra := 1423)
      (shared := shared) (hlookup := hlookup)
  have hconvertInt256 :=
    call_convert_uint256_to_int256_direct (v := result) (fuel := fuel + extra)
      (extra := 1998) (shared := shared) (hlookup := hlookup)
  have hconvertNarrow :=
    call_convert_int256_to_int128_direct (v := result) (fuel := fuel + extra)
      (extra := 1997) (shared := shared) (hlookup := hlookup)
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
  simp only [Nat.reduceAdd, FormalYul.word, s, ay, absTree, signTree, scaleShiftTree,
    scaleClzBias] at hscaleShift
  simp only [Nat.reduceAdd, FormalYul.word, shift, k, kTree, s, ay, absTree, signTree,
    scaleShiftTree, scaleClzBias] at hconvertShiftOut
  simp only [Nat.reduceAdd, FormalYul.word, mulExpRayZeroMax] at hZM
  simp only [Nat.reduceAdd, FormalYul.word, k, kTree, scale, shift, s, ay, absTree,
    signTree, scaleShiftTree, scaleClzBias, mulExpRayZeroMax, evmShl_one_c0] at hkernel
  simp only [Nat.reduceAdd, FormalYul.word,
    result, mulMagnitudeTree, r0MulTree, mulScaleTree, mulShiftTree,
    tTree, vTree, evTree, odTree, todTree, kTree, scaleShiftTree, absTree, signTree,
    tArgShift, k27Q235, ln2Q235, squareShift,
    ev0, ev1, ev2, ev3, ev4, evShift1, evShift2, evShift3, evShift4,
    od0, od1, od2, od3, od4, odShift1, odShift2, odShift3, odShift4,
    todShift, marginWord, scaleClzBias, mulExpRayZeroMax] at hconvertInt256 hconvertNarrow
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
          2) = 0 := by
    simpa [mulExpGuardTree, mulShiftTree, scaleShiftTree, absTree, signTree, kTree,
      scaleClzBias, hhiMinusOne] using hguard
  have hresultOrder : result = mulExpTree y x := by
    have hor : evmOr (evmLt 0 (absTree y)) (signTree y) =
        evmOr (signTree y) (evmLt 0 (absTree y)) := by
      unfold evmOr
      rw [Nat.lor_comm]
    dsimp only [result]
    rw [hor]
    unfold mulExpTree sgnTree evmMul
    rw [Nat.mul_comm]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    FormalYul.word,
    hconvertY1, hconvert255, hshiftSign, hsignAsUint, hconvertY2, hayAsUint, hwrapAy,
    hguardUnfold,
    hzeroInit, hclz, hscaleClzBias, hwrapS,
    hconvert127, hshrAy, hwrapAdd, hoctave, hconvertS, hwrapShift,
    hHi, hcleanupXForHi,
    hconvertTwo, hcleanupShift, hOrGuard, hscaleShift,
    hconvertShiftOut, hZM, hkernel, hconvertInt256, hconvertNarrow,
    FormalYul.Preservation.uint256_ofNat_lt_eq_word_evmLt,
    FormalYul.Preservation.uint256_ofNat_mul_eq_word_evmMul,
    FormalYul.Preservation.uint256_ofNat_or_eq_word_evmOr,
    Common.Word.uint256_ofNat_xor_eq_word_evmXor,
    uint256_ofNat_slt_eq_word_evmSlt,
    uint256_ofNat_sgt_eq_word_evmSgt,
    mulExpTree, mulMagnitudeTree, sgnTree, r0MulTree, mulScaleTree, mulShiftTree,
    tTree, vTree, evTree, odTree, todTree,
    tArgShift, k27Q235, ln2Q235, squareShift,
    ev0, ev1, ev2, ev3, ev4, evShift1, evShift2, evShift3, evShift4,
    od0, od1, od2, od3, od4, odShift1, odShift2, odShift3, odShift4,
    todShift, marginWord,
    scaleShiftTree, absTree, signTree, kTree,
    scaleClzBias, mulExpRayZeroMax]
  change EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word result) =
    FormalYul.word (mulExpTree y x)
  rw [hresultOrder]
  exact hresultClean

set_option maxHeartbeats 12000000 in
/-- `fun_wrap_mulExpRay(y, x)` forwards to the value path. -/
theorem call_fun_wrap_mulExpRay_direct
    (y x fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hclean : EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word y) =
      FormalYul.word y)
    (hresultClean :
      EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word (mulExpTree y x)) =
        FormalYul.word (mulExpTree y x))
    (hguard : mulExpGuardTree y x = 0) :
    EvmYul.Yul.call (fuel + (extra + 2300)) [FormalYul.word y, FormalYul.word x]
      (.some yulName_fun_wrap_mulExpRay) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (mulExpTree y x)]) := by
  rw [show fuel + (extra + 2300) = (fuel + extra) + 2300 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_wrap_mulExpRay]
  simp only [yulFunctionBody_fun_wrap_mulExpRay,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hinner :=
    call_fun_mulExpRay_direct (y := y) (x := x) (fuel := fuel + extra) (extra := 89)
      (shared := shared) (hlookup := hlookup) (hclean := hclean)
      (hresultClean := hresultClean) (hguard := hguard)
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun_mulExpRay] at hinner
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    call_zero_value_for_split_t_int128_direct (fuel := fuel + extra) (extra := 2276)
      (shared := shared) (hlookup := hlookup),
    hinner]

set_option maxHeartbeats 12000000 in
/-- The external `mulExpRay` entrypoint ABI-encodes and returns the value tree. -/
theorem external_fun_wrap_mulExpRay_calldata_result
    (y x : Nat) (store : EvmYul.Yul.VarStore)
    (hclean : EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word y) =
      FormalYul.word y)
    (hresultClean :
      EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word (mulExpTree y x)) =
        FormalYul.word (mulExpTree y x))
    (hguard : mulExpGuardTree y x = 0) :
    ((match
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_mulExpRay) (.some yulContract)
        (EvmYul.Yul.State.Ok (mulExpSharedAfterFreePtr y x) store)
    with
    | .error (.YulHalt state _) => FormalYul.resultWord (FormalYul.returnOf state)
    | .error .Revert => .error "revert"
    | .error err => .error (reprStr err)
    | .ok (state, _) => FormalYul.resultWord (FormalYul.returnOf state)) :
      Except String Nat) =
      .ok (mulExpTree y x) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [mulExpSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_mulExpRay]
  simp only [yulFunctionBody_external_fun_wrap_mulExpRay,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word (mulExpTree y x))
      (Finmap.insert "param_0" (FormalYul.word y)
        (Finmap.insert "param_1" (FormalYul.word x)
          (Inhabited.default : EvmYul.Yul.VarStore)))
  let memPos :=
    ((EvmYul.Yul.State.Ok (mulExpSharedAfterFreePtr y x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { mulExpSharedAfterFreePtr y x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (mulExpSharedAfterFreePtr y x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_int128t_int256_of_mul_calldata (y := y) (x := x)
      (fuel := 0) (extra := 999464)
      (shared := mulExpSharedAfterFreePtr y x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := mulExpSharedAfterFreePtr_lookup y x)
      (hdata := mulExpSharedAfterFreePtr_calldata y x) (hclean := hclean)
  simp only [Nat.reduceAdd, FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_mulExpRay_direct (y := y) (x := x) (fuel := 0) (extra := 997683)
      (shared := mulExpSharedAfterFreePtr y x)
      (store := Finmap.insert "param_0" (FormalYul.word y)
        (Finmap.insert "param_1" (FormalYul.word x)
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := mulExpSharedAfterFreePtr_lookup y x) (hclean := hclean)
      (hresultClean := hresultClean) (hguard := hguard)
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun_wrap_mulExpRay] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := mulExpSharedAfterFreePtr y x)
      (store := baseStore) (hlookup := mulExpSharedAfterFreePtr_lookup y x)
  simp only [FormalYul.word, baseStore] at halloc
  have hencode :=
    call_abi_encode_tuple_t_int128__to_t_int128__fromStack_direct
      (headStart := memPos) (v := mulExpTree y x) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by simp [memShared, mulExpSharedAfterFreePtr_lookup y x])
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
      ((mulExpSharedAfterFreePtr y x).mload (EvmYul.UInt256.ofNat 64)).1 =
        EvmYul.UInt256.ofNat 128 := by
    simpa [FormalYul.word] using mulExpSharedAfterFreePtr_mload64 y x
  rw [hmload]
  have hretLen :
      EvmYul.UInt256.ofNat 128 + EvmYul.UInt256.ofNat 32 - EvmYul.UInt256.ofNat 128 =
        FormalYul.word 32 := by decide
  rw [hretLen]
  rw [FormalYul.Preservation.resultWord_evmReturn_mstore_word]
  have hnat :
      (EvmYul.UInt256.ofNat (mulExpTree y x)).toNat = mulExpTree y x := by
    change FormalYul.wordNat (EvmYul.UInt256.ofNat (mulExpTree y x)) = mulExpTree y x
    exact (FormalYul.Preservation.wordNat_ofNat (mulExpTree y x)).trans
      (FormalYul.Preservation.u256_eq_of_lt _ (mulExpTree_lt y x))
  exact (congrArg (fun w => Except.ok w.toNat) hresultClean).trans (congrArg Except.ok hnat)

set_option maxHeartbeats 12000000 in
/-- The external `mulExpRay` entrypoint on the value path halts (returns). -/
theorem external_fun_wrap_mulExpRay_calldata_halts
    (y x : Nat) (store : EvmYul.Yul.VarStore)
    (hclean : EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word y) =
      FormalYul.word y)
    (hresultClean :
      EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word (mulExpTree y x)) =
        FormalYul.word (mulExpTree y x))
    (hguard : mulExpGuardTree y x = 0) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_mulExpRay) (.some yulContract)
        (EvmYul.Yul.State.Ok (mulExpSharedAfterFreePtr y x) store) =
        .error (.YulHalt state value) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [mulExpSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_mulExpRay]
  simp only [yulFunctionBody_external_fun_wrap_mulExpRay,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word (mulExpTree y x))
      (Finmap.insert "param_0" (FormalYul.word y)
        (Finmap.insert "param_1" (FormalYul.word x)
          (Inhabited.default : EvmYul.Yul.VarStore)))
  let memPos :=
    ((EvmYul.Yul.State.Ok (mulExpSharedAfterFreePtr y x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { mulExpSharedAfterFreePtr y x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (mulExpSharedAfterFreePtr y x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_int128t_int256_of_mul_calldata (y := y) (x := x)
      (fuel := 0) (extra := 999464)
      (shared := mulExpSharedAfterFreePtr y x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := mulExpSharedAfterFreePtr_lookup y x)
      (hdata := mulExpSharedAfterFreePtr_calldata y x) (hclean := hclean)
  simp only [Nat.reduceAdd, FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_mulExpRay_direct (y := y) (x := x) (fuel := 0) (extra := 997683)
      (shared := mulExpSharedAfterFreePtr y x)
      (store := Finmap.insert "param_0" (FormalYul.word y)
        (Finmap.insert "param_1" (FormalYul.word x)
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := mulExpSharedAfterFreePtr_lookup y x) (hclean := hclean)
      (hresultClean := hresultClean) (hguard := hguard)
  simp only [Nat.reduceAdd, FormalYul.word, yulName_fun_wrap_mulExpRay] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := mulExpSharedAfterFreePtr y x)
      (store := baseStore) (hlookup := mulExpSharedAfterFreePtr_lookup y x)
  simp only [FormalYul.word, baseStore] at halloc
  have hencode :=
    call_abi_encode_tuple_t_int128__to_t_int128__fromStack_direct
      (headStart := memPos) (v := mulExpTree y x) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by simp [memShared, mulExpSharedAfterFreePtr_lookup y x])
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
/-- Result, starting from the exact state the dispatcher hands the external `mulExpRay`
function. -/
theorem external_fun_wrap_mulExpRay_dispatcher_state_result
    (y x : Nat)
    (hclean : EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word y) =
      FormalYul.word y)
    (hresultClean :
      EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word (mulExpTree y x)) =
        FormalYul.word (mulExpTree y x))
    (hguard : mulExpGuardTree y x = 0) :
    ((match
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
            (Inhabited.default : EvmYul.Yul.VarStore)))
    with
    | .error (.YulHalt state _) => FormalYul.resultWord (FormalYul.returnOf state)
    | .error .Revert => .error "revert"
    | .error err => .error (reprStr err)
    | .ok (state, _) => FormalYul.resultWord (FormalYul.returnOf state)) :
      Except String Nat) =
      .ok (mulExpTree y x) := by
  rw [sharedFor_inherited_mstore_mk_eq_mulExpSharedAfterFreePtr_raw]
  exact external_fun_wrap_mulExpRay_calldata_result y x
    (store := Finmap.insert "selector"
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok (mulExpSharedAfterFreePtr y x)
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224))
      (Inhabited.default : EvmYul.Yul.VarStore))
    hclean hresultClean hguard

set_option maxHeartbeats 12000000 in
/-- Halt, starting from the exact state the dispatcher hands the external `mulExpRay`
function. -/
theorem external_fun_wrap_mulExpRay_dispatcher_state_halts
    (y x : Nat)
    (hclean : EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word y) =
      FormalYul.word y)
    (hresultClean :
      EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word (mulExpTree y x)) =
        FormalYul.word (mulExpTree y x))
    (hguard : mulExpGuardTree y x = 0) :
    ∃ state value,
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
        .error (.YulHalt state value) := by
  rw [sharedFor_inherited_mstore_mk_eq_mulExpSharedAfterFreePtr_raw]
  exact external_fun_wrap_mulExpRay_calldata_halts y x
    (store := Finmap.insert "selector"
        (EvmYul.UInt256.shiftRight
          (EvmYul.State.calldataload
            (EvmYul.Yul.State.Ok (mulExpSharedAfterFreePtr y x)
              (Inhabited.default : EvmYul.Yul.VarStore)).toState
            (EvmYul.UInt256.ofNat 0))
          (EvmYul.UInt256.ofNat 224))
        (Inhabited.default : EvmYul.Yul.VarStore))
    hclean hresultClean hguard

set_option maxHeartbeats 12000000 in
/-- **Value path.** With canonical input and result words, a zero guard makes the compiled runtime
return the signed dynamic-scale arithmetic tree — for every multiplier, including zero. -/
theorem run_mul_exp_ray_evm_eq_tree_of_guard (y x : Nat)
    (hclean : EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word y) =
      FormalYul.word y)
    (hresultClean :
      EvmYul.UInt256.signextend (FormalYul.word 15) (FormalYul.word (mulExpTree y x)) =
        FormalYul.word (mulExpTree y x))
    (hguard : mulExpGuardTree y x = 0) :
    run_mul_exp_ray_evm y x = .ok (mulExpTree y x) := by
  obtain ⟨haltState, _haltValue, hhalt⟩ :=
    external_fun_wrap_mulExpRay_dispatcher_state_halts y x hclean hresultClean hguard
  have hresult :=
    external_fun_wrap_mulExpRay_dispatcher_state_result y x hclean hresultClean hguard
  rw [hhalt] at hresult
  have hReturn :
      FormalYul.Preservation.DispatcherReturn yulContract
        (FormalYul.calldata selector_mulExpRay [y, x]) 999998 (FormalYul.returnOf haltState) := by
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
    rw [selectSwitchCase_mulExpRay_sharedFor_mk_raw y x]
    simp +decide [hhalt, EvmYul.Yul.exec.eq_def,
      EvmYul.Yul.execCall.eq_def,
      EvmYul.Yul.reverse', EvmYul.Yul.multifill']
  unfold run_mul_exp_ray_evm
  exact FormalYul.Preservation.callWord_ok_of_dispatcherReturn_result_1000000
    (contract := yulContract) (selector := selector_mulExpRay) (args := [y, x])
    (hReturn := hReturn) (by simpa using hresult)

end ExpYul
