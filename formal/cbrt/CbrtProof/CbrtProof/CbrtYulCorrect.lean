import CbrtProof.CbrtYulProof
import CbrtProof.CbrtEvmMath

set_option maxHeartbeats 8000000
set_option linter.style.nameCheck false

namespace CbrtYul

open FormalYul
open CbrtEvmMath

private theorem call_zero_value_for_split_t_uint256_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [] (.some "zero_value_for_split_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_zero_value_for_split_t_uint256]
  simp only [yulFunction_zero_value_for_split_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [



    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

private theorem call_fun__cbrt_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
      EvmYul.Yul.call (fuel + 200) [FormalYul.word x] (.some yulName_fun__cbrt)
        (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
      .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (innerCbrt (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__cbrt]
  simp only [yulFunction_fun__cbrt, yulFunction_fun__cbrt_11,
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
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 176)
      (shared := shared)
      (store := Finmap.insert "var_x_4" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_shiftRight, FormalYul.Preservation.wordNat_shiftLeft,
    FormalYul.Preservation.wordNat_add, FormalYul.Preservation.wordNat_sub,
    FormalYul.Preservation.wordNat_mul, FormalYul.Preservation.wordNat_div,
    FormalYul.Preservation.wordNat_clz, FormalYul.Preservation.wordNat_ofNat]
  have hinnerLt : innerCbrt (FormalYul.u256 x) < WORD_MOD :=
    innerCbrt_lt_word (FormalYul.u256 x)
      (by exact Nat.mod_lt x (by unfold WORD_MOD; exact Nat.two_pow_pos 256))
  simpa [FormalYul.Preservation.evmShr_u256_left, FormalYul.Preservation.evmShr_u256_right,
    FormalYul.Preservation.evmShl_u256_left, FormalYul.Preservation.evmShl_u256_right,
    FormalYul.Preservation.evmSub_u256_left, FormalYul.Preservation.evmSub_u256_right,
    FormalYul.Preservation.evmAdd_u256_left, FormalYul.Preservation.evmAdd_u256_right,
    FormalYul.Preservation.evmMul_u256_left, FormalYul.Preservation.evmMul_u256_right,
    FormalYul.Preservation.evmDiv_u256_left, FormalYul.Preservation.evmDiv_u256_right,
    FormalYul.Preservation.evmMod_u256_left, FormalYul.Preservation.evmMod_u256_right,
    FormalYul.Preservation.evmClz_u256, FormalYul.u256_u256,
    FormalYul.Preservation.u256_evmShr, u256_eq_of_lt _ hinnerLt] using
    cbrtCoreEvmExpression_eq_innerCbrt x

private theorem call_fun_cbrt_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
      EvmYul.Yul.call (fuel + 360) [FormalYul.word x] (.some yulName_fun_cbrt)
        (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
      .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (floorCbrt (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_cbrt]
  simp only [yulFunction_fun_cbrt, yulFunction_fun_cbrt_27,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcbrtFuel : fuel + 352 = (fuel + 152) + 200 := by omega
  have hCallCbrt :=
    call_fun__cbrt_direct (x := x) (fuel := fuel + 152) (shared := shared)
      (store := Finmap.insert "expr_21"
        (EvmYul.UInt256.ofNat x)
          (Finmap.insert "_8"
            (EvmYul.UInt256.ofNat x)
            (Finmap.insert "var_z_17" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "zero_t_uint256_7" (EvmYul.UInt256.ofNat 0)
                (Finmap.insert "var_x_14" (EvmYul.UInt256.ofNat x)
                  (Inhabited.default : EvmYul.Yul.VarStore))))))
      (hlookup := hlookup)
  simp [FormalYul.word, yulName_fun__cbrt] at hCallCbrt
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    hcbrtFuel, hCallCbrt,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 336)
      (shared := shared)
      (store := Finmap.insert "var_x_14" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_sub, FormalYul.Preservation.wordNat_lt,
    FormalYul.Preservation.wordNat_div, FormalYul.Preservation.wordNat_ofNat]
  have hxW : FormalYul.u256 x < WORD_MOD :=
    Nat.mod_lt x (by unfold WORD_MOD; exact Nat.two_pow_pos 256)
  have hinnerW : innerCbrt (FormalYul.u256 x) < WORD_MOD :=
    innerCbrt_lt_word (FormalYul.u256 x) hxW
  have hfloorW : floorCbrt (FormalYul.u256 x) < WORD_MOD :=
    floorCbrt_lt_word (FormalYul.u256 x) hxW
  have hcorr := cbrtFloorEvmCorrection_eq_floorCbrt x
  simpa [FormalYul.Preservation.evmSub_u256_left, FormalYul.Preservation.evmSub_u256_right,
    FormalYul.Preservation.evmLt_u256_left, FormalYul.Preservation.evmLt_u256_right,
    FormalYul.Preservation.evmDiv_u256_left, FormalYul.Preservation.evmDiv_u256_right,
    FormalYul.Preservation.evmMul_u256_left, FormalYul.Preservation.evmMul_u256_right,
    FormalYul.u256_u256, u256_eq_of_lt _ hinnerW, u256_eq_of_lt _ hfloorW] using hcorr

private theorem call_fun_cbrtUp_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
      EvmYul.Yul.call (fuel + 420) [FormalYul.word x] (.some yulName_fun_cbrtUp)
        (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
      .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (cbrtUp256 (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_cbrtUp]
  simp only [yulFunction_fun_cbrtUp, yulFunction_fun_cbrtUp_43,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hCallCbrt :=
    call_fun__cbrt_direct (x := x) (fuel := fuel + 212) (shared := shared)
      (store := Finmap.insert "expr_37"
        (EvmYul.UInt256.ofNat x)
          (Finmap.insert "_6"
            (EvmYul.UInt256.ofNat x)
            (Finmap.insert "var_z_33" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "zero_t_uint256_5" (EvmYul.UInt256.ofNat 0)
                (Finmap.insert "var_x_30" (EvmYul.UInt256.ofNat x)
                  (Inhabited.default : EvmYul.Yul.VarStore))))))
      (hlookup := hlookup)
  simp [FormalYul.word, yulName_fun__cbrt] at hCallCbrt
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    hCallCbrt,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 396)
      (shared := shared)
      (store := Finmap.insert "var_x_30" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_add, FormalYul.Preservation.wordNat_lt,
    FormalYul.Preservation.wordNat_mul,
    FormalYul.Preservation.wordNat_ofNat]
  have hxW : FormalYul.u256 x < WORD_MOD :=
    Nat.mod_lt x (by unfold WORD_MOD; exact Nat.two_pow_pos 256)
  have hinnerW : innerCbrt (FormalYul.u256 x) < WORD_MOD :=
    innerCbrt_lt_word (FormalYul.u256 x) hxW
  have hupW : cbrtUp256 (FormalYul.u256 x) < WORD_MOD :=
    cbrtUp256_lt_word (FormalYul.u256 x) hxW
  have hround := cbrtUpEvmCorrection_eq_cbrtUp256_all x
  simpa [FormalYul.Preservation.evmAdd_u256_left, FormalYul.Preservation.evmAdd_u256_right,
    FormalYul.Preservation.evmGt_u256_left, FormalYul.Preservation.evmGt_u256_right,
    FormalYul.Preservation.evmLt_u256_left, FormalYul.Preservation.evmLt_u256_right,
    FormalYul.Preservation.evmMul_u256_left, FormalYul.Preservation.evmMul_u256_right,
    FormalYul.u256_u256, u256_eq_of_lt _ hinnerW, u256_eq_of_lt _ hupW] using hround

private theorem call_fun_wrap_cbrt_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
      EvmYul.Yul.call (fuel + 460) [FormalYul.word x] (.some yulName_fun_wrap_cbrt)
        (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
      .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (floorCbrt (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_wrap_cbrt]
  simp only [yulFunction_fun_wrap_cbrt, yulFunction_fun_wrap_cbrt_62,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcbrtFuel : fuel + 451 = (fuel + 91) + 360 := by omega
  have hCallCbrt :=
    call_fun_cbrt_direct (x := x) (fuel := fuel + 91) (shared := shared)
      (store := Finmap.insert "expr_58"
        (EvmYul.UInt256.ofNat x)
          (Finmap.insert "_4"
            (EvmYul.UInt256.ofNat x)
            (Finmap.insert "expr_56_address" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "var__54" (EvmYul.UInt256.ofNat 0)
                (Finmap.insert "zero_t_uint256_3" (EvmYul.UInt256.ofNat 0)
                  (Finmap.insert "var_x_51" (EvmYul.UInt256.ofNat x)
                    (Inhabited.default : EvmYul.Yul.VarStore)))))))
      (hlookup := hlookup)
  simp [FormalYul.word, yulName_fun_cbrt] at hCallCbrt
  simp +decide [EvmYul.Yul.execCall.eq_def,

    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    hcbrtFuel, hCallCbrt,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 436)
      (shared := shared)
      (store := Finmap.insert "var_x_51" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]

private theorem call_fun_wrap_cbrtUp_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
      EvmYul.Yul.call (fuel + 520) [FormalYul.word x] (.some yulName_fun_wrap_cbrtUp)
        (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
      .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (cbrtUp256 (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_wrap_cbrtUp]
  simp only [yulFunction_fun_wrap_cbrtUp, yulFunction_fun_wrap_cbrtUp_75,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcbrtFuel : fuel + 511 = (fuel + 91) + 420 := by omega
  have hCallCbrt :=
    call_fun_cbrtUp_direct (x := x) (fuel := fuel + 91) (shared := shared)
      (store := Finmap.insert "expr_71"
        (EvmYul.UInt256.ofNat x)
          (Finmap.insert "_2"
            (EvmYul.UInt256.ofNat x)
            (Finmap.insert "expr_69_address" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "var__67" (EvmYul.UInt256.ofNat 0)
                (Finmap.insert "zero_t_uint256_1" (EvmYul.UInt256.ofNat 0)
                  (Finmap.insert "var_x_64" (EvmYul.UInt256.ofNat x)
                    (Inhabited.default : EvmYul.Yul.VarStore)))))))
      (hlookup := hlookup)
  simp [FormalYul.word, yulName_fun_cbrtUp] at hCallCbrt
  simp +decide [EvmYul.Yul.execCall.eq_def,

    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    hcbrtFuel, hCallCbrt,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 496)
      (shared := shared)
      (store := Finmap.insert "var_x_64" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]

private theorem call_cleanup_t_uint256_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v] (.some "cleanup_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_cleanup_t_uint256]
  simp only [yulFunction_cleanup_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [



    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert]

private theorem call_validator_revert_t_uint256_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [v] (.some "validator_revert_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, []) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_validator_revert_t_uint256]
  simp only [yulFunction_validator_revert_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcleanup :=
    call_cleanup_t_uint256_direct (v := v) (fuel := fuel + 31) (shared := shared)
      (store := Finmap.insert "value" v (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [] at hcleanup
  simp +decide [EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    hcleanup]

private def cbrtSharedAfterFreePtr (x : Nat) : EvmYul.SharedState .Yul :=
  let shared := FormalYul.sharedFor yulContract (selector_cbrt ++ FormalYul.encodeWords [x])
  { shared with toMachineState := shared.toMachineState.mstore (FormalYul.word 64) (FormalYul.word 128) }

private def cbrtUpSharedAfterFreePtr (x : Nat) : EvmYul.SharedState .Yul :=
  let shared := FormalYul.sharedFor yulContract (selector_cbrtUp ++ FormalYul.encodeWords [x])
  { shared with toMachineState := shared.toMachineState.mstore (FormalYul.word 64) (FormalYul.word 128) }

private theorem sharedFor_mstore_eq_cbrtSharedAfterFreePtr (x : Nat) :
    { (FormalYul.sharedFor yulContract (selector_cbrt ++ FormalYul.encodeWords [x])) with
      toMachineState :=
        (FormalYul.sharedFor yulContract (selector_cbrt ++ FormalYul.encodeWords [x])).toMachineState.mstore
          (FormalYul.word 64) (FormalYul.word 128) } =
      cbrtSharedAfterFreePtr x := rfl

private theorem sharedFor_mstore_mk_eq_cbrtSharedAfterFreePtr (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_cbrt ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_cbrt ++ FormalYul.encodeWords [x])).toMachineState.mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      cbrtSharedAfterFreePtr x := rfl

private theorem sharedFor_mstore_eq_cbrtUpSharedAfterFreePtr (x : Nat) :
    { (FormalYul.sharedFor yulContract (selector_cbrtUp ++ FormalYul.encodeWords [x])) with
      toMachineState :=
        (FormalYul.sharedFor yulContract (selector_cbrtUp ++ FormalYul.encodeWords [x])).toMachineState.mstore
          (FormalYul.word 64) (FormalYul.word 128) } =
      cbrtUpSharedAfterFreePtr x := rfl

private theorem sharedFor_mstore_mk_eq_cbrtUpSharedAfterFreePtr (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_cbrtUp ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_cbrtUp ++ FormalYul.encodeWords [x])).toMachineState.mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      cbrtUpSharedAfterFreePtr x := rfl

private theorem sharedFor_inherited_mstore_mk_eq_cbrtSharedAfterFreePtr (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_cbrt ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_cbrt ++ FormalYul.encodeWords [x])).mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      cbrtSharedAfterFreePtr x := rfl

private theorem sharedFor_inherited_mstore_mk_eq_cbrtSharedAfterFreePtr_raw (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_cbrt ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_cbrt ++ FormalYul.encodeWords [x])).mstore
          (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128))) =
      cbrtSharedAfterFreePtr x := by
  simpa [FormalYul.word] using sharedFor_inherited_mstore_mk_eq_cbrtSharedAfterFreePtr x

private theorem sharedFor_inherited_mstore_mk_eq_cbrtUpSharedAfterFreePtr (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_cbrtUp ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_cbrtUp ++ FormalYul.encodeWords [x])).mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      cbrtUpSharedAfterFreePtr x := rfl

private theorem sharedFor_inherited_mstore_mk_eq_cbrtUpSharedAfterFreePtr_raw (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_cbrtUp ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_cbrtUp ++ FormalYul.encodeWords [x])).mstore
          (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128))) =
      cbrtUpSharedAfterFreePtr x := by
  simpa [FormalYul.word] using sharedFor_inherited_mstore_mk_eq_cbrtUpSharedAfterFreePtr x

@[simp]
private theorem cbrtSharedAfterFreePtr_lookup (x : Nat) :
    (cbrtSharedAfterFreePtr x).accountMap.find?
        (cbrtSharedAfterFreePtr x).executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract) := by
  simp [cbrtSharedAfterFreePtr]

@[simp]
private theorem cbrtUpSharedAfterFreePtr_lookup (x : Nat) :
    (cbrtUpSharedAfterFreePtr x).accountMap.find?
        (cbrtUpSharedAfterFreePtr x).executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract) := by
  simp [cbrtUpSharedAfterFreePtr]

@[simp]
private theorem cbrtSharedAfterFreePtr_calldata (x : Nat) :
    (cbrtSharedAfterFreePtr x).executionEnv.calldata =
      selector_cbrt ++ FormalYul.encodeWords [x] := by
  simp [cbrtSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
private theorem cbrtUpSharedAfterFreePtr_calldata (x : Nat) :
    (cbrtUpSharedAfterFreePtr x).executionEnv.calldata =
      selector_cbrtUp ++ FormalYul.encodeWords [x] := by
  simp [cbrtUpSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
private theorem cbrtSharedAfterFreePtr_weiValue (x : Nat) :
    (cbrtSharedAfterFreePtr x).executionEnv.weiValue = ({ val := 0 } : EvmYul.UInt256) := by
  simp [cbrtSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
private theorem cbrtUpSharedAfterFreePtr_weiValue (x : Nat) :
    (cbrtUpSharedAfterFreePtr x).executionEnv.weiValue = ({ val := 0 } : EvmYul.UInt256) := by
  simp [cbrtUpSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
private theorem cbrt_calldata_size (x : Nat) :
    (selector_cbrt ++ FormalYul.encodeWords [x]).size = 36 := by
  simp [selector_cbrt, FormalYul.encodeWords,
    FormalYul.bytes, ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
    FormalYul.Preservation.encodeWord_size]

@[simp]
private theorem cbrtUp_calldata_size (x : Nat) :
    (selector_cbrtUp ++ FormalYul.encodeWords [x]).size = 36 := by
  simp [selector_cbrtUp, FormalYul.encodeWords,
    FormalYul.bytes, ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
    FormalYul.Preservation.encodeWord_size]

@[simp]
private theorem sharedFor_cbrt_calldata_size (x : Nat) :
    (FormalYul.sharedFor yulContract
      (selector_cbrt ++ FormalYul.encodeWords [x])).executionEnv.calldata.size = 36 := by
  simp [FormalYul.sharedFor, FormalYul.envFor, cbrt_calldata_size]

@[simp]
private theorem calldataload_cbrt_arg_of_calldata
    (x : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hdata : shared.executionEnv.calldata = selector_cbrt ++ FormalYul.encodeWords [x]) :
    EvmYul.State.calldataload
      (EvmYul.Yul.State.Ok shared store).toState (FormalYul.word 4) =
      FormalYul.word x := by
  simp [EvmYul.State.calldataload, EvmYul.Yul.State.toState, hdata,
    selector_cbrt, FormalYul.encodeWords]

@[simp]
private theorem calldataload_cbrtUp_arg_of_calldata
    (x : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hdata : shared.executionEnv.calldata = selector_cbrtUp ++ FormalYul.encodeWords [x]) :
    EvmYul.State.calldataload
      (EvmYul.Yul.State.Ok shared store).toState (FormalYul.word 4) =
      FormalYul.word x := by
  simp [EvmYul.State.calldataload, EvmYul.Yul.State.toState, hdata,
    selector_cbrtUp, FormalYul.encodeWords]

private theorem call_abi_decode_t_uint256_cbrt_of_calldata
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_cbrt ++ FormalYul.encodeWords [x]) :
    EvmYul.Yul.call (fuel + 80) [FormalYul.word 4, FormalYul.word 36]
      (.some "abi_decode_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word x]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_abi_decode_t_uint256]
  simp only [yulFunction_abi_decode_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hvalidator :=
    call_validator_revert_t_uint256_direct (v := FormalYul.word x) (fuel := fuel + 15)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word x)
        (Finmap.insert "offset" (FormalYul.word 4)
          (Finmap.insert "end" (FormalYul.word 36) (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup)
  simp [FormalYul.word] at hvalidator
  have hload :=
    calldataload_cbrt_arg_of_calldata x shared
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
    Finmap.lookup_insert, FormalYul.word, hload, hvalidator,
    ]

private theorem call_abi_decode_tuple_t_uint256_cbrt_of_calldata
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_cbrt ++ FormalYul.encodeWords [x]) :
    EvmYul.Yul.call (fuel + 130) [FormalYul.word 4, FormalYul.word 36]
      (.some "abi_decode_tuple_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word x]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_abi_decode_tuple_t_uint256]
  simp only [yulFunction_abi_decode_tuple_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hdecode :=
    call_abi_decode_t_uint256_cbrt_of_calldata (x := x) (fuel := fuel + 43)
      (shared := shared)
      (store := Finmap.insert "offset" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "headStart" (FormalYul.word 4)
          (Finmap.insert "dataEnd" (FormalYul.word 36)
            (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup) (hdata := hdata)
  simp [FormalYul.word] at hdecode
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hdecode]

private theorem call_abi_decode_t_uint256_cbrtUp_of_calldata
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_cbrtUp ++ FormalYul.encodeWords [x]) :
    EvmYul.Yul.call (fuel + 80) [FormalYul.word 4, FormalYul.word 36]
      (.some "abi_decode_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word x]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_abi_decode_t_uint256]
  simp only [yulFunction_abi_decode_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hvalidator :=
    call_validator_revert_t_uint256_direct (v := FormalYul.word x) (fuel := fuel + 15)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word x)
        (Finmap.insert "offset" (FormalYul.word 4)
          (Finmap.insert "end" (FormalYul.word 36) (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup)
  simp [FormalYul.word] at hvalidator
  have hload :=
    calldataload_cbrtUp_arg_of_calldata x shared
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
    Finmap.lookup_insert, FormalYul.word, hload, hvalidator,
    ]

private theorem call_abi_decode_tuple_t_uint256_cbrtUp_of_calldata
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_cbrtUp ++ FormalYul.encodeWords [x]) :
    EvmYul.Yul.call (fuel + 130) [FormalYul.word 4, FormalYul.word 36]
      (.some "abi_decode_tuple_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word x]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_abi_decode_tuple_t_uint256]
  simp only [yulFunction_abi_decode_tuple_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hdecode :=
    call_abi_decode_t_uint256_cbrtUp_of_calldata (x := x) (fuel := fuel + 43)
      (shared := shared)
      (store := Finmap.insert "offset" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "headStart" (FormalYul.word 4)
          (Finmap.insert "dataEnd" (FormalYul.word 36)
            (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup) (hdata := hdata)
  simp [FormalYul.word] at hdecode
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hdecode]

private theorem call_allocate_unbounded_direct
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
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_allocate_unbounded]
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

private theorem call_abi_encode_t_uint256_to_t_uint256_fromStack_direct
    (value pos : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 90) [value, pos] (.some "abi_encode_t_uint256_to_t_uint256_fromStack")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok ((EvmYul.Yul.State.Ok shared store).setMachineState
      ((EvmYul.Yul.State.Ok shared store).toMachineState.mstore pos value), []) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_abi_encode_t_uint256_to_t_uint256_fromStack]
  simp only [yulFunction_abi_encode_t_uint256_to_t_uint256_fromStack,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcleanup :=
    call_cleanup_t_uint256_direct (v := value) (fuel := fuel + 64) (shared := shared)
      (store := Finmap.insert "value" value
        (Finmap.insert "pos" pos (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup)
  simp [] at hcleanup
  simp +decide [EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    hcleanup]

private theorem call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack_direct
    (headStart value : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 150) [headStart, value]
      (.some "abi_encode_tuple_t_uint256__to_t_uint256__fromStack")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok ((EvmYul.Yul.State.Ok shared store).setMachineState
      ((EvmYul.Yul.State.Ok shared store).toMachineState.mstore headStart value),
      [headStart + FormalYul.word 32]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_abi_encode_tuple_t_uint256__to_t_uint256__fromStack]
  simp only [yulFunction_abi_encode_tuple_t_uint256__to_t_uint256__fromStack,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hencode :=
    call_abi_encode_t_uint256_to_t_uint256_fromStack_direct
      (value := value) (pos := headStart + FormalYul.word 0) (fuel := fuel + 55)
      (shared := shared)
      (store := Finmap.insert "tail" (headStart + FormalYul.word 32)
        (Finmap.insert "headStart" headStart
          (Finmap.insert "value0" value (Inhabited.default : EvmYul.Yul.VarStore))))
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

@[simp]
private theorem cbrtSharedAfterFreePtr_mload64 (x : Nat) :
    ((cbrtSharedAfterFreePtr x).mload (FormalYul.word 64)).1 = FormalYul.word 128 := by
  exact FormalYul.Preservation.sharedFor_mload_freePtr_after_mstore yulContract
    (selector_cbrt ++ FormalYul.encodeWords [x])

@[simp]
private theorem cbrtUpSharedAfterFreePtr_mload64 (x : Nat) :
    ((cbrtUpSharedAfterFreePtr x).mload (FormalYul.word 64)).1 = FormalYul.word 128 := by
  exact FormalYul.Preservation.sharedFor_mload_freePtr_after_mstore yulContract
    (selector_cbrtUp ++ FormalYul.encodeWords [x])

private theorem call_shift_right_224_unsigned_direct
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

@[simp]
private theorem cbrt_selector_afterFreePtr (x : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok (cbrtSharedAfterFreePtr x)
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 1457466198 := by
  let tail : List UInt8 := (FormalYul.encodeWord x).data.toList.take 28
  have htailLen : tail.length = 28 := by
    simp [tail, FormalYul.Preservation.encodeWord_data_toList]
  have hread :
      ((selector_cbrt ++ FormalYul.encodeWords [x]).readBytes 0 32).data.toList =
        [0x56, 0xdf, 0x2b, 0x56] ++ tail := by
    simp [tail, ByteArray.readBytes, selector_cbrt, FormalYul.encodeWords, FormalYul.bytes,
      ByteArray.push, ByteArray.empty, ByteArray.emptyWithCapacity]
    change (ffi.ByteArray.zeroes
        (OfNat.ofNat 32 - OfNat.ofNat
          (4 + (List.take 28
            (List.map (fun i => FormalYul.byteAt (FormalYul.u256 x) (31 - i))
              (List.range 32))).length))).data = #[]
    rw [show (List.take 28
        (List.map (fun i => FormalYul.byteAt (FormalYul.u256 x) (31 - i))
          (List.range 32))).length = 28 by simp]
    have hz : (OfNat.ofNat 32 - OfNat.ofNat (4 + 28) : USize) = 0 := by
      apply USize.ext
      simp
    rw [hz]
    rfl
  have hselector :=
    FormalYul.Preservation.shiftRight_calldataload_selector_of_readBytes
      (shared := cbrtSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (selectorBytes := [0x56, 0xdf, 0x2b, 0x56]) (tail := tail)
      (by decide) htailLen
      (by simpa [cbrtSharedAfterFreePtr_calldata] using hread)
  simpa [EvmYul.fromBytesBigEndian, EvmYul.fromBytes', FormalYul.word] using hselector

@[simp]
private theorem cbrt_selector_sharedFor_mk (x : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_cbrt ++ FormalYul.encodeWords [x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_cbrt ++ FormalYul.encodeWords [x])).mstore
                (FormalYul.word 64) (FormalYul.word 128)))
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 1457466198 := by
  rw [sharedFor_inherited_mstore_mk_eq_cbrtSharedAfterFreePtr]
  exact cbrt_selector_afterFreePtr x

@[simp]
private theorem selectSwitchCase_cbrt_sharedFor_mk (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (EvmYul.SharedState.mk
              (FormalYul.sharedFor yulContract
                (selector_cbrt ++ FormalYul.encodeWords [x])).toState
              ((FormalYul.sharedFor yulContract
                (selector_cbrt ++ FormalYul.encodeWords [x])).mstore
                  (FormalYul.word 64) (FormalYul.word 128)))
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (FormalYul.word 0))
        (FormalYul.word 224))
      [(FormalYul.word 703788273,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrtUp_75") [])]),
        (FormalYul.word 1457466198,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrt_62") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrt_62") [])] := by
  rw [cbrt_selector_sharedFor_mk]
  rfl

private theorem selectSwitchCase_cbrt_sharedFor_mk_raw (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (EvmYul.SharedState.mk
              (FormalYul.sharedFor yulContract
                (selector_cbrt ++ FormalYul.encodeWords [x])).toState
              ((FormalYul.sharedFor yulContract
                (selector_cbrt ++ FormalYul.encodeWords [x])).mstore
                  (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224))
      [(EvmYul.UInt256.ofNat 703788273,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrtUp_75") [])]),
        (EvmYul.UInt256.ofNat 1457466198,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrt_62") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrt_62") [])] := by
  simpa [FormalYul.word] using selectSwitchCase_cbrt_sharedFor_mk x

private theorem cbrtUp_selector_afterFreePtr (x : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok (cbrtUpSharedAfterFreePtr x)
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 703788273 := by
  let tail : List UInt8 := (FormalYul.encodeWord x).data.toList.take 28
  have htailLen : tail.length = 28 := by
    simp [tail, FormalYul.Preservation.encodeWord_data_toList]
  have hread :
      ((selector_cbrtUp ++ FormalYul.encodeWords [x]).readBytes 0 32).data.toList =
        [0x29, 0xf2, 0xf4, 0xf1] ++ tail := by
    simp [tail, ByteArray.readBytes, selector_cbrtUp, FormalYul.encodeWords, FormalYul.bytes,
      ByteArray.push, ByteArray.empty, ByteArray.emptyWithCapacity]
    change (ffi.ByteArray.zeroes
        (OfNat.ofNat 32 - OfNat.ofNat
          (4 + (List.take 28
            (List.map (fun i => FormalYul.byteAt (FormalYul.u256 x) (31 - i))
              (List.range 32))).length))).data = #[]
    rw [show (List.take 28
        (List.map (fun i => FormalYul.byteAt (FormalYul.u256 x) (31 - i))
          (List.range 32))).length = 28 by simp]
    have hz : (OfNat.ofNat 32 - OfNat.ofNat (4 + 28) : USize) = 0 := by
      apply USize.ext
      simp
    rw [hz]
    rfl
  have hselector :=
    FormalYul.Preservation.shiftRight_calldataload_selector_of_readBytes
      (shared := cbrtUpSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (selectorBytes := [0x29, 0xf2, 0xf4, 0xf1]) (tail := tail)
      (by decide) htailLen
      (by simpa [cbrtUpSharedAfterFreePtr_calldata] using hread)
  simpa [EvmYul.fromBytesBigEndian, EvmYul.fromBytes', FormalYul.word] using hselector

private theorem selectSwitchCase_cbrtUp_sharedFor_mk_raw (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (EvmYul.SharedState.mk
              (FormalYul.sharedFor yulContract
                (selector_cbrtUp ++ FormalYul.encodeWords [x])).toState
              ((FormalYul.sharedFor yulContract
                (selector_cbrtUp ++ FormalYul.encodeWords [x])).mstore
                  (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224))
      [(EvmYul.UInt256.ofNat 703788273,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrtUp_75") [])]),
        (EvmYul.UInt256.ofNat 1457466198,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrt_62") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrtUp_75") [])] := by
  rw [show
    (EvmYul.SharedState.mk
      (FormalYul.sharedFor yulContract
        (selector_cbrtUp ++ FormalYul.encodeWords [x])).toState
      ((FormalYul.sharedFor yulContract
        (selector_cbrtUp ++ FormalYul.encodeWords [x])).mstore
          (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128))) =
      cbrtUpSharedAfterFreePtr x by
        simpa [FormalYul.word] using sharedFor_inherited_mstore_mk_eq_cbrtUpSharedAfterFreePtr x]
  rw [show EvmYul.UInt256.ofNat 0 = FormalYul.word 0 by rfl]
  rw [show EvmYul.UInt256.ofNat 224 = FormalYul.word 224 by rfl]
  rw [cbrtUp_selector_afterFreePtr x]
  rfl

private theorem selectSwitchCase_cbrt_sharedFor_mk_raw_method (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (((EvmYul.Yul.State.Ok
        (EvmYul.SharedState.mk
          (FormalYul.sharedFor yulContract
            (selector_cbrt ++ FormalYul.encodeWords [x])).toState
          ((FormalYul.sharedFor yulContract
            (selector_cbrt ++ FormalYul.encodeWords [x])).mstore
              (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
        (Inhabited.default : EvmYul.Yul.VarStore)).toState.calldataload
          (EvmYul.UInt256.ofNat 0)).shiftRight
        (EvmYul.UInt256.ofNat 224))
      [(EvmYul.UInt256.ofNat 703788273,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrtUp_75") [])]),
        (EvmYul.UInt256.ofNat 1457466198,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrt_62") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrt_62") [])] := by
  simpa using selectSwitchCase_cbrt_sharedFor_mk_raw x

private theorem selectSwitchCase_cbrt_sharedFor_record_raw_method (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (((EvmYul.Yul.State.Ok
        { toState :=
            (FormalYul.sharedFor yulContract
              (selector_cbrt ++ FormalYul.encodeWords [x])).toState,
          toMachineState :=
            (FormalYul.sharedFor yulContract
              (selector_cbrt ++ FormalYul.encodeWords [x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128) }
        (Inhabited.default : EvmYul.Yul.VarStore)).toState.calldataload
          (EvmYul.UInt256.ofNat 0)).shiftRight
        (EvmYul.UInt256.ofNat 224))
      [(EvmYul.UInt256.ofNat 703788273,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrtUp_75") [])]),
        (EvmYul.UInt256.ofNat 1457466198,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrt_62") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrt_62") [])] := by
  simpa using selectSwitchCase_cbrt_sharedFor_mk_raw_method x

private theorem selectSwitchCase_cbrt_sharedFor_let_raw_method (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (((EvmYul.Yul.State.Ok
        (let __State :=
            (FormalYul.sharedFor yulContract
              (selector_cbrt ++ FormalYul.encodeWords [x])).toState
         let __MachineState :=
            (FormalYul.sharedFor yulContract
              (selector_cbrt ++ FormalYul.encodeWords [x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)
         { toState := __State, toMachineState := __MachineState })
        (Inhabited.default : EvmYul.Yul.VarStore)).toState.calldataload
          (EvmYul.UInt256.ofNat 0)).shiftRight
        (EvmYul.UInt256.ofNat 224))
      [(EvmYul.UInt256.ofNat 703788273,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrtUp_75") [])]),
        (EvmYul.UInt256.ofNat 1457466198,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrt_62") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrt_62") [])] := by
  simpa using selectSwitchCase_cbrt_sharedFor_record_raw_method x

private theorem selectSwitchCase_cbrt_sharedFor_have_raw_method (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (((EvmYul.Yul.State.Ok
        (have __State :=
            (FormalYul.sharedFor yulContract
              (selector_cbrt ++ FormalYul.encodeWords [x])).toState
         have __MachineState :=
            (FormalYul.sharedFor yulContract
              (selector_cbrt ++ FormalYul.encodeWords [x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)
         { toState := __State, toMachineState := __MachineState })
        (Inhabited.default : EvmYul.Yul.VarStore)).toState.calldataload
          (EvmYul.UInt256.ofNat 0)).shiftRight
        (EvmYul.UInt256.ofNat 224))
      [(EvmYul.UInt256.ofNat 703788273,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrtUp_75") [])]),
        (EvmYul.UInt256.ofNat 1457466198,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrt_62") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_cbrt_62") [])] := by
  simpa using selectSwitchCase_cbrt_sharedFor_record_raw_method x

private theorem external_fun_wrap_cbrt_cbrt_calldata_result_999989
    (x : Nat) (store : EvmYul.Yul.VarStore) :
    ((match
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_cbrt) (.some yulContract)
        (EvmYul.Yul.State.Ok (cbrtSharedAfterFreePtr x) store)
    with
    | .error (.YulHalt state _) => FormalYul.resultWord (FormalYul.returnOf state)
    | .error .Revert => .error "revert"
    | .error err => .error (reprStr err)
    | .ok (state, _) => FormalYul.resultWord (FormalYul.returnOf state)) :
      Except String Nat) =
      .ok (floorCbrt (FormalYul.u256 x)) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [
    cbrtSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_cbrt]
  simp only [yulFunction_external_fun_wrap_cbrt, yulFunction_external_fun_wrap_cbrt_62,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := floorCbrt (FormalYul.u256 x)
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word ret)
      (Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let memPos :=
    ((EvmYul.Yul.State.Ok (cbrtSharedAfterFreePtr x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { cbrtSharedAfterFreePtr x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (cbrtSharedAfterFreePtr x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_uint256_cbrt_of_calldata (x := x) (fuel := 999854)
      (shared := cbrtSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := cbrtSharedAfterFreePtr_lookup x) (hdata := cbrtSharedAfterFreePtr_calldata x)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_cbrt_direct (x := x) (fuel := 999523) (shared := cbrtSharedAfterFreePtr x)
      (store := Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := cbrtSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, yulName_fun_wrap_cbrt] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := cbrtSharedAfterFreePtr x)
      (store := baseStore) (hlookup := cbrtSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, baseStore] at halloc
  have hencode :=
    call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack_direct
      (headStart := memPos) (value := FormalYul.word ret) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by
        simp [memShared, cbrtSharedAfterFreePtr_lookup x])
  simp [FormalYul.word, memShared, encStore, memPos, baseStore, ret] at hencode
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,

    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    EvmYul.Yul.State.toMachineState, FormalYul.returnOf,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    hdecode, hwrap, halloc, hencode, ret]
  have hmload :
      ((cbrtSharedAfterFreePtr x).mload (EvmYul.UInt256.ofNat 64)).1 =
        EvmYul.UInt256.ofNat 128 := by
    simpa [FormalYul.word] using cbrtSharedAfterFreePtr_mload64 x
  rw [hmload]
  have hretLen :
      EvmYul.UInt256.ofNat 128 + EvmYul.UInt256.ofNat 32 -
          EvmYul.UInt256.ofNat 128 =
        FormalYul.word 32 := by
    decide
  rw [hretLen]
  rw [FormalYul.Preservation.resultWord_evmReturn_mstore_word]
  have hnat :
      (EvmYul.UInt256.ofNat (floorCbrt (FormalYul.u256 x))).toNat =
        floorCbrt (FormalYul.u256 x) := by
    change FormalYul.wordNat (EvmYul.UInt256.ofNat (floorCbrt (FormalYul.u256 x))) =
      floorCbrt (FormalYul.u256 x)
    exact (FormalYul.Preservation.wordNat_ofNat (floorCbrt (FormalYul.u256 x))).trans
      (u256_eq_of_lt _ (floorCbrt_lt_word _ (Nat.mod_lt x (by
        unfold WORD_MOD
        exact Nat.two_pow_pos 256))))
  rw [hnat]

private theorem external_fun_wrap_cbrt_cbrt_calldata_halts_999989
    (x : Nat) (store : EvmYul.Yul.VarStore) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_cbrt) (.some yulContract)
        (EvmYul.Yul.State.Ok (cbrtSharedAfterFreePtr x) store) =
        .error (.YulHalt state value) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [
    cbrtSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_cbrt]
  simp only [yulFunction_external_fun_wrap_cbrt, yulFunction_external_fun_wrap_cbrt_62,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := floorCbrt (FormalYul.u256 x)
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word ret)
      (Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let memPos :=
    ((EvmYul.Yul.State.Ok (cbrtSharedAfterFreePtr x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { cbrtSharedAfterFreePtr x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (cbrtSharedAfterFreePtr x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_uint256_cbrt_of_calldata (x := x) (fuel := 999854)
      (shared := cbrtSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := cbrtSharedAfterFreePtr_lookup x) (hdata := cbrtSharedAfterFreePtr_calldata x)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_cbrt_direct (x := x) (fuel := 999523) (shared := cbrtSharedAfterFreePtr x)
      (store := Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := cbrtSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, yulName_fun_wrap_cbrt] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := cbrtSharedAfterFreePtr x)
      (store := baseStore) (hlookup := cbrtSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, baseStore] at halloc
  have hencode :=
    call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack_direct
      (headStart := memPos) (value := FormalYul.word ret) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by
        simp [memShared, cbrtSharedAfterFreePtr_lookup x])
  simp [FormalYul.word, memShared, encStore, memPos, baseStore, ret] at hencode
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,

    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    EvmYul.Yul.State.toMachineState,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    hdecode, hwrap, halloc, hencode, ret]

private theorem external_fun_wrap_cbrtUp_cbrtUp_calldata_result_999989
    (x : Nat) (store : EvmYul.Yul.VarStore) :
    ((match
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_cbrtUp) (.some yulContract)
        (EvmYul.Yul.State.Ok (cbrtUpSharedAfterFreePtr x) store)
    with
    | .error (.YulHalt state _) => FormalYul.resultWord (FormalYul.returnOf state)
    | .error .Revert => .error "revert"
    | .error err => .error (reprStr err)
    | .ok (state, _) => FormalYul.resultWord (FormalYul.returnOf state)) :
      Except String Nat) =
      .ok (cbrtUp256 (FormalYul.u256 x)) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [
    cbrtUpSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_cbrtUp]
  simp only [yulFunction_external_fun_wrap_cbrtUp, yulFunction_external_fun_wrap_cbrtUp_75,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := cbrtUp256 (FormalYul.u256 x)
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word ret)
      (Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let memPos :=
    ((EvmYul.Yul.State.Ok (cbrtUpSharedAfterFreePtr x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { cbrtUpSharedAfterFreePtr x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (cbrtUpSharedAfterFreePtr x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_uint256_cbrtUp_of_calldata (x := x) (fuel := 999854)
      (shared := cbrtUpSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := cbrtUpSharedAfterFreePtr_lookup x) (hdata := cbrtUpSharedAfterFreePtr_calldata x)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_cbrtUp_direct (x := x) (fuel := 999463) (shared := cbrtUpSharedAfterFreePtr x)
      (store := Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := cbrtUpSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, yulName_fun_wrap_cbrtUp] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := cbrtUpSharedAfterFreePtr x)
      (store := baseStore) (hlookup := cbrtUpSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, baseStore] at halloc
  have hencode :=
    call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack_direct
      (headStart := memPos) (value := FormalYul.word ret) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by
        simp [memShared, cbrtUpSharedAfterFreePtr_lookup x])
  simp [FormalYul.word, memShared, encStore, memPos, baseStore, ret] at hencode
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,

    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    EvmYul.Yul.State.toMachineState, FormalYul.returnOf,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    hdecode, hwrap, halloc, hencode, ret]
  have hmload :
      ((cbrtUpSharedAfterFreePtr x).mload (EvmYul.UInt256.ofNat 64)).1 =
        EvmYul.UInt256.ofNat 128 := by
    simpa [FormalYul.word] using cbrtUpSharedAfterFreePtr_mload64 x
  rw [hmload]
  have hretLen :
      EvmYul.UInt256.ofNat 128 + EvmYul.UInt256.ofNat 32 -
          EvmYul.UInt256.ofNat 128 =
        FormalYul.word 32 := by
    decide
  rw [hretLen]
  rw [FormalYul.Preservation.resultWord_evmReturn_mstore_word]
  have hnat :
      (EvmYul.UInt256.ofNat (cbrtUp256 (FormalYul.u256 x))).toNat =
        cbrtUp256 (FormalYul.u256 x) := by
    change FormalYul.wordNat (EvmYul.UInt256.ofNat (cbrtUp256 (FormalYul.u256 x))) =
      cbrtUp256 (FormalYul.u256 x)
    exact (FormalYul.Preservation.wordNat_ofNat (cbrtUp256 (FormalYul.u256 x))).trans
      (u256_eq_of_lt _ (cbrtUp256_lt_word _ (Nat.mod_lt x (by
        unfold WORD_MOD
        exact Nat.two_pow_pos 256))))
  rw [hnat]

private theorem external_fun_wrap_cbrtUp_cbrtUp_calldata_halts_999989
    (x : Nat) (store : EvmYul.Yul.VarStore) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_cbrtUp) (.some yulContract)
        (EvmYul.Yul.State.Ok (cbrtUpSharedAfterFreePtr x) store) =
        .error (.YulHalt state value) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [
    cbrtUpSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_cbrtUp]
  simp only [yulFunction_external_fun_wrap_cbrtUp, yulFunction_external_fun_wrap_cbrtUp_75,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := cbrtUp256 (FormalYul.u256 x)
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word ret)
      (Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let memPos :=
    ((EvmYul.Yul.State.Ok (cbrtUpSharedAfterFreePtr x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { cbrtUpSharedAfterFreePtr x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (cbrtUpSharedAfterFreePtr x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_uint256_cbrtUp_of_calldata (x := x) (fuel := 999854)
      (shared := cbrtUpSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := cbrtUpSharedAfterFreePtr_lookup x) (hdata := cbrtUpSharedAfterFreePtr_calldata x)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_cbrtUp_direct (x := x) (fuel := 999463) (shared := cbrtUpSharedAfterFreePtr x)
      (store := Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := cbrtUpSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, yulName_fun_wrap_cbrtUp] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := cbrtUpSharedAfterFreePtr x)
      (store := baseStore) (hlookup := cbrtUpSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, baseStore] at halloc
  have hencode :=
    call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack_direct
      (headStart := memPos) (value := FormalYul.word ret) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by
        simp [memShared, cbrtUpSharedAfterFreePtr_lookup x])
  simp [FormalYul.word, memShared, encStore, memPos, baseStore, ret] at hencode
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,

    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    EvmYul.Yul.State.toMachineState,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    hdecode, hwrap, halloc, hencode, ret]

private theorem external_fun_wrap_cbrt_dispatcher_state_result (x : Nat) :
    ((match
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_cbrt) (.some yulContract)
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_cbrt ++ FormalYul.encodeWords [x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_cbrt ++ FormalYul.encodeWords [x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
          (Finmap.insert "selector"
            (EvmYul.UInt256.shiftRight
              (EvmYul.State.calldataload
                (EvmYul.Yul.State.Ok
                  (EvmYul.SharedState.mk
                    (FormalYul.sharedFor yulContract
                      (selector_cbrt ++ FormalYul.encodeWords [x])).toState
                    ((FormalYul.sharedFor yulContract
                      (selector_cbrt ++ FormalYul.encodeWords [x])).mstore
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
      .ok (floorCbrt (FormalYul.u256 x)) := by
  rw [sharedFor_inherited_mstore_mk_eq_cbrtSharedAfterFreePtr_raw]
  exact external_fun_wrap_cbrt_cbrt_calldata_result_999989 (x := x)
    (store := Finmap.insert "selector"
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok (cbrtSharedAfterFreePtr x)
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224))
      (Inhabited.default : EvmYul.Yul.VarStore))

private theorem external_fun_wrap_cbrt_dispatcher_state_halts (x : Nat) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_cbrt) (.some yulContract)
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_cbrt ++ FormalYul.encodeWords [x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_cbrt ++ FormalYul.encodeWords [x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
          (Finmap.insert "selector"
            (EvmYul.UInt256.shiftRight
              (EvmYul.State.calldataload
                (EvmYul.Yul.State.Ok
                  (EvmYul.SharedState.mk
                    (FormalYul.sharedFor yulContract
                      (selector_cbrt ++ FormalYul.encodeWords [x])).toState
                    ((FormalYul.sharedFor yulContract
                      (selector_cbrt ++ FormalYul.encodeWords [x])).mstore
                        (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
                  (Inhabited.default : EvmYul.Yul.VarStore)).toState
                (EvmYul.UInt256.ofNat 0))
              (EvmYul.UInt256.ofNat 224))
            (Inhabited.default : EvmYul.Yul.VarStore))) =
        .error (.YulHalt state value) := by
  rw [sharedFor_inherited_mstore_mk_eq_cbrtSharedAfterFreePtr_raw]
  exact external_fun_wrap_cbrt_cbrt_calldata_halts_999989 (x := x)
    (store := Finmap.insert "selector"
        (EvmYul.UInt256.shiftRight
          (EvmYul.State.calldataload
            (EvmYul.Yul.State.Ok (cbrtSharedAfterFreePtr x)
              (Inhabited.default : EvmYul.Yul.VarStore)).toState
            (EvmYul.UInt256.ofNat 0))
          (EvmYul.UInt256.ofNat 224))
        (Inhabited.default : EvmYul.Yul.VarStore))

private theorem dispatcherReturn_cbrtUp
    (x : Nat) (haltState : EvmYul.Yul.State) (haltValue : EvmYul.Literal)
    (hhalt :
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_cbrtUp) (.some yulContract)
        (EvmYul.Yul.State.Ok (cbrtUpSharedAfterFreePtr x)
          (Finmap.insert "selector" (FormalYul.word 703788273)
            (Inhabited.default : EvmYul.Yul.VarStore))) =
        .error (.YulHalt haltState haltValue)) :
    FormalYul.Preservation.DispatcherReturn yulContract
      (FormalYul.calldata selector_cbrtUp [x]) 999998 (FormalYul.returnOf haltState) := by
  let start := FormalYul.stateFor yulContract (FormalYul.calldata selector_cbrtUp [x])
  let afterFreePtr : EvmYul.Yul.State :=
    EvmYul.Yul.State.Ok (cbrtUpSharedAfterFreePtr x)
      (Inhabited.default : EvmYul.Yul.VarStore)
  let afterSelector : EvmYul.Yul.State :=
    EvmYul.Yul.State.Ok (cbrtUpSharedAfterFreePtr x)
      (Finmap.insert "selector" (FormalYul.word 703788273)
        (Inhabited.default : EvmYul.Yul.VarStore))
  apply FormalYul.Preservation.dispatcherReturn_of_execReturn
    (hdispatcher := yulContract_dispatcher)
  simpa [start, afterFreePtr, afterSelector, yulDispatcher, FormalYul.calldata,
      yulName_external_fun_wrap_cbrtUp] using
    (FormalYul.Preservation.execReturn_block_if_switch_selected_call_nil
      (fuel := 999989)
      (first :=
        EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call
            (Sum.inl (EvmYul.Operation.StackMemFlow EvmYul.Operation.SMSFOp.MSTORE))
            [EvmYul.Yul.Ast.Expr.Lit (EvmYul.UInt256.ofNat 64),
              EvmYul.Yul.Ast.Expr.Lit (EvmYul.UInt256.ofNat 128)]))
      (fallback :=
        EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call
            (Sum.inr "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74")
            []))
      (letStmt :=
        EvmYul.Yul.Ast.Stmt.Let ["selector"]
          (some
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "shift_right_224_unsigned")
              [EvmYul.Yul.Ast.Expr.Call
                (Sum.inl (EvmYul.Operation.Env EvmYul.Operation.EOp.CALLDATALOAD))
                [EvmYul.Yul.Ast.Expr.Lit (EvmYul.UInt256.ofNat 0)]])))
      (ifCond :=
        EvmYul.Yul.Ast.Expr.Call
          (Sum.inl (EvmYul.Operation.CompBit EvmYul.Operation.CBLOp.ISZERO))
          [EvmYul.Yul.Ast.Expr.Call
            (Sum.inl (EvmYul.Operation.CompBit EvmYul.Operation.CBLOp.LT))
            [EvmYul.Yul.Ast.Expr.Call
              (Sum.inl (EvmYul.Operation.Env EvmYul.Operation.EOp.CALLDATASIZE)) [],
              EvmYul.Yul.Ast.Expr.Lit (EvmYul.UInt256.ofNat 4)]])
      (switchCond := EvmYul.Yul.Ast.Expr.Var "selector")
      (cases :=
        [(FormalYul.word 703788273,
            [EvmYul.Yul.Ast.Stmt.ExprStmtCall
              (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_cbrtUp) [])]),
          (FormalYul.word 1457466198,
            [EvmYul.Yul.Ast.Stmt.ExprStmtCall
              (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_cbrt) [])])])
      (defaultStmts := [])
      (fn := yulName_external_fun_wrap_cbrtUp)
      (code := .some yulContract)
      (start := start)
      (afterFirst := afterFreePtr)
      (branchStart := afterFreePtr)
      (afterLet := afterSelector)
      (switchStart := afterSelector)
      (condValue := FormalYul.word 1)
      (selector := FormalYul.word 703788273)
      (result := FormalYul.returnOf haltState)
      (hfirst := by
        simp +decide [start, afterFreePtr, FormalYul.stateFor, FormalYul.calldata,

          EvmYul.Yul.execPrimCall.eq_def,
          EvmYul.Yul.reverse', EvmYul.Yul.cons',
          EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,

          EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,


          EvmYul.Yul.State.toMachineState,




          sharedFor_inherited_mstore_mk_eq_cbrtUpSharedAfterFreePtr_raw])
      (hcond := by
        simp +decide [afterFreePtr,
          EvmYul.Yul.evalPrimCall.eq_def,
          EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
          EvmYul.Yul.evalTail.eq_def,
          EvmYul.Yul.State.executionEnv, FormalYul.word,
          cbrtUpSharedAfterFreePtr_calldata, cbrtUp_calldata_size])
      (hcondNe := by decide)
      (hlet := by
        have hselector :
            ((EvmYul.Yul.State.Ok (cbrtUpSharedAfterFreePtr x)
                (Inhabited.default : EvmYul.Yul.VarStore)).toState.calldataload
                (EvmYul.UInt256.ofNat 0)).shiftRight
              (EvmYul.UInt256.ofNat 224) =
              EvmYul.UInt256.ofNat 703788273 := by
          simpa [FormalYul.word] using cbrtUp_selector_afterFreePtr x
        simp +decide [afterFreePtr, afterSelector,
          EvmYul.Yul.execCall.eq_def,
          EvmYul.Yul.evalPrimCall.eq_def,
          EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
          EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,

          EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,



          FormalYul.word, call_shift_right_224_unsigned_direct,
          hselector,
          ])
      (hswitchEval := by
        simp [afterSelector])
      (hselect := by
        rfl)
      (hcall := by
        exact ⟨haltState, haltValue, hhalt, rfl⟩))

theorem run_cbrt_floor_evm_eq_floorCbrt (x : Nat) :
    run_cbrt_floor_evm x = .ok (floorCbrt (FormalYul.u256 x)) := by
  obtain ⟨haltState, _haltValue, hhalt⟩ :=
    external_fun_wrap_cbrt_dispatcher_state_halts x
  have hresult := external_fun_wrap_cbrt_dispatcher_state_result x
  rw [hhalt] at hresult
  have hReturn :
      FormalYul.Preservation.DispatcherReturn yulContract
        (FormalYul.calldata selector_cbrt [x]) 999998 (FormalYul.returnOf haltState) := by
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
      EvmYul.Yul.State.executionEnv,
      EvmYul.Yul.State.toMachineState,
      FormalYul.word,


      call_shift_right_224_unsigned_direct,
      ]
    rw [selectSwitchCase_cbrt_sharedFor_mk_raw x]
    simp +decide [hhalt, EvmYul.Yul.exec.eq_def,
      EvmYul.Yul.execCall.eq_def,

      EvmYul.Yul.reverse', EvmYul.Yul.multifill',









      ]
  unfold run_cbrt_floor_evm run_cbrt_evm
  exact FormalYul.Preservation.callWord_ok_of_dispatcherReturn_result_1000000
    (contract := yulContract) (selector := selector_cbrt) (args := [x])
    (hReturn := hReturn) (by simpa using hresult)

theorem run_cbrt_floor_evm_eq_icbrt (x : Nat) :
    run_cbrt_floor_evm x = .ok (icbrt (FormalYul.u256 x)) := by
  rw [run_cbrt_floor_evm_eq_floorCbrt]
  rw [floorCbrt_correct_u256_eq_all]
  exact Nat.mod_lt x (by unfold WORD_MOD; exact Nat.two_pow_pos 256)

theorem run_cbrt_up_evm_eq_cbrtUp256 (x : Nat) :
    run_cbrt_up_evm x = .ok (cbrtUp256 (FormalYul.u256 x)) := by
  let selectorStore :=
    Finmap.insert "selector" (FormalYul.word 703788273)
      (Inhabited.default : EvmYul.Yul.VarStore)
  obtain ⟨haltState, haltValue, hhalt⟩ :=
    external_fun_wrap_cbrtUp_cbrtUp_calldata_halts_999989 (x := x)
      (store := selectorStore)
  have hresult :=
    external_fun_wrap_cbrtUp_cbrtUp_calldata_result_999989 (x := x)
      (store := selectorStore)
  rw [hhalt] at hresult
  have hReturn :
      FormalYul.Preservation.DispatcherReturn yulContract
        (FormalYul.calldata selector_cbrtUp [x]) 999998 (FormalYul.returnOf haltState) :=
    dispatcherReturn_cbrtUp x haltState haltValue (by
      simpa [selectorStore] using hhalt)
  unfold run_cbrt_up_evm
  exact FormalYul.Preservation.callWord_ok_of_dispatcherReturn_result_1000000
    (contract := yulContract) (selector := selector_cbrtUp) (args := [x])
    (hReturn := hReturn) (by simpa using hresult)

end CbrtYul
