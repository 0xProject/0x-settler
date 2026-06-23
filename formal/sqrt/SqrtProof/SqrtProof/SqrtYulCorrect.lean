import SqrtProof.SqrtYulProof
import SqrtProof.SqrtEvmMath

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.style.nameCheck false

namespace SqrtYul

open FormalYul
open SqrtEvmMath

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

private theorem call_fun__sqrt_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 200) [FormalYul.word x] (.some yulName_fun__sqrt)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (innerSqrt (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__sqrt]
  simp only [yulFunction_fun__sqrt, yulFunction_fun__sqrt_11,
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
    FormalYul.Preservation.wordNat_div, FormalYul.Preservation.wordNat_clz,
    FormalYul.Preservation.wordNat_ofNat]
  have hinnerLt : innerSqrt (FormalYul.u256 x) < WORD_MOD :=
    innerSqrt_lt_word (FormalYul.u256 x)
      (by exact Nat.mod_lt x (by unfold WORD_MOD; exact Nat.two_pow_pos 256))
  simpa [FormalYul.Preservation.evmShr_u256_left, FormalYul.Preservation.evmShr_u256_right,
    FormalYul.Preservation.evmShl_u256_left, FormalYul.Preservation.evmShl_u256_right,
    FormalYul.Preservation.evmSub_u256_left, FormalYul.Preservation.evmSub_u256_right,
    FormalYul.Preservation.evmAdd_u256_left, FormalYul.Preservation.evmAdd_u256_right,
    FormalYul.Preservation.evmDiv_u256_left, FormalYul.Preservation.evmDiv_u256_right,
    FormalYul.Preservation.evmClz_u256, FormalYul.u256_u256,
    FormalYul.Preservation.u256_evmShr, u256_eq_of_lt _ hinnerLt] using
    innerSqrt_evmSteps_eq (FormalYul.u256 x)
      (by exact Nat.mod_lt x (by unfold WORD_MOD; exact Nat.two_pow_pos 256))

private theorem call_fun_sqrt_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 360) [FormalYul.word x] (.some yulName_fun_sqrt)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (floorSqrt (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_sqrt]
  simp only [yulFunction_fun_sqrt, yulFunction_fun_sqrt_27,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hsqrtFuel : fuel + 352 = (fuel + 152) + 200 := by omega
  have hCallSqrt :=
    call_fun__sqrt_direct (x := x) (fuel := fuel + 152) (shared := shared)
      (store := Finmap.insert "expr_21"
        (EvmYul.UInt256.ofNat x)
        (Finmap.insert "_6"
          (EvmYul.UInt256.ofNat x)
          (Finmap.insert "var_z_17" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "zero_t_uint256_5" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "var_x_14" (EvmYul.UInt256.ofNat x)
                (Inhabited.default : EvmYul.Yul.VarStore))))))
      (hlookup := hlookup)
  simp [FormalYul.word, yulName_fun__sqrt] at hCallSqrt
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    hsqrtFuel, hCallSqrt,
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
  have hinnerW : innerSqrt (FormalYul.u256 x) < WORD_MOD :=
    innerSqrt_lt_word (FormalYul.u256 x) hxW
  have hfloorW : floorSqrt (FormalYul.u256 x) < WORD_MOD :=
    floorSqrt_lt_word (FormalYul.u256 x) hxW
  have hcorr := floorSqrt_evmCorrection_eq (FormalYul.u256 x) hxW
  simpa [FormalYul.Preservation.evmSub_u256_left, FormalYul.Preservation.evmSub_u256_right,
    FormalYul.Preservation.evmLt_u256_left, FormalYul.Preservation.evmLt_u256_right,
    FormalYul.Preservation.evmDiv_u256_left, FormalYul.Preservation.evmDiv_u256_right,
    FormalYul.u256_u256, u256_eq_of_lt _ hinnerW, u256_eq_of_lt _ hfloorW] using hcorr

private theorem call_fun_sqrtUp_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 420) [FormalYul.word x] (.some yulName_fun_sqrtUp)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (sqrtUp256 (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_sqrtUp]
  simp only [yulFunction_fun_sqrtUp, yulFunction_fun_sqrtUp_43,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hCallSqrt :=
    call_fun__sqrt_direct (x := x) (fuel := fuel + 212) (shared := shared)
      (store := Finmap.insert "expr_37"
        (EvmYul.UInt256.ofNat x)
        (Finmap.insert "_8"
          (EvmYul.UInt256.ofNat x)
          (Finmap.insert "var_z_33" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "zero_t_uint256_7" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "var_x_30" (EvmYul.UInt256.ofNat x)
                (Inhabited.default : EvmYul.Yul.VarStore))))))
      (hlookup := hlookup)
  simp [FormalYul.word, yulName_fun__sqrt] at hCallSqrt
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    hCallSqrt,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 396)
      (shared := shared)
      (store := Finmap.insert "var_x_30" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_add, FormalYul.Preservation.wordNat_gt,
    FormalYul.Preservation.wordNat_lt, FormalYul.Preservation.wordNat_mul,
    FormalYul.Preservation.wordNat_ofNat]
  have hxW : FormalYul.u256 x < WORD_MOD :=
    Nat.mod_lt x (by unfold WORD_MOD; exact Nat.two_pow_pos 256)
  have hbr : natSqrt (FormalYul.u256 x) <= innerSqrt (FormalYul.u256 x) ∧
      innerSqrt (FormalYul.u256 x) <= natSqrt (FormalYul.u256 x) + 1 := by
    simpa using innerSqrt_bracket_u256_all (FormalYul.u256 x)
      (by simpa [WORD_MOD] using hxW)
  have hm128 : natSqrt (FormalYul.u256 x) < 2 ^ 128 :=
    m_lt_pow128_of_u256 (natSqrt (FormalYul.u256 x)) (FormalYul.u256 x)
      (natSqrt_sq_le (FormalYul.u256 x)) hxW
  have hinnerW : innerSqrt (FormalYul.u256 x) < WORD_MOD :=
    innerSqrt_lt_word (FormalYul.u256 x) hxW
  have hzLe128 : innerSqrt (FormalYul.u256 x) <= 2 ^ 128 := by omega
  have hround :=
    sqrtUp_step_evm_eq_inner_round (FormalYul.u256 x) (innerSqrt (FormalYul.u256 x))
      hxW hzLe128
  have hceil :=
    sqrtUpInner_eq_sqrtUp256_u256 (FormalYul.u256 x) (by simpa [WORD_MOD] using hxW)
  have hupW : sqrtUp256 (FormalYul.u256 x) < WORD_MOD := sqrtUp256_lt_word (FormalYul.u256 x) hxW
  simpa [FormalYul.Preservation.evmAdd_u256_left, FormalYul.Preservation.evmAdd_u256_right,
    FormalYul.Preservation.evmGt_u256_left, FormalYul.Preservation.evmGt_u256_right,
    FormalYul.Preservation.evmLt_u256_left, FormalYul.Preservation.evmLt_u256_right,
    FormalYul.Preservation.evmMul_u256_left, FormalYul.Preservation.evmMul_u256_right,
    FormalYul.u256_u256, u256_eq_of_lt _ hinnerW, u256_eq_of_lt _ hupW] using hround.trans hceil

private theorem call_fun_wrap_sqrt_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 460) [FormalYul.word x] (.some yulName_fun_wrap_sqrt)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (floorSqrt (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_wrap_sqrt]
  simp only [yulFunction_fun_wrap_sqrt, yulFunction_fun_wrap_sqrt_62,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hsqrtFuel : fuel + 451 = (fuel + 91) + 360 := by omega
  have hCallSqrt :=
    call_fun_sqrt_direct (x := x) (fuel := fuel + 91) (shared := shared)
      (store := Finmap.insert "expr_58"
        (EvmYul.UInt256.ofNat x)
        (Finmap.insert "_2"
          (EvmYul.UInt256.ofNat x)
          (Finmap.insert "expr_56_address" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "var__54" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "zero_t_uint256_1" (EvmYul.UInt256.ofNat 0)
                (Finmap.insert "var_x_51" (EvmYul.UInt256.ofNat x)
                  (Inhabited.default : EvmYul.Yul.VarStore)))))))
      (hlookup := hlookup)
  simp [FormalYul.word, yulName_fun_sqrt] at hCallSqrt
  simp +decide [EvmYul.Yul.execCall.eq_def,

    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    hsqrtFuel, hCallSqrt,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 436)
      (shared := shared)
      (store := Finmap.insert "var_x_51" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]

private theorem call_fun_wrap_sqrtUp_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 520) [FormalYul.word x] (.some yulName_fun_wrap_sqrtUp)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (sqrtUp256 (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_wrap_sqrtUp]
  simp only [yulFunction_fun_wrap_sqrtUp, yulFunction_fun_wrap_sqrtUp_75,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hsqrtFuel : fuel + 511 = (fuel + 91) + 420 := by omega
  have hCallSqrt :=
    call_fun_sqrtUp_direct (x := x) (fuel := fuel + 91) (shared := shared)
      (store := Finmap.insert "expr_71"
        (EvmYul.UInt256.ofNat x)
        (Finmap.insert "_4"
          (EvmYul.UInt256.ofNat x)
          (Finmap.insert "expr_69_address" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "var__67" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "zero_t_uint256_3" (EvmYul.UInt256.ofNat 0)
                (Finmap.insert "var_x_64" (EvmYul.UInt256.ofNat x)
                  (Inhabited.default : EvmYul.Yul.VarStore)))))))
      (hlookup := hlookup)
  simp [FormalYul.word, yulName_fun_sqrtUp] at hCallSqrt
  simp +decide [EvmYul.Yul.execCall.eq_def,

    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    hsqrtFuel, hCallSqrt,
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

private def sqrtSharedAfterFreePtr (x : Nat) : EvmYul.SharedState .Yul :=
  let shared := FormalYul.sharedFor yulContract (selector_sqrt ++ FormalYul.encodeWords [x])
  { shared with toMachineState := shared.toMachineState.mstore (FormalYul.word 64) (FormalYul.word 128) }

private def sqrtUpSharedAfterFreePtr (x : Nat) : EvmYul.SharedState .Yul :=
  let shared := FormalYul.sharedFor yulContract (selector_sqrtUp ++ FormalYul.encodeWords [x])
  { shared with toMachineState := shared.toMachineState.mstore (FormalYul.word 64) (FormalYul.word 128) }

private theorem sharedFor_mstore_eq_sqrtSharedAfterFreePtr (x : Nat) :
    { (FormalYul.sharedFor yulContract (selector_sqrt ++ FormalYul.encodeWords [x])) with
      toMachineState :=
        (FormalYul.sharedFor yulContract (selector_sqrt ++ FormalYul.encodeWords [x])).toMachineState.mstore
          (FormalYul.word 64) (FormalYul.word 128) } =
      sqrtSharedAfterFreePtr x := rfl

private theorem sharedFor_mstore_mk_eq_sqrtSharedAfterFreePtr (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_sqrt ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_sqrt ++ FormalYul.encodeWords [x])).toMachineState.mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      sqrtSharedAfterFreePtr x := rfl

private theorem sharedFor_mstore_eq_sqrtUpSharedAfterFreePtr (x : Nat) :
    { (FormalYul.sharedFor yulContract (selector_sqrtUp ++ FormalYul.encodeWords [x])) with
      toMachineState :=
        (FormalYul.sharedFor yulContract (selector_sqrtUp ++ FormalYul.encodeWords [x])).toMachineState.mstore
          (FormalYul.word 64) (FormalYul.word 128) } =
      sqrtUpSharedAfterFreePtr x := rfl

private theorem sharedFor_mstore_mk_eq_sqrtUpSharedAfterFreePtr (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_sqrtUp ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_sqrtUp ++ FormalYul.encodeWords [x])).toMachineState.mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      sqrtUpSharedAfterFreePtr x := rfl

private theorem sharedFor_inherited_mstore_mk_eq_sqrtSharedAfterFreePtr (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_sqrt ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      sqrtSharedAfterFreePtr x := rfl

private theorem sharedFor_inherited_mstore_mk_eq_sqrtSharedAfterFreePtr_raw (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_sqrt ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
          (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128))) =
      sqrtSharedAfterFreePtr x := by
  simpa [FormalYul.word] using sharedFor_inherited_mstore_mk_eq_sqrtSharedAfterFreePtr x

private theorem sharedFor_inherited_mstore_mk_eq_sqrtUpSharedAfterFreePtr (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_sqrtUp ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_sqrtUp ++ FormalYul.encodeWords [x])).mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      sqrtUpSharedAfterFreePtr x := rfl

private theorem sharedFor_inherited_mstore_mk_eq_sqrtUpSharedAfterFreePtr_raw (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_sqrtUp ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_sqrtUp ++ FormalYul.encodeWords [x])).mstore
          (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128))) =
      sqrtUpSharedAfterFreePtr x := by
  simpa [FormalYul.word] using sharedFor_inherited_mstore_mk_eq_sqrtUpSharedAfterFreePtr x

@[simp]
private theorem sqrtSharedAfterFreePtr_lookup (x : Nat) :
    (sqrtSharedAfterFreePtr x).accountMap.find?
        (sqrtSharedAfterFreePtr x).executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract) := by
  simp [sqrtSharedAfterFreePtr]

@[simp]
private theorem sqrtUpSharedAfterFreePtr_lookup (x : Nat) :
    (sqrtUpSharedAfterFreePtr x).accountMap.find?
        (sqrtUpSharedAfterFreePtr x).executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract) := by
  simp [sqrtUpSharedAfterFreePtr]

@[simp]
private theorem sqrtSharedAfterFreePtr_calldata (x : Nat) :
    (sqrtSharedAfterFreePtr x).executionEnv.calldata =
      selector_sqrt ++ FormalYul.encodeWords [x] := by
  simp [sqrtSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
private theorem sqrtUpSharedAfterFreePtr_calldata (x : Nat) :
    (sqrtUpSharedAfterFreePtr x).executionEnv.calldata =
      selector_sqrtUp ++ FormalYul.encodeWords [x] := by
  simp [sqrtUpSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
private theorem sqrtSharedAfterFreePtr_weiValue (x : Nat) :
    (sqrtSharedAfterFreePtr x).executionEnv.weiValue = ({ val := 0 } : EvmYul.UInt256) := by
  simp [sqrtSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
private theorem sqrtUpSharedAfterFreePtr_weiValue (x : Nat) :
    (sqrtUpSharedAfterFreePtr x).executionEnv.weiValue = ({ val := 0 } : EvmYul.UInt256) := by
  simp [sqrtUpSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
private theorem sqrt_calldata_size (x : Nat) :
    (selector_sqrt ++ FormalYul.encodeWords [x]).size = 36 := by
  simp [selector_sqrt, FormalYul.encodeWords,
    FormalYul.bytes, ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
    FormalYul.Preservation.encodeWord_size]

@[simp]
private theorem sqrtUp_calldata_size (x : Nat) :
    (selector_sqrtUp ++ FormalYul.encodeWords [x]).size = 36 := by
  simp [selector_sqrtUp, FormalYul.encodeWords,
    FormalYul.bytes, ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
    FormalYul.Preservation.encodeWord_size]

@[simp]
private theorem sharedFor_sqrt_calldata_size (x : Nat) :
    (FormalYul.sharedFor yulContract
      (selector_sqrt ++ FormalYul.encodeWords [x])).executionEnv.calldata.size = 36 := by
  simp [FormalYul.sharedFor, FormalYul.envFor, sqrt_calldata_size]

@[simp]
private theorem calldataload_sqrt_arg_of_calldata
    (x : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hdata : shared.executionEnv.calldata = selector_sqrt ++ FormalYul.encodeWords [x]) :
    EvmYul.State.calldataload
      (EvmYul.Yul.State.Ok shared store).toState (FormalYul.word 4) =
      FormalYul.word x := by
  simp [EvmYul.State.calldataload, EvmYul.Yul.State.toState, hdata,
    selector_sqrt, FormalYul.encodeWords]

@[simp]
private theorem calldataload_sqrtUp_arg_of_calldata
    (x : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hdata : shared.executionEnv.calldata = selector_sqrtUp ++ FormalYul.encodeWords [x]) :
    EvmYul.State.calldataload
      (EvmYul.Yul.State.Ok shared store).toState (FormalYul.word 4) =
      FormalYul.word x := by
  simp [EvmYul.State.calldataload, EvmYul.Yul.State.toState, hdata,
    selector_sqrtUp, FormalYul.encodeWords]

private theorem call_abi_decode_t_uint256_sqrt_of_calldata
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_sqrt ++ FormalYul.encodeWords [x]) :
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
    calldataload_sqrt_arg_of_calldata x shared
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

private theorem call_abi_decode_tuple_t_uint256_sqrt_of_calldata
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_sqrt ++ FormalYul.encodeWords [x]) :
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
    call_abi_decode_t_uint256_sqrt_of_calldata (x := x) (fuel := fuel + 43)
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

private theorem call_abi_decode_t_uint256_sqrtUp_of_calldata
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_sqrtUp ++ FormalYul.encodeWords [x]) :
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
    calldataload_sqrtUp_arg_of_calldata x shared
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

private theorem call_abi_decode_tuple_t_uint256_sqrtUp_of_calldata
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_sqrtUp ++ FormalYul.encodeWords [x]) :
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
    call_abi_decode_t_uint256_sqrtUp_of_calldata (x := x) (fuel := fuel + 43)
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
private theorem sqrtSharedAfterFreePtr_mload64 (x : Nat) :
    ((sqrtSharedAfterFreePtr x).mload (FormalYul.word 64)).1 = FormalYul.word 128 := by
  exact FormalYul.Preservation.sharedFor_mload_freePtr_after_mstore yulContract
    (selector_sqrt ++ FormalYul.encodeWords [x])

@[simp]
private theorem sqrtUpSharedAfterFreePtr_mload64 (x : Nat) :
    ((sqrtUpSharedAfterFreePtr x).mload (FormalYul.word 64)).1 = FormalYul.word 128 := by
  exact FormalYul.Preservation.sharedFor_mload_freePtr_after_mstore yulContract
    (selector_sqrtUp ++ FormalYul.encodeWords [x])

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
private theorem sqrt_selector_afterFreePtr (x : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok (sqrtSharedAfterFreePtr x)
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 1529414794 := by
  have hselector :=
    FormalYul.Preservation.shiftRight_calldataload_selector_single_arg_of_calldata
      (shared := sqrtSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (a := 0x5b) (b := 0x29) (c := 0x04) (d := 0x8a) (x := x)
      (by simp [selector_sqrt])
  simpa [EvmYul.fromBytesBigEndian, EvmYul.fromBytes', FormalYul.word] using hselector

@[simp]
private theorem sqrt_selector_sharedFor_mk (x : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_sqrt ++ FormalYul.encodeWords [x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
                (FormalYul.word 64) (FormalYul.word 128)))
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 1529414794 := by
  rw [sharedFor_inherited_mstore_mk_eq_sqrtSharedAfterFreePtr]
  exact sqrt_selector_afterFreePtr x

@[simp]
private theorem selectSwitchCase_sqrt_sharedFor_mk (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (EvmYul.SharedState.mk
              (FormalYul.sharedFor yulContract
                (selector_sqrt ++ FormalYul.encodeWords [x])).toState
              ((FormalYul.sharedFor yulContract
                (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
                  (FormalYul.word 64) (FormalYul.word 128)))
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (FormalYul.word 0))
        (FormalYul.word 224))
      [(FormalYul.word 1529414794,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrt_62") [])]),
        (FormalYul.word 1707723681,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrtUp_75") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrt_62") [])] := by
  rw [sqrt_selector_sharedFor_mk]
  rfl

private theorem selectSwitchCase_sqrt_sharedFor_mk_raw (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (EvmYul.SharedState.mk
              (FormalYul.sharedFor yulContract
                (selector_sqrt ++ FormalYul.encodeWords [x])).toState
              ((FormalYul.sharedFor yulContract
                (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
                  (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224))
      [(EvmYul.UInt256.ofNat 1529414794,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrt_62") [])]),
        (EvmYul.UInt256.ofNat 1707723681,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrtUp_75") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrt_62") [])] := by
  simpa [FormalYul.word] using selectSwitchCase_sqrt_sharedFor_mk x

private theorem sqrtUp_selector_afterFreePtr (x : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x)
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 1707723681 := by
  have hselector :=
    FormalYul.Preservation.shiftRight_calldataload_selector_single_arg_of_calldata
      (shared := sqrtUpSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (a := 0x65) (b := 0xc9) (c := 0xcb) (d := 0xa1) (x := x)
      (by simp [selector_sqrtUp])
  simpa [EvmYul.fromBytesBigEndian, EvmYul.fromBytes', FormalYul.word] using hselector

private theorem selectSwitchCase_sqrtUp_sharedFor_mk_raw (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (EvmYul.SharedState.mk
              (FormalYul.sharedFor yulContract
                (selector_sqrtUp ++ FormalYul.encodeWords [x])).toState
              ((FormalYul.sharedFor yulContract
                (selector_sqrtUp ++ FormalYul.encodeWords [x])).mstore
                  (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224))
      [(EvmYul.UInt256.ofNat 1529414794,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrt_62") [])]),
        (EvmYul.UInt256.ofNat 1707723681,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrtUp_75") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_sqrtUp_75") [])] := by
  rw [show
    (EvmYul.SharedState.mk
      (FormalYul.sharedFor yulContract
        (selector_sqrtUp ++ FormalYul.encodeWords [x])).toState
      ((FormalYul.sharedFor yulContract
        (selector_sqrtUp ++ FormalYul.encodeWords [x])).mstore
          (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128))) =
      sqrtUpSharedAfterFreePtr x by
        simpa [FormalYul.word] using sharedFor_inherited_mstore_mk_eq_sqrtUpSharedAfterFreePtr x]
  rw [show EvmYul.UInt256.ofNat 0 = FormalYul.word 0 by rfl]
  rw [show EvmYul.UInt256.ofNat 224 = FormalYul.word 224 by rfl]
  rw [sqrtUp_selector_afterFreePtr x]
  rfl

private theorem external_fun_wrap_sqrt_sqrt_calldata_result_999989
    (x : Nat) (store : EvmYul.Yul.VarStore) :
    ((match
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_sqrt) (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrtSharedAfterFreePtr x) store)
    with
    | .error (.YulHalt state _) => FormalYul.resultWord (FormalYul.returnOf state)
    | .error .Revert => .error "revert"
    | .error err => .error (reprStr err)
    | .ok (state, _) => FormalYul.resultWord (FormalYul.returnOf state)) :
      Except String Nat) =
      .ok (floorSqrt (FormalYul.u256 x)) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [
    sqrtSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_sqrt]
  simp only [yulFunction_external_fun_wrap_sqrt, yulFunction_external_fun_wrap_sqrt_62,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := floorSqrt (FormalYul.u256 x)
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word ret)
      (Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let memPos :=
    ((EvmYul.Yul.State.Ok (sqrtSharedAfterFreePtr x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { sqrtSharedAfterFreePtr x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (sqrtSharedAfterFreePtr x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_uint256_sqrt_of_calldata (x := x) (fuel := 999854)
      (shared := sqrtSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := sqrtSharedAfterFreePtr_lookup x) (hdata := sqrtSharedAfterFreePtr_calldata x)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_sqrt_direct (x := x) (fuel := 999523) (shared := sqrtSharedAfterFreePtr x)
      (store := Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := sqrtSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, yulName_fun_wrap_sqrt] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := sqrtSharedAfterFreePtr x)
      (store := baseStore) (hlookup := sqrtSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, baseStore] at halloc
  have hencode :=
    call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack_direct
      (headStart := memPos) (value := FormalYul.word ret) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by
        simp [memShared, sqrtSharedAfterFreePtr_lookup x])
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
      ((sqrtSharedAfterFreePtr x).mload (EvmYul.UInt256.ofNat 64)).1 =
        EvmYul.UInt256.ofNat 128 := by
    simpa [FormalYul.word] using sqrtSharedAfterFreePtr_mload64 x
  rw [hmload]
  have hretLen :
      EvmYul.UInt256.ofNat 128 + EvmYul.UInt256.ofNat 32 -
          EvmYul.UInt256.ofNat 128 =
        FormalYul.word 32 := by
    decide
  rw [hretLen]
  rw [FormalYul.Preservation.resultWord_evmReturn_mstore_word]
  have hnat :
      (EvmYul.UInt256.ofNat (floorSqrt (FormalYul.u256 x))).toNat =
        floorSqrt (FormalYul.u256 x) := by
    change FormalYul.wordNat (EvmYul.UInt256.ofNat (floorSqrt (FormalYul.u256 x))) =
      floorSqrt (FormalYul.u256 x)
    exact (FormalYul.Preservation.wordNat_ofNat (floorSqrt (FormalYul.u256 x))).trans
      (u256_eq_of_lt _ (floorSqrt_lt_word _ (Nat.mod_lt x (by
        unfold WORD_MOD
        exact Nat.two_pow_pos 256))))
  rw [hnat]

private theorem external_fun_wrap_sqrt_sqrt_calldata_halts_999989
    (x : Nat) (store : EvmYul.Yul.VarStore) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_sqrt) (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrtSharedAfterFreePtr x) store) =
        .error (.YulHalt state value) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [
    sqrtSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_sqrt]
  simp only [yulFunction_external_fun_wrap_sqrt, yulFunction_external_fun_wrap_sqrt_62,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := floorSqrt (FormalYul.u256 x)
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word ret)
      (Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let memPos :=
    ((EvmYul.Yul.State.Ok (sqrtSharedAfterFreePtr x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { sqrtSharedAfterFreePtr x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (sqrtSharedAfterFreePtr x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_uint256_sqrt_of_calldata (x := x) (fuel := 999854)
      (shared := sqrtSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := sqrtSharedAfterFreePtr_lookup x) (hdata := sqrtSharedAfterFreePtr_calldata x)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_sqrt_direct (x := x) (fuel := 999523) (shared := sqrtSharedAfterFreePtr x)
      (store := Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := sqrtSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, yulName_fun_wrap_sqrt] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := sqrtSharedAfterFreePtr x)
      (store := baseStore) (hlookup := sqrtSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, baseStore] at halloc
  have hencode :=
    call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack_direct
      (headStart := memPos) (value := FormalYul.word ret) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by
        simp [memShared, sqrtSharedAfterFreePtr_lookup x])
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

private theorem external_fun_wrap_sqrtUp_sqrtUp_calldata_result_999989
    (x : Nat) (store : EvmYul.Yul.VarStore) :
    ((match
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_sqrtUp) (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x) store)
    with
    | .error (.YulHalt state _) => FormalYul.resultWord (FormalYul.returnOf state)
    | .error .Revert => .error "revert"
    | .error err => .error (reprStr err)
    | .ok (state, _) => FormalYul.resultWord (FormalYul.returnOf state)) :
      Except String Nat) =
      .ok (sqrtUp256 (FormalYul.u256 x)) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [
    sqrtUpSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_sqrtUp]
  simp only [yulFunction_external_fun_wrap_sqrtUp, yulFunction_external_fun_wrap_sqrtUp_75,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := sqrtUp256 (FormalYul.u256 x)
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word ret)
      (Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let memPos :=
    ((EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { sqrtUpSharedAfterFreePtr x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_uint256_sqrtUp_of_calldata (x := x) (fuel := 999854)
      (shared := sqrtUpSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := sqrtUpSharedAfterFreePtr_lookup x) (hdata := sqrtUpSharedAfterFreePtr_calldata x)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_sqrtUp_direct (x := x) (fuel := 999463) (shared := sqrtUpSharedAfterFreePtr x)
      (store := Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := sqrtUpSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, yulName_fun_wrap_sqrtUp] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := sqrtUpSharedAfterFreePtr x)
      (store := baseStore) (hlookup := sqrtUpSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, baseStore] at halloc
  have hencode :=
    call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack_direct
      (headStart := memPos) (value := FormalYul.word ret) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by
        simp [memShared, sqrtUpSharedAfterFreePtr_lookup x])
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
      ((sqrtUpSharedAfterFreePtr x).mload (EvmYul.UInt256.ofNat 64)).1 =
        EvmYul.UInt256.ofNat 128 := by
    simpa [FormalYul.word] using sqrtUpSharedAfterFreePtr_mload64 x
  rw [hmload]
  have hretLen :
      EvmYul.UInt256.ofNat 128 + EvmYul.UInt256.ofNat 32 -
          EvmYul.UInt256.ofNat 128 =
        FormalYul.word 32 := by
    decide
  rw [hretLen]
  rw [FormalYul.Preservation.resultWord_evmReturn_mstore_word]
  have hnat :
      (EvmYul.UInt256.ofNat (sqrtUp256 (FormalYul.u256 x))).toNat =
        sqrtUp256 (FormalYul.u256 x) := by
    change FormalYul.wordNat (EvmYul.UInt256.ofNat (sqrtUp256 (FormalYul.u256 x))) =
      sqrtUp256 (FormalYul.u256 x)
    exact (FormalYul.Preservation.wordNat_ofNat (sqrtUp256 (FormalYul.u256 x))).trans
      (u256_eq_of_lt _ (sqrtUp256_lt_word _ (Nat.mod_lt x (by
        unfold WORD_MOD
        exact Nat.two_pow_pos 256))))
  rw [hnat]

private theorem external_fun_wrap_sqrtUp_sqrtUp_calldata_halts_999989
    (x : Nat) (store : EvmYul.Yul.VarStore) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_sqrtUp) (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x) store) =
        .error (.YulHalt state value) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [
    sqrtUpSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_sqrtUp]
  simp only [yulFunction_external_fun_wrap_sqrtUp, yulFunction_external_fun_wrap_sqrtUp_75,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := sqrtUp256 (FormalYul.u256 x)
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word ret)
      (Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let memPos :=
    ((EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { sqrtUpSharedAfterFreePtr x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_uint256_sqrtUp_of_calldata (x := x) (fuel := 999854)
      (shared := sqrtUpSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := sqrtUpSharedAfterFreePtr_lookup x) (hdata := sqrtUpSharedAfterFreePtr_calldata x)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_sqrtUp_direct (x := x) (fuel := 999463) (shared := sqrtUpSharedAfterFreePtr x)
      (store := Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := sqrtUpSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, yulName_fun_wrap_sqrtUp] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := sqrtUpSharedAfterFreePtr x)
      (store := baseStore) (hlookup := sqrtUpSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, baseStore] at halloc
  have hencode :=
    call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack_direct
      (headStart := memPos) (value := FormalYul.word ret) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by
        simp [memShared, sqrtUpSharedAfterFreePtr_lookup x])
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

private theorem external_fun_wrap_sqrt_dispatcher_state_result (x : Nat) :
    ((match
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_sqrt) (.some yulContract)
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_sqrt ++ FormalYul.encodeWords [x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
          (Finmap.insert "selector"
            (EvmYul.UInt256.shiftRight
              (EvmYul.State.calldataload
                (EvmYul.Yul.State.Ok
                  (EvmYul.SharedState.mk
                    (FormalYul.sharedFor yulContract
                      (selector_sqrt ++ FormalYul.encodeWords [x])).toState
                    ((FormalYul.sharedFor yulContract
                      (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
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
      .ok (floorSqrt (FormalYul.u256 x)) := by
  rw [sharedFor_inherited_mstore_mk_eq_sqrtSharedAfterFreePtr_raw]
  exact external_fun_wrap_sqrt_sqrt_calldata_result_999989 (x := x)
    (store := Finmap.insert "selector"
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok (sqrtSharedAfterFreePtr x)
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224))
      (Inhabited.default : EvmYul.Yul.VarStore))

private theorem external_fun_wrap_sqrt_dispatcher_state_halts (x : Nat) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_sqrt) (.some yulContract)
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_sqrt ++ FormalYul.encodeWords [x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
          (Finmap.insert "selector"
            (EvmYul.UInt256.shiftRight
              (EvmYul.State.calldataload
                (EvmYul.Yul.State.Ok
                  (EvmYul.SharedState.mk
                    (FormalYul.sharedFor yulContract
                      (selector_sqrt ++ FormalYul.encodeWords [x])).toState
                    ((FormalYul.sharedFor yulContract
                      (selector_sqrt ++ FormalYul.encodeWords [x])).mstore
                        (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
                  (Inhabited.default : EvmYul.Yul.VarStore)).toState
                (EvmYul.UInt256.ofNat 0))
              (EvmYul.UInt256.ofNat 224))
            (Inhabited.default : EvmYul.Yul.VarStore))) =
        .error (.YulHalt state value) := by
  rw [sharedFor_inherited_mstore_mk_eq_sqrtSharedAfterFreePtr_raw]
  exact external_fun_wrap_sqrt_sqrt_calldata_halts_999989 (x := x)
    (store := Finmap.insert "selector"
        (EvmYul.UInt256.shiftRight
          (EvmYul.State.calldataload
            (EvmYul.Yul.State.Ok (sqrtSharedAfterFreePtr x)
              (Inhabited.default : EvmYul.Yul.VarStore)).toState
            (EvmYul.UInt256.ofNat 0))
          (EvmYul.UInt256.ofNat 224))
        (Inhabited.default : EvmYul.Yul.VarStore))

private theorem dispatcherReturn_sqrtUp
    (x : Nat) (haltState : EvmYul.Yul.State) (haltValue : EvmYul.Literal)
    (hhalt :
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_sqrtUp) (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x)
          (Finmap.insert "selector" (FormalYul.word 1707723681)
            (Inhabited.default : EvmYul.Yul.VarStore))) =
        .error (.YulHalt haltState haltValue)) :
    FormalYul.Preservation.DispatcherReturn yulContract
      (FormalYul.calldata selector_sqrtUp [x]) 999998 (FormalYul.returnOf haltState) := by
  let start := FormalYul.stateFor yulContract (FormalYul.calldata selector_sqrtUp [x])
  let afterFreePtr : EvmYul.Yul.State :=
    EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x)
      (Inhabited.default : EvmYul.Yul.VarStore)
  let afterSelector : EvmYul.Yul.State :=
    EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x)
      (Finmap.insert "selector" (FormalYul.word 1707723681)
        (Inhabited.default : EvmYul.Yul.VarStore))
  apply FormalYul.Preservation.dispatcherReturn_of_execReturn
    (hdispatcher := yulContract_dispatcher)
  simpa [start, afterFreePtr, afterSelector, yulDispatcher, FormalYul.calldata,
      yulName_external_fun_wrap_sqrtUp] using
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
        [(FormalYul.word 1529414794,
            [EvmYul.Yul.Ast.Stmt.ExprStmtCall
              (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_sqrt) [])]),
          (FormalYul.word 1707723681,
            [EvmYul.Yul.Ast.Stmt.ExprStmtCall
              (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_sqrtUp) [])])])
      (defaultStmts := [])
      (fn := yulName_external_fun_wrap_sqrtUp)
      (code := .some yulContract)
      (start := start)
      (afterFirst := afterFreePtr)
      (branchStart := afterFreePtr)
      (afterLet := afterSelector)
      (switchStart := afterSelector)
      (condValue := FormalYul.word 1)
      (selector := FormalYul.word 1707723681)
      (result := FormalYul.returnOf haltState)
      (hfirst := by
        simp +decide [start, afterFreePtr, FormalYul.stateFor, FormalYul.calldata,

          EvmYul.Yul.execPrimCall.eq_def,
          EvmYul.Yul.reverse', EvmYul.Yul.cons',
          EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,

          EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,


          EvmYul.Yul.State.toMachineState,




          sharedFor_inherited_mstore_mk_eq_sqrtUpSharedAfterFreePtr_raw])
      (hcond := by
        simp +decide [afterFreePtr,
          EvmYul.Yul.evalPrimCall.eq_def,
          EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
          EvmYul.Yul.evalTail.eq_def,
          EvmYul.Yul.State.executionEnv, FormalYul.word,
          sqrtUpSharedAfterFreePtr_calldata, sqrtUp_calldata_size])
      (hcondNe := by decide)
      (hlet := by
        have hselector :
            ((EvmYul.Yul.State.Ok (sqrtUpSharedAfterFreePtr x)
                (Inhabited.default : EvmYul.Yul.VarStore)).toState.calldataload
                (EvmYul.UInt256.ofNat 0)).shiftRight
              (EvmYul.UInt256.ofNat 224) =
              EvmYul.UInt256.ofNat 1707723681 := by
          simpa [FormalYul.word] using sqrtUp_selector_afterFreePtr x
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

theorem run_sqrt_floor_evm_eq_floorSqrt (x : Nat) :
    run_sqrt_floor_evm x = .ok (floorSqrt (FormalYul.u256 x)) := by
  obtain ⟨haltState, _haltValue, hhalt⟩ :=
    external_fun_wrap_sqrt_dispatcher_state_halts x
  have hresult := external_fun_wrap_sqrt_dispatcher_state_result x
  rw [hhalt] at hresult
  have hReturn :
      FormalYul.Preservation.DispatcherReturn yulContract
        (FormalYul.calldata selector_sqrt [x]) 999998 (FormalYul.returnOf haltState) := by
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
    rw [selectSwitchCase_sqrt_sharedFor_mk_raw x]
    simp +decide [hhalt, EvmYul.Yul.exec.eq_def,
      EvmYul.Yul.execCall.eq_def,

      EvmYul.Yul.reverse', EvmYul.Yul.multifill',









      ]
  unfold run_sqrt_floor_evm run_sqrt_evm
  exact FormalYul.Preservation.callWord_ok_of_dispatcherReturn_result_1000000
    (contract := yulContract) (selector := selector_sqrt) (args := [x])
    (hReturn := hReturn) (by simpa using hresult)

theorem run_sqrt_floor_evm_eq_natSqrt (x : Nat) :
    run_sqrt_floor_evm x = .ok (natSqrt (FormalYul.u256 x)) := by
  rw [run_sqrt_floor_evm_eq_floorSqrt]
  rw [floorSqrt_eq_natSqrt_u256]
  simpa [FormalYul.u256, FormalYul.WORD_MOD] using Nat.mod_lt x (Nat.two_pow_pos 256)

theorem run_sqrt_up_evm_eq_sqrtUp256 (x : Nat) :
    run_sqrt_up_evm x = .ok (sqrtUp256 (FormalYul.u256 x)) := by
  let selectorStore :=
    Finmap.insert "selector" (FormalYul.word 1707723681)
      (Inhabited.default : EvmYul.Yul.VarStore)
  obtain ⟨haltState, haltValue, hhalt⟩ :=
    external_fun_wrap_sqrtUp_sqrtUp_calldata_halts_999989 (x := x)
      (store := selectorStore)
  have hresult :=
    external_fun_wrap_sqrtUp_sqrtUp_calldata_result_999989 (x := x)
      (store := selectorStore)
  rw [hhalt] at hresult
  have hReturn :
      FormalYul.Preservation.DispatcherReturn yulContract
        (FormalYul.calldata selector_sqrtUp [x]) 999998 (FormalYul.returnOf haltState) :=
    dispatcherReturn_sqrtUp x haltState haltValue (by
      simpa [selectorStore] using hhalt)
  unfold run_sqrt_up_evm
  exact FormalYul.Preservation.callWord_ok_of_dispatcherReturn_result_1000000
    (contract := yulContract) (selector := selector_sqrtUp) (args := [x])
    (hReturn := hReturn) (by simpa using hresult)

end SqrtYul
