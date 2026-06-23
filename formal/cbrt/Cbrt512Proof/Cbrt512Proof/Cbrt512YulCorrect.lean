import Cbrt512Proof.Cbrt512YulProof
import Cbrt512Proof.Cbrt512Correct
import CbrtProof.CbrtEvmMath

set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024
set_option linter.style.nameCheck false

namespace Cbrt512Yul

open FormalYul
open CbrtEvmMath

private theorem call_zero_value_for_split_t_uint256_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
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

private theorem call_on_checkpoint
    (fuel extra : Nat) (args : List EvmYul.Literal)
    (fn : Option EvmYul.Yul.Ast.YulFunctionName)
    (code : Option EvmYul.Yul.Ast.YulContract)
    (jump : EvmYul.Yul.Jump) :
    EvmYul.Yul.call (fuel + (extra + 1)) args fn code (EvmYul.Yul.State.Checkpoint jump) =
      .ok (EvmYul.Yul.State.Checkpoint jump, [({ val := 0 } : EvmYul.UInt256)]) := by
  rw [show fuel + (extra + 1) = Nat.succ (fuel + extra) by omega]
  simp [EvmYul.Yul.call.eq_def]

private theorem call_zero_value_for_split_t_userDefinedValueType_uint512_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) []
      (.some "zero_value_for_split_t_userDefinedValueType$_uint512_$113")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions,
    lookup_zero_value_for_split_t_userDefinedValueType__uint512__113]
  simp only [yulFunction_zero_value_for_split_t_userDefinedValueType__uint512__113,
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

private theorem call_cleanup_t_uint256_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v] (.some "cleanup_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_cleanup_t_uint256]
  simp only [yulFunction_cleanup_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert]

private theorem call_cleanup_t_rational_0_by_1_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v] (.some "cleanup_t_rational_0_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_cleanup_t_rational_0_by_1]
  simp only [yulFunction_cleanup_t_rational_0_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert]

private theorem call_identity_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v] (.some "identity")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_identity]
  simp only [yulFunction_identity,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert]

private theorem call_convert_t_rational_0_by_1_to_t_uint256_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100) [FormalYul.word value]
      (.some "convert_t_rational_0_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word value]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_convert_t_rational_0_by_1_to_t_uint256]
  simp only [yulFunction_convert_t_rational_0_by_1_to_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.exec.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    FormalYul.word]
  rw [call_cleanup_t_rational_0_by_1_direct
    (v := EvmYul.UInt256.ofNat value) (fuel := fuel + 72)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat value)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide
  rw [call_identity_direct
    (v := EvmYul.UInt256.ofNat value) (fuel := fuel + 74)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat value)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide
  rw [call_cleanup_t_uint256_direct
    (v := EvmYul.UInt256.ofNat value) (fuel := fuel + 76)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat value)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide

private theorem call_cleanup_t_uint8_direct
    (v fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 40) [FormalYul.word v] (.some "cleanup_t_uint8")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmAnd v 255)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_cleanup_t_uint8]
  simp only [yulFunction_cleanup_t_uint8,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_and, FormalYul.Preservation.wordNat_ofNat]
  simp [FormalYul.Preservation.evmAnd_u256_left]

private theorem call_cleanup_t_rational_1_by_1_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v] (.some "cleanup_t_rational_1_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_cleanup_t_rational_1_by_1]
  simp only [yulFunction_cleanup_t_rational_1_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert]

private theorem call_cleanup_t_rational_2_by_1_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v] (.some "cleanup_t_rational_2_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_cleanup_t_rational_2_by_1]
  simp only [yulFunction_cleanup_t_rational_2_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert]

private theorem call_cleanup_t_rational_3_by_1_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v] (.some "cleanup_t_rational_3_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_cleanup_t_rational_3_by_1]
  simp only [yulFunction_cleanup_t_rational_3_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert]

private theorem call_cleanup_t_rational_86_by_1_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v] (.some "cleanup_t_rational_86_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_cleanup_t_rational_86_by_1]
  simp only [yulFunction_cleanup_t_rational_86_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert]

private theorem call_cleanup_t_rational_22141993662453218394297550_by_1_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v]
      (.some "cleanup_t_rational_22141993662453218394297550_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions,
    lookup_cleanup_t_rational_22141993662453218394297550_by_1]
  simp only [yulFunction_cleanup_t_rational_22141993662453218394297550_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert]

private theorem call_cleanup_t_rational_77371252455336267181195263_by_1_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v]
      (.some "cleanup_t_rational_77371252455336267181195263_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions,
    lookup_cleanup_t_rational_77371252455336267181195263_by_1]
  simp only [yulFunction_cleanup_t_rational_77371252455336267181195263_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert]

private theorem call_convert_t_rational_3_by_1_to_t_uint256_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100) [FormalYul.word value]
      (.some "convert_t_rational_3_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word value]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_convert_t_rational_3_by_1_to_t_uint256]
  simp only [yulFunction_convert_t_rational_3_by_1_to_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.exec.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    FormalYul.word]
  rw [call_cleanup_t_rational_3_by_1_direct
    (v := EvmYul.UInt256.ofNat value) (fuel := fuel + 72)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat value)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide
  rw [call_identity_direct
    (v := EvmYul.UInt256.ofNat value) (fuel := fuel + 74)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat value)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide
  rw [call_cleanup_t_uint256_direct
    (v := EvmYul.UInt256.ofNat value) (fuel := fuel + 76)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat value)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide

private theorem call_convert_t_rational_to_t_uint8_direct
    (name : EvmYul.Yul.Ast.YulFunctionName)
    (cleanupName : EvmYul.Yul.Ast.YulFunctionName)
    (cleanupFun convertFun : EvmYul.Yul.Ast.FunctionDefinition)
    (lookupCleanup :
      yulFunctions.lookup cleanupName = some cleanupFun)
    (lookupConvert :
      yulFunctions.lookup name = some convertFun)
    (hconvert :
      convertFun =
        EvmYul.Yul.Ast.FunctionDefinition.Def ["value"] ["converted"]
          [EvmYul.Yul.Ast.Stmt.Let ["converted"]
            (some
              (EvmYul.Yul.Ast.Expr.Call (Sum.inr "cleanup_t_uint8")
                [EvmYul.Yul.Ast.Expr.Call (Sum.inr "identity")
                  [EvmYul.Yul.Ast.Expr.Call (Sum.inr cleanupName)
                    [EvmYul.Yul.Ast.Expr.Var "value"]]]))])
    (hcleanup :
      cleanupFun =
        EvmYul.Yul.Ast.FunctionDefinition.Def ["value"] ["cleaned"]
          [EvmYul.Yul.Ast.Stmt.Let ["cleaned"] (some (EvmYul.Yul.Ast.Expr.Var "value"))])
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 120) [FormalYul.word value] (.some name)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmAnd value 255)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookupConvert]
  rw [hconvert]
  simp only [
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.exec.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    FormalYul.word]
  have hcleanupCall :
      EvmYul.Yul.call (fuel + 112) [EvmYul.UInt256.ofNat value] (.some cleanupName)
        (.some yulContract)
        (EvmYul.Yul.State.Ok shared
          (Finmap.insert "value" (EvmYul.UInt256.ofNat value)
            (Inhabited.default : EvmYul.Yul.VarStore))) =
      .ok (EvmYul.Yul.State.Ok shared
          (Finmap.insert "value" (EvmYul.UInt256.ofNat value)
            (Inhabited.default : EvmYul.Yul.VarStore)),
        [EvmYul.UInt256.ofNat value]) := by
    rw [EvmYul.Yul.call.eq_def]
    simp only [hlookup, Option.getD_some, yulContract_functions, lookupCleanup]
    rw [hcleanup]
    simp only [
      FormalYul.Preservation.functionDefinition_params_def,
      FormalYul.Preservation.functionDefinition_rets_def,
      FormalYul.Preservation.functionDefinition_body_def,
      EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
    simp +decide [
      EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
      EvmYul.Yul.State.reviveJump,
      EvmYul.Yul.State.overwrite?,
      Finmap.lookup_insert]
  rw [hcleanupCall]
  simp +decide
  rw [call_identity_direct
    (v := EvmYul.UInt256.ofNat value) (fuel := fuel + 94)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat value)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide
  have hCleanup8 :
      EvmYul.Yul.call (fuel + 116) [EvmYul.UInt256.ofNat value] (.some "cleanup_t_uint8")
        (.some yulContract)
        (EvmYul.Yul.State.Ok shared
          (Finmap.insert "value" (EvmYul.UInt256.ofNat value)
            (Inhabited.default : EvmYul.Yul.VarStore))) =
      .ok (EvmYul.Yul.State.Ok shared
          (Finmap.insert "value" (EvmYul.UInt256.ofNat value)
            (Inhabited.default : EvmYul.Yul.VarStore)),
        [EvmYul.UInt256.ofNat (FormalYul.evmAnd value 255)]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_cleanup_t_uint8_direct
        (v := value) (fuel := fuel + 76) (shared := shared)
        (store := Finmap.insert "value" (EvmYul.UInt256.ofNat value)
          (Inhabited.default : EvmYul.Yul.VarStore))
        (hlookup := hlookup)
  rw [hCleanup8]
  simp +decide

private theorem call_convert_t_rational_2_by_1_to_t_uint8_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 120) [FormalYul.word value]
      (.some "convert_t_rational_2_by_1_to_t_uint8")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmAnd value 255)]) := by
  exact call_convert_t_rational_to_t_uint8_direct
    (name := "convert_t_rational_2_by_1_to_t_uint8")
    (cleanupName := "cleanup_t_rational_2_by_1")
    (cleanupFun := yulFunction_cleanup_t_rational_2_by_1)
    (convertFun := yulFunction_convert_t_rational_2_by_1_to_t_uint8)
    (lookupCleanup := lookup_cleanup_t_rational_2_by_1)
    (lookupConvert := lookup_convert_t_rational_2_by_1_to_t_uint8)
    (hconvert := rfl) (hcleanup := rfl)
    (value := value) (fuel := fuel) (shared := shared) (store := store)
    (hlookup := hlookup)

private theorem call_convert_t_rational_86_by_1_to_t_uint8_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 120) [FormalYul.word value]
      (.some "convert_t_rational_86_by_1_to_t_uint8")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmAnd value 255)]) := by
  exact call_convert_t_rational_to_t_uint8_direct
    (name := "convert_t_rational_86_by_1_to_t_uint8")
    (cleanupName := "cleanup_t_rational_86_by_1")
    (cleanupFun := yulFunction_cleanup_t_rational_86_by_1)
    (convertFun := yulFunction_convert_t_rational_86_by_1_to_t_uint8)
    (lookupCleanup := lookup_cleanup_t_rational_86_by_1)
    (lookupConvert := lookup_convert_t_rational_86_by_1_to_t_uint8)
    (hconvert := rfl) (hcleanup := rfl)
    (value := value) (fuel := fuel) (shared := shared) (store := store)
    (hlookup := hlookup)

private theorem call_convert_t_rational_to_t_uint256_direct
    (name : EvmYul.Yul.Ast.YulFunctionName)
    (cleanupName : EvmYul.Yul.Ast.YulFunctionName)
    (cleanupFun convertFun : EvmYul.Yul.Ast.FunctionDefinition)
    (lookupCleanup :
      yulFunctions.lookup cleanupName = some cleanupFun)
    (lookupConvert :
      yulFunctions.lookup name = some convertFun)
    (hconvert :
      convertFun =
        EvmYul.Yul.Ast.FunctionDefinition.Def ["value"] ["converted"]
          [EvmYul.Yul.Ast.Stmt.Let ["converted"]
            (some
              (EvmYul.Yul.Ast.Expr.Call (Sum.inr "cleanup_t_uint256")
                [EvmYul.Yul.Ast.Expr.Call (Sum.inr "identity")
                  [EvmYul.Yul.Ast.Expr.Call (Sum.inr cleanupName)
                    [EvmYul.Yul.Ast.Expr.Var "value"]]]))])
    (hcleanup :
      cleanupFun =
        EvmYul.Yul.Ast.FunctionDefinition.Def ["value"] ["cleaned"]
          [EvmYul.Yul.Ast.Stmt.Let ["cleaned"] (some (EvmYul.Yul.Ast.Expr.Var "value"))])
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100) [FormalYul.word value] (.some name)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word value]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookupConvert]
  rw [hconvert]
  simp only [
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.exec.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    FormalYul.word]
  have hcleanupCall :
      EvmYul.Yul.call (fuel + 92) [EvmYul.UInt256.ofNat value] (.some cleanupName)
        (.some yulContract)
        (EvmYul.Yul.State.Ok shared
          (Finmap.insert "value" (EvmYul.UInt256.ofNat value)
            (Inhabited.default : EvmYul.Yul.VarStore))) =
      .ok (EvmYul.Yul.State.Ok shared
          (Finmap.insert "value" (EvmYul.UInt256.ofNat value)
            (Inhabited.default : EvmYul.Yul.VarStore)),
        [EvmYul.UInt256.ofNat value]) := by
    rw [EvmYul.Yul.call.eq_def]
    simp only [hlookup, Option.getD_some, yulContract_functions, lookupCleanup]
    rw [hcleanup]
    simp only [
      FormalYul.Preservation.functionDefinition_params_def,
      FormalYul.Preservation.functionDefinition_rets_def,
      FormalYul.Preservation.functionDefinition_body_def,
      EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
    simp +decide [
      EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
      EvmYul.Yul.State.reviveJump,
      EvmYul.Yul.State.overwrite?,
      Finmap.lookup_insert]
  rw [hcleanupCall]
  simp +decide
  rw [call_identity_direct
    (v := EvmYul.UInt256.ofNat value) (fuel := fuel + 74)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat value)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide
  rw [call_cleanup_t_uint256_direct
    (v := EvmYul.UInt256.ofNat value) (fuel := fuel + 76)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat value)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide

private theorem call_convert_t_rational_1_by_1_to_t_uint256_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100) [FormalYul.word value]
      (.some "convert_t_rational_1_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word value]) := by
  exact call_convert_t_rational_to_t_uint256_direct
    (name := "convert_t_rational_1_by_1_to_t_uint256")
    (cleanupName := "cleanup_t_rational_1_by_1")
    (cleanupFun := yulFunction_cleanup_t_rational_1_by_1)
    (convertFun := yulFunction_convert_t_rational_1_by_1_to_t_uint256)
    (lookupCleanup := lookup_cleanup_t_rational_1_by_1)
    (lookupConvert := lookup_convert_t_rational_1_by_1_to_t_uint256)
    (hconvert := rfl) (hcleanup := rfl)
    (value := value) (fuel := fuel) (shared := shared) (store := store)
    (hlookup := hlookup)

private theorem call_convert_t_rational_22141993662453218394297550_by_1_to_t_uint256_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100) [FormalYul.word value]
      (.some "convert_t_rational_22141993662453218394297550_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word value]) := by
  exact call_convert_t_rational_to_t_uint256_direct
    (name := "convert_t_rational_22141993662453218394297550_by_1_to_t_uint256")
    (cleanupName := "cleanup_t_rational_22141993662453218394297550_by_1")
    (cleanupFun := yulFunction_cleanup_t_rational_22141993662453218394297550_by_1)
    (convertFun := yulFunction_convert_t_rational_22141993662453218394297550_by_1_to_t_uint256)
    (lookupCleanup := lookup_cleanup_t_rational_22141993662453218394297550_by_1)
    (lookupConvert := lookup_convert_t_rational_22141993662453218394297550_by_1_to_t_uint256)
    (hconvert := rfl) (hcleanup := rfl)
    (value := value) (fuel := fuel) (shared := shared) (store := store)
    (hlookup := hlookup)

private theorem call_convert_t_rational_77371252455336267181195263_by_1_to_t_uint256_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100) [FormalYul.word value]
      (.some "convert_t_rational_77371252455336267181195263_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word value]) := by
  exact call_convert_t_rational_to_t_uint256_direct
    (name := "convert_t_rational_77371252455336267181195263_by_1_to_t_uint256")
    (cleanupName := "cleanup_t_rational_77371252455336267181195263_by_1")
    (cleanupFun := yulFunction_cleanup_t_rational_77371252455336267181195263_by_1)
    (convertFun := yulFunction_convert_t_rational_77371252455336267181195263_by_1_to_t_uint256)
    (lookupCleanup := lookup_cleanup_t_rational_77371252455336267181195263_by_1)
    (lookupConvert := lookup_convert_t_rational_77371252455336267181195263_by_1_to_t_uint256)
    (hconvert := rfl) (hcleanup := rfl)
    (value := value) (fuel := fuel) (shared := shared) (store := store)
    (hlookup := hlookup)

private theorem call_zero_value_for_split_t_bool_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [] (.some "zero_value_for_split_t_bool")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_zero_value_for_split_t_bool]
  simp only [yulFunction_zero_value_for_split_t_bool,
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

private theorem call_fun_clz_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [FormalYul.word x] (.some yulName_fun_clz)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmClz x)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_clz]
  simp only [yulFunction_fun_clz, yulFunction_fun_clz_6141,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 36)
      (shared := shared)
      (store := Finmap.insert "var_x_6134" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_clz]
  simp [FormalYul.Preservation.evmClz_u256]

private theorem call_fun_unsafeDiv_direct
    (numerator denominator fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [FormalYul.word numerator, FormalYul.word denominator]
      (.some "fun_unsafeDiv_5899") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmDiv numerator denominator)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_unsafeDiv_5899]
  simp only [yulFunction_fun_unsafeDiv_5899,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 36)
      (shared := shared)
      (store := Finmap.insert "var_numerator_5890" (EvmYul.UInt256.ofNat numerator)
        (Finmap.insert "var_denominator_5892" (EvmYul.UInt256.ofNat denominator)
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_div]
  simp [FormalYul.Preservation.evmDiv_u256_left, FormalYul.Preservation.evmDiv_u256_right]

private theorem call_fun_unsafeDec_direct
    (x b fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [FormalYul.word x, FormalYul.word b]
      (.some "fun_unsafeDec_5854") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmSub x b)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_unsafeDec_5854]
  simp only [yulFunction_fun_unsafeDec_5854,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 36)
      (shared := shared)
      (store := Finmap.insert "var_x_5845" (EvmYul.UInt256.ofNat x)
        (Finmap.insert "var_b_5847" (EvmYul.UInt256.ofNat b)
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_sub]
  simp [FormalYul.Preservation.evmSub_u256_left, FormalYul.Preservation.evmSub_u256_right]

private theorem call_fun_unsafeDec_word_direct
    (x fuel : Nat) (b : EvmYul.UInt256)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [FormalYul.word x, b]
      (.some "fun_unsafeDec_5854") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmSub x (FormalYul.wordNat b))]) := by
  have hbmod : FormalYul.u256 (FormalYul.wordNat b) = FormalYul.wordNat b := by
    cases b with
    | mk bv =>
      cases bv with
      | mk bv hbv =>
        have hbv' : bv < FormalYul.WORD_MOD := by
          simpa [FormalYul.WORD_MOD, EvmYul.UInt256.size] using hbv
        change bv % FormalYul.WORD_MOD = bv
        exact Nat.mod_eq_of_lt hbv'
  have hb : b = FormalYul.word (FormalYul.wordNat b) := by
    apply FormalYul.Preservation.eq_of_wordNat_eq
    simp [FormalYul.Preservation.wordNat_word, hbmod]
  have hcall := call_fun_unsafeDec_direct
    (x := x) (b := FormalYul.wordNat b) (fuel := fuel)
    (shared := shared) (store := store) (hlookup := hlookup)
  rwa [← hb] at hcall

private theorem call_fun_unsafeInc_direct
    (x b fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [FormalYul.word x, FormalYul.word b]
      (.some "fun_unsafeInc_5817") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmAdd x b)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_unsafeInc_5817]
  simp only [yulFunction_fun_unsafeInc_5817,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 36)
      (shared := shared)
      (store := Finmap.insert "var_x_5808" (EvmYul.UInt256.ofNat x)
        (Finmap.insert "var_b_5810" (EvmYul.UInt256.ofNat b)
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_add]
  simp [FormalYul.Preservation.evmAdd_u256_left, FormalYul.Preservation.evmAdd_u256_right]

private theorem call_fun_and_direct
    (a b fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [FormalYul.word a, FormalYul.word b]
      (.some "fun_and_5596") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmAnd a b)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_and_5596]
  simp only [yulFunction_fun_and_5596,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    call_zero_value_for_split_t_bool_direct (fuel := fuel) (extra := 36)
      (shared := shared)
      (store := Finmap.insert "var_a_5587" (EvmYul.UInt256.ofNat a)
        (Finmap.insert "var_b_5589" (EvmYul.UInt256.ofNat b)
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_and]
  simp [FormalYul.Preservation.evmAnd_u256_left, FormalYul.Preservation.evmAnd_u256_right]

private theorem call_fun_or_direct
    (a b fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [FormalYul.word a, FormalYul.word b]
      (.some "fun_or_5585") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmOr a b)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_or_5585]
  simp only [yulFunction_fun_or_5585,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    call_zero_value_for_split_t_bool_direct (fuel := fuel) (extra := 36)
      (shared := shared)
      (store := Finmap.insert "var_a_5576" (EvmYul.UInt256.ofNat a)
        (Finmap.insert "var_b_5578" (EvmYul.UInt256.ofNat b)
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_or]
  simp [FormalYul.Preservation.evmOr_u256_left, FormalYul.Preservation.evmOr_u256_right]

private theorem call_wrapping_add_t_uint256_direct
    (x y fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 80) [FormalYul.word x, FormalYul.word y]
      (.some "wrapping_add_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmAdd x y)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_wrapping_add_t_uint256]
  simp only [yulFunction_wrapping_add_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcleanup :=
    call_cleanup_t_uint256_direct
      (v := EvmYul.UInt256.ofNat x + EvmYul.UInt256.ofNat y)
      (fuel := fuel + 56) (shared := shared)
      (store := Finmap.insert "x" (EvmYul.UInt256.ofNat x)
        (Finmap.insert "y" (EvmYul.UInt256.ofNat y)
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup)
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hcleanup]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_add]
  simp [FormalYul.Preservation.evmAdd_u256_left, FormalYul.Preservation.evmAdd_u256_right]

private theorem call_wrapping_add_t_uint256_raw_direct
    (x y fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 80)) [FormalYul.word x, FormalYul.word y]
      (.some "wrapping_add_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmAdd x y)]) := by
  rw [show fuel + (extra + 80) = (fuel + extra) + 80 by omega]
  exact call_wrapping_add_t_uint256_direct
    (x := x) (y := y) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_wrapping_sub_t_uint256_direct
    (x y fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 80) [FormalYul.word x, FormalYul.word y]
      (.some "wrapping_sub_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmSub x y)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_wrapping_sub_t_uint256]
  simp only [yulFunction_wrapping_sub_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcleanup :=
    call_cleanup_t_uint256_direct
      (v := EvmYul.UInt256.ofNat x - EvmYul.UInt256.ofNat y)
      (fuel := fuel + 56) (shared := shared)
      (store := Finmap.insert "x" (EvmYul.UInt256.ofNat x)
        (Finmap.insert "y" (EvmYul.UInt256.ofNat y)
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup)
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hcleanup]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_sub]
  simp [FormalYul.Preservation.evmSub_u256_left, FormalYul.Preservation.evmSub_u256_right]

private theorem call_wrapping_sub_t_uint256_raw_direct
    (x y fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 80)) [FormalYul.word x, FormalYul.word y]
      (.some "wrapping_sub_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmSub x y)]) := by
  rw [show fuel + (extra + 80) = (fuel + extra) + 80 by omega]
  exact call_wrapping_sub_t_uint256_direct
    (x := x) (y := y) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_wrapping_div_t_uint256_by_three_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 120) [FormalYul.word x, FormalYul.word 3]
      (.some "wrapping_div_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmDiv x 3)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_wrapping_div_t_uint256]
  simp only [yulFunction_wrapping_div_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let baseStore : EvmYul.Yul.VarStore :=
    Finmap.insert "x" (EvmYul.UInt256.ofNat x)
      (Finmap.insert "y" (EvmYul.UInt256.ofNat 3)
        (Inhabited.default : EvmYul.Yul.VarStore))
  have hcleanupX :
      EvmYul.Yul.call (fuel + 116) [EvmYul.UInt256.ofNat x]
        (.some "cleanup_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok shared baseStore) =
      .ok (EvmYul.Yul.State.Ok shared baseStore, [EvmYul.UInt256.ofNat x]) := by
    simpa [baseStore, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_cleanup_t_uint256_direct
        (v := EvmYul.UInt256.ofNat x) (fuel := fuel + 96)
        (shared := shared) (store := baseStore) (hlookup := hlookup)
  have hcleanupY :
      EvmYul.Yul.call (fuel + 115) [EvmYul.UInt256.ofNat 3]
        (.some "cleanup_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok shared baseStore) =
      .ok (EvmYul.Yul.State.Ok shared baseStore, [EvmYul.UInt256.ofNat 3]) := by
    simpa [baseStore, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_cleanup_t_uint256_direct
        (v := EvmYul.UInt256.ofNat 3) (fuel := fuel + 95)
        (shared := shared) (store := baseStore) (hlookup := hlookup)
  simp +decide [baseStore, hcleanupX, hcleanupY,
    EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_div, FormalYul.Preservation.wordNat_ofNat]
  simp [FormalYul.Preservation.evmDiv_u256_left]

private theorem call_wrapping_div_t_uint256_by_three_raw_direct
    (x fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120)) [FormalYul.word x, FormalYul.word 3]
      (.some "wrapping_div_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmDiv x 3)]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  exact call_wrapping_div_t_uint256_by_three_direct
    (x := x) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_wrapping_mul_t_uint256_direct
    (x y fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 80) [FormalYul.word x, FormalYul.word y]
      (.some "wrapping_mul_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmMul x y)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_wrapping_mul_t_uint256]
  simp only [yulFunction_wrapping_mul_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcleanup :=
    call_cleanup_t_uint256_direct
      (v := EvmYul.UInt256.ofNat x * EvmYul.UInt256.ofNat y)
      (fuel := fuel + 56) (shared := shared)
      (store := Finmap.insert "x" (EvmYul.UInt256.ofNat x)
        (Finmap.insert "y" (EvmYul.UInt256.ofNat y)
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup)
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hcleanup]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_mul]
  simp [FormalYul.Preservation.evmMul_u256_left, FormalYul.Preservation.evmMul_u256_right]

private theorem call_wrapping_mul_t_uint256_raw_direct
    (x y fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 80)) [FormalYul.word x, FormalYul.word y]
      (.some "wrapping_mul_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmMul x y)]) := by
  rw [show fuel + (extra + 80) = (fuel + extra) + 80 by omega]
  exact call_wrapping_mul_t_uint256_direct
    (x := x) (y := y) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_shift_right_unsigned_dynamic_direct
    (bits value fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 40) [FormalYul.word bits, FormalYul.word value]
      (.some "shift_right_unsigned_dynamic") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShr bits value)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_shift_right_unsigned_dynamic]
  simp only [yulFunction_shift_right_unsigned_dynamic,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_shiftRight, FormalYul.Preservation.wordNat_ofNat]
  simp [FormalYul.Preservation.evmShr_u256_left, FormalYul.Preservation.evmShr_u256_right]

private theorem call_shift_left_dynamic_direct
    (bits value fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 40) [FormalYul.word bits, FormalYul.word value]
      (.some "shift_left_dynamic") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShl bits value)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_shift_left_dynamic]
  simp only [yulFunction_shift_left_dynamic,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_shiftLeft, FormalYul.Preservation.wordNat_ofNat]
  simp [FormalYul.Preservation.evmShl_u256_left, FormalYul.Preservation.evmShl_u256_right]

private theorem call_shift_right_t_uint256_t_uint8_direct
    (value bits fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100) [FormalYul.word value, FormalYul.word bits]
      (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShr (FormalYul.evmAnd bits 255) value)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_shift_right_t_uint256_t_uint8]
  simp only [yulFunction_shift_right_t_uint256_t_uint8,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let baseStore : EvmYul.Yul.VarStore :=
    Finmap.insert "value" (EvmYul.UInt256.ofNat value)
      (Finmap.insert "bits" (EvmYul.UInt256.ofNat bits)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let bitsStore : EvmYul.Yul.VarStore :=
    Finmap.insert "bits" (EvmYul.UInt256.ofNat (FormalYul.evmAnd bits 255)) baseStore
  have hCleanupBits :
      EvmYul.Yul.call (fuel + 96) [EvmYul.UInt256.ofNat bits]
        (.some "cleanup_t_uint8") (.some yulContract)
        (EvmYul.Yul.State.Ok shared baseStore) =
      .ok (EvmYul.Yul.State.Ok shared baseStore,
        [EvmYul.UInt256.ofNat (FormalYul.evmAnd bits 255)]) := by
    simpa [baseStore, FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_cleanup_t_uint8_direct
        (v := bits) (fuel := fuel + 56) (shared := shared) (store := baseStore)
        (hlookup := hlookup)
  have hCleanupValue :
      EvmYul.Yul.call (fuel + 91) [EvmYul.UInt256.ofNat value]
        (.some "cleanup_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok shared bitsStore) =
      .ok (EvmYul.Yul.State.Ok shared bitsStore, [EvmYul.UInt256.ofNat value]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_cleanup_t_uint256_direct
        (v := EvmYul.UInt256.ofNat value) (fuel := fuel + 71)
        (shared := shared) (store := bitsStore) (hlookup := hlookup)
  have hShift :
      EvmYul.Yul.call (fuel + 93)
        [EvmYul.UInt256.ofNat (FormalYul.evmAnd bits 255), EvmYul.UInt256.ofNat value]
        (.some "shift_right_unsigned_dynamic") (.some yulContract)
        (EvmYul.Yul.State.Ok shared bitsStore) =
      .ok (EvmYul.Yul.State.Ok shared bitsStore,
        [FormalYul.word (FormalYul.evmShr (FormalYul.evmAnd bits 255) value)]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_shift_right_unsigned_dynamic_direct
        (bits := FormalYul.evmAnd bits 255) (value := value) (fuel := fuel + 53)
        (shared := shared) (store := bitsStore) (hlookup := hlookup)
  have hCleanupResult :
      EvmYul.Yul.call (fuel + 95)
        [EvmYul.UInt256.ofNat (FormalYul.evmShr (FormalYul.evmAnd bits 255) value)]
        (.some "cleanup_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok shared bitsStore) =
      .ok (EvmYul.Yul.State.Ok shared bitsStore,
        [EvmYul.UInt256.ofNat (FormalYul.evmShr (FormalYul.evmAnd bits 255) value)]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_cleanup_t_uint256_direct
        (v := FormalYul.word (FormalYul.evmShr (FormalYul.evmAnd bits 255) value))
        (fuel := fuel + 75) (shared := shared) (store := bitsStore) (hlookup := hlookup)
  simp +decide [baseStore, bitsStore, hCleanupBits, hCleanupValue, hShift, hCleanupResult,
    EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

private theorem call_shift_left_t_uint256_t_uint8_direct
    (value bits fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100) [FormalYul.word value, FormalYul.word bits]
      (.some "shift_left_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShl (FormalYul.evmAnd bits 255) value)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_shift_left_t_uint256_t_uint8]
  simp only [yulFunction_shift_left_t_uint256_t_uint8,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let baseStore : EvmYul.Yul.VarStore :=
    Finmap.insert "value" (EvmYul.UInt256.ofNat value)
      (Finmap.insert "bits" (EvmYul.UInt256.ofNat bits)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let bitsStore : EvmYul.Yul.VarStore :=
    Finmap.insert "bits" (EvmYul.UInt256.ofNat (FormalYul.evmAnd bits 255)) baseStore
  have hCleanupBits :
      EvmYul.Yul.call (fuel + 96) [EvmYul.UInt256.ofNat bits]
        (.some "cleanup_t_uint8") (.some yulContract)
        (EvmYul.Yul.State.Ok shared baseStore) =
      .ok (EvmYul.Yul.State.Ok shared baseStore,
        [EvmYul.UInt256.ofNat (FormalYul.evmAnd bits 255)]) := by
    simpa [baseStore, FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_cleanup_t_uint8_direct
        (v := bits) (fuel := fuel + 56) (shared := shared) (store := baseStore)
        (hlookup := hlookup)
  have hCleanupValue :
      EvmYul.Yul.call (fuel + 91) [EvmYul.UInt256.ofNat value]
        (.some "cleanup_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok shared bitsStore) =
      .ok (EvmYul.Yul.State.Ok shared bitsStore, [EvmYul.UInt256.ofNat value]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_cleanup_t_uint256_direct
        (v := EvmYul.UInt256.ofNat value) (fuel := fuel + 71)
        (shared := shared) (store := bitsStore) (hlookup := hlookup)
  have hShift :
      EvmYul.Yul.call (fuel + 93)
        [EvmYul.UInt256.ofNat (FormalYul.evmAnd bits 255), EvmYul.UInt256.ofNat value]
        (.some "shift_left_dynamic") (.some yulContract)
        (EvmYul.Yul.State.Ok shared bitsStore) =
      .ok (EvmYul.Yul.State.Ok shared bitsStore,
        [FormalYul.word (FormalYul.evmShl (FormalYul.evmAnd bits 255) value)]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_shift_left_dynamic_direct
        (bits := FormalYul.evmAnd bits 255) (value := value) (fuel := fuel + 53)
        (shared := shared) (store := bitsStore) (hlookup := hlookup)
  have hCleanupResult :
      EvmYul.Yul.call (fuel + 95)
        [EvmYul.UInt256.ofNat (FormalYul.evmShl (FormalYul.evmAnd bits 255) value)]
        (.some "cleanup_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok shared bitsStore) =
      .ok (EvmYul.Yul.State.Ok shared bitsStore,
        [EvmYul.UInt256.ofNat (FormalYul.evmShl (FormalYul.evmAnd bits 255) value)]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_cleanup_t_uint256_direct
        (v := FormalYul.word (FormalYul.evmShl (FormalYul.evmAnd bits 255) value))
        (fuel := fuel + 75) (shared := shared) (store := bitsStore) (hlookup := hlookup)
  simp +decide [baseStore, bitsStore, hCleanupBits, hCleanupValue, hShift, hCleanupResult,
    EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

private theorem call_shift_right_t_uint256_t_uint256_direct
    (value bits fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100) [FormalYul.word value, FormalYul.word bits]
      (.some "shift_right_t_uint256_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShr bits value)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_shift_right_t_uint256_t_uint256]
  simp only [yulFunction_shift_right_t_uint256_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let baseStore : EvmYul.Yul.VarStore :=
    Finmap.insert "value" (EvmYul.UInt256.ofNat value)
      (Finmap.insert "bits" (EvmYul.UInt256.ofNat bits)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let bitsStore : EvmYul.Yul.VarStore :=
    Finmap.insert "bits" (EvmYul.UInt256.ofNat bits) baseStore
  have hCleanupBits :
      EvmYul.Yul.call (fuel + 96) [EvmYul.UInt256.ofNat bits]
        (.some "cleanup_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok shared baseStore) =
      .ok (EvmYul.Yul.State.Ok shared baseStore, [EvmYul.UInt256.ofNat bits]) := by
    simpa [baseStore, FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_cleanup_t_uint256_direct
        (v := EvmYul.UInt256.ofNat bits) (fuel := fuel + 76)
        (shared := shared) (store := baseStore) (hlookup := hlookup)
  have hCleanupValue :
      EvmYul.Yul.call (fuel + 91) [EvmYul.UInt256.ofNat value]
        (.some "cleanup_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok shared bitsStore) =
      .ok (EvmYul.Yul.State.Ok shared bitsStore, [EvmYul.UInt256.ofNat value]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_cleanup_t_uint256_direct
        (v := EvmYul.UInt256.ofNat value) (fuel := fuel + 71)
        (shared := shared) (store := bitsStore) (hlookup := hlookup)
  have hShift :
      EvmYul.Yul.call (fuel + 93) [EvmYul.UInt256.ofNat bits, EvmYul.UInt256.ofNat value]
        (.some "shift_right_unsigned_dynamic") (.some yulContract)
        (EvmYul.Yul.State.Ok shared bitsStore) =
      .ok (EvmYul.Yul.State.Ok shared bitsStore,
        [FormalYul.word (FormalYul.evmShr bits value)]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_shift_right_unsigned_dynamic_direct
        (bits := bits) (value := value) (fuel := fuel + 53)
        (shared := shared) (store := bitsStore) (hlookup := hlookup)
  have hCleanupResult :
      EvmYul.Yul.call (fuel + 95) [EvmYul.UInt256.ofNat (FormalYul.evmShr bits value)]
        (.some "cleanup_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok shared bitsStore) =
      .ok (EvmYul.Yul.State.Ok shared bitsStore,
        [EvmYul.UInt256.ofNat (FormalYul.evmShr bits value)]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_cleanup_t_uint256_direct
        (v := FormalYul.word (FormalYul.evmShr bits value)) (fuel := fuel + 75)
        (shared := shared) (store := bitsStore) (hlookup := hlookup)
  simp +decide [baseStore, bitsStore, hCleanupBits, hCleanupValue, hShift, hCleanupResult,
    EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

private theorem call_fun__shl256_direct
    (xHi xLo s fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100) [FormalYul.word xHi, FormalYul.word xLo, FormalYul.word s]
      (.some yulName_fun__shl256) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShr (FormalYul.evmSub 256 s) xHi),
       FormalYul.word (FormalYul.evmOr (FormalYul.evmShl s xHi)
         (FormalYul.evmShr (FormalYul.evmSub 256 s) xLo)),
       FormalYul.word (FormalYul.evmShl s xLo)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun__shl256]
  simp only [yulFunction_fun__shl256, yulFunction_fun__shl256_3075,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 76)
      (shared := shared)
      (store := Finmap.insert "var_x_hi_3060" (EvmYul.UInt256.ofNat xHi)
        (Finmap.insert "var_x_lo_3062" (EvmYul.UInt256.ofNat xLo)
          (Finmap.insert "var_s_3064" (EvmYul.UInt256.ofNat s)
            (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup),
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 74)
      (shared := shared)
      (store := Finmap.insert "var_r_ex_3067" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "zero_t_uint256_45" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "var_x_hi_3060" (EvmYul.UInt256.ofNat xHi)
            (Finmap.insert "var_x_lo_3062" (EvmYul.UInt256.ofNat xLo)
              (Finmap.insert "var_s_3064" (EvmYul.UInt256.ofNat s)
                (Inhabited.default : EvmYul.Yul.VarStore))))))
      (hlookup := hlookup),
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 72)
      (shared := shared)
      (store := Finmap.insert "var_r_hi_3069" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "zero_t_uint256_46" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "var_r_ex_3067" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "zero_t_uint256_45" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "var_x_hi_3060" (EvmYul.UInt256.ofNat xHi)
                (Finmap.insert "var_x_lo_3062" (EvmYul.UInt256.ofNat xLo)
                  (Finmap.insert "var_s_3064" (EvmYul.UInt256.ofNat s)
                    (Inhabited.default : EvmYul.Yul.VarStore))))))))
      (hlookup := hlookup)]
  constructor
  · apply FormalYul.Preservation.eq_of_wordNat_eq
    simp only [FormalYul.Preservation.wordNat_shiftRight,
      FormalYul.Preservation.wordNat_sub, FormalYul.Preservation.wordNat_ofNat]
    simp [FormalYul.Preservation.evmShr_u256_right,
      FormalYul.Preservation.evmSub_u256_right]
  · constructor
    · apply FormalYul.Preservation.eq_of_wordNat_eq
      simp only [FormalYul.Preservation.wordNat_or,
        FormalYul.Preservation.wordNat_shiftLeft,
        FormalYul.Preservation.wordNat_shiftRight, FormalYul.Preservation.wordNat_sub,
        FormalYul.Preservation.wordNat_ofNat]
      simp [FormalYul.Preservation.evmShl_u256_left,
        FormalYul.Preservation.evmShl_u256_right,
        FormalYul.Preservation.evmShr_u256_right,
        FormalYul.Preservation.evmSub_u256_right]
    · apply FormalYul.Preservation.eq_of_wordNat_eq
      simp only [FormalYul.Preservation.wordNat_shiftLeft]
      simp [FormalYul.Preservation.evmShl_u256_left,
        FormalYul.Preservation.evmShl_u256_right]

private theorem call_fun__cbrt_newtonRaphsonStep_direct
    (x r fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 300) [FormalYul.word x, FormalYul.word r]
      (.some yulName_fun__cbrt_newtonRaphsonStep) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word
        (FormalYul.evmDiv
          (FormalYul.evmAdd (FormalYul.evmAdd
            (FormalYul.evmDiv x (FormalYul.evmMul r r)) r) r) 3)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__cbrt_newtonRaphsonStep]
  simp only [yulFunction_fun__cbrt_newtonRaphsonStep,
    yulFunction_fun__cbrt_newtonRaphsonStep_4694,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let paramStore : EvmYul.Yul.VarStore :=
    Finmap.insert "var_x_4671" (EvmYul.UInt256.ofNat x)
      (Finmap.insert "var_r_4673" (EvmYul.UInt256.ofNat r)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let zeroStore : EvmYul.Yul.VarStore :=
    Finmap.insert "var__4676" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "zero_t_uint256_110" (EvmYul.UInt256.ofNat 0) paramStore)
  have hzero :
      EvmYul.Yul.call (fuel + 296) [] (.some "zero_value_for_split_t_uint256")
        (.some yulContract) (EvmYul.Yul.State.Ok shared paramStore) =
      .ok (EvmYul.Yul.State.Ok shared paramStore, [FormalYul.word 0]) := by
    simpa [paramStore, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_zero_value_for_split_t_uint256_direct
        (fuel := fuel) (extra := 276) (shared := shared) (store := paramStore)
        (hlookup := hlookup)
  let mulStore : EvmYul.Yul.VarStore :=
    Finmap.insert "expr_4681" (EvmYul.UInt256.ofNat r)
      (Finmap.insert "_113" (EvmYul.UInt256.ofNat r)
        (Finmap.insert "expr_4680" (EvmYul.UInt256.ofNat r)
          (Finmap.insert "_112" (EvmYul.UInt256.ofNat r)
            (Finmap.insert "expr_4679_self" (EvmYul.UInt256.ofNat x)
              (Finmap.insert "expr_4678" (EvmYul.UInt256.ofNat x)
                (Finmap.insert "_111" (EvmYul.UInt256.ofNat x) zeroStore))))))
  let rr := FormalYul.evmMul r r
  have hmul :
      EvmYul.Yul.call (fuel + 287) [EvmYul.UInt256.ofNat r, EvmYul.UInt256.ofNat r]
        (.some "wrapping_mul_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok shared mulStore) =
      .ok (EvmYul.Yul.State.Ok shared mulStore, [EvmYul.UInt256.ofNat rr]) := by
    simpa [mulStore, rr, FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_wrapping_mul_t_uint256_direct
        (x := r) (y := r) (fuel := fuel + 207)
        (shared := shared) (store := mulStore) (hlookup := hlookup)
  let afterMulStore : EvmYul.Yul.VarStore :=
    Finmap.insert "expr_4682" (EvmYul.UInt256.ofNat rr) mulStore
  let q := FormalYul.evmDiv x rr
  have hdiv :
      EvmYul.Yul.call (fuel + 286) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat rr]
        (.some "fun_unsafeDiv_5899") (.some yulContract)
        (EvmYul.Yul.State.Ok shared afterMulStore) =
      .ok (EvmYul.Yul.State.Ok shared afterMulStore, [EvmYul.UInt256.ofNat q]) := by
    simpa [afterMulStore, q, FormalYul.word, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      call_fun_unsafeDiv_direct
        (numerator := x) (denominator := rr) (fuel := fuel + 226)
        (shared := shared) (store := afterMulStore) (hlookup := hlookup)
  let afterDivStore : EvmYul.Yul.VarStore :=
    Finmap.insert "expr_4683" (EvmYul.UInt256.ofNat q) afterMulStore
  let add1Store : EvmYul.Yul.VarStore :=
    Finmap.insert "expr_4684" (EvmYul.UInt256.ofNat r)
      (Finmap.insert "_114" (EvmYul.UInt256.ofNat r) afterDivStore)
  let sum1 := FormalYul.evmAdd q r
  have hadd1 :
      EvmYul.Yul.call (fuel + 283) [EvmYul.UInt256.ofNat q, EvmYul.UInt256.ofNat r]
        (.some "wrapping_add_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok shared add1Store) =
      .ok (EvmYul.Yul.State.Ok shared add1Store, [EvmYul.UInt256.ofNat sum1]) := by
    simpa [add1Store, sum1, FormalYul.word, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      call_wrapping_add_t_uint256_direct
        (x := q) (y := r) (fuel := fuel + 203)
        (shared := shared) (store := add1Store) (hlookup := hlookup)
  let afterAdd1Store : EvmYul.Yul.VarStore :=
    Finmap.insert "expr_4685" (EvmYul.UInt256.ofNat sum1) add1Store
  let add2Store : EvmYul.Yul.VarStore :=
    Finmap.insert "expr_4686" (EvmYul.UInt256.ofNat r)
      (Finmap.insert "_115" (EvmYul.UInt256.ofNat r) afterAdd1Store)
  let sum2 := FormalYul.evmAdd sum1 r
  have hadd2 :
      EvmYul.Yul.call (fuel + 280) [EvmYul.UInt256.ofNat sum1, EvmYul.UInt256.ofNat r]
        (.some "wrapping_add_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok shared add2Store) =
      .ok (EvmYul.Yul.State.Ok shared add2Store, [EvmYul.UInt256.ofNat sum2]) := by
    simpa [add2Store, sum2, FormalYul.word, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      call_wrapping_add_t_uint256_direct
        (x := sum1) (y := r) (fuel := fuel + 200)
        (shared := shared) (store := add2Store) (hlookup := hlookup)
  let afterAdd2Store : EvmYul.Yul.VarStore :=
    Finmap.insert "expr_4687" (EvmYul.UInt256.ofNat sum2) add2Store
  let convertStore : EvmYul.Yul.VarStore :=
    Finmap.insert "expr_4689" (EvmYul.UInt256.ofNat 3)
      (Finmap.insert "expr_4688" (EvmYul.UInt256.ofNat sum2) afterAdd2Store)
  have hconvert :
      EvmYul.Yul.call (fuel + 275) [EvmYul.UInt256.ofNat 3]
        (.some "convert_t_rational_3_by_1_to_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok shared convertStore) =
      .ok (EvmYul.Yul.State.Ok shared convertStore, [EvmYul.UInt256.ofNat 3]) := by
    simpa [convertStore, FormalYul.word, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      call_convert_t_rational_3_by_1_to_t_uint256_direct
        (value := 3) (fuel := fuel + 175)
        (shared := shared) (store := convertStore) (hlookup := hlookup)
  let out := FormalYul.evmDiv sum2 3
  have hdiv3 :
      EvmYul.Yul.call (fuel + 277) [EvmYul.UInt256.ofNat sum2, EvmYul.UInt256.ofNat 3]
        (.some "wrapping_div_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok shared convertStore) =
      .ok (EvmYul.Yul.State.Ok shared convertStore, [EvmYul.UInt256.ofNat out]) := by
    simpa [convertStore, out, FormalYul.word, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      call_wrapping_div_t_uint256_by_three_direct
        (x := sum2) (fuel := fuel + 157)
        (shared := shared) (store := convertStore) (hlookup := hlookup)
  simp +decide [paramStore, zeroStore, mulStore, afterMulStore, afterDivStore,
    add1Store, afterAdd1Store, add2Store, afterAdd2Store, convertStore,
    rr, q, sum1, sum2, out,
    EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
    Finmap.lookup_insert, FormalYul.word,
    hzero, hmul, hdiv, hadd1, hadd2, hconvert, hdiv3]

private theorem call_fun__cbrt_newtonRaphsonStep_raw_direct
    (x r fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 300)) [FormalYul.word x, FormalYul.word r]
      (.some yulName_fun__cbrt_newtonRaphsonStep) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word
        (FormalYul.evmDiv
          (FormalYul.evmAdd (FormalYul.evmAdd
            (FormalYul.evmDiv x (FormalYul.evmMul r r)) r) r) 3)]) := by
  rw [show fuel + (extra + 300) = (fuel + extra) + 300 by omega]
  exact call_fun__cbrt_newtonRaphsonStep_direct
    (x := x) (r := r) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_convert_t_rational_2_by_1_to_t_uint8_raw_direct
    (value fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120)) [FormalYul.word value]
      (.some "convert_t_rational_2_by_1_to_t_uint8")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmAnd value 255)]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  exact call_convert_t_rational_2_by_1_to_t_uint8_direct
    (value := value) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_convert_t_rational_seed_to_t_uint256_raw_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 100))
      [FormalYul.word 22141993662453218394297550]
      (.some "convert_t_rational_22141993662453218394297550_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word 22141993662453218394297550]) := by
  rw [show fuel + (extra + 100) = (fuel + extra) + 100 by omega]
  exact call_convert_t_rational_22141993662453218394297550_by_1_to_t_uint256_direct
    (value := 22141993662453218394297550) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_convert_t_rational_3_by_1_to_t_uint256_raw_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 100)) [FormalYul.word 3]
      (.some "convert_t_rational_3_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 3]) := by
  rw [show fuel + (extra + 100) = (fuel + extra) + 100 by omega]
  exact call_convert_t_rational_3_by_1_to_t_uint256_direct
    (value := 3) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_convert_t_rational_86_by_1_to_t_uint8_raw_direct
    (value fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 120)) [FormalYul.word value]
      (.some "convert_t_rational_86_by_1_to_t_uint8")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmAnd value 255)]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  exact call_convert_t_rational_86_by_1_to_t_uint8_direct
    (value := value) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_convert_t_rational_1_by_1_to_t_uint256_raw_direct
    (value fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 100)) [FormalYul.word value]
      (.some "convert_t_rational_1_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word value]) := by
  rw [show fuel + (extra + 100) = (fuel + extra) + 100 by omega]
  exact call_convert_t_rational_1_by_1_to_t_uint256_direct
    (value := value) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_convert_t_rational_77371252455336267181195263_by_1_to_t_uint256_raw_direct
    (value fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 100)) [FormalYul.word value]
      (.some "convert_t_rational_77371252455336267181195263_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word value]) := by
  rw [show fuel + (extra + 100) = (fuel + extra) + 100 by omega]
  exact call_convert_t_rational_77371252455336267181195263_by_1_to_t_uint256_direct
    (value := value) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_fun_clz_raw_direct
    (x fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 60)) [FormalYul.word x] (.some yulName_fun_clz)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmClz x)]) := by
  rw [show fuel + (extra + 60) = (fuel + extra) + 60 by omega]
  exact call_fun_clz_direct
    (x := x) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_fun_unsafeDiv_raw_direct
    (numerator denominator fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 60)) [FormalYul.word numerator, FormalYul.word denominator]
      (.some "fun_unsafeDiv_5899") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmDiv numerator denominator)]) := by
  rw [show fuel + (extra + 60) = (fuel + extra) + 60 by omega]
  exact call_fun_unsafeDiv_direct
    (numerator := numerator) (denominator := denominator) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_fun_unsafeInc_raw_direct
    (x b fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 60)) [FormalYul.word x, FormalYul.word b]
      (.some "fun_unsafeInc_5817") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmAdd x b)]) := by
  rw [show fuel + (extra + 60) = (fuel + extra) + 60 by omega]
  exact call_fun_unsafeInc_direct
    (x := x) (b := b) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_fun_and_raw_direct
    (a b fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 60)) [FormalYul.word a, FormalYul.word b]
      (.some "fun_and_5596") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmAnd a b)]) := by
  rw [show fuel + (extra + 60) = (fuel + extra) + 60 by omega]
  exact call_fun_and_direct
    (a := a) (b := b) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_fun_or_raw_direct
    (a b fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 60)) [FormalYul.word a, FormalYul.word b]
      (.some "fun_or_5585") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmOr a b)]) := by
  rw [show fuel + (extra + 60) = (fuel + extra) + 60 by omega]
  exact call_fun_or_direct
    (a := a) (b := b) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_shift_right_t_uint256_t_uint8_raw_direct
    (value bits fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 100)) [FormalYul.word value, FormalYul.word bits]
      (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShr (FormalYul.evmAnd bits 255) value)]) := by
  rw [show fuel + (extra + 100) = (fuel + extra) + 100 by omega]
  exact call_shift_right_t_uint256_t_uint8_direct
    (value := value) (bits := bits) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_shift_left_t_uint256_t_uint8_raw_direct
    (value bits fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 100)) [FormalYul.word value, FormalYul.word bits]
      (.some "shift_left_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShl (FormalYul.evmAnd bits 255) value)]) := by
  rw [show fuel + (extra + 100) = (fuel + extra) + 100 by omega]
  exact call_shift_left_t_uint256_t_uint8_direct
    (value := value) (bits := bits) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_shift_right_t_uint256_t_uint256_raw_direct
    (value bits fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 100)) [FormalYul.word value, FormalYul.word bits]
      (.some "shift_right_t_uint256_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShr bits value)]) := by
  rw [show fuel + (extra + 100) = (fuel + extra) + 100 by omega]
  exact call_shift_right_t_uint256_t_uint256_direct
    (value := value) (bits := bits) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_fun_unsafeDec_raw_direct
    (x b fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 60)) [FormalYul.word x, FormalYul.word b]
      (.some "fun_unsafeDec_5854") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmSub x b)]) := by
  rw [show fuel + (extra + 60) = (fuel + extra) + 60 by omega]
  exact call_fun_unsafeDec_direct
    (x := x) (b := b) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_cleanup_t_uint256_raw_direct
    (v : EvmYul.UInt256) (fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [v] (.some "cleanup_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  exact call_cleanup_t_uint256_direct
    (v := v) (fuel := fuel + extra) (shared := shared) (store := store)
    (hlookup := hlookup)

private theorem call_fun__shl256_raw_direct
    (xHi xLo s fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 100)) [FormalYul.word xHi, FormalYul.word xLo, FormalYul.word s]
      (.some yulName_fun__shl256) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShr (FormalYul.evmSub 256 s) xHi),
       FormalYul.word (FormalYul.evmOr (FormalYul.evmShl s xHi)
         (FormalYul.evmShr (FormalYul.evmSub 256 s) xLo)),
       FormalYul.word (FormalYul.evmShl s xLo)]) := by
  rw [show fuel + (extra + 100) = (fuel + extra) + 100 by omega]
  exact call_fun__shl256_direct
    (xHi := xHi) (xLo := xLo) (s := s) (fuel := fuel + extra)
    (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_fun__cbrt512_shifted_pair_raw_direct
    (xHi xLo fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    let shift := FormalYul.evmDiv (FormalYul.evmClz xHi) 3
    let shift3 := FormalYul.evmMul shift 3
    EvmYul.Yul.call (fuel + (extra + 100))
      [FormalYul.word xHi, FormalYul.word xLo, FormalYul.word shift3]
      (.some yulName_fun__shl256) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShr (FormalYul.evmSub 256 shift3) xHi),
       FormalYul.word (FormalYul.evmOr (FormalYul.evmShl shift3 xHi)
         (FormalYul.evmShr (FormalYul.evmSub 256 shift3) xLo)),
       FormalYul.word (FormalYul.evmShl shift3 xLo)]) := by
  intro shift shift3
  exact call_fun__shl256_raw_direct
    (xHi := xHi) (xLo := xLo) (s := shift3)
    (fuel := fuel) (extra := extra) (shared := shared) (store := store)
    (hlookup := hlookup)

set_option linter.unusedSimpArgs false in
private theorem call_fun__cbrt_karatsubaQuotient_raw_direct
    (res xLo d fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    let n := FormalYul.evmOr (FormalYul.evmShl 86 res) xLo
    let q0 := FormalYul.evmDiv n d
    let rem0 := FormalYul.evmMod n d
    let c := FormalYul.evmShr 170 res
    let q1 := FormalYul.evmAdd q0 (FormalYul.evmDiv (FormalYul.evmNot 0) d)
    let rem1 := FormalYul.evmAdd rem0
      (FormalYul.evmAdd 1 (FormalYul.evmMod (FormalYul.evmNot 0) d))
    let q2 := FormalYul.evmAdd q1 (FormalYul.evmDiv rem1 d)
    let rem2 := FormalYul.evmMod rem1 d
    let out : Nat × Nat := if c = 0 then (q0, rem0) else (q2, rem2)
    EvmYul.Yul.call (fuel + (extra + 600))
      [FormalYul.word res, FormalYul.word xLo, FormalYul.word d]
      (.some yulName_fun__cbrt_karatsubaQuotient) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word out.1, FormalYul.word out.2]) := by
  rw [show fuel + (extra + 600) = (fuel + extra) + 600 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_fun__cbrt_karatsubaQuotient]
  simp only [yulFunction_fun__cbrt_karatsubaQuotient,
    yulFunction_fun__cbrt_karatsubaQuotient_4819,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let n := FormalYul.evmOr (FormalYul.evmShl 86 res) xLo
  let q0 := FormalYul.evmDiv n d
  let rem0 := FormalYul.evmMod n d
  let c := FormalYul.evmShr 170 res
  let q1 := FormalYul.evmAdd q0 (FormalYul.evmDiv (FormalYul.evmNot 0) d)
  let rem1 := FormalYul.evmAdd rem0
    (FormalYul.evmAdd 1 (FormalYul.evmMod (FormalYul.evmNot 0) d))
  let q2 := FormalYul.evmAdd q1 (FormalYul.evmDiv rem1 d)
  let rem2 := FormalYul.evmMod rem1 d
  let out : Nat × Nat := if c = 0 then (q0, rem0) else (q2, rem2)
  let paramStore :=
    Finmap.insert "var_res_4806" (EvmYul.UInt256.ofNat res)
      (Finmap.insert "var_x_lo_4808" (EvmYul.UInt256.ofNat xLo)
        (Finmap.insert "var_d_4810" (EvmYul.UInt256.ofNat d)
          (Inhabited.default : EvmYul.Yul.VarStore)))
  have hzeroRLo :
      EvmYul.Yul.call (fuel + extra + 596) [] (.some "zero_value_for_split_t_uint256")
        (.some yulContract) (EvmYul.Yul.State.Ok shared paramStore) =
      .ok (EvmYul.Yul.State.Ok shared paramStore, [FormalYul.word 0]) := by
    simpa [paramStore, FormalYul.word, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      call_zero_value_for_split_t_uint256_direct
        (fuel := fuel + extra) (extra := 576) (shared := shared)
        (store := paramStore) (hlookup := hlookup)
  let afterRLoZeroStore :=
    Finmap.insert "var_r_lo_4813" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "zero_t_uint256_80" (EvmYul.UInt256.ofNat 0) paramStore)
  have hzeroResOut :
      EvmYul.Yul.call (fuel + extra + 594) [] (.some "zero_value_for_split_t_uint256")
        (.some yulContract) (EvmYul.Yul.State.Ok shared afterRLoZeroStore) =
      .ok (EvmYul.Yul.State.Ok shared afterRLoZeroStore, [FormalYul.word 0]) := by
    simpa [afterRLoZeroStore, FormalYul.word, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      call_zero_value_for_split_t_uint256_direct
        (fuel := fuel + extra) (extra := 574) (shared := shared)
        (store := afterRLoZeroStore) (hlookup := hlookup)
  by_cases hc : c = 0
  · have hcond :
        EvmYul.UInt256.ofNat c = ({ val := 0 } : EvmYul.UInt256) := by
      rw [hc]
      exact (show ({ val := 0 } : EvmYul.UInt256) = EvmYul.UInt256.ofNat 0 by rfl).symm
    simp +decide [n, q0, rem0, c, q1, rem1, q2, rem2, out, hc, hcond,
      FormalYul.Preservation.uint256_ofNat_add_eq_word_evmAdd,
      FormalYul.Preservation.uint256_ofNat_div_eq_word_evmDiv,
      FormalYul.Preservation.uint256_ofNat_mod_eq_word_evmMod,
      FormalYul.Preservation.uint256_ofNat_uint256_mod_eq_word_evmMod,
      FormalYul.Preservation.uint256_ofNat_not_eq_word_evmNot,
      FormalYul.Preservation.uint256_ofNat_or_eq_word_evmOr,
      FormalYul.Preservation.uint256_ofNat_shiftLeft_eq_word_evmShl,
      FormalYul.Preservation.uint256_ofNat_shiftRight_eq_word_evmShr,
      EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
      EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
      EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
      EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
      EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
      EvmYul.Yul.State.store,
      GetElem?.getElem!, decidableGetElem?,
      EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
      EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
      EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
      Finmap.lookup_insert, Finmap.lookup_insert_of_ne, FormalYul.word,
      paramStore, afterRLoZeroStore, hzeroRLo, hzeroResOut]
  · have hcLt : c < FormalYul.WORD_MOD := by
      simpa [c] using FormalYul.Preservation.evmShr_lt_WORD_MOD 170 res
    have hcond :
        ¬ EvmYul.UInt256.ofNat c = ({ val := 0 } : EvmYul.UInt256) := by
      intro h
      have hw := congrArg FormalYul.wordNat h
      simp only [FormalYul.Preservation.wordNat_ofNat] at hw
      have hzeroNat : FormalYul.wordNat ({ val := 0 } : EvmYul.UInt256) = 0 := rfl
      rw [hzeroNat] at hw
      have hmod : FormalYul.u256 c = c := FormalYul.u256_eq_self_of_lt hcLt
      rw [hmod] at hw
      exact hc hw
    simp +decide [n, q0, rem0, c, q1, rem1, q2, rem2, out, hc, hcond,
      FormalYul.Preservation.uint256_ofNat_add_eq_word_evmAdd,
      FormalYul.Preservation.uint256_ofNat_div_eq_word_evmDiv,
      FormalYul.Preservation.uint256_ofNat_mod_eq_word_evmMod,
      FormalYul.Preservation.uint256_ofNat_uint256_mod_eq_word_evmMod,
      FormalYul.Preservation.uint256_ofNat_not_eq_word_evmNot,
      FormalYul.Preservation.uint256_ofNat_or_eq_word_evmOr,
      FormalYul.Preservation.uint256_ofNat_shiftLeft_eq_word_evmShl,
      FormalYul.Preservation.uint256_ofNat_shiftRight_eq_word_evmShr,
      EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
      EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
      EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
      EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
      EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
      EvmYul.Yul.State.store,
      GetElem?.getElem!, decidableGetElem?,
      EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
      EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
      EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
      Finmap.lookup_insert, Finmap.lookup_insert_of_ne, FormalYul.word,
      paramStore, afterRLoZeroStore, hzeroRLo, hzeroResOut]

private theorem call_fun__cbrt_quadraticCorrection_enters_generated_body
    (rHi rLo res fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 900) [FormalYul.word rHi, FormalYul.word rLo,
      FormalYul.word res]
      (.some yulName_fun__cbrt_quadraticCorrection) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    (match
      EvmYul.Yul.exec (fuel + 899)
        (EvmYul.Yul.Ast.Stmt.Block yulFunction_fun__cbrt_quadraticCorrection.body)
        (.some yulContract)
        (EvmYul.Yul.State.mkOk
          ((EvmYul.Yul.State.Ok shared store).initcall
            yulFunction_fun__cbrt_quadraticCorrection.params
            [FormalYul.word rHi, FormalYul.word rLo, FormalYul.word res])) with
    | .error e => .error e
    | .ok s₂ =>
      .ok (s₂.reviveJump.overwrite? (EvmYul.Yul.State.Ok shared store)
          |>.setStore (EvmYul.Yul.State.Ok shared store),
        List.map s₂.lookup! yulFunction_fun__cbrt_quadraticCorrection.rets)) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_fun__cbrt_quadraticCorrection]
  rfl

private theorem call_fun__cbrt_baseCase_enters_generated_body
    (xHi fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 2200) [FormalYul.word xHi]
      (.some yulName_fun__cbrt_baseCase) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    (match
      EvmYul.Yul.exec (fuel + 2199)
        (EvmYul.Yul.Ast.Stmt.Block yulFunction_fun__cbrt_baseCase_4803.body)
        (.some yulContract)
        (EvmYul.Yul.State.mkOk
          ((EvmYul.Yul.State.Ok shared store).initcall
            yulFunction_fun__cbrt_baseCase_4803.params [FormalYul.word xHi])) with
    | .error e => .error e
    | .ok s₂ =>
      .ok (s₂.reviveJump.overwrite? (EvmYul.Yul.State.Ok shared store)
          |>.setStore (EvmYul.Yul.State.Ok shared store),
        List.map s₂.lookup! yulFunction_fun__cbrt_baseCase_4803.rets)) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_fun__cbrt_baseCase, yulFunction_fun__cbrt_baseCase]
  rfl

private theorem call_fun__cbrt512_enters_generated_body
    (xHi xLo fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 980) [FormalYul.word xHi, FormalYul.word xLo]
      (.some yulName_fun__cbrt512) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    (match
      EvmYul.Yul.exec (fuel + 979)
        (EvmYul.Yul.Ast.Stmt.Block yulFunction_fun__cbrt512.body)
        (.some yulContract)
        (EvmYul.Yul.State.mkOk
          ((EvmYul.Yul.State.Ok shared store).initcall
            yulFunction_fun__cbrt512.params [FormalYul.word xHi, FormalYul.word xLo])) with
    | .error e => .error e
    | .ok s₂ =>
      .ok (s₂.reviveJump.overwrite? (EvmYul.Yul.State.Ok shared store)
          |>.setStore (EvmYul.Yul.State.Ok shared store),
        List.map s₂.lookup! yulFunction_fun__cbrt512.rets)) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_fun__cbrt512, yulFunction_fun__cbrt512]
  rfl

private theorem call_fun__cbrt512_raw_enters_generated_body
    (xHi xLo fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 979) [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
      (.some yulName_fun__cbrt512) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    (match
      EvmYul.Yul.exec (fuel + 978)
        (EvmYul.Yul.Ast.Stmt.Block yulFunction_fun__cbrt512.body)
        (.some yulContract)
        (EvmYul.Yul.State.mkOk
          ((EvmYul.Yul.State.Ok shared store).initcall
            yulFunction_fun__cbrt512.params
            [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo])) with
    | .error e => .error e
    | .ok s₂ =>
      .ok (s₂.reviveJump.overwrite? (EvmYul.Yul.State.Ok shared store)
          |>.setStore (EvmYul.Yul.State.Ok shared store),
        List.map s₂.lookup! yulFunction_fun__cbrt512.rets)) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_fun__cbrt512, yulFunction_fun__cbrt512]
  rfl

@[simp] private theorem call_zero_value_for_split_t_uint256_cbrt512_init_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 976) [] (.some "zero_value_for_split_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_zero_value_for_split_t_uint256_direct
      (fuel := fuel) (extra := 956) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_zero_value_for_split_t_uint256_cbrt512_raw_init_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 975) [] (.some "zero_value_for_split_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_zero_value_for_split_t_uint256_direct
      (fuel := fuel) (extra := 955) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_fun_clz_cbrt512_core_raw_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 971) [EvmYul.UInt256.ofNat x] (.some "fun_clz_6141")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmClz x)]) := by
  simpa [FormalYul.word, yulName_fun_clz, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using
    call_fun_clz_raw_direct (x := x) (fuel := fuel) (extra := 911)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun_clz_cbrt512_core_raw_offset_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 970) [EvmYul.UInt256.ofNat x] (.some "fun_clz_6141")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmClz x)]) := by
  simpa [FormalYul.word, yulName_fun_clz, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using
    call_fun_clz_raw_direct (x := x) (fuel := fuel) (extra := 910)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_convert_t_rational_3_by_1_to_t_uint256_cbrt512_div_raw_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 967) [EvmYul.UInt256.ofNat 3]
      (.some "convert_t_rational_3_by_1_to_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 3]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_3_by_1_to_t_uint256_raw_direct
      (fuel := fuel) (extra := 867) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_convert_t_rational_3_by_1_to_t_uint256_cbrt512_div_raw_offset_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 966) [EvmYul.UInt256.ofNat 3]
      (.some "convert_t_rational_3_by_1_to_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 3]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_3_by_1_to_t_uint256_raw_direct
      (fuel := fuel) (extra := 866) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_wrapping_div_t_uint256_by_three_cbrt512_core_raw_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 969) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat 3]
      (.some "wrapping_div_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmDiv x 3)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_wrapping_div_t_uint256_by_three_raw_direct
      (x := x) (fuel := fuel) (extra := 849)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_wrapping_div_t_uint256_by_three_cbrt512_core_raw_offset_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 968) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat 3]
      (.some "wrapping_div_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmDiv x 3)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_wrapping_div_t_uint256_by_three_raw_direct
      (x := x) (fuel := fuel) (extra := 848)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_convert_t_rational_3_by_1_to_t_uint256_cbrt512_mul_raw_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 958) [EvmYul.UInt256.ofNat 3]
      (.some "convert_t_rational_3_by_1_to_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 3]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_3_by_1_to_t_uint256_raw_direct
      (fuel := fuel) (extra := 858) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_convert_t_rational_3_by_1_to_t_uint256_cbrt512_mul_raw_offset_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 957) [EvmYul.UInt256.ofNat 3]
      (.some "convert_t_rational_3_by_1_to_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 3]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_3_by_1_to_t_uint256_raw_direct
      (fuel := fuel) (extra := 857) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_wrapping_mul_t_uint256_cbrt512_core_raw_direct
    (x y fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 960) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat y]
      (.some "wrapping_mul_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmMul x y)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_wrapping_mul_t_uint256_raw_direct
      (x := x) (y := y) (fuel := fuel) (extra := 880)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_wrapping_mul_t_uint256_cbrt512_core_raw_offset_direct
    (x y fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 959) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat y]
      (.some "wrapping_mul_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmMul x y)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_wrapping_mul_t_uint256_raw_direct
      (x := x) (y := y) (fuel := fuel) (extra := 879)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun__cbrt512_core_shifted_pair_generated_direct
    (xHi xLo s fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 959)
      [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo, EvmYul.UInt256.ofNat s]
      (.some "fun__shl256_3075") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShr (FormalYul.evmSub 256 s) xHi),
       FormalYul.word (FormalYul.evmOr (FormalYul.evmShl s xHi)
         (FormalYul.evmShr (FormalYul.evmSub 256 s) xLo)),
       FormalYul.word (FormalYul.evmShl s xLo)]) := by
  simpa [FormalYul.word, yulName_fun__shl256] using
    call_fun__shl256_raw_direct
      (xHi := xHi) (xLo := xLo) (s := s) (fuel := fuel) (extra := 859)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun__cbrt512_core_shifted_pair_generated_raw_offset_direct
    (xHi xLo s fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 958)
      [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo, EvmYul.UInt256.ofNat s]
      (.some "fun__shl256_3075") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShr (FormalYul.evmSub 256 s) xHi),
       FormalYul.word (FormalYul.evmOr (FormalYul.evmShl s xHi)
         (FormalYul.evmShr (FormalYul.evmSub 256 s) xLo)),
       FormalYul.word (FormalYul.evmShl s xLo)]) := by
  simpa [FormalYul.word, yulName_fun__shl256] using
    call_fun__shl256_raw_direct
      (xHi := xHi) (xLo := xLo) (s := s) (fuel := fuel) (extra := 858)
      (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_fun__cbrt_baseCase_core_generated_body
    (xHi fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 954) [EvmYul.UInt256.ofNat xHi]
      (.some "fun__cbrt_baseCase_4803") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    (match
      EvmYul.Yul.exec (fuel + 953)
        (EvmYul.Yul.Ast.Stmt.Block yulFunction_fun__cbrt_baseCase_4803.body)
        (.some yulContract)
        (EvmYul.Yul.State.mkOk
          ((EvmYul.Yul.State.Ok shared store).initcall
            yulFunction_fun__cbrt_baseCase_4803.params [EvmYul.UInt256.ofNat xHi])) with
    | .error e => .error e
    | .ok s₂ =>
      .ok (s₂.reviveJump.overwrite? (EvmYul.Yul.State.Ok shared store)
          |>.setStore (EvmYul.Yul.State.Ok shared store),
        List.map s₂.lookup! yulFunction_fun__cbrt_baseCase_4803.rets)) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_fun__cbrt_baseCase, yulFunction_fun__cbrt_baseCase]
  rfl

private theorem call_fun__cbrt_baseCase_core_raw_generated_body
    (xHi fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 953) [EvmYul.UInt256.ofNat xHi]
      (.some "fun__cbrt_baseCase_4803") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    (match
      EvmYul.Yul.exec (fuel + 952)
        (EvmYul.Yul.Ast.Stmt.Block yulFunction_fun__cbrt_baseCase_4803.body)
        (.some yulContract)
        (EvmYul.Yul.State.mkOk
          ((EvmYul.Yul.State.Ok shared store).initcall
            yulFunction_fun__cbrt_baseCase_4803.params [EvmYul.UInt256.ofNat xHi])) with
    | .error e => .error e
    | .ok s₂ =>
      .ok (s₂.reviveJump.overwrite? (EvmYul.Yul.State.Ok shared store)
          |>.setStore (EvmYul.Yul.State.Ok shared store),
        List.map s₂.lookup! yulFunction_fun__cbrt_baseCase_4803.rets)) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_fun__cbrt_baseCase, yulFunction_fun__cbrt_baseCase]
  rfl

@[simp] private theorem call_convert_t_rational_2_by_1_to_t_uint8_baseCase_raw_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 942) [EvmYul.UInt256.ofNat 2]
      (.some "convert_t_rational_2_by_1_to_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmAnd 2 255)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_2_by_1_to_t_uint8_raw_direct
      (value := 2) (fuel := fuel) (extra := 822)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_shift_right_t_uint256_t_uint8_baseCase_raw_direct
    (x bits fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 940)
      [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat bits]
      (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShr (FormalYul.evmAnd bits 255) x)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_right_t_uint256_t_uint8_raw_direct
      (value := x) (bits := bits) (fuel := fuel) (extra := 840)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_convert_t_rational_seed_to_t_uint256_baseCase_raw_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 937)
      [EvmYul.UInt256.ofNat 22141993662453218394297550]
      (.some "convert_t_rational_22141993662453218394297550_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word 22141993662453218394297550]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_seed_to_t_uint256_raw_direct
      (fuel := fuel) (extra := 837)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun__cbrt_newtonRaphsonStep_baseCase_raw_930_direct
    (x r fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 930) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat r]
      (.some "fun__cbrt_newtonRaphsonStep_4694") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word
        (FormalYul.evmDiv
          (FormalYul.evmAdd (FormalYul.evmAdd
            (FormalYul.evmDiv x (FormalYul.evmMul r r)) r) r) 3)]) := by
  simpa [FormalYul.word, yulName_fun__cbrt_newtonRaphsonStep, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using
    call_fun__cbrt_newtonRaphsonStep_raw_direct
      (x := x) (r := r) (fuel := fuel) (extra := 630)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun__cbrt_newtonRaphsonStep_baseCase_raw_923_direct
    (x r fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 923) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat r]
      (.some "fun__cbrt_newtonRaphsonStep_4694") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word
        (FormalYul.evmDiv
          (FormalYul.evmAdd (FormalYul.evmAdd
            (FormalYul.evmDiv x (FormalYul.evmMul r r)) r) r) 3)]) := by
  simpa [FormalYul.word, yulName_fun__cbrt_newtonRaphsonStep, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using
    call_fun__cbrt_newtonRaphsonStep_raw_direct
      (x := x) (r := r) (fuel := fuel) (extra := 623)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun__cbrt_newtonRaphsonStep_baseCase_raw_916_direct
    (x r fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 916) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat r]
      (.some "fun__cbrt_newtonRaphsonStep_4694") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word
        (FormalYul.evmDiv
          (FormalYul.evmAdd (FormalYul.evmAdd
            (FormalYul.evmDiv x (FormalYul.evmMul r r)) r) r) 3)]) := by
  simpa [FormalYul.word, yulName_fun__cbrt_newtonRaphsonStep, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using
    call_fun__cbrt_newtonRaphsonStep_raw_direct
      (x := x) (r := r) (fuel := fuel) (extra := 616)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun__cbrt_newtonRaphsonStep_baseCase_raw_909_direct
    (x r fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 909) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat r]
      (.some "fun__cbrt_newtonRaphsonStep_4694") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word
        (FormalYul.evmDiv
          (FormalYul.evmAdd (FormalYul.evmAdd
            (FormalYul.evmDiv x (FormalYul.evmMul r r)) r) r) 3)]) := by
  simpa [FormalYul.word, yulName_fun__cbrt_newtonRaphsonStep, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using
    call_fun__cbrt_newtonRaphsonStep_raw_direct
      (x := x) (r := r) (fuel := fuel) (extra := 609)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun__cbrt_newtonRaphsonStep_baseCase_raw_902_direct
    (x r fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 902) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat r]
      (.some "fun__cbrt_newtonRaphsonStep_4694") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word
        (FormalYul.evmDiv
          (FormalYul.evmAdd (FormalYul.evmAdd
            (FormalYul.evmDiv x (FormalYul.evmMul r r)) r) r) 3)]) := by
  simpa [FormalYul.word, yulName_fun__cbrt_newtonRaphsonStep, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using
    call_fun__cbrt_newtonRaphsonStep_raw_direct
      (x := x) (r := r) (fuel := fuel) (extra := 602)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun__cbrt_newtonRaphsonStep_baseCase_raw_895_direct
    (x r fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 895) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat r]
      (.some "fun__cbrt_newtonRaphsonStep_4694") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word
        (FormalYul.evmDiv
          (FormalYul.evmAdd (FormalYul.evmAdd
            (FormalYul.evmDiv x (FormalYul.evmMul r r)) r) r) 3)]) := by
  simpa [FormalYul.word, yulName_fun__cbrt_newtonRaphsonStep, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using
    call_fun__cbrt_newtonRaphsonStep_raw_direct
      (x := x) (r := r) (fuel := fuel) (extra := 595)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_wrapping_mul_t_uint256_baseCase_raw_888_direct
    (x y fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 888) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat y]
      (.some "wrapping_mul_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmMul x y)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_wrapping_mul_t_uint256_raw_direct
      (x := x) (y := y) (fuel := fuel) (extra := 808)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_wrapping_mul_t_uint256_baseCase_raw_882_direct
    (x y fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 882) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat y]
      (.some "wrapping_mul_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmMul x y)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_wrapping_mul_t_uint256_raw_direct
      (x := x) (y := y) (fuel := fuel) (extra := 802)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_cleanup_t_uint256_baseCase_raw_871_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 871) [v] (.some "cleanup_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_uint256_raw_direct
      (v := v) (fuel := fuel) (extra := 851)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_cleanup_t_uint256_baseCase_raw_869_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 869) [v] (.some "cleanup_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_uint256_raw_direct
      (v := v) (fuel := fuel) (extra := 849)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun_unsafeDec_baseCase_raw_872_direct
    (x fuel : Nat) (b : EvmYul.UInt256) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 872) [EvmYul.UInt256.ofNat x, b]
      (.some "fun_unsafeDec_5854") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmSub x (FormalYul.wordNat b))]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_unsafeDec_word_direct
      (x := x) (b := b) (fuel := fuel + 812)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_wrapping_mul_t_uint256_baseCase_raw_865_direct
    (x y fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 865) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat y]
      (.some "wrapping_mul_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmMul x y)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_wrapping_mul_t_uint256_raw_direct
      (x := x) (y := y) (fuel := fuel) (extra := 785)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_wrapping_mul_t_uint256_baseCase_raw_858_direct
    (x y fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 858) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat y]
      (.some "wrapping_mul_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmMul x y)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_wrapping_mul_t_uint256_raw_direct
      (x := x) (y := y) (fuel := fuel) (extra := 778)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_wrapping_sub_t_uint256_baseCase_raw_851_direct
    (x y fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 851) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat y]
      (.some "wrapping_sub_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmSub x y)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_wrapping_sub_t_uint256_raw_direct
      (x := x) (y := y) (fuel := fuel) (extra := 771)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_convert_t_rational_3_by_1_to_t_uint256_baseCase_raw_843_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 843) [EvmYul.UInt256.ofNat 3]
      (.some "convert_t_rational_3_by_1_to_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 3]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_3_by_1_to_t_uint256_raw_direct
      (fuel := fuel) (extra := 743)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_wrapping_mul_t_uint256_baseCase_raw_845_direct
    (x y fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 845) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat y]
      (.some "wrapping_mul_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmMul x y)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_wrapping_mul_t_uint256_raw_direct
      (x := x) (y := y) (fuel := fuel) (extra := 765)
      (shared := shared) (store := store) (hlookup := hlookup)

set_option maxRecDepth 100000 in
private theorem call_fun__cbrt_baseCase_core_raw_direct
    (xHi fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    let x := FormalYul.evmShr (FormalYul.evmAnd (FormalYul.evmAnd 2 255) 255) xHi
    let seed := 22141993662453218394297550
    let z1 := FormalYul.evmDiv
      (FormalYul.evmAdd
        (FormalYul.evmAdd (FormalYul.evmDiv x (FormalYul.evmMul seed seed)) seed)
        seed) 3
    let z2 := FormalYul.evmDiv
      (FormalYul.evmAdd
        (FormalYul.evmAdd (FormalYul.evmDiv x (FormalYul.evmMul z1 z1)) z1)
        z1) 3
    let z3 := FormalYul.evmDiv
      (FormalYul.evmAdd
        (FormalYul.evmAdd (FormalYul.evmDiv x (FormalYul.evmMul z2 z2)) z2)
        z2) 3
    let z4 := FormalYul.evmDiv
      (FormalYul.evmAdd
        (FormalYul.evmAdd (FormalYul.evmDiv x (FormalYul.evmMul z3 z3)) z3)
        z3) 3
    let z5 := FormalYul.evmDiv
      (FormalYul.evmAdd
        (FormalYul.evmAdd (FormalYul.evmDiv x (FormalYul.evmMul z4 z4)) z4)
        z4) 3
    let z6 := FormalYul.evmDiv
      (FormalYul.evmAdd
        (FormalYul.evmAdd (FormalYul.evmDiv x (FormalYul.evmMul z5 z5)) z5)
        z5) 3
    let z6sq := FormalYul.evmMul z6 z6
    let z6cube := FormalYul.evmMul z6sq z6
    let r := FormalYul.evmSub z6 (FormalYul.evmGt z6cube x)
    let r2 := FormalYul.evmMul r r
    let r3 := FormalYul.evmMul r2 r
    let res := FormalYul.evmSub x r3
    let d := FormalYul.evmMul r2 3
    EvmYul.Yul.call (fuel + 953) [EvmYul.UInt256.ofNat xHi]
      (.some "fun__cbrt_baseCase_4803") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word r, FormalYul.word res, FormalYul.word d]) := by
  intro x seed z1 z2 z3 z4 z5 z6 z6sq z6cube r r2 r3 res d
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_fun__cbrt_baseCase, yulFunction_fun__cbrt_baseCase,
    yulFunction_fun__cbrt_baseCase_4803,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup,
    EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.store,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne, FormalYul.word,
    seed, x, z1, z2, z3, z4, z5, z6, z6sq, z6cube, r, r2, r3, res, d,
    call_zero_value_for_split_t_uint256_direct]

private def cbrt512BaseCaseCore (xHi : Nat) : Nat × Nat × Nat :=
  let x := FormalYul.evmShr (FormalYul.evmAnd (FormalYul.evmAnd 2 255) 255) xHi
  let seed := 22141993662453218394297550
  let z1 := FormalYul.evmDiv
    (FormalYul.evmAdd
      (FormalYul.evmAdd (FormalYul.evmDiv x (FormalYul.evmMul seed seed)) seed)
      seed) 3
  let z2 := FormalYul.evmDiv
    (FormalYul.evmAdd
      (FormalYul.evmAdd (FormalYul.evmDiv x (FormalYul.evmMul z1 z1)) z1)
      z1) 3
  let z3 := FormalYul.evmDiv
    (FormalYul.evmAdd
      (FormalYul.evmAdd (FormalYul.evmDiv x (FormalYul.evmMul z2 z2)) z2)
      z2) 3
  let z4 := FormalYul.evmDiv
    (FormalYul.evmAdd
      (FormalYul.evmAdd (FormalYul.evmDiv x (FormalYul.evmMul z3 z3)) z3)
      z3) 3
  let z5 := FormalYul.evmDiv
    (FormalYul.evmAdd
      (FormalYul.evmAdd (FormalYul.evmDiv x (FormalYul.evmMul z4 z4)) z4)
      z4) 3
  let z6 := FormalYul.evmDiv
    (FormalYul.evmAdd
      (FormalYul.evmAdd (FormalYul.evmDiv x (FormalYul.evmMul z5 z5)) z5)
      z5) 3
  let z6sq := FormalYul.evmMul z6 z6
  let z6cube := FormalYul.evmMul z6sq z6
  let r := FormalYul.evmSub z6 (FormalYul.evmGt z6cube x)
  let r2 := FormalYul.evmMul r r
  let r3 := FormalYul.evmMul r2 r
  let res := FormalYul.evmSub x r3
  let d := FormalYul.evmMul r2 3
  (r, res, d)

private def cbrt512BaseR (xHi : Nat) : Nat :=
  (cbrt512BaseCaseCore xHi).1

private def cbrt512BaseRes (xHi : Nat) : Nat :=
  (cbrt512BaseCaseCore xHi).2.1

private def cbrt512BaseD (xHi : Nat) : Nat :=
  (cbrt512BaseCaseCore xHi).2.2

private def cbrt512CoreShift (xHi : Nat) : Nat :=
  FormalYul.evmDiv (FormalYul.evmClz xHi) 3

private def cbrt512CoreShift3 (xHi : Nat) : Nat :=
  FormalYul.evmMul (cbrt512CoreShift xHi) 3

private def cbrt512ShiftedHi (xHi xLo : Nat) : Nat :=
  FormalYul.evmOr (FormalYul.evmShl (cbrt512CoreShift3 xHi) xHi)
    (FormalYul.evmShr (FormalYul.evmSub 256 (cbrt512CoreShift3 xHi)) xLo)

private def cbrt512ShiftedLo (xHi xLo : Nat) : Nat :=
  FormalYul.evmShl (cbrt512CoreShift3 xHi) xLo

private def cbrt512LimbHi (shiftedHi shiftedLo : Nat) : Nat :=
  FormalYul.evmOr (FormalYul.evmShl 84 (FormalYul.evmAnd 3 shiftedHi))
    (FormalYul.evmShr 172 shiftedLo)

private def cbrt512KaratsubaOut (shiftedHi shiftedLo : Nat) : Nat × Nat :=
  let res := cbrt512BaseRes shiftedHi
  let d := cbrt512BaseD shiftedHi
  let limbHi := cbrt512LimbHi shiftedHi shiftedLo
  let n := FormalYul.evmOr (FormalYul.evmShl 86 res) limbHi
  let q0 := FormalYul.evmDiv n d
  let rem0 := FormalYul.evmMod n d
  let c := FormalYul.evmShr 170 res
  let q1 := FormalYul.evmAdd q0 (FormalYul.evmDiv (FormalYul.evmNot 0) d)
  let rem1 := FormalYul.evmAdd rem0
    (FormalYul.evmAdd 1 (FormalYul.evmMod (FormalYul.evmNot 0) d))
  let q2 := FormalYul.evmAdd q1 (FormalYul.evmDiv rem1 d)
  let rem2 := FormalYul.evmMod rem1 d
  if c = 0 then (q0, rem0) else (q2, rem2)

private theorem call_fun__cbrt_baseCase_core_raw_result_direct
    (xHi fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 953) [EvmYul.UInt256.ofNat xHi]
      (.some "fun__cbrt_baseCase_4803") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (cbrt512BaseR xHi), FormalYul.word (cbrt512BaseRes xHi),
        FormalYul.word (cbrt512BaseD xHi)]) := by
  simpa [cbrt512BaseR, cbrt512BaseRes, cbrt512BaseD, cbrt512BaseCaseCore] using
    call_fun__cbrt_baseCase_core_raw_direct
      (xHi := xHi) (fuel := fuel) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_zero_value_for_split_t_uint256_cbrt512_limb_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 949) [] (.some "zero_value_for_split_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_zero_value_for_split_t_uint256_direct
      (fuel := fuel) (extra := 929) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_zero_value_for_split_t_uint256_cbrt512_raw_limb_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 948) [] (.some "zero_value_for_split_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_zero_value_for_split_t_uint256_direct
      (fuel := fuel) (extra := 928) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_zero_value_for_split_t_uint256_cbrt512_rlo_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 944) [] (.some "zero_value_for_split_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_zero_value_for_split_t_uint256_direct
      (fuel := fuel) (extra := 924) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_zero_value_for_split_t_uint256_cbrt512_raw_rlo_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 943) [] (.some "zero_value_for_split_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_zero_value_for_split_t_uint256_direct
      (fuel := fuel) (extra := 923) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_fun__cbrt_karatsubaQuotient_core_generated_direct
    (res xLo d fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    let n := FormalYul.evmOr (FormalYul.evmShl 86 res) xLo
    let q0 := FormalYul.evmDiv n d
    let rem0 := FormalYul.evmMod n d
    let c := FormalYul.evmShr 170 res
    let q1 := FormalYul.evmAdd q0 (FormalYul.evmDiv (FormalYul.evmNot 0) d)
    let rem1 := FormalYul.evmAdd rem0
      (FormalYul.evmAdd 1 (FormalYul.evmMod (FormalYul.evmNot 0) d))
    let q2 := FormalYul.evmAdd q1 (FormalYul.evmDiv rem1 d)
    let rem2 := FormalYul.evmMod rem1 d
    let out : Nat × Nat := if c = 0 then (q0, rem0) else (q2, rem2)
    EvmYul.Yul.call (fuel + 937)
      [EvmYul.UInt256.ofNat res, EvmYul.UInt256.ofNat xLo, EvmYul.UInt256.ofNat d]
      (.some "fun__cbrt_karatsubaQuotient_4819") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word out.1, FormalYul.word out.2]) := by
  simpa [FormalYul.word, yulName_fun__cbrt_karatsubaQuotient] using
    call_fun__cbrt_karatsubaQuotient_raw_direct
      (res := res) (xLo := xLo) (d := d) (fuel := fuel) (extra := 337)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun__cbrt_karatsubaQuotient_core_generated_raw_offset_direct
    (res xLo d fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    let n := FormalYul.evmOr (FormalYul.evmShl 86 res) xLo
    let q0 := FormalYul.evmDiv n d
    let rem0 := FormalYul.evmMod n d
    let c := FormalYul.evmShr 170 res
    let q1 := FormalYul.evmAdd q0 (FormalYul.evmDiv (FormalYul.evmNot 0) d)
    let rem1 := FormalYul.evmAdd rem0
      (FormalYul.evmAdd 1 (FormalYul.evmMod (FormalYul.evmNot 0) d))
    let q2 := FormalYul.evmAdd q1 (FormalYul.evmDiv rem1 d)
    let rem2 := FormalYul.evmMod rem1 d
    let out : Nat × Nat := if c = 0 then (q0, rem0) else (q2, rem2)
    EvmYul.Yul.call (fuel + 936)
      [EvmYul.UInt256.ofNat res, EvmYul.UInt256.ofNat xLo, EvmYul.UInt256.ofNat d]
      (.some "fun__cbrt_karatsubaQuotient_4819") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word out.1, FormalYul.word out.2]) := by
  simpa [FormalYul.word, yulName_fun__cbrt_karatsubaQuotient] using
    call_fun__cbrt_karatsubaQuotient_raw_direct
      (res := res) (xLo := xLo) (d := d) (fuel := fuel) (extra := 336)
      (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_fun__cbrt_quadraticCorrection_core_generated_body
    (rHi rLo res fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 928)
      [EvmYul.UInt256.ofNat rHi, EvmYul.UInt256.ofNat rLo,
        EvmYul.UInt256.ofNat res]
      (.some "fun__cbrt_quadraticCorrection_4921") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    (match
      EvmYul.Yul.exec (fuel + 927)
        (EvmYul.Yul.Ast.Stmt.Block yulFunction_fun__cbrt_quadraticCorrection.body)
        (.some yulContract)
        (EvmYul.Yul.State.mkOk
          ((EvmYul.Yul.State.Ok shared store).initcall
            yulFunction_fun__cbrt_quadraticCorrection.params
            [EvmYul.UInt256.ofNat rHi, EvmYul.UInt256.ofNat rLo,
              EvmYul.UInt256.ofNat res])) with
    | .error e => .error e
    | .ok s₂ =>
      .ok (s₂.reviveJump.overwrite? (EvmYul.Yul.State.Ok shared store)
          |>.setStore (EvmYul.Yul.State.Ok shared store),
        List.map s₂.lookup! yulFunction_fun__cbrt_quadraticCorrection.rets)) := by
  simpa [FormalYul.word, yulName_fun__cbrt_quadraticCorrection,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun__cbrt_quadraticCorrection_enters_generated_body
      (rHi := rHi) (rLo := rLo) (res := res) (fuel := fuel + 28)
      (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_fun__cbrt_quadraticCorrection_core_raw_generated_body
    (rHi rLo res fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 927)
      [EvmYul.UInt256.ofNat rHi, EvmYul.UInt256.ofNat rLo,
        EvmYul.UInt256.ofNat res]
      (.some "fun__cbrt_quadraticCorrection_4921") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    (match
      EvmYul.Yul.exec (fuel + 926)
        (EvmYul.Yul.Ast.Stmt.Block yulFunction_fun__cbrt_quadraticCorrection.body)
        (.some yulContract)
        (EvmYul.Yul.State.mkOk
          ((EvmYul.Yul.State.Ok shared store).initcall
            yulFunction_fun__cbrt_quadraticCorrection.params
            [EvmYul.UInt256.ofNat rHi, EvmYul.UInt256.ofNat rLo,
              EvmYul.UInt256.ofNat res])) with
    | .error e => .error e
    | .ok s₂ =>
      .ok (s₂.reviveJump.overwrite? (EvmYul.Yul.State.Ok shared store)
          |>.setStore (EvmYul.Yul.State.Ok shared store),
        List.map s₂.lookup! yulFunction_fun__cbrt_quadraticCorrection.rets)) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_fun__cbrt_quadraticCorrection]
  rfl

@[simp] private theorem call_shift_right_t_uint256_t_uint256_core_generated_direct
    (value bits fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 922)
      [EvmYul.UInt256.ofNat value, EvmYul.UInt256.ofNat bits]
      (.some "shift_right_t_uint256_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShr bits value)]) := by
  simpa [FormalYul.word] using
    call_shift_right_t_uint256_t_uint256_raw_direct
      (value := value) (bits := bits) (fuel := fuel) (extra := 822)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_shift_right_t_uint256_t_uint256_core_generated_raw_offset_direct
    (value bits fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 921)
      [EvmYul.UInt256.ofNat value, EvmYul.UInt256.ofNat bits]
      (.some "shift_right_t_uint256_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShr bits value)]) := by
  simpa [FormalYul.word] using
    call_shift_right_t_uint256_t_uint256_raw_direct
      (value := value) (bits := bits) (fuel := fuel) (extra := 821)
      (shared := shared) (store := store) (hlookup := hlookup)

set_option maxRecDepth 100000 in
private theorem call_fun__cbrt512_raw_of_subcall_semantics
    (xHi xLo rHi res d corr fuel : Nat)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hbase :
      let shift := FormalYul.evmDiv (FormalYul.evmClz xHi) 3
      let shift3 := FormalYul.evmMul shift 3
      let shiftedHi := FormalYul.evmOr (FormalYul.evmShl shift3 xHi)
        (FormalYul.evmShr (FormalYul.evmSub 256 shift3) xLo)
      ∀ callerStore,
        EvmYul.Yul.call (fuel + 953) [EvmYul.UInt256.ofNat shiftedHi]
          (.some "fun__cbrt_baseCase_4803") (.some yulContract)
          (EvmYul.Yul.State.Ok shared callerStore) =
        .ok (EvmYul.Yul.State.Ok shared callerStore,
          [FormalYul.word rHi, FormalYul.word res, FormalYul.word d]))
    (hquad :
      let shift := FormalYul.evmDiv (FormalYul.evmClz xHi) 3
      let shift3 := FormalYul.evmMul shift 3
      let shiftedHi := FormalYul.evmOr (FormalYul.evmShl shift3 xHi)
        (FormalYul.evmShr (FormalYul.evmSub 256 shift3) xLo)
      let shiftedLo := FormalYul.evmShl shift3 xLo
      let limbHi := FormalYul.evmOr (FormalYul.evmShl 84 (FormalYul.evmAnd 3 shiftedHi))
        (FormalYul.evmShr 172 shiftedLo)
      let n := FormalYul.evmOr (FormalYul.evmShl 86 res) limbHi
      let q0 := FormalYul.evmDiv n d
      let rem0 := FormalYul.evmMod n d
      let c := FormalYul.evmShr 170 res
      let q1 := FormalYul.evmAdd q0 (FormalYul.evmDiv (FormalYul.evmNot 0) d)
      let rem1 := FormalYul.evmAdd rem0
        (FormalYul.evmAdd 1 (FormalYul.evmMod (FormalYul.evmNot 0) d))
      let q2 := FormalYul.evmAdd q1 (FormalYul.evmDiv rem1 d)
      let rem2 := FormalYul.evmMod rem1 d
      let out : Nat × Nat := if c = 0 then (q0, rem0) else (q2, rem2)
      ∀ callerStore,
        EvmYul.Yul.call (fuel + 927)
          [EvmYul.UInt256.ofNat rHi, EvmYul.UInt256.ofNat out.1,
            EvmYul.UInt256.ofNat out.2]
          (.some "fun__cbrt_quadraticCorrection_4921") (.some yulContract)
          (EvmYul.Yul.State.Ok shared callerStore) =
        .ok (EvmYul.Yul.State.Ok shared callerStore, [FormalYul.word corr])) :
    let shift := FormalYul.evmDiv (FormalYul.evmClz xHi) 3
    EvmYul.Yul.call (fuel + 979) [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
      (.some yulName_fun__cbrt512) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmShr shift corr)]) := by
  have hkaratsuba :
      let shift := FormalYul.evmDiv (FormalYul.evmClz xHi) 3
      let shift3 := FormalYul.evmMul shift 3
      let shiftedHi := FormalYul.evmOr (FormalYul.evmShl shift3 xHi)
        (FormalYul.evmShr (FormalYul.evmSub 256 shift3) xLo)
      let shiftedLo := FormalYul.evmShl shift3 xLo
      let limbHi := FormalYul.evmOr (FormalYul.evmShl 84 (FormalYul.evmAnd 3 shiftedHi))
        (FormalYul.evmShr 172 shiftedLo)
      let n := FormalYul.evmOr (FormalYul.evmShl 86 res) limbHi
      let q0 := FormalYul.evmDiv n d
      let rem0 := FormalYul.evmMod n d
      let c := FormalYul.evmShr 170 res
      let q1 := FormalYul.evmAdd q0 (FormalYul.evmDiv (FormalYul.evmNot 0) d)
      let rem1 := FormalYul.evmAdd rem0
        (FormalYul.evmAdd 1 (FormalYul.evmMod (FormalYul.evmNot 0) d))
      let q2 := FormalYul.evmAdd q1 (FormalYul.evmDiv rem1 d)
      let rem2 := FormalYul.evmMod rem1 d
      let out : Nat × Nat := if c = 0 then (q0, rem0) else (q2, rem2)
      ∀ callerStore,
        EvmYul.Yul.call (fuel + 936)
          [EvmYul.UInt256.ofNat res,
            EvmYul.UInt256.lor
              (EvmYul.UInt256.shiftLeft
                (EvmYul.UInt256.land (EvmYul.UInt256.ofNat 3)
                  (EvmYul.UInt256.ofNat shiftedHi))
                (EvmYul.UInt256.ofNat 84))
              (EvmYul.UInt256.shiftRight (EvmYul.UInt256.ofNat shiftedLo)
                (EvmYul.UInt256.ofNat 172)),
            EvmYul.UInt256.ofNat d]
          (.some "fun__cbrt_karatsubaQuotient_4819") (.some yulContract)
          (EvmYul.Yul.State.Ok shared callerStore) =
        .ok (EvmYul.Yul.State.Ok shared callerStore,
          [FormalYul.word out.1, FormalYul.word out.2]) := by
    intro shift shift3 shiftedHi shiftedLo limbHi n q0 rem0 c q1 rem1 q2 rem2 out
      callerStore
    have hlimb :
        EvmYul.UInt256.lor
            (EvmYul.UInt256.shiftLeft
              (EvmYul.UInt256.land (EvmYul.UInt256.ofNat 3)
                (EvmYul.UInt256.ofNat shiftedHi))
              (EvmYul.UInt256.ofNat 84))
            (EvmYul.UInt256.shiftRight (EvmYul.UInt256.ofNat shiftedLo)
              (EvmYul.UInt256.ofNat 172)) =
          EvmYul.UInt256.ofNat limbHi := by
      simp [limbHi, FormalYul.word,
        FormalYul.Preservation.uint256_ofNat_and_eq_word_evmAnd,
        FormalYul.Preservation.uint256_ofNat_or_eq_word_evmOr,
        FormalYul.Preservation.uint256_ofNat_shiftLeft_eq_word_evmShl,
        FormalYul.Preservation.uint256_ofNat_shiftRight_eq_word_evmShr]
    rw [hlimb]
    simpa [n, q0, rem0, c, q1, rem1, q2, rem2, out, FormalYul.word] using
      call_fun__cbrt_karatsubaQuotient_core_generated_raw_offset_direct
        (res := res) (xLo := limbHi) (d := d) (fuel := fuel)
        (shared := shared) (store := callerStore) (hlookup := hlookup)
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_fun__cbrt512, yulFunction_fun__cbrt512,
    yulFunction_fun__cbrt_4991,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.store,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    FormalYul.word, hbase, hkaratsuba, hquad]

private theorem call_fun__cbrt512_raw_of_generated_baseCase_and_quadratic_semantics
    (xHi xLo corr fuel : Nat)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hquad :
      let shiftedHi := cbrt512ShiftedHi xHi xLo
      let shiftedLo := cbrt512ShiftedLo xHi xLo
      let rHi := cbrt512BaseR shiftedHi
      let out := cbrt512KaratsubaOut shiftedHi shiftedLo
      ∀ callerStore,
        EvmYul.Yul.call (fuel + 927)
          [EvmYul.UInt256.ofNat rHi, EvmYul.UInt256.ofNat out.1,
            EvmYul.UInt256.ofNat out.2]
          (.some "fun__cbrt_quadraticCorrection_4921") (.some yulContract)
          (EvmYul.Yul.State.Ok shared callerStore) =
        .ok (EvmYul.Yul.State.Ok shared callerStore, [FormalYul.word corr])) :
    let shift := FormalYul.evmDiv (FormalYul.evmClz xHi) 3
    EvmYul.Yul.call (fuel + 979) [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
      (.some yulName_fun__cbrt512) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmShr shift corr)]) := by
  apply call_fun__cbrt512_raw_of_subcall_semantics
    (xHi := xHi) (xLo := xLo)
    (rHi := cbrt512BaseR (cbrt512ShiftedHi xHi xLo))
    (res := cbrt512BaseRes (cbrt512ShiftedHi xHi xLo))
    (d := cbrt512BaseD (cbrt512ShiftedHi xHi xLo))
    (corr := corr) (fuel := fuel) (shared := shared) (store := store)
    (hlookup := hlookup)
  · intro shift shift3 shiftedHi callerStore
    simpa [cbrt512ShiftedHi, cbrt512CoreShift, cbrt512CoreShift3] using
      call_fun__cbrt_baseCase_core_raw_result_direct
        (xHi := shiftedHi) (fuel := fuel) (shared := shared) (store := callerStore)
        (hlookup := hlookup)
  · simpa [cbrt512ShiftedHi, cbrt512ShiftedLo, cbrt512CoreShift,
      cbrt512CoreShift3, cbrt512LimbHi, cbrt512KaratsubaOut] using hquad

private theorem call_fun_tmp_128_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 40) [] (.some yulName_fun_tmp) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_tmp]
  simp only [yulFunction_fun_tmp, yulFunction_fun_tmp_128,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hzero :=
    call_zero_value_for_split_t_userDefinedValueType_uint512_direct
      (fuel := fuel) (extra := 16) (shared := shared)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  have hzero' :
      EvmYul.Yul.call (fuel + 36) []
        (.some "zero_value_for_split_t_userDefinedValueType$_uint512_$113")
        (.some yulContract) (EvmYul.Yul.State.Ok shared
          (Inhabited.default : EvmYul.Yul.VarStore)) =
      .ok (EvmYul.Yul.State.Ok shared (Inhabited.default : EvmYul.Yul.VarStore),
        [FormalYul.word 0]) := by
    simpa using hzero
  simp [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.multifill',
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill, EvmYul.Yul.State.lookup!,
    EvmYul.Yul.State.setStore, EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?, hzero', FormalYul.word]

private def sharedAfterFrom0 (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat) :
    EvmYul.SharedState .Yul :=
  { shared with
    toMachineState :=
      ((shared.toMachineState.mstore (FormalYul.word 0) (FormalYul.word xHi)).mstore
        (FormalYul.word 32) (FormalYul.word xLo)) }

private theorem sharedAfterFrom0_lookup
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    (sharedAfterFrom0 shared xHi xLo).accountMap.find?
        (sharedAfterFrom0 shared xHi xLo).executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract) := by
  simpa [sharedAfterFrom0] using
    FormalYul.Preservation.shared_mstore_two_words_lookup
      (shared := shared) (pos0 := FormalYul.word 0) (pos1 := FormalYul.word 32)
      (value0 := FormalYul.word xHi) (value1 := FormalYul.word xLo)
      (account := FormalYul.accountFor yulContract) hlookup

private theorem sharedAfterFrom0_mload0
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    ((sharedAfterFrom0 shared xHi xLo).mload (FormalYul.word 0)).1 =
      FormalYul.word xHi := by
  simpa [sharedAfterFrom0] using
    FormalYul.Preservation.mload_two_word_write_first shared.toMachineState
      (FormalYul.word xHi) (FormalYul.word xLo) hactive

private theorem sharedAfterFrom0_mload32
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    ((sharedAfterFrom0 shared xHi xLo).mload (FormalYul.word 32)).1 =
      FormalYul.word xLo := by
  simpa [sharedAfterFrom0] using
    FormalYul.Preservation.mload_two_word_write_second shared.toMachineState
      (FormalYul.word xHi) (FormalYul.word xLo) hactive

private theorem sharedAfterFrom0_mload0_state
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    ((sharedAfterFrom0 shared xHi xLo).mload (FormalYul.word 0)).2 =
      (sharedAfterFrom0 shared xHi xLo).toMachineState := by
  simpa [sharedAfterFrom0] using
    FormalYul.Preservation.mload_two_word_write_first_state shared.toMachineState
      (FormalYul.word xHi) (FormalYul.word xLo) hactive

private theorem sharedAfterFrom0_mload32_state
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    ((sharedAfterFrom0 shared xHi xLo).mload (FormalYul.word 32)).2 =
      (sharedAfterFrom0 shared xHi xLo).toMachineState := by
  simpa [sharedAfterFrom0] using
    FormalYul.Preservation.mload_two_word_write_second_state shared.toMachineState
      (FormalYul.word xHi) (FormalYul.word xLo) hactive

private theorem call_fun_from_156_zero_direct
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100) [FormalYul.word 0, FormalYul.word xHi, FormalYul.word xLo]
      (.some yulName_fun_from) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [FormalYul.word 0]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_from]
  simp only [yulFunction_fun_from, yulFunction_fun_from_156,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let zeroStore :=
    Finmap.insert "var_r_144" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "var_x_hi_146" (EvmYul.UInt256.ofNat xHi)
        (Finmap.insert "var_x_lo_148" (EvmYul.UInt256.ofNat xLo)
          (Inhabited.default : EvmYul.Yul.VarStore)))
  have hzero :
      EvmYul.Yul.call (fuel + 96) []
        (.some "zero_value_for_split_t_userDefinedValueType$_uint512_$113")
        (.some yulContract) (EvmYul.Yul.State.Ok shared zeroStore) =
      .ok (EvmYul.Yul.State.Ok shared zeroStore, [FormalYul.word 0]) := by
    simpa [zeroStore] using
      call_zero_value_for_split_t_userDefinedValueType_uint512_direct
        (fuel := fuel) (extra := 76) (shared := shared)
        (store := zeroStore) (hlookup := hlookup)
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.setMachineState, EvmYul.Yul.State.toMachineState,
    EvmYul.Yul.State.store,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    hzero, sharedAfterFrom0, zeroStore, FormalYul.word, Finmap.lookup_insert,
    Finmap.lookup_insert_of_ne]

private theorem call_fun_into_182_from0_direct
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    EvmYul.Yul.call (fuel + 120) [FormalYul.word 0]
      (.some yulName_fun_into) (.some yulContract)
      (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [FormalYul.word xHi, FormalYul.word xLo]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [sharedAfterFrom0_lookup shared xHi xLo hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_into]
  simp only [yulFunction_fun_into, yulFunction_fun_into_182,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let hiZeroStore :=
    Finmap.insert "var_x_173" (EvmYul.UInt256.ofNat 0)
      (Inhabited.default : EvmYul.Yul.VarStore)
  have hzeroHi :
      EvmYul.Yul.call (fuel + 116) [] (.some "zero_value_for_split_t_uint256")
        (.some yulContract) (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo)
          hiZeroStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) hiZeroStore,
        [FormalYul.word 0]) := by
    simpa [hiZeroStore] using
      call_zero_value_for_split_t_uint256_direct
        (fuel := fuel) (extra := 96) (shared := sharedAfterFrom0 shared xHi xLo)
        (store := hiZeroStore)
        (hlookup := sharedAfterFrom0_lookup shared xHi xLo hlookup)
  let loZeroStore :=
    Finmap.insert "var_r_hi_176" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "zero_t_uint256_21" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "var_x_173" (EvmYul.UInt256.ofNat 0)
          (Inhabited.default : EvmYul.Yul.VarStore)))
  have hzeroLo :
      EvmYul.Yul.call (fuel + 114) [] (.some "zero_value_for_split_t_uint256")
        (.some yulContract) (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo)
          loZeroStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) loZeroStore,
        [FormalYul.word 0]) := by
    simpa [loZeroStore] using
      call_zero_value_for_split_t_uint256_direct
        (fuel := fuel) (extra := 94) (shared := sharedAfterFrom0 shared xHi xLo)
        (store := loZeroStore)
        (hlookup := sharedAfterFrom0_lookup shared xHi xLo hlookup)
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.setMachineState, EvmYul.Yul.State.toMachineState,
    EvmYul.Yul.State.store,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    hzeroHi, hzeroLo, hiZeroStore, loZeroStore, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  have h0state :
      ((sharedAfterFrom0 shared xHi xLo).mload (EvmYul.UInt256.ofNat 0)).2 =
        (sharedAfterFrom0 shared xHi xLo).toMachineState := by
    simpa [FormalYul.word] using sharedAfterFrom0_mload0_state shared xHi xLo hactive
  have h32state :
      ((sharedAfterFrom0 shared xHi xLo).mload (EvmYul.UInt256.ofNat 32)).2 =
        (sharedAfterFrom0 shared xHi xLo).toMachineState := by
    simpa [FormalYul.word] using sharedAfterFrom0_mload32_state shared xHi xLo hactive
  have h0value :
      ((sharedAfterFrom0 shared xHi xLo).mload (EvmYul.UInt256.ofNat 0)).1 =
        EvmYul.UInt256.ofNat xHi := by
    simpa [FormalYul.word] using sharedAfterFrom0_mload0 shared xHi xLo hactive
  have h32value :
      ((sharedAfterFrom0 shared xHi xLo).mload (EvmYul.UInt256.ofNat 32)).1 =
        EvmYul.UInt256.ofNat xLo := by
    simpa [FormalYul.word] using sharedAfterFrom0_mload32 shared xHi xLo hactive
  constructor
  · rw [h0state, h32state]
  · constructor
    · exact h0value
    · rw [h0state]
      exact h32value

private theorem call_fun__cbrt256_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 200) [FormalYul.word x] (.some yulName_fun__cbrt256)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (innerCbrt (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun__cbrt256]
  simp only [yulFunction_fun__cbrt256, yulFunction_fun__cbrt_6096,
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
      (store := Finmap.insert "var_x_6089" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_shiftRight, FormalYul.Preservation.wordNat_shiftLeft,
    FormalYul.Preservation.wordNat_add, FormalYul.Preservation.wordNat_sub,
    FormalYul.Preservation.wordNat_mul, FormalYul.Preservation.wordNat_div,
    FormalYul.Preservation.wordNat_clz,
    FormalYul.Preservation.wordNat_ofNat]
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
    FormalYul.Preservation.u256_evmShr, FormalYul.Preservation.u256_eq_of_lt _ hinnerLt] using
    cbrtCoreEvmExpression_eq_innerCbrt x

private theorem call_fun_cbrt256_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 360) [FormalYul.word x] (.some yulName_fun_cbrt256)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (floorCbrt (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_cbrt256]
  simp only [yulFunction_fun_cbrt256, yulFunction_fun_cbrt_6112,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcbrtFuel : fuel + 352 = (fuel + 152) + 200 := by omega
  have hCallCbrt :=
    call_fun__cbrt256_direct (x := x) (fuel := fuel + 152) (shared := shared)
      (store := Finmap.insert "expr_6106"
        (EvmYul.UInt256.ofNat x)
          (Finmap.insert "_42"
            (EvmYul.UInt256.ofNat x)
            (Finmap.insert "var_z_6102" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "zero_t_uint256_41" (EvmYul.UInt256.ofNat 0)
                (Finmap.insert "var_x_6099" (EvmYul.UInt256.ofNat x)
                  (Inhabited.default : EvmYul.Yul.VarStore))))))
      (hlookup := hlookup)
  simp [FormalYul.word, yulName_fun__cbrt256] at hCallCbrt
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
      (store := Finmap.insert "var_x_6099" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_sub, FormalYul.Preservation.wordNat_lt,
    FormalYul.Preservation.wordNat_div, FormalYul.Preservation.wordNat_mul,
    FormalYul.Preservation.wordNat_ofNat]
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
    FormalYul.u256_u256, FormalYul.Preservation.u256_eq_of_lt _ hinnerW,
    FormalYul.Preservation.u256_eq_of_lt _ hfloorW] using hcorr

private theorem call_fun_cbrtUp256_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 420) [FormalYul.word x] (.some yulName_fun_cbrtUp256)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (cbrtUp256 (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_cbrtUp256]
  simp only [yulFunction_fun_cbrtUp256, yulFunction_fun_cbrtUp_6128,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hCallCbrt :=
    call_fun__cbrt256_direct (x := x) (fuel := fuel + 212) (shared := shared)
      (store := Finmap.insert "expr_6122"
        (EvmYul.UInt256.ofNat x)
          (Finmap.insert "_24"
            (EvmYul.UInt256.ofNat x)
            (Finmap.insert "var_z_6118" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "zero_t_uint256_23" (EvmYul.UInt256.ofNat 0)
                (Finmap.insert "var_x_6115" (EvmYul.UInt256.ofNat x)
                  (Inhabited.default : EvmYul.Yul.VarStore))))))
      (hlookup := hlookup)
  simp [FormalYul.word, yulName_fun__cbrt256] at hCallCbrt
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
      (store := Finmap.insert "var_x_6115" (EvmYul.UInt256.ofNat x)
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
    FormalYul.u256_u256, FormalYul.Preservation.u256_eq_of_lt _ hinnerW,
    FormalYul.Preservation.u256_eq_of_lt _ hupW] using hround

private theorem call_fun_into_182_from0_raw_direct
    (xHi xLo : Nat) (fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    EvmYul.Yul.call (fuel + (extra + 120)) [EvmYul.UInt256.ofNat 0]
      (.some yulName_fun_into) (.some yulContract)
      (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]) := by
  rw [show fuel + (extra + 120) = (fuel + extra) + 120 by omega]
  simpa [FormalYul.word] using
    call_fun_into_182_from0_direct (xHi := xHi) (xLo := xLo)
      (fuel := fuel + extra) (shared := shared) (store := store)
      (hlookup := hlookup) (hactive := hactive)

private theorem call_convert_t_rational_0_by_1_to_t_uint256_raw_direct
    (value fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 100)) [FormalYul.word value]
      (.some "convert_t_rational_0_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word value]) := by
  rw [show fuel + (extra + 100) = (fuel + extra) + 100 by omega]
  exact call_convert_t_rational_0_by_1_to_t_uint256_direct
    (value := value) (fuel := fuel + extra) (shared := shared) (store := store)
    (hlookup := hlookup)

private theorem call_fun_cbrt256_raw_direct
    (x fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 360)) [FormalYul.word x] (.some yulName_fun_cbrt256)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (floorCbrt (FormalYul.u256 x))]) := by
  rw [show fuel + (extra + 360) = (fuel + extra) + 360 by omega]
  exact call_fun_cbrt256_direct
    (x := x) (fuel := fuel + extra) (shared := shared) (store := store)
    (hlookup := hlookup)

private theorem call_fun_cbrtUp256_raw_direct
    (x fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 420)) [FormalYul.word x] (.some yulName_fun_cbrtUp256)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (cbrtUp256 (FormalYul.u256 x))]) := by
  rw [show fuel + (extra + 420) = (fuel + extra) + 420 by omega]
  exact call_fun_cbrtUp256_direct
    (x := x) (fuel := fuel + extra) (shared := shared) (store := store)
    (hlookup := hlookup)

private theorem call_fun_cbrt512_zero_from0_direct
    (xLo fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    EvmYul.Yul.call (fuel + 1000) [FormalYul.word 0]
      (.some yulName_fun_cbrt512) (.some yulContract)
      (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) store,
      [FormalYul.word (floorCbrt (FormalYul.u256 xLo))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [sharedAfterFrom0_lookup shared 0 xLo hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_cbrt512]
  simp only [yulFunction_fun_cbrt512, yulFunction_fun_cbrt_5025,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let zeroStore :=
    Finmap.insert "var_x_4994" (EvmYul.UInt256.ofNat 0)
      (Inhabited.default : EvmYul.Yul.VarStore)
  have hzero :
      EvmYul.Yul.call (fuel + 996) [] (.some "zero_value_for_split_t_uint256")
        (.some yulContract) (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo)
          zeroStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) zeroStore,
        [FormalYul.word 0]) := by
    simpa [zeroStore] using
      call_zero_value_for_split_t_uint256_direct
        (fuel := fuel) (extra := 976) (shared := sharedAfterFrom0 shared 0 xLo)
        (store := zeroStore)
        (hlookup := sharedAfterFrom0_lookup shared 0 xLo hlookup)
  let intoStore :=
    Finmap.insert "expr_5004_self" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "expr_5003" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "_16" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "var_r_4997" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "zero_t_uint256_15" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "var_x_4994" (EvmYul.UInt256.ofNat 0)
                (Inhabited.default : EvmYul.Yul.VarStore))))))
  have hinto :
      EvmYul.Yul.call (fuel + 991) [EvmYul.UInt256.ofNat 0]
        (.some yulName_fun_into) (.some yulContract)
        (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) intoStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) intoStore,
        [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat xLo]) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_into_182_from0_raw_direct (xHi := 0) (xLo := xLo)
        (fuel := fuel) (extra := 871) (shared := shared) (store := intoStore)
        (hlookup := hlookup) (hactive := hactive)
  let convertStore :=
    Finmap.insert "expr_5008" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "expr_5007" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "_17" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "var_x_lo_5002" (EvmYul.UInt256.ofNat xLo)
            (Finmap.insert "var_x_hi_5000" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "expr_5005_component_1" (EvmYul.UInt256.ofNat 0)
                (Finmap.insert "expr_5005_component_2" (EvmYul.UInt256.ofNat xLo)
                  (Finmap.insert "expr_5004_self" (EvmYul.UInt256.ofNat 0)
                    (Finmap.insert "expr_5003" (EvmYul.UInt256.ofNat 0)
                      (Finmap.insert "_16" (EvmYul.UInt256.ofNat 0)
                        (Finmap.insert "var_r_4997" (EvmYul.UInt256.ofNat 0)
                          (Finmap.insert "zero_t_uint256_15" (EvmYul.UInt256.ofNat 0)
                            (Finmap.insert "var_x_4994" (EvmYul.UInt256.ofNat 0)
                              (Inhabited.default : EvmYul.Yul.VarStore)))))))))))))
  have hconvert :
      EvmYul.Yul.call (fuel + 983) [EvmYul.UInt256.ofNat 0]
        (.some "convert_t_rational_0_by_1_to_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) convertStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) convertStore,
        [EvmYul.UInt256.ofNat 0]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_convert_t_rational_0_by_1_to_t_uint256_raw_direct
        (value := 0) (fuel := fuel) (extra := 883)
        (shared := sharedAfterFrom0 shared 0 xLo) (store := convertStore)
        (hlookup := sharedAfterFrom0_lookup shared 0 xLo hlookup)
  have hcleanup :
      EvmYul.Yul.call (fuel + 981) [EvmYul.UInt256.ofNat 0]
        (.some "cleanup_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) convertStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) convertStore,
        [EvmYul.UInt256.ofNat 0]) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_cleanup_t_uint256_raw_direct
        (v := EvmYul.UInt256.ofNat 0) (fuel := fuel) (extra := 961)
        (shared := sharedAfterFrom0 shared 0 xLo) (store := convertStore)
        (hlookup := sharedAfterFrom0_lookup shared 0 xLo hlookup)
  let cbrtStore :=
    Finmap.insert "expr_5011_self" (EvmYul.UInt256.ofNat xLo)
      (Finmap.insert "expr_5010" (EvmYul.UInt256.ofNat xLo)
        (Finmap.insert "_18" (EvmYul.UInt256.ofNat xLo)
          (Finmap.insert "expr_5009" ((EvmYul.UInt256.ofNat 0).eq (EvmYul.UInt256.ofNat 0))
            convertStore)))
  have hcbrt :
      EvmYul.Yul.call (fuel + 979) [EvmYul.UInt256.ofNat xLo]
        (.some yulName_fun_cbrt256) (.some yulContract)
        (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) cbrtStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) cbrtStore,
        [FormalYul.word (floorCbrt (FormalYul.u256 xLo))]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_cbrt256_raw_direct
        (x := xLo) (fuel := fuel) (extra := 619)
        (shared := sharedAfterFrom0 shared 0 xLo) (store := cbrtStore)
        (hlookup := sharedAfterFrom0_lookup shared 0 xLo hlookup)
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.store,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    hzero, hinto, hconvert, hcleanup, hcbrt,
    zeroStore, intoStore, convertStore, cbrtStore, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    call_on_checkpoint
      (fuel := fuel)]

private theorem call_fun_cbrt512_high_from0_of_core_direct
    (xHi xLo r fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3)
    (hxHi : xHi < FormalYul.WORD_MOD) (hxLo : xLo < FormalYul.WORD_MOD)
    (hxHiPos : 0 < xHi) (hr : r < FormalYul.WORD_MOD)
    (hcube : r * r * r < FormalYul.WORD_MOD * FormalYul.WORD_MOD)
    (hwithin :
      icbrt (xHi * FormalYul.WORD_MOD + xLo) ≤ r ∧
        r ≤ icbrt (xHi * FormalYul.WORD_MOD + xLo) + 1) :
    (let zeroStore :=
      Finmap.insert "var_x_4994" (EvmYul.UInt256.ofNat 0)
        (Inhabited.default : EvmYul.Yul.VarStore)
     let intoStore :=
      Finmap.insert "expr_5004_self" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "expr_5003" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "_16" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "var_r_4997" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "zero_t_uint256_15" (EvmYul.UInt256.ofNat 0)
                zeroStore))))
     let convertStore :=
      Finmap.insert "expr_5008" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "expr_5007" (EvmYul.UInt256.ofNat xHi)
          (Finmap.insert "_17" (EvmYul.UInt256.ofNat xHi)
            (Finmap.insert "var_x_lo_5002" (EvmYul.UInt256.ofNat xLo)
              (Finmap.insert "var_x_hi_5000" (EvmYul.UInt256.ofNat xHi)
                (Finmap.insert "expr_5005_component_1" (EvmYul.UInt256.ofNat xHi)
                  (Finmap.insert "expr_5005_component_2" (EvmYul.UInt256.ofNat xLo)
                    intoStore))))))
     let coreStore :=
      Finmap.insert "expr_5019" (EvmYul.UInt256.ofNat xLo)
        (Finmap.insert "_20" (EvmYul.UInt256.ofNat xLo)
          (Finmap.insert "expr_5018" (EvmYul.UInt256.ofNat xHi)
            (Finmap.insert "_19" (EvmYul.UInt256.ofNat xHi)
              (Finmap.insert "expr_5009" (EvmYul.UInt256.ofNat 0) convertStore))))
     EvmYul.Yul.call (fuel + 979)
      [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
      (.some yulName_fun__cbrt512) (.some yulContract)
      (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) coreStore) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) coreStore,
      [FormalYul.word r])) →
    EvmYul.Yul.call (fuel + 1000) [FormalYul.word 0]
      (.some yulName_fun_cbrt512) (.some yulContract)
      (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [FormalYul.word (icbrt (xHi * FormalYul.WORD_MOD + xLo))]) := by
  intro hcoreRaw
  rw [EvmYul.Yul.call.eq_def]
  simp only [sharedAfterFrom0_lookup shared xHi xLo hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_cbrt512]
  simp only [yulFunction_fun_cbrt512, yulFunction_fun_cbrt_5025,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let zeroStore :=
    Finmap.insert "var_x_4994" (EvmYul.UInt256.ofNat 0)
      (Inhabited.default : EvmYul.Yul.VarStore)
  have hzero :
      EvmYul.Yul.call (fuel + 996) [] (.some "zero_value_for_split_t_uint256")
        (.some yulContract) (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo)
          zeroStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) zeroStore,
        [FormalYul.word 0]) := by
    simpa [zeroStore] using
      call_zero_value_for_split_t_uint256_direct
        (fuel := fuel) (extra := 976) (shared := sharedAfterFrom0 shared xHi xLo)
        (store := zeroStore)
        (hlookup := sharedAfterFrom0_lookup shared xHi xLo hlookup)
  let intoStore :=
    Finmap.insert "expr_5004_self" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "expr_5003" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "_16" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "var_r_4997" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "zero_t_uint256_15" (EvmYul.UInt256.ofNat 0)
              zeroStore))))
  have hinto :
      EvmYul.Yul.call (fuel + 991) [EvmYul.UInt256.ofNat 0]
        (.some yulName_fun_into) (.some yulContract)
        (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) intoStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) intoStore,
        [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_into_182_from0_raw_direct (xHi := xHi) (xLo := xLo)
        (fuel := fuel) (extra := 871) (shared := shared) (store := intoStore)
        (hlookup := hlookup) (hactive := hactive)
  let convertStore :=
    Finmap.insert "expr_5008" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "expr_5007" (EvmYul.UInt256.ofNat xHi)
        (Finmap.insert "_17" (EvmYul.UInt256.ofNat xHi)
          (Finmap.insert "var_x_lo_5002" (EvmYul.UInt256.ofNat xLo)
            (Finmap.insert "var_x_hi_5000" (EvmYul.UInt256.ofNat xHi)
              (Finmap.insert "expr_5005_component_1" (EvmYul.UInt256.ofNat xHi)
                (Finmap.insert "expr_5005_component_2" (EvmYul.UInt256.ofNat xLo)
                  intoStore))))))
  have hconvert :
      EvmYul.Yul.call (fuel + 983) [EvmYul.UInt256.ofNat 0]
        (.some "convert_t_rational_0_by_1_to_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) convertStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) convertStore,
        [EvmYul.UInt256.ofNat 0]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_convert_t_rational_0_by_1_to_t_uint256_raw_direct
        (value := 0) (fuel := fuel) (extra := 883)
        (shared := sharedAfterFrom0 shared xHi xLo) (store := convertStore)
        (hlookup := sharedAfterFrom0_lookup shared xHi xLo hlookup)
  have hcleanup :
      EvmYul.Yul.call (fuel + 981) [EvmYul.UInt256.ofNat xHi]
        (.some "cleanup_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) convertStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) convertStore,
        [EvmYul.UInt256.ofNat xHi]) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_cleanup_t_uint256_raw_direct
        (v := EvmYul.UInt256.ofNat xHi) (fuel := fuel) (extra := 961)
        (shared := sharedAfterFrom0 shared xHi xLo) (store := convertStore)
        (hlookup := sharedAfterFrom0_lookup shared xHi xLo hlookup)
  have hcond :
      (EvmYul.UInt256.ofNat xHi).eq (EvmYul.UInt256.ofNat 0) =
        EvmYul.UInt256.ofNat 0 := by
    have hne : EvmYul.UInt256.ofNat xHi ≠ EvmYul.UInt256.ofNat 0 := by
      intro h
      have hw := congrArg FormalYul.wordNat h
      simp only [FormalYul.Preservation.wordNat_ofNat] at hw
      rw [FormalYul.Preservation.u256_eq_of_lt xHi hxHi] at hw
      simp [FormalYul.u256, FormalYul.WORD_MOD] at hw
      omega
    unfold EvmYul.UInt256.eq EvmYul.UInt256.fromBool
    simp [hne]
  let coreStore :=
    Finmap.insert "expr_5019" (EvmYul.UInt256.ofNat xLo)
      (Finmap.insert "_20" (EvmYul.UInt256.ofNat xLo)
        (Finmap.insert "expr_5018" (EvmYul.UInt256.ofNat xHi)
          (Finmap.insert "_19" (EvmYul.UInt256.ofNat xHi)
            (Finmap.insert "expr_5009" (EvmYul.UInt256.ofNat 0) convertStore))))
  have hcore :
      EvmYul.Yul.call (fuel + 979)
        [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
        (.some yulName_fun__cbrt512) (.some yulContract)
        (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) coreStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) coreStore,
        [FormalYul.word r]) := by
    simpa [zeroStore, intoStore, convertStore, coreStore] using hcoreRaw
  have hfloor := cbrt512_floorCorrection_correct xHi xLo r hxHi hxLo hr hcube hwithin
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.store,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    hzero, hinto, hconvert, hcleanup, hcond, hcore,
    zeroStore, intoStore, convertStore, coreStore, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_sub, FormalYul.Preservation.wordNat_or,
    FormalYul.Preservation.wordNat_and, FormalYul.Preservation.wordNat_eq,
    FormalYul.Preservation.wordNat_gt, FormalYul.Preservation.wordNat_mul,
    FormalYul.Preservation.wordNat_ofNat]
  simp [hfloor.symm]

private theorem call_fun_cbrtUp512_zero_from0_direct
    (xLo fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    EvmYul.Yul.call (fuel + 1000) [FormalYul.word 0]
      (.some yulName_fun_cbrtUp512) (.some yulContract)
      (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) store,
      [FormalYul.word (cbrtUp256 (FormalYul.u256 xLo))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [sharedAfterFrom0_lookup shared 0 xLo hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_cbrtUp512]
  simp only [yulFunction_fun_cbrtUp512, yulFunction_fun_cbrtUp_5059,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let zeroStore :=
    Finmap.insert "var_x_5028" (EvmYul.UInt256.ofNat 0)
      (Inhabited.default : EvmYul.Yul.VarStore)
  have hzero :
      EvmYul.Yul.call (fuel + 996) [] (.some "zero_value_for_split_t_uint256")
        (.some yulContract) (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo)
          zeroStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) zeroStore,
        [FormalYul.word 0]) := by
    simpa [zeroStore] using
      call_zero_value_for_split_t_uint256_direct
        (fuel := fuel) (extra := 976) (shared := sharedAfterFrom0 shared 0 xLo)
        (store := zeroStore)
        (hlookup := sharedAfterFrom0_lookup shared 0 xLo hlookup)
  let intoStore :=
    Finmap.insert "expr_5038_self" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "expr_5037" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "_10" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "var_r_5031" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "zero_t_uint256_9" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "var_x_5028" (EvmYul.UInt256.ofNat 0)
                (Inhabited.default : EvmYul.Yul.VarStore))))))
  have hinto :
      EvmYul.Yul.call (fuel + 991) [EvmYul.UInt256.ofNat 0]
        (.some yulName_fun_into) (.some yulContract)
        (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) intoStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) intoStore,
        [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat xLo]) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_into_182_from0_raw_direct (xHi := 0) (xLo := xLo)
        (fuel := fuel) (extra := 871) (shared := shared) (store := intoStore)
        (hlookup := hlookup) (hactive := hactive)
  let convertStore :=
    Finmap.insert "expr_5042" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "expr_5041" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "_11" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "var_x_lo_5036" (EvmYul.UInt256.ofNat xLo)
            (Finmap.insert "var_x_hi_5034" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "expr_5039_component_1" (EvmYul.UInt256.ofNat 0)
                (Finmap.insert "expr_5039_component_2" (EvmYul.UInt256.ofNat xLo)
                  (Finmap.insert "expr_5038_self" (EvmYul.UInt256.ofNat 0)
                    (Finmap.insert "expr_5037" (EvmYul.UInt256.ofNat 0)
                      (Finmap.insert "_10" (EvmYul.UInt256.ofNat 0)
                        (Finmap.insert "var_r_5031" (EvmYul.UInt256.ofNat 0)
                          (Finmap.insert "zero_t_uint256_9" (EvmYul.UInt256.ofNat 0)
                            (Finmap.insert "var_x_5028" (EvmYul.UInt256.ofNat 0)
                              (Inhabited.default : EvmYul.Yul.VarStore)))))))))))))
  have hconvert :
      EvmYul.Yul.call (fuel + 983) [EvmYul.UInt256.ofNat 0]
        (.some "convert_t_rational_0_by_1_to_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) convertStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) convertStore,
        [EvmYul.UInt256.ofNat 0]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_convert_t_rational_0_by_1_to_t_uint256_raw_direct
        (value := 0) (fuel := fuel) (extra := 883)
        (shared := sharedAfterFrom0 shared 0 xLo) (store := convertStore)
        (hlookup := sharedAfterFrom0_lookup shared 0 xLo hlookup)
  have hcleanup :
      EvmYul.Yul.call (fuel + 981) [EvmYul.UInt256.ofNat 0]
        (.some "cleanup_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) convertStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) convertStore,
        [EvmYul.UInt256.ofNat 0]) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_cleanup_t_uint256_raw_direct
        (v := EvmYul.UInt256.ofNat 0) (fuel := fuel) (extra := 961)
        (shared := sharedAfterFrom0 shared 0 xLo) (store := convertStore)
        (hlookup := sharedAfterFrom0_lookup shared 0 xLo hlookup)
  let cbrtStore :=
    Finmap.insert "expr_5045_self" (EvmYul.UInt256.ofNat xLo)
      (Finmap.insert "expr_5044" (EvmYul.UInt256.ofNat xLo)
        (Finmap.insert "_12" (EvmYul.UInt256.ofNat xLo)
          (Finmap.insert "expr_5043" ((EvmYul.UInt256.ofNat 0).eq (EvmYul.UInt256.ofNat 0))
            convertStore)))
  have hcbrt :
      EvmYul.Yul.call (fuel + 979) [EvmYul.UInt256.ofNat xLo]
        (.some yulName_fun_cbrtUp256) (.some yulContract)
        (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) cbrtStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) cbrtStore,
        [FormalYul.word (cbrtUp256 (FormalYul.u256 xLo))]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_cbrtUp256_raw_direct
        (x := xLo) (fuel := fuel) (extra := 559)
        (shared := sharedAfterFrom0 shared 0 xLo) (store := cbrtStore)
        (hlookup := sharedAfterFrom0_lookup shared 0 xLo hlookup)
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.store,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    hzero, hinto, hconvert, hcleanup, hcbrt,
    zeroStore, intoStore, convertStore, cbrtStore, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    call_on_checkpoint
      (fuel := fuel)]

private theorem call_fun_wrap_cbrt512_zero_direct
    (xLo fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    EvmYul.Yul.call (fuel + 1300) [FormalYul.word 0, FormalYul.word xLo]
      (.some yulName_fun_wrap_cbrt512) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) store,
      [FormalYul.word (floorCbrt (FormalYul.u256 xLo))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_wrap_cbrt512]
  simp only [yulFunction_fun_wrap_cbrt512, yulFunction_fun_wrap_cbrt512_6227,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let paramStore :=
    Finmap.insert "var_x_hi_6210" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "var_x_lo_6212" (EvmYul.UInt256.ofNat xLo)
        (Inhabited.default : EvmYul.Yul.VarStore))
  have hzero :
      EvmYul.Yul.call (fuel + 1296) [] (.some "zero_value_for_split_t_uint256")
        (.some yulContract) (EvmYul.Yul.State.Ok shared paramStore) =
      .ok (EvmYul.Yul.State.Ok shared paramStore, [FormalYul.word 0]) := by
    simpa [paramStore] using
      call_zero_value_for_split_t_uint256_direct
        (fuel := fuel) (extra := 1276) (shared := shared) (store := paramStore)
        (hlookup := hlookup)
  let tmpStore :=
    Finmap.insert "var__6215" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "zero_t_uint256_4" (EvmYul.UInt256.ofNat 0) paramStore)
  have htmp :
      EvmYul.Yul.call (fuel + 1294) [] (.some yulName_fun_tmp) (.some yulContract)
        (EvmYul.Yul.State.Ok shared tmpStore) =
      .ok (EvmYul.Yul.State.Ok shared tmpStore, [FormalYul.word 0]) := by
    simpa [tmpStore, FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_tmp_128_direct (fuel := fuel + 1254) (shared := shared)
        (store := tmpStore) (hlookup := hlookup)
  let fromStore :=
    Finmap.insert "expr_6221" (EvmYul.UInt256.ofNat xLo)
      (Finmap.insert "_6" (EvmYul.UInt256.ofNat xLo)
        (Finmap.insert "expr_6220" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "_5" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "expr_6219_self" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "expr_6218" (EvmYul.UInt256.ofNat 0) tmpStore)))))
  have hfrom :
      EvmYul.Yul.call (fuel + 1288)
        [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat xLo]
        (.some yulName_fun_from) (.some yulContract)
        (EvmYul.Yul.State.Ok shared fromStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) fromStore,
        [EvmYul.UInt256.ofNat 0]) := by
    simpa [fromStore, FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_from_156_zero_direct (xHi := 0) (xLo := xLo)
        (fuel := fuel + 1188) (shared := shared) (store := fromStore)
        (hlookup := hlookup)
  let cbrtStore :=
    Finmap.insert "expr_6223_self" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "expr_6222" (EvmYul.UInt256.ofNat 0) fromStore)
  have hcbrt :
      EvmYul.Yul.call (fuel + 1286) [EvmYul.UInt256.ofNat 0]
        (.some yulName_fun_cbrt512) (.some yulContract)
        (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) cbrtStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) cbrtStore,
        [FormalYul.word (floorCbrt (FormalYul.u256 xLo))]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_cbrt512_zero_from0_direct (xLo := xLo) (fuel := fuel + 286)
        (shared := shared) (store := cbrtStore)
        (hlookup := hlookup) (hactive := hactive)
  simp +decide [EvmYul.Yul.exec.eq_def,
    EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.store,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
    hzero, htmp, hfrom, hcbrt, paramStore, tmpStore, fromStore, cbrtStore,
    FormalYul.word, Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

private theorem call_fun_wrap_cbrt512_high_of_core_direct
    (xHi xLo r fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3)
    (hxHi : xHi < FormalYul.WORD_MOD) (hxLo : xLo < FormalYul.WORD_MOD)
    (hxHiPos : 0 < xHi) (hr : r < FormalYul.WORD_MOD)
    (hcube : r * r * r < FormalYul.WORD_MOD * FormalYul.WORD_MOD)
    (hwithin :
      icbrt (xHi * FormalYul.WORD_MOD + xLo) ≤ r ∧
        r ≤ icbrt (xHi * FormalYul.WORD_MOD + xLo) + 1)
    (hcoreRaw :
      (let zeroStore :=
        Finmap.insert "var_x_4994" (EvmYul.UInt256.ofNat 0)
          (Inhabited.default : EvmYul.Yul.VarStore)
       let intoStore :=
        Finmap.insert "expr_5004_self" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "expr_5003" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "_16" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "var_r_4997" (EvmYul.UInt256.ofNat 0)
                (Finmap.insert "zero_t_uint256_15" (EvmYul.UInt256.ofNat 0)
                  zeroStore))))
       let convertStore :=
        Finmap.insert "expr_5008" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "expr_5007" (EvmYul.UInt256.ofNat xHi)
            (Finmap.insert "_17" (EvmYul.UInt256.ofNat xHi)
              (Finmap.insert "var_x_lo_5002" (EvmYul.UInt256.ofNat xLo)
                (Finmap.insert "var_x_hi_5000" (EvmYul.UInt256.ofNat xHi)
                  (Finmap.insert "expr_5005_component_1" (EvmYul.UInt256.ofNat xHi)
                    (Finmap.insert "expr_5005_component_2" (EvmYul.UInt256.ofNat xLo)
                      intoStore))))))
       let coreStore :=
        Finmap.insert "expr_5019" (EvmYul.UInt256.ofNat xLo)
          (Finmap.insert "_20" (EvmYul.UInt256.ofNat xLo)
            (Finmap.insert "expr_5018" (EvmYul.UInt256.ofNat xHi)
              (Finmap.insert "_19" (EvmYul.UInt256.ofNat xHi)
                (Finmap.insert "expr_5009" (EvmYul.UInt256.ofNat 0) convertStore))))
       EvmYul.Yul.call (fuel + 1265)
        [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
        (.some yulName_fun__cbrt512) (.some yulContract)
        (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) coreStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) coreStore,
        [FormalYul.word r]))) :
    EvmYul.Yul.call (fuel + 1300) [FormalYul.word xHi, FormalYul.word xLo]
      (.some yulName_fun_wrap_cbrt512) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [FormalYul.word (icbrt (xHi * FormalYul.WORD_MOD + xLo))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_wrap_cbrt512]
  simp only [yulFunction_fun_wrap_cbrt512, yulFunction_fun_wrap_cbrt512_6227,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let paramStore :=
    Finmap.insert "var_x_hi_6210" (EvmYul.UInt256.ofNat xHi)
      (Finmap.insert "var_x_lo_6212" (EvmYul.UInt256.ofNat xLo)
        (Inhabited.default : EvmYul.Yul.VarStore))
  have hzero :
      EvmYul.Yul.call (fuel + 1296) [] (.some "zero_value_for_split_t_uint256")
        (.some yulContract) (EvmYul.Yul.State.Ok shared paramStore) =
      .ok (EvmYul.Yul.State.Ok shared paramStore, [FormalYul.word 0]) := by
    simpa [paramStore] using
      call_zero_value_for_split_t_uint256_direct
        (fuel := fuel) (extra := 1276) (shared := shared) (store := paramStore)
        (hlookup := hlookup)
  let tmpStore :=
    Finmap.insert "var__6215" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "zero_t_uint256_4" (EvmYul.UInt256.ofNat 0) paramStore)
  have htmp :
      EvmYul.Yul.call (fuel + 1294) [] (.some yulName_fun_tmp) (.some yulContract)
        (EvmYul.Yul.State.Ok shared tmpStore) =
      .ok (EvmYul.Yul.State.Ok shared tmpStore, [FormalYul.word 0]) := by
    simpa [tmpStore, FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_tmp_128_direct (fuel := fuel + 1254) (shared := shared)
        (store := tmpStore) (hlookup := hlookup)
  let fromStore :=
    Finmap.insert "expr_6221" (EvmYul.UInt256.ofNat xLo)
      (Finmap.insert "_6" (EvmYul.UInt256.ofNat xLo)
        (Finmap.insert "expr_6220" (EvmYul.UInt256.ofNat xHi)
          (Finmap.insert "_5" (EvmYul.UInt256.ofNat xHi)
            (Finmap.insert "expr_6219_self" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "expr_6218" (EvmYul.UInt256.ofNat 0) tmpStore)))))
  have hfrom :
      EvmYul.Yul.call (fuel + 1288)
        [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
        (.some yulName_fun_from) (.some yulContract)
        (EvmYul.Yul.State.Ok shared fromStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) fromStore,
        [EvmYul.UInt256.ofNat 0]) := by
    simpa [fromStore, FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_from_156_zero_direct (xHi := xHi) (xLo := xLo)
        (fuel := fuel + 1188) (shared := shared) (store := fromStore)
        (hlookup := hlookup)
  let cbrtStore :=
    Finmap.insert "expr_6223_self" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "expr_6222" (EvmYul.UInt256.ofNat 0) fromStore)
  have hcoreForCbrt :
      (let zeroStore :=
        Finmap.insert "var_x_4994" (EvmYul.UInt256.ofNat 0)
          (Inhabited.default : EvmYul.Yul.VarStore)
       let intoStore :=
        Finmap.insert "expr_5004_self" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "expr_5003" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "_16" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "var_r_4997" (EvmYul.UInt256.ofNat 0)
                (Finmap.insert "zero_t_uint256_15" (EvmYul.UInt256.ofNat 0)
                  zeroStore))))
       let convertStore :=
        Finmap.insert "expr_5008" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "expr_5007" (EvmYul.UInt256.ofNat xHi)
            (Finmap.insert "_17" (EvmYul.UInt256.ofNat xHi)
              (Finmap.insert "var_x_lo_5002" (EvmYul.UInt256.ofNat xLo)
                (Finmap.insert "var_x_hi_5000" (EvmYul.UInt256.ofNat xHi)
                  (Finmap.insert "expr_5005_component_1" (EvmYul.UInt256.ofNat xHi)
                    (Finmap.insert "expr_5005_component_2" (EvmYul.UInt256.ofNat xLo)
                      intoStore))))))
       let coreStore :=
        Finmap.insert "expr_5019" (EvmYul.UInt256.ofNat xLo)
          (Finmap.insert "_20" (EvmYul.UInt256.ofNat xLo)
            (Finmap.insert "expr_5018" (EvmYul.UInt256.ofNat xHi)
              (Finmap.insert "_19" (EvmYul.UInt256.ofNat xHi)
                (Finmap.insert "expr_5009" (EvmYul.UInt256.ofNat 0) convertStore))))
       EvmYul.Yul.call ((fuel + 286) + 979)
        [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
        (.some yulName_fun__cbrt512) (.some yulContract)
        (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) coreStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) coreStore,
        [FormalYul.word r])) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcoreRaw
  have hcbrt :
      EvmYul.Yul.call (fuel + 1286) [EvmYul.UInt256.ofNat 0]
        (.some yulName_fun_cbrt512) (.some yulContract)
        (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) cbrtStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) cbrtStore,
        [FormalYul.word (icbrt (xHi * FormalYul.WORD_MOD + xLo))]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_cbrt512_high_from0_of_core_direct
        (xHi := xHi) (xLo := xLo) (r := r) (fuel := fuel + 286)
        (shared := shared) (store := cbrtStore) (hlookup := hlookup)
        (hactive := hactive) (hxHi := hxHi) (hxLo := hxLo)
        (hxHiPos := hxHiPos) (hr := hr) (hcube := hcube)
        (hwithin := hwithin) hcoreForCbrt
  simp +decide [EvmYul.Yul.exec.eq_def,
    EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.store,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
    hzero, htmp, hfrom, hcbrt, paramStore, tmpStore, fromStore, cbrtStore,
    FormalYul.word, Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

private theorem call_fun_wrap_cbrtUp512_zero_direct
    (xLo fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    EvmYul.Yul.call (fuel + 1300) [FormalYul.word 0, FormalYul.word xLo]
      (.some yulName_fun_wrap_cbrtUp512) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) store,
      [FormalYul.word (cbrtUp256 (FormalYul.u256 xLo))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_wrap_cbrtUp512]
  simp only [yulFunction_fun_wrap_cbrtUp512, yulFunction_fun_wrap_cbrtUp512_6246,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let paramStore :=
    Finmap.insert "var_x_hi_6229" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "var_x_lo_6231" (EvmYul.UInt256.ofNat xLo)
        (Inhabited.default : EvmYul.Yul.VarStore))
  have hzero :
      EvmYul.Yul.call (fuel + 1296) [] (.some "zero_value_for_split_t_uint256")
        (.some yulContract) (EvmYul.Yul.State.Ok shared paramStore) =
      .ok (EvmYul.Yul.State.Ok shared paramStore, [FormalYul.word 0]) := by
    simpa [paramStore] using
      call_zero_value_for_split_t_uint256_direct
        (fuel := fuel) (extra := 1276) (shared := shared) (store := paramStore)
        (hlookup := hlookup)
  let tmpStore :=
    Finmap.insert "var__6234" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "zero_t_uint256_1" (EvmYul.UInt256.ofNat 0) paramStore)
  have htmp :
      EvmYul.Yul.call (fuel + 1294) [] (.some yulName_fun_tmp) (.some yulContract)
        (EvmYul.Yul.State.Ok shared tmpStore) =
      .ok (EvmYul.Yul.State.Ok shared tmpStore, [FormalYul.word 0]) := by
    simpa [tmpStore, FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_tmp_128_direct (fuel := fuel + 1254) (shared := shared)
        (store := tmpStore) (hlookup := hlookup)
  let fromStore :=
    Finmap.insert "expr_6240" (EvmYul.UInt256.ofNat xLo)
      (Finmap.insert "_3" (EvmYul.UInt256.ofNat xLo)
        (Finmap.insert "expr_6239" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "_2" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "expr_6238_self" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "expr_6237" (EvmYul.UInt256.ofNat 0) tmpStore)))))
  have hfrom :
      EvmYul.Yul.call (fuel + 1288)
        [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat xLo]
        (.some yulName_fun_from) (.some yulContract)
        (EvmYul.Yul.State.Ok shared fromStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) fromStore,
        [EvmYul.UInt256.ofNat 0]) := by
    simpa [fromStore, FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_from_156_zero_direct (xHi := 0) (xLo := xLo)
        (fuel := fuel + 1188) (shared := shared) (store := fromStore)
        (hlookup := hlookup)
  let cbrtStore :=
    Finmap.insert "expr_6242_self" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "expr_6241" (EvmYul.UInt256.ofNat 0) fromStore)
  have hcbrt :
      EvmYul.Yul.call (fuel + 1286) [EvmYul.UInt256.ofNat 0]
        (.some yulName_fun_cbrtUp512) (.some yulContract)
        (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) cbrtStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared 0 xLo) cbrtStore,
        [FormalYul.word (cbrtUp256 (FormalYul.u256 xLo))]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_cbrtUp512_zero_from0_direct (xLo := xLo) (fuel := fuel + 286)
        (shared := shared) (store := cbrtStore)
        (hlookup := hlookup) (hactive := hactive)
  simp +decide [EvmYul.Yul.exec.eq_def,
    EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.store,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
    hzero, htmp, hfrom, hcbrt, paramStore, tmpStore, fromStore, cbrtStore,
    FormalYul.word, Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

private theorem call_validator_revert_t_uint256_direct
    (v : EvmYul.UInt256) (fuel : Nat)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 30) [v] (.some "validator_revert_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, []) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_validator_revert_t_uint256]
  simp only [yulFunction_validator_revert_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcleanup :
      EvmYul.Yul.call (fuel + 21) [v] (.some "cleanup_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok shared
          (Finmap.insert "value" v (Inhabited.default : EvmYul.Yul.VarStore))) =
      .ok (EvmYul.Yul.State.Ok shared
          (Finmap.insert "value" v (Inhabited.default : EvmYul.Yul.VarStore)), [v]) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_cleanup_t_uint256_direct (v := v) (fuel := fuel + 1)
        (shared := shared)
        (store := Finmap.insert "value" v (Inhabited.default : EvmYul.Yul.VarStore))
        (hlookup := hlookup)
  simp +decide [EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    hcleanup]

private theorem call_allocate_unbounded_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 30) [] (.some "allocate_unbounded") (.some yulContract)
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
  simp +decide [EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.toMachineState, FormalYul.word,
    Finmap.lookup_insert]

private theorem call_abi_encode_t_uint256_to_t_uint256_fromStack_direct
    (value pos : EvmYul.UInt256) (fuel : Nat)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 80) [value, pos]
      (.some "abi_encode_t_uint256_to_t_uint256_fromStack") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok
      ((EvmYul.Yul.State.Ok shared store).setMachineState
        ((EvmYul.Yul.State.Ok shared store).toMachineState.mstore pos value),
        []) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_abi_encode_t_uint256_to_t_uint256_fromStack]
  simp only [yulFunction_abi_encode_t_uint256_to_t_uint256_fromStack,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcleanup :
      EvmYul.Yul.call (fuel + 74) [value] (.some "cleanup_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok shared
          (Finmap.insert "value" value
            (Finmap.insert "pos" pos (Inhabited.default : EvmYul.Yul.VarStore)))) =
      .ok (EvmYul.Yul.State.Ok shared
          (Finmap.insert "value" value
            (Finmap.insert "pos" pos (Inhabited.default : EvmYul.Yul.VarStore))), [value]) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_cleanup_t_uint256_direct (v := value) (fuel := fuel + 54)
        (shared := shared)
        (store := Finmap.insert "value" value
          (Finmap.insert "pos" pos (Inhabited.default : EvmYul.Yul.VarStore)))
        (hlookup := hlookup)
  simp +decide [EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.toMachineState, hcleanup]

private theorem call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack_direct
    (pos value : EvmYul.UInt256) (fuel : Nat)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 120) [pos, value]
      (.some "abi_encode_tuple_t_uint256__to_t_uint256__fromStack") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok
      ((EvmYul.Yul.State.Ok shared store).setMachineState
        ((EvmYul.Yul.State.Ok shared store).toMachineState.mstore pos value),
        [pos + EvmYul.UInt256.ofNat 32]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_abi_encode_tuple_t_uint256__to_t_uint256__fromStack]
  simp only [yulFunction_abi_encode_tuple_t_uint256__to_t_uint256__fromStack,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let encStore : EvmYul.Yul.VarStore :=
    Finmap.insert "tail" (pos + EvmYul.UInt256.ofNat 32)
      (Finmap.insert "headStart" pos
        (Finmap.insert "value0" value (Inhabited.default : EvmYul.Yul.VarStore)))
  have hencode :
      EvmYul.Yul.call (fuel + 115) [value, pos]
        (.some "abi_encode_t_uint256_to_t_uint256_fromStack") (.some yulContract)
        (EvmYul.Yul.State.Ok shared encStore) =
      .ok ((EvmYul.Yul.State.Ok shared encStore).setMachineState
          ((EvmYul.Yul.State.Ok shared encStore).toMachineState.mstore pos value), []) := by
    simpa [encStore, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_abi_encode_t_uint256_to_t_uint256_fromStack_direct
        (value := value) (pos := pos) (fuel := fuel + 35)
        (shared := shared) (store := encStore) (hlookup := hlookup)
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.toMachineState,
    hencode, encStore, Finmap.lookup_insert]

@[simp] private theorem uint256_add_sub_self_32 (p : EvmYul.UInt256) :
    p + EvmYul.UInt256.ofNat 32 - p = EvmYul.UInt256.ofNat 32 := by
  apply FormalYul.Preservation.eq_of_wordNat_eq
  change FormalYul.wordNat (p + EvmYul.UInt256.ofNat 32 - p) =
    FormalYul.wordNat (EvmYul.UInt256.ofNat 32)
  simp only [FormalYul.Preservation.wordNat_sub, FormalYul.Preservation.wordNat_add,
    FormalYul.Preservation.wordNat_ofNat]
  unfold FormalYul.evmAdd FormalYul.evmSub FormalYul.u256 FormalYul.WORD_MOD
  let n := FormalYul.wordNat p
  have hn : n < 2 ^ 256 := by
    change FormalYul.wordNat p < 2 ^ 256
    simp [FormalYul.wordNat, EvmYul.UInt256.toNat, EvmYul.UInt256.size]
  have hM32 : 32 < 2 ^ 256 := by norm_num
  change (((n % 2 ^ 256 + 32 % 2 ^ 256 % 2 ^ 256) % 2 ^ 256 % 2 ^ 256 +
      2 ^ 256 - n % 2 ^ 256) % 2 ^ 256) = 32 % 2 ^ 256
  rw [Nat.mod_eq_of_lt hn]
  rw [Nat.mod_eq_of_lt hM32]
  by_cases h : n + 32 < 2 ^ 256
  · rw [Nat.mod_eq_of_lt h]
    rw [Nat.mod_eq_of_lt h]
    have hsum : n + 32 + 2 ^ 256 - n = 2 ^ 256 + 32 := by omega
    rw [hsum]
    rw [Nat.add_mod_left]
    exact Nat.mod_eq_of_lt hM32
  · have hge : n + 32 ≥ 2 ^ 256 := by omega
    rw [Nat.mod_eq_sub_mod hge]
    have hsmall : n + 32 - 2 ^ 256 < 2 ^ 256 := by omega
    rw [Nat.mod_eq_of_lt hsmall]
    rw [Nat.mod_eq_of_lt hsmall]
    have hsum : n + 32 - 2 ^ 256 + 2 ^ 256 - n = 32 := by omega
    rw [hsum]

private theorem call_abi_decode_t_uint256_selector_two_args_arg0_of_calldata
    (a b c d xHi xLo fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata =
      FormalYul.bytes [a, b, c, d] ++ FormalYul.encodeWords [xHi, xLo]) :
    EvmYul.Yul.call (fuel + 50) [FormalYul.word 4, FormalYul.word 68]
      (.some "abi_decode_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word xHi]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_abi_decode_t_uint256]
  simp only [yulFunction_abi_decode_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hvalidator :
      EvmYul.Yul.call (fuel + 45) [FormalYul.word xHi] (.some "validator_revert_t_uint256")
        (.some yulContract) (EvmYul.Yul.State.Ok shared
          (Finmap.insert "value" (FormalYul.word xHi)
            (Finmap.insert "offset" (FormalYul.word 4)
              (Finmap.insert "end" (FormalYul.word 68)
                (Inhabited.default : EvmYul.Yul.VarStore))))) =
      .ok (EvmYul.Yul.State.Ok shared
          (Finmap.insert "value" (FormalYul.word xHi)
            (Finmap.insert "offset" (FormalYul.word 4)
              (Finmap.insert "end" (FormalYul.word 68)
                (Inhabited.default : EvmYul.Yul.VarStore)))), []) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_validator_revert_t_uint256_direct (v := FormalYul.word xHi)
        (fuel := fuel + 15) (shared := shared)
        (store := Finmap.insert "value" (FormalYul.word xHi)
          (Finmap.insert "offset" (FormalYul.word 4)
            (Finmap.insert "end" (FormalYul.word 68)
              (Inhabited.default : EvmYul.Yul.VarStore))))
        (hlookup := hlookup)
  have hload :
      EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok shared
          (Finmap.insert "offset" (FormalYul.word 4)
            (Finmap.insert "end" (FormalYul.word 68)
              (Inhabited.default : EvmYul.Yul.VarStore)))).toState
        (FormalYul.word 4) = FormalYul.word xHi := by
    exact FormalYul.Preservation.calldataload_two_args_first_of_calldata
      (a := a) (b := b) (c := c) (d := d) (x := xHi) (y := xLo)
      (shared := shared)
      (store := Finmap.insert "offset" (FormalYul.word 4)
        (Finmap.insert "end" (FormalYul.word 68)
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hdata := hdata)
  simp +decide [hload, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    hvalidator, Finmap.lookup_insert]

private theorem call_abi_decode_t_uint256_selector_two_args_arg1_of_calldata
    (a b c d xHi xLo fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata =
      FormalYul.bytes [a, b, c, d] ++ FormalYul.encodeWords [xHi, xLo]) :
    EvmYul.Yul.call (fuel + 50) [FormalYul.word 36, FormalYul.word 68]
      (.some "abi_decode_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word xLo]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_abi_decode_t_uint256]
  simp only [yulFunction_abi_decode_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hvalidator :
      EvmYul.Yul.call (fuel + 45) [FormalYul.word xLo] (.some "validator_revert_t_uint256")
        (.some yulContract) (EvmYul.Yul.State.Ok shared
          (Finmap.insert "value" (FormalYul.word xLo)
            (Finmap.insert "offset" (FormalYul.word 36)
              (Finmap.insert "end" (FormalYul.word 68)
                (Inhabited.default : EvmYul.Yul.VarStore))))) =
      .ok (EvmYul.Yul.State.Ok shared
          (Finmap.insert "value" (FormalYul.word xLo)
            (Finmap.insert "offset" (FormalYul.word 36)
              (Finmap.insert "end" (FormalYul.word 68)
                (Inhabited.default : EvmYul.Yul.VarStore)))), []) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_validator_revert_t_uint256_direct (v := FormalYul.word xLo)
        (fuel := fuel + 15) (shared := shared)
        (store := Finmap.insert "value" (FormalYul.word xLo)
          (Finmap.insert "offset" (FormalYul.word 36)
            (Finmap.insert "end" (FormalYul.word 68)
              (Inhabited.default : EvmYul.Yul.VarStore))))
        (hlookup := hlookup)
  have hload :
      EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok shared
          (Finmap.insert "offset" (FormalYul.word 36)
            (Finmap.insert "end" (FormalYul.word 68)
              (Inhabited.default : EvmYul.Yul.VarStore)))).toState
        (FormalYul.word 36) = FormalYul.word xLo := by
    exact FormalYul.Preservation.calldataload_two_args_second_of_calldata
      (a := a) (b := b) (c := c) (d := d) (x := xHi) (y := xLo)
      (shared := shared)
      (store := Finmap.insert "offset" (FormalYul.word 36)
        (Finmap.insert "end" (FormalYul.word 68)
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hdata := hdata)
  simp +decide [hload, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    hvalidator, Finmap.lookup_insert]

private theorem call_abi_decode_t_uint256_selector_two_args_arg0_153_formal
    (a b c d xHi xLo fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata =
      FormalYul.bytes [a, b, c, d] ++ FormalYul.encodeWords [xHi, xLo]) :
    EvmYul.Yul.call (fuel + 153) [FormalYul.word 4, FormalYul.word 68]
      (.some "abi_decode_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word xHi]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_abi_decode_t_uint256_selector_two_args_arg0_of_calldata
      (a := a) (b := b) (c := c) (d := d) (xHi := xHi) (xLo := xLo)
      (fuel := fuel + 103) (shared := shared)
      (store := store) (hlookup := hlookup) (hdata := hdata)

private theorem call_abi_decode_t_uint256_selector_two_args_arg1_152
    (a b c d xHi xLo fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata =
      FormalYul.bytes [a, b, c, d] ++ FormalYul.encodeWords [xHi, xLo]) :
    EvmYul.Yul.call (fuel + 152) [EvmYul.UInt256.ofNat 36, EvmYul.UInt256.ofNat 68]
      (.some "abi_decode_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat xLo]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_abi_decode_t_uint256_selector_two_args_arg1_of_calldata
      (a := a) (b := b) (c := c) (d := d) (xHi := xHi) (xLo := xLo)
      (fuel := fuel + 102) (shared := shared)
      (store := store) (hlookup := hlookup) (hdata := hdata)

private theorem call_abi_decode_tuple_t_uint256t_uint256_selector_two_args_of_calldata
    (a b c d xHi xLo fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata =
      FormalYul.bytes [a, b, c, d] ++ FormalYul.encodeWords [xHi, xLo]) :
    EvmYul.Yul.call (fuel + 160) [FormalYul.word 4, FormalYul.word 68]
      (.some "abi_decode_tuple_t_uint256t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word xHi, FormalYul.word xLo]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_abi_decode_tuple_t_uint256t_uint256]
  simp only [yulFunction_abi_decode_tuple_t_uint256t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?]
  rw [call_abi_decode_t_uint256_selector_two_args_arg0_153_formal
      a b c d xHi xLo fuel shared _ hlookup hdata]
  simp +decide only [GetElem?.getElem!, GetElem.getElem, decidableGetElem?,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.store, List.zip,
    List.zipWith_cons_cons, List.zipWith_nil_right, List.foldr,
    Finmap.lookup_insert, Finmap.mem_insert, dif_pos, Option.get!, FormalYul.word]
  let decoded0Store : EvmYul.Yul.VarStore :=
    Finmap.insert "offset" (FormalYul.word 32)
      (Finmap.insert "value0" (FormalYul.word xHi)
        (Finmap.insert "offset" (FormalYul.word 0)
          (Finmap.insert "headStart" (FormalYul.word 4)
            (Finmap.insert "dataEnd" (FormalYul.word 68)
              (Inhabited.default : EvmYul.Yul.VarStore)))))
  have hadd : EvmYul.UInt256.ofNat 4 + EvmYul.UInt256.ofNat 32 =
      EvmYul.UInt256.ofNat 36 := by
    decide
  have hsecond :
      EvmYul.Yul.call (fuel + 152)
        [EvmYul.UInt256.ofNat 4 + EvmYul.UInt256.ofNat 32, EvmYul.UInt256.ofNat 68]
        (.some "abi_decode_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok shared
          (Finmap.insert "offset" (EvmYul.UInt256.ofNat 32)
            (Finmap.insert "value0" (EvmYul.UInt256.ofNat xHi)
              (Finmap.insert "offset" (EvmYul.UInt256.ofNat 0)
                (Finmap.insert "headStart" (EvmYul.UInt256.ofNat 4)
                  (Finmap.insert "dataEnd" (EvmYul.UInt256.ofNat 68)
                    (Inhabited.default : EvmYul.Yul.VarStore))))))) =
      .ok (EvmYul.Yul.State.Ok shared
          (Finmap.insert "offset" (EvmYul.UInt256.ofNat 32)
            (Finmap.insert "value0" (EvmYul.UInt256.ofNat xHi)
              (Finmap.insert "offset" (EvmYul.UInt256.ofNat 0)
                (Finmap.insert "headStart" (EvmYul.UInt256.ofNat 4)
                  (Finmap.insert "dataEnd" (EvmYul.UInt256.ofNat 68)
                    (Inhabited.default : EvmYul.Yul.VarStore)))))),
        [EvmYul.UInt256.ofNat xLo]) := by
    simpa [decoded0Store, FormalYul.word, hadd, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      call_abi_decode_t_uint256_selector_two_args_arg1_152
        a b c d xHi xLo fuel shared decoded0Store hlookup hdata
  simp +decide [hsecond, List.zipWith_cons_cons, List.zipWith_nil_right,
    List.foldr, Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

private def cbrt512SharedAfterFreePtr (xHi xLo : Nat) : EvmYul.SharedState .Yul :=
  let shared := FormalYul.sharedFor yulContract
    (selector_cbrt512 ++ FormalYul.encodeWords [xHi, xLo])
  { shared with toMachineState := shared.toMachineState.mstore (FormalYul.word 64) (FormalYul.word 128) }

private def cbrtUp512SharedAfterFreePtr (xHi xLo : Nat) : EvmYul.SharedState .Yul :=
  let shared := FormalYul.sharedFor yulContract
    (selector_cbrtUp512 ++ FormalYul.encodeWords [xHi, xLo])
  { shared with toMachineState := shared.toMachineState.mstore (FormalYul.word 64) (FormalYul.word 128) }

private theorem sharedFor_inherited_mstore_mk_eq_cbrt512SharedAfterFreePtr
    (xHi xLo : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract
          (selector_cbrt512 ++ FormalYul.encodeWords [xHi, xLo])).toState
        ((FormalYul.sharedFor yulContract
          (selector_cbrt512 ++ FormalYul.encodeWords [xHi, xLo])).mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      cbrt512SharedAfterFreePtr xHi xLo := rfl

private theorem sharedFor_inherited_mstore_mk_eq_cbrt512SharedAfterFreePtr_raw
    (xHi xLo : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract
          (selector_cbrt512 ++ FormalYul.encodeWords [xHi, xLo])).toState
        ((FormalYul.sharedFor yulContract
          (selector_cbrt512 ++ FormalYul.encodeWords [xHi, xLo])).mstore
          (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128))) =
      cbrt512SharedAfterFreePtr xHi xLo := by
  simpa [FormalYul.word] using
    sharedFor_inherited_mstore_mk_eq_cbrt512SharedAfterFreePtr xHi xLo

private theorem sharedFor_inherited_mstore_mk_eq_cbrtUp512SharedAfterFreePtr
    (xHi xLo : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract
          (selector_cbrtUp512 ++ FormalYul.encodeWords [xHi, xLo])).toState
        ((FormalYul.sharedFor yulContract
          (selector_cbrtUp512 ++ FormalYul.encodeWords [xHi, xLo])).mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      cbrtUp512SharedAfterFreePtr xHi xLo := rfl

private theorem sharedFor_inherited_mstore_mk_eq_cbrtUp512SharedAfterFreePtr_raw
    (xHi xLo : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract
          (selector_cbrtUp512 ++ FormalYul.encodeWords [xHi, xLo])).toState
        ((FormalYul.sharedFor yulContract
          (selector_cbrtUp512 ++ FormalYul.encodeWords [xHi, xLo])).mstore
          (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128))) =
      cbrtUp512SharedAfterFreePtr xHi xLo := by
  simpa [FormalYul.word] using
    sharedFor_inherited_mstore_mk_eq_cbrtUp512SharedAfterFreePtr xHi xLo

@[simp] private theorem cbrt512SharedAfterFreePtr_lookup (xHi xLo : Nat) :
    (cbrt512SharedAfterFreePtr xHi xLo).accountMap.find?
      (cbrt512SharedAfterFreePtr xHi xLo).executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract) := by
  simp [cbrt512SharedAfterFreePtr]

@[simp] private theorem cbrtUp512SharedAfterFreePtr_lookup (xHi xLo : Nat) :
    (cbrtUp512SharedAfterFreePtr xHi xLo).accountMap.find?
      (cbrtUp512SharedAfterFreePtr xHi xLo).executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract) := by
  simp [cbrtUp512SharedAfterFreePtr]

@[simp] private theorem cbrt512SharedAfterFreePtr_calldata (xHi xLo : Nat) :
    (cbrt512SharedAfterFreePtr xHi xLo).executionEnv.calldata =
      selector_cbrt512 ++ FormalYul.encodeWords [xHi, xLo] := by
  simp [cbrt512SharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp] private theorem cbrtUp512SharedAfterFreePtr_calldata (xHi xLo : Nat) :
    (cbrtUp512SharedAfterFreePtr xHi xLo).executionEnv.calldata =
      selector_cbrtUp512 ++ FormalYul.encodeWords [xHi, xLo] := by
  simp [cbrtUp512SharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp] private theorem cbrt512SharedAfterFreePtr_weiValue (xHi xLo : Nat) :
    (cbrt512SharedAfterFreePtr xHi xLo).executionEnv.weiValue =
      ({ val := 0 } : EvmYul.UInt256) := by
  simp [cbrt512SharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp] private theorem cbrtUp512SharedAfterFreePtr_weiValue (xHi xLo : Nat) :
    (cbrtUp512SharedAfterFreePtr xHi xLo).executionEnv.weiValue =
      ({ val := 0 } : EvmYul.UInt256) := by
  simp [cbrtUp512SharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp] private theorem cbrt512SharedAfterFreePtr_activeWords (xHi xLo : Nat) :
    (cbrt512SharedAfterFreePtr xHi xLo).toMachineState.activeWords = FormalYul.word 3 := by
  simp [cbrt512SharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor,
    EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord, EvmYul.MachineState.M,
    FormalYul.word]
  decide

@[simp] private theorem cbrtUp512SharedAfterFreePtr_activeWords (xHi xLo : Nat) :
    (cbrtUp512SharedAfterFreePtr xHi xLo).toMachineState.activeWords = FormalYul.word 3 := by
  simp [cbrtUp512SharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor,
    EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord, EvmYul.MachineState.M,
    FormalYul.word]
  decide

@[simp] private theorem cbrt512_calldata_size (xHi xLo : Nat) :
    (selector_cbrt512 ++ FormalYul.encodeWords [xHi, xLo]).size = 68 := by
  have hHi : (FormalYul.encodeWord xHi).size = 32 := by
    change (FormalYul.encodeWord xHi).data.size = 32
    rw [← Array.length_toList]
    simp [FormalYul.Preservation.encodeWord_data_toList]
  have hLo : (FormalYul.encodeWord xLo).size = 32 := by
    change (FormalYul.encodeWord xLo).data.size = 32
    rw [← Array.length_toList]
    simp [FormalYul.Preservation.encodeWord_data_toList]
  simp [selector_cbrt512, FormalYul.encodeWords,
    FormalYul.bytes, ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
    hHi, hLo]

@[simp] private theorem cbrtUp512_calldata_size (xHi xLo : Nat) :
    (selector_cbrtUp512 ++ FormalYul.encodeWords [xHi, xLo]).size = 68 := by
  have hHi : (FormalYul.encodeWord xHi).size = 32 := by
    change (FormalYul.encodeWord xHi).data.size = 32
    rw [← Array.length_toList]
    simp [FormalYul.Preservation.encodeWord_data_toList]
  have hLo : (FormalYul.encodeWord xLo).size = 32 := by
    change (FormalYul.encodeWord xLo).data.size = 32
    rw [← Array.length_toList]
    simp [FormalYul.Preservation.encodeWord_data_toList]
  simp [selector_cbrtUp512, FormalYul.encodeWords,
    FormalYul.bytes, ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
    hHi, hLo]

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

@[simp] private theorem cbrt512_selector_afterFreePtr (xHi xLo : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok (cbrt512SharedAfterFreePtr xHi xLo)
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 2822396936 := by
  let tail : List UInt8 := (FormalYul.encodeWord xHi).data.toList.take 28
  have htailLen : tail.length = 28 := by
    simp [tail, FormalYul.Preservation.encodeWord_data_toList]
  have hread :
      ((selector_cbrt512 ++ FormalYul.encodeWords [xHi, xLo]).readBytes 0 32).data.toList =
        [0xa8, 0x3a, 0x5c, 0x08] ++ tail := by
    simp [tail, ByteArray.readBytes, selector_cbrt512, FormalYul.encodeWords, FormalYul.bytes,
      ByteArray.push, ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.size,
      ffi.ByteArray.zeroes, List.take_append, FormalYul.Preservation.encodeWord_data_toList]
  have hselector :=
    FormalYul.Preservation.shiftRight_calldataload_selector_of_readBytes
      (shared := cbrt512SharedAfterFreePtr xHi xLo)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (selectorBytes := [0xa8, 0x3a, 0x5c, 0x08]) (tail := tail)
      (by decide) htailLen
      (by simpa [cbrt512SharedAfterFreePtr_calldata] using hread)
  simpa [EvmYul.fromBytesBigEndian, EvmYul.fromBytes', FormalYul.word] using hselector

@[simp] private theorem cbrtUp512_selector_afterFreePtr (xHi xLo : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok (cbrtUp512SharedAfterFreePtr xHi xLo)
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 2080592636 := by
  let tail : List UInt8 := (FormalYul.encodeWord xHi).data.toList.take 28
  have htailLen : tail.length = 28 := by
    simp [tail, FormalYul.Preservation.encodeWord_data_toList]
  have hread :
      ((selector_cbrtUp512 ++ FormalYul.encodeWords [xHi, xLo]).readBytes 0 32).data.toList =
        [0x7c, 0x03, 0x52, 0xfc] ++ tail := by
    simp [tail, ByteArray.readBytes, selector_cbrtUp512, FormalYul.encodeWords, FormalYul.bytes,
      ByteArray.push, ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.size,
      ffi.ByteArray.zeroes, List.take_append, FormalYul.Preservation.encodeWord_data_toList]
  have hselector :=
    FormalYul.Preservation.shiftRight_calldataload_selector_of_readBytes
      (shared := cbrtUp512SharedAfterFreePtr xHi xLo)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (selectorBytes := [0x7c, 0x03, 0x52, 0xfc]) (tail := tail)
      (by decide) htailLen
      (by simpa [cbrtUp512SharedAfterFreePtr_calldata] using hread)
  simpa [EvmYul.fromBytesBigEndian, EvmYul.fromBytes', FormalYul.word] using hselector

private theorem external_fun_wrap_cbrt512_zero_calldata_halts_999989
    (xLo : Nat) (store : EvmYul.Yul.VarStore) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_cbrt512) (.some yulContract)
        (EvmYul.Yul.State.Ok (cbrt512SharedAfterFreePtr 0 xLo) store) =
        .error (.YulHalt state value) ∧
      FormalYul.resultWord (FormalYul.returnOf state) =
        .ok (floorCbrt (FormalYul.u256 xLo)) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [
    cbrt512SharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_cbrt512]
  simp only [yulFunction_external_fun_wrap_cbrt512, yulFunction_external_fun_wrap_cbrt512_6227,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := floorCbrt (FormalYul.u256 xLo)
  let paramStore : EvmYul.Yul.VarStore :=
    Finmap.insert "param_0" (FormalYul.word 0)
      (Finmap.insert "param_1" (FormalYul.word xLo)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let baseStore : EvmYul.Yul.VarStore :=
    Finmap.insert "ret_0" (FormalYul.word ret) paramStore
  let wrapShared := sharedAfterFrom0 (cbrt512SharedAfterFreePtr 0 xLo) 0 xLo
  let memPos :=
    ((EvmYul.Yul.State.Ok wrapShared baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { wrapShared with
      toMachineState :=
        ((EvmYul.Yul.State.Ok wrapShared baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_uint256t_uint256_selector_two_args_of_calldata
      (a := 0xa8) (b := 0x3a) (c := 0x5c) (d := 0x08)
      (xHi := 0) (xLo := xLo) (fuel := 999824)
      (shared := cbrt512SharedAfterFreePtr 0 xLo)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := cbrt512SharedAfterFreePtr_lookup 0 xLo)
      (hdata := by
        rw [cbrt512SharedAfterFreePtr_calldata]
        rfl)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_cbrt512_zero_direct (xLo := xLo) (fuel := 998683)
      (shared := cbrt512SharedAfterFreePtr 0 xLo) (store := paramStore)
      (hlookup := cbrt512SharedAfterFreePtr_lookup 0 xLo)
      (hactive := cbrt512SharedAfterFreePtr_activeWords 0 xLo)
  simp [FormalYul.word, yulName_fun_wrap_cbrt512, paramStore] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999952) (shared := wrapShared)
      (store := baseStore)
      (hlookup := sharedAfterFrom0_lookup (cbrt512SharedAfterFreePtr 0 xLo) 0 xLo
        (cbrt512SharedAfterFreePtr_lookup 0 xLo))
  simp [FormalYul.word, baseStore, paramStore, ret, wrapShared] at halloc
  have hencode :=
    call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack_direct
      (pos := memPos) (value := FormalYul.word ret) (fuel := 999861)
      (shared := memShared) (store := encStore)
      (hlookup := by
        simp [memShared, wrapShared,
          sharedAfterFrom0_lookup (cbrt512SharedAfterFreePtr 0 xLo) 0 xLo
            (cbrt512SharedAfterFreePtr_lookup 0 xLo)])
  simp [FormalYul.word, memShared, encStore, memPos, baseStore, paramStore, ret,
    wrapShared] at hencode
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
    hdecode, hwrap, halloc, hencode]
  have hresult := FormalYul.Preservation.resultWord_evmReturn_mstore_word
    (((sharedAfterFrom0 (cbrt512SharedAfterFreePtr 0 xLo) 0 xLo).mload
      (EvmYul.UInt256.ofNat 64)).2)
    (((sharedAfterFrom0 (cbrt512SharedAfterFreePtr 0 xLo) 0 xLo).mload
      (EvmYul.UInt256.ofNat 64)).1)
    (EvmYul.UInt256.ofNat (floorCbrt (FormalYul.u256 xLo)))
  simp [FormalYul.word] at hresult
  rw [hresult]
  have hnat :
      (EvmYul.UInt256.ofNat (floorCbrt (FormalYul.u256 xLo))).toNat =
        floorCbrt (FormalYul.u256 xLo) := by
    change FormalYul.wordNat (EvmYul.UInt256.ofNat (floorCbrt (FormalYul.u256 xLo))) =
      floorCbrt (FormalYul.u256 xLo)
    exact (FormalYul.Preservation.wordNat_ofNat (floorCbrt (FormalYul.u256 xLo))).trans
      (FormalYul.Preservation.u256_eq_of_lt _
        (floorCbrt_lt_word (FormalYul.u256 xLo)
          (Nat.mod_lt xLo (by unfold WORD_MOD; exact Nat.two_pow_pos 256))))
  rw [hnat]

private theorem external_fun_wrap_cbrtUp512_zero_calldata_halts_999989
    (xLo : Nat) (store : EvmYul.Yul.VarStore) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_cbrtUp512)
        (.some yulContract)
        (EvmYul.Yul.State.Ok (cbrtUp512SharedAfterFreePtr 0 xLo) store) =
        .error (.YulHalt state value) ∧
      FormalYul.resultWord (FormalYul.returnOf state) =
        .ok (cbrtUp256 (FormalYul.u256 xLo)) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [
    cbrtUp512SharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_cbrtUp512]
  simp only [yulFunction_external_fun_wrap_cbrtUp512,
    yulFunction_external_fun_wrap_cbrtUp512_6246,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := cbrtUp256 (FormalYul.u256 xLo)
  let paramStore : EvmYul.Yul.VarStore :=
    Finmap.insert "param_0" (FormalYul.word 0)
      (Finmap.insert "param_1" (FormalYul.word xLo)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let baseStore : EvmYul.Yul.VarStore :=
    Finmap.insert "ret_0" (FormalYul.word ret) paramStore
  let wrapShared := sharedAfterFrom0 (cbrtUp512SharedAfterFreePtr 0 xLo) 0 xLo
  let memPos :=
    ((EvmYul.Yul.State.Ok wrapShared baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { wrapShared with
      toMachineState :=
        ((EvmYul.Yul.State.Ok wrapShared baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_uint256t_uint256_selector_two_args_of_calldata
      (a := 0x7c) (b := 0x03) (c := 0x52) (d := 0xfc)
      (xHi := 0) (xLo := xLo) (fuel := 999824)
      (shared := cbrtUp512SharedAfterFreePtr 0 xLo)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := cbrtUp512SharedAfterFreePtr_lookup 0 xLo)
      (hdata := by
        rw [cbrtUp512SharedAfterFreePtr_calldata]
        rfl)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_cbrtUp512_zero_direct (xLo := xLo) (fuel := 998683)
      (shared := cbrtUp512SharedAfterFreePtr 0 xLo) (store := paramStore)
      (hlookup := cbrtUp512SharedAfterFreePtr_lookup 0 xLo)
      (hactive := cbrtUp512SharedAfterFreePtr_activeWords 0 xLo)
  simp [FormalYul.word, yulName_fun_wrap_cbrtUp512, paramStore] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999952) (shared := wrapShared)
      (store := baseStore)
      (hlookup := sharedAfterFrom0_lookup (cbrtUp512SharedAfterFreePtr 0 xLo) 0 xLo
        (cbrtUp512SharedAfterFreePtr_lookup 0 xLo))
  simp [FormalYul.word, baseStore, paramStore, ret, wrapShared] at halloc
  have hencode :=
    call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack_direct
      (pos := memPos) (value := FormalYul.word ret) (fuel := 999861)
      (shared := memShared) (store := encStore)
      (hlookup := by
        simp [memShared, wrapShared,
          sharedAfterFrom0_lookup (cbrtUp512SharedAfterFreePtr 0 xLo) 0 xLo
            (cbrtUp512SharedAfterFreePtr_lookup 0 xLo)])
  simp [FormalYul.word, memShared, encStore, memPos, baseStore, paramStore, ret,
    wrapShared] at hencode
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
    hdecode, hwrap, halloc, hencode]
  have hresult := FormalYul.Preservation.resultWord_evmReturn_mstore_word
    (((sharedAfterFrom0 (cbrtUp512SharedAfterFreePtr 0 xLo) 0 xLo).mload
      (EvmYul.UInt256.ofNat 64)).2)
    (((sharedAfterFrom0 (cbrtUp512SharedAfterFreePtr 0 xLo) 0 xLo).mload
      (EvmYul.UInt256.ofNat 64)).1)
    (EvmYul.UInt256.ofNat (cbrtUp256 (FormalYul.u256 xLo)))
  simp [FormalYul.word] at hresult
  rw [hresult]
  have hnat :
      (EvmYul.UInt256.ofNat (cbrtUp256 (FormalYul.u256 xLo))).toNat =
        cbrtUp256 (FormalYul.u256 xLo) := by
    change FormalYul.wordNat (EvmYul.UInt256.ofNat (cbrtUp256 (FormalYul.u256 xLo))) =
      cbrtUp256 (FormalYul.u256 xLo)
    exact (FormalYul.Preservation.wordNat_ofNat (cbrtUp256 (FormalYul.u256 xLo))).trans
      (FormalYul.Preservation.u256_eq_of_lt _
        (cbrtUp256_lt_word (FormalYul.u256 xLo)
          (Nat.mod_lt xLo (by unfold WORD_MOD; exact Nat.two_pow_pos 256))))
  rw [hnat]

private theorem dispatcherReturn_cbrt512_zero
    (xLo : Nat) (haltState : EvmYul.Yul.State) (haltValue : EvmYul.Literal)
    (hhalt :
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_cbrt512) (.some yulContract)
        (EvmYul.Yul.State.Ok (cbrt512SharedAfterFreePtr 0 xLo)
          (Finmap.insert "selector" (FormalYul.word 2822396936)
            (Inhabited.default : EvmYul.Yul.VarStore))) =
        .error (.YulHalt haltState haltValue)) :
    FormalYul.Preservation.DispatcherReturn yulContract
      (FormalYul.calldata selector_cbrt512 [0, xLo]) 999998 (FormalYul.returnOf haltState) := by
  let start := FormalYul.stateFor yulContract
    (FormalYul.calldata selector_cbrt512 [0, xLo])
  let afterFreePtr : EvmYul.Yul.State :=
    EvmYul.Yul.State.Ok (cbrt512SharedAfterFreePtr 0 xLo)
      (Inhabited.default : EvmYul.Yul.VarStore)
  let afterSelector : EvmYul.Yul.State :=
    EvmYul.Yul.State.Ok (cbrt512SharedAfterFreePtr 0 xLo)
      (Finmap.insert "selector" (FormalYul.word 2822396936)
        (Inhabited.default : EvmYul.Yul.VarStore))
  apply FormalYul.Preservation.dispatcherReturn_of_execReturn
    (hdispatcher := yulContract_dispatcher)
  simpa [start, afterFreePtr, afterSelector, yulDispatcher, FormalYul.calldata,
      yulName_external_fun_wrap_cbrt512, yulName_external_fun_wrap_cbrtUp512] using
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
        [(FormalYul.word 2080592636,
            [EvmYul.Yul.Ast.Stmt.ExprStmtCall
              (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_cbrtUp512) [])]),
          (FormalYul.word 2822396936,
            [EvmYul.Yul.Ast.Stmt.ExprStmtCall
              (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_cbrt512) [])])])
      (defaultStmts := [])
      (fn := yulName_external_fun_wrap_cbrt512)
      (code := .some yulContract)
      (start := start)
      (afterFirst := afterFreePtr)
      (branchStart := afterFreePtr)
      (afterLet := afterSelector)
      (switchStart := afterSelector)
      (condValue := FormalYul.word 1)
      (selector := FormalYul.word 2822396936)
      (result := FormalYul.returnOf haltState)
      (hfirst := by
        simp +decide [start, afterFreePtr, FormalYul.stateFor, FormalYul.calldata,
          EvmYul.Yul.execPrimCall.eq_def,
          EvmYul.Yul.reverse', EvmYul.Yul.cons',
          EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
          EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
          EvmYul.Yul.State.toMachineState,
          sharedFor_inherited_mstore_mk_eq_cbrt512SharedAfterFreePtr_raw])
      (hcond := by
        simp +decide [afterFreePtr,
          EvmYul.Yul.evalPrimCall.eq_def,
          EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
          EvmYul.Yul.evalTail.eq_def,
          EvmYul.Yul.State.executionEnv, FormalYul.word,
          cbrt512SharedAfterFreePtr_calldata, cbrt512_calldata_size])
      (hcondNe := by decide)
      (hlet := by
        have hselector :
            ((EvmYul.Yul.State.Ok (cbrt512SharedAfterFreePtr 0 xLo)
                (Inhabited.default : EvmYul.Yul.VarStore)).toState.calldataload
                (EvmYul.UInt256.ofNat 0)).shiftRight
              (EvmYul.UInt256.ofNat 224) =
              EvmYul.UInt256.ofNat 2822396936 := by
          simpa [FormalYul.word] using cbrt512_selector_afterFreePtr 0 xLo
        simp +decide [afterFreePtr, afterSelector,
          EvmYul.Yul.execCall.eq_def,
          EvmYul.Yul.evalPrimCall.eq_def,
          EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
          EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
          EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
          FormalYul.word, call_shift_right_224_unsigned_direct,
          hselector])
      (hswitchEval := by
        simp [afterSelector])
      (hselect := by
        rfl)
      (hcall := by
        exact ⟨haltState, haltValue, hhalt, rfl⟩))

private theorem dispatcherReturn_cbrtUp512_zero
    (xLo : Nat) (haltState : EvmYul.Yul.State) (haltValue : EvmYul.Literal)
    (hhalt :
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_cbrtUp512)
        (.some yulContract)
        (EvmYul.Yul.State.Ok (cbrtUp512SharedAfterFreePtr 0 xLo)
          (Finmap.insert "selector" (FormalYul.word 2080592636)
            (Inhabited.default : EvmYul.Yul.VarStore))) =
        .error (.YulHalt haltState haltValue)) :
    FormalYul.Preservation.DispatcherReturn yulContract
      (FormalYul.calldata selector_cbrtUp512 [0, xLo]) 999998
      (FormalYul.returnOf haltState) := by
  let start := FormalYul.stateFor yulContract
    (FormalYul.calldata selector_cbrtUp512 [0, xLo])
  let afterFreePtr : EvmYul.Yul.State :=
    EvmYul.Yul.State.Ok (cbrtUp512SharedAfterFreePtr 0 xLo)
      (Inhabited.default : EvmYul.Yul.VarStore)
  let afterSelector : EvmYul.Yul.State :=
    EvmYul.Yul.State.Ok (cbrtUp512SharedAfterFreePtr 0 xLo)
      (Finmap.insert "selector" (FormalYul.word 2080592636)
        (Inhabited.default : EvmYul.Yul.VarStore))
  apply FormalYul.Preservation.dispatcherReturn_of_execReturn
    (hdispatcher := yulContract_dispatcher)
  simpa [start, afterFreePtr, afterSelector, yulDispatcher, FormalYul.calldata,
      yulName_external_fun_wrap_cbrt512, yulName_external_fun_wrap_cbrtUp512] using
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
        [(FormalYul.word 2080592636,
            [EvmYul.Yul.Ast.Stmt.ExprStmtCall
              (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_cbrtUp512) [])]),
          (FormalYul.word 2822396936,
            [EvmYul.Yul.Ast.Stmt.ExprStmtCall
              (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_cbrt512) [])])])
      (defaultStmts := [])
      (fn := yulName_external_fun_wrap_cbrtUp512)
      (code := .some yulContract)
      (start := start)
      (afterFirst := afterFreePtr)
      (branchStart := afterFreePtr)
      (afterLet := afterSelector)
      (switchStart := afterSelector)
      (condValue := FormalYul.word 1)
      (selector := FormalYul.word 2080592636)
      (result := FormalYul.returnOf haltState)
      (hfirst := by
        simp +decide [start, afterFreePtr, FormalYul.stateFor, FormalYul.calldata,
          EvmYul.Yul.execPrimCall.eq_def,
          EvmYul.Yul.reverse', EvmYul.Yul.cons',
          EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
          EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
          EvmYul.Yul.State.toMachineState,
          sharedFor_inherited_mstore_mk_eq_cbrtUp512SharedAfterFreePtr_raw])
      (hcond := by
        simp +decide [afterFreePtr,
          EvmYul.Yul.evalPrimCall.eq_def,
          EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
          EvmYul.Yul.evalTail.eq_def,
          EvmYul.Yul.State.executionEnv, FormalYul.word,
          cbrtUp512SharedAfterFreePtr_calldata, cbrtUp512_calldata_size])
      (hcondNe := by decide)
      (hlet := by
        have hselector :
            ((EvmYul.Yul.State.Ok (cbrtUp512SharedAfterFreePtr 0 xLo)
                (Inhabited.default : EvmYul.Yul.VarStore)).toState.calldataload
                (EvmYul.UInt256.ofNat 0)).shiftRight
              (EvmYul.UInt256.ofNat 224) =
              EvmYul.UInt256.ofNat 2080592636 := by
          simpa [FormalYul.word] using cbrtUp512_selector_afterFreePtr 0 xLo
        simp +decide [afterFreePtr, afterSelector,
          EvmYul.Yul.execCall.eq_def,
          EvmYul.Yul.evalPrimCall.eq_def,
          EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
          EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
          EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
          FormalYul.word, call_shift_right_224_unsigned_direct,
          hselector])
      (hswitchEval := by
        simp [afterSelector])
      (hselect := by
        rfl)
      (hcall := by
        exact ⟨haltState, haltValue, hhalt, rfl⟩))

theorem run_cbrt512_wrapper_evm_zero_hi_eq_icbrt
    (xLo : Nat) :
    run_cbrt512_wrapper_evm 0 xLo =
      .ok (icbrt (FormalYul.u256 xLo)) := by
  let selectorStore :=
    Finmap.insert "selector" (FormalYul.word 2822396936)
      (Inhabited.default : EvmYul.Yul.VarStore)
  obtain ⟨haltState, haltValue, hhalt, hresult⟩ :=
    external_fun_wrap_cbrt512_zero_calldata_halts_999989 xLo selectorStore
  have hReturn :
      FormalYul.Preservation.DispatcherReturn yulContract
        (FormalYul.calldata selector_cbrt512 [0, xLo]) 999998
        (FormalYul.returnOf haltState) :=
    dispatcherReturn_cbrt512_zero xLo haltState haltValue (by
      simpa [selectorStore] using hhalt)
  have hcall :
      run_cbrt512_wrapper_evm 0 xLo =
        .ok (floorCbrt (FormalYul.u256 xLo)) := by
    unfold run_cbrt512_wrapper_evm
    exact FormalYul.Preservation.callWord_ok_of_dispatcherReturn_result_1000000
      (contract := yulContract) (selector := selector_cbrt512) (args := [0, xLo])
      (hReturn := hReturn) hresult
  have hfloor :
      floorCbrt (FormalYul.u256 xLo) = icbrt (FormalYul.u256 xLo) :=
    floorCbrt_correct_u256_eq_all (FormalYul.u256 xLo)
      (Nat.mod_lt xLo (by unfold WORD_MOD; exact Nat.two_pow_pos 256))
  simpa [hfloor] using hcall

theorem run_cbrtUp512_wrapper_evm_zero_hi_eq_cbrtUp512
    (xLo : Nat) :
    run_cbrtUp512_wrapper_evm 0 xLo =
      .ok (cbrtUp512 (FormalYul.u256 xLo)) := by
  let selectorStore :=
    Finmap.insert "selector" (FormalYul.word 2080592636)
      (Inhabited.default : EvmYul.Yul.VarStore)
  obtain ⟨haltState, haltValue, hhalt, hresult⟩ :=
    external_fun_wrap_cbrtUp512_zero_calldata_halts_999989 xLo selectorStore
  have hReturn :
      FormalYul.Preservation.DispatcherReturn yulContract
        (FormalYul.calldata selector_cbrtUp512 [0, xLo]) 999998
        (FormalYul.returnOf haltState) :=
    dispatcherReturn_cbrtUp512_zero xLo haltState haltValue (by
      simpa [selectorStore] using hhalt)
  have hcall :
      run_cbrtUp512_wrapper_evm 0 xLo =
        .ok (cbrtUp256 (FormalYul.u256 xLo)) := by
    unfold run_cbrtUp512_wrapper_evm
    exact FormalYul.Preservation.callWord_ok_of_dispatcherReturn_result_1000000
      (contract := yulContract) (selector := selector_cbrtUp512) (args := [0, xLo])
      (hReturn := hReturn) hresult
  have hx256 : FormalYul.u256 xLo < 2 ^ 256 := by
    exact Nat.mod_lt xLo (by unfold WORD_MOD; exact Nat.two_pow_pos 256)
  have hx512 : FormalYul.u256 xLo < 2 ^ 512 :=
    Nat.lt_of_lt_of_le hx256 (Nat.pow_le_pow_right (by omega) (by omega))
  have hceil256 := cbrtUp256_ceil_u256 (FormalYul.u256 xLo) hx256
  have hceil512 := cbrtUp512_correct (FormalYul.u256 xLo) hx512
  have hEq : cbrtUp256 (FormalYul.u256 xLo) = cbrtUp512 (FormalYul.u256 xLo) := by
    exact le_antisymm
      (hceil256.2 (cbrtUp512 (FormalYul.u256 xLo)) hceil512.1)
      (hceil512.2 (cbrtUp256 (FormalYul.u256 xLo)) hceil256.1)
  simpa [hEq] using hcall

private theorem uint512_lt_512 (xHi xLo : Nat) :
    FormalYul.u256 xHi * 2 ^ 256 + FormalYul.u256 xLo < 2 ^ 512 := by
  have hHi : FormalYul.u256 xHi < 2 ^ 256 := by
    unfold FormalYul.u256 FormalYul.WORD_MOD
    exact Nat.mod_lt xHi (Nat.two_pow_pos 256)
  have hLo : FormalYul.u256 xLo < 2 ^ 256 := by
    unfold FormalYul.u256 FormalYul.WORD_MOD
    exact Nat.mod_lt xLo (Nat.two_pow_pos 256)
  calc FormalYul.u256 xHi * 2 ^ 256 + FormalYul.u256 xLo
      ≤ (2 ^ 256 - 1) * 2 ^ 256 + (2 ^ 256 - 1) := by omega
    _ < 2 ^ 512 := by omega

theorem cbrtUp512_uint512_correct (xHi xLo : Nat) :
    let x := FormalYul.u256 xHi * 2 ^ 256 + FormalYul.u256 xLo
    let r := cbrtUp512 x
    x ≤ r * r * r ∧ ∀ y, x ≤ y * y * y → r ≤ y := by
  exact cbrtUp512_correct
    (FormalYul.u256 xHi * 2 ^ 256 + FormalYul.u256 xLo)
    (uint512_lt_512 xHi xLo)

end Cbrt512Yul
