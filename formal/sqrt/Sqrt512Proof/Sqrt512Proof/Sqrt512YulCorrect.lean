import Sqrt512Proof.Sqrt512YulProof
import Sqrt512Proof.Sqrt512Correct
import Sqrt512Proof.SqrtUpCorrect
import SqrtProof.SqrtEvmMath

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024
set_option linter.style.nameCheck false

namespace Sqrt512Yul

open FormalYul
open SqrtEvmMath

private theorem evmLt_01 (a b : Nat) :
    FormalYul.evmLt a b = 0 ∨ FormalYul.evmLt a b = 1 := by
  unfold FormalYul.evmLt
  split <;> simp

private theorem evmGt_01 (a b : Nat) :
    FormalYul.evmGt a b = 0 ∨ FormalYul.evmGt a b = 1 := by
  unfold FormalYul.evmGt
  split <;> simp

private theorem evmEq_01 (a b : Nat) :
    FormalYul.evmEq a b = 0 ∨ FormalYul.evmEq a b = 1 := by
  unfold FormalYul.evmEq
  split <;> simp

private theorem evmLt_zero_of_01 (b : Nat) (hb : b = 0 ∨ b = 1) :
    FormalYul.evmLt 0 b = b := by
  rcases hb with rfl | rfl <;>
    norm_num [FormalYul.evmLt, FormalYul.u256, FormalYul.WORD_MOD]

private theorem evmMul_evmLt_zero_eq_evmAnd_of_01
    (a b : Nat) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    FormalYul.evmMul a (FormalYul.evmLt 0 b) = FormalYul.evmAnd a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    norm_num [FormalYul.evmMul, FormalYul.evmLt, FormalYul.evmAnd,
      FormalYul.u256, FormalYul.WORD_MOD]

private theorem evmMul_eq_evmAnd_of_01
    (a b : Nat) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    FormalYul.evmMul a b = FormalYul.evmAnd a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    norm_num [FormalYul.evmMul, FormalYul.evmAnd, FormalYul.u256, FormalYul.WORD_MOD]

@[simp] private theorem evmLt_zero_evmLt (a b : Nat) :
    FormalYul.evmLt 0 (FormalYul.evmLt a b) = FormalYul.evmLt a b :=
  evmLt_zero_of_01 _ (evmLt_01 a b)

@[simp] private theorem evmMul_evmEq_evmLt_zero_evmLt
    (a b c d : Nat) :
    FormalYul.evmMul (FormalYul.evmEq a b)
        (FormalYul.evmLt 0 (FormalYul.evmLt c d)) =
      FormalYul.evmAnd (FormalYul.evmEq a b) (FormalYul.evmLt c d) :=
  evmMul_evmLt_zero_eq_evmAnd_of_01 _ _ (evmEq_01 a b) (evmLt_01 c d)

@[simp] private theorem evmMul_evmEq_evmLt (a b c d : Nat) :
    FormalYul.evmMul (FormalYul.evmEq a b) (FormalYul.evmLt c d) =
      FormalYul.evmAnd (FormalYul.evmEq a b) (FormalYul.evmLt c d) :=
  evmMul_eq_evmAnd_of_01 _ _ (evmEq_01 a b) (evmLt_01 c d)

@[simp] private theorem evmLt_zero_evmOr_evmLt_evmAnd_evmEq_evmLt
    (a b c d e f : Nat) :
    FormalYul.evmLt 0
        (FormalYul.evmOr (FormalYul.evmLt a b)
          (FormalYul.evmAnd (FormalYul.evmEq c d) (FormalYul.evmLt e f))) =
      FormalYul.evmOr (FormalYul.evmLt a b)
        (FormalYul.evmAnd (FormalYul.evmEq c d) (FormalYul.evmLt e f)) :=
  evmLt_zero_of_01 _ <|
    FormalYul.Preservation.evmOr_01 _ _ (evmLt_01 a b) <|
      FormalYul.Preservation.evmAnd_01 _ _ (evmEq_01 c d) (evmLt_01 e f)

@[simp] private theorem evmLt_zero_evmOr_evmGt_evmAnd_evmEq_evmGt
    (a b c d e f : Nat) :
    FormalYul.evmLt 0
        (FormalYul.evmOr (FormalYul.evmGt a b)
          (FormalYul.evmAnd (FormalYul.evmEq c d) (FormalYul.evmGt e f))) =
      FormalYul.evmOr (FormalYul.evmGt a b)
        (FormalYul.evmAnd (FormalYul.evmEq c d) (FormalYul.evmGt e f)) :=
  evmLt_zero_of_01 _ <|
    FormalYul.Preservation.evmOr_01 _ _ (evmGt_01 a b) <|
      FormalYul.Preservation.evmAnd_01 _ _ (evmEq_01 c d) (evmGt_01 e f)

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

private theorem call_zero_value_for_split_t_userDefinedValueType_uint512_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [] (.some "zero_value_for_split_t_userDefinedValueType$_uint512_$113")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_zero_value_for_split_t_userDefinedValueType__uint512__113]
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

private theorem call_zero_value_for_split_t_bool_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
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
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert]

@[simp] private theorem call_cleanup_t_uint256_966_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 966) [v] (.some "cleanup_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_uint256_direct
      (v := v) (fuel := fuel + 946) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_cleanup_t_uint256_964_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 964) [v] (.some "cleanup_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_uint256_direct
      (v := v) (fuel := fuel + 944) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_cleanup_t_uint256_953_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 953) [v] (.some "cleanup_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_uint256_direct
      (v := v) (fuel := fuel + 933) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_cleanup_t_uint256_951_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 951) [v] (.some "cleanup_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_uint256_direct
      (v := v) (fuel := fuel + 931) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_cleanup_t_uint256_949_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 949) [v] (.some "cleanup_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_uint256_direct
      (v := v) (fuel := fuel + 929) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_cleanup_t_uint256_933_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 933) [v] (.some "cleanup_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_uint256_direct
      (v := v) (fuel := fuel + 913) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_cleanup_t_uint256_931_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 931) [v] (.some "cleanup_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_uint256_direct
      (v := v) (fuel := fuel + 911) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_cleanup_t_uint256_929_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 929) [v] (.some "cleanup_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_uint256_direct
      (v := v) (fuel := fuel + 909) (shared := shared) (store := store)
      (hlookup := hlookup)

private theorem call_cleanup_t_rational_1_by_1_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
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

private theorem call_cleanup_t_rational_0_by_1_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
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
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v] (.some "identity")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_identity]
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

private theorem call_cleanup_t_uint8_direct
    (v fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 40) [FormalYul.word v] (.some "cleanup_t_uint8")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmAnd v 255)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_cleanup_t_uint8]
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

private theorem call_convert_t_rational_1_by_1_to_t_uint8_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 120) [FormalYul.word value]
      (.some "convert_t_rational_1_by_1_to_t_uint8")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmAnd value 255)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_convert_t_rational_1_by_1_to_t_uint8]
  simp only [yulFunction_convert_t_rational_1_by_1_to_t_uint8,
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
  rw [call_cleanup_t_rational_1_by_1_direct
    (v := EvmYul.UInt256.ofNat value) (fuel := fuel + 92)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat value)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
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

private theorem call_convert_t_rational_0_by_1_to_t_uint256_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
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

private theorem call_shift_right_unsigned_dynamic_direct
    (bits value fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 40) [FormalYul.word bits, FormalYul.word value]
      (.some "shift_right_unsigned_dynamic") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmShr bits value)]) := by
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

private theorem call_shift_right_t_uint256_t_uint8_one_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100) [FormalYul.word value, FormalYul.word 1]
      (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmShr 1 value)]) := by
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
      (Finmap.insert "bits" (EvmYul.UInt256.ofNat 1)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let bitsStore : EvmYul.Yul.VarStore :=
    Finmap.insert "bits" (EvmYul.UInt256.ofNat 1) baseStore
  have hCleanupBits :
      EvmYul.Yul.call (fuel + 96) [EvmYul.UInt256.ofNat 1]
        (.some "cleanup_t_uint8") (.some yulContract)
        (EvmYul.Yul.State.Ok shared baseStore) =
      .ok (EvmYul.Yul.State.Ok shared baseStore, [EvmYul.UInt256.ofNat 1]) := by
    simpa [baseStore, FormalYul.word, FormalYul.evmAnd,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_cleanup_t_uint8_direct
        (v := 1) (fuel := fuel + 56) (shared := shared) (store := baseStore)
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
      EvmYul.Yul.call (fuel + 93) [EvmYul.UInt256.ofNat 1, EvmYul.UInt256.ofNat value]
        (.some "shift_right_unsigned_dynamic") (.some yulContract)
        (EvmYul.Yul.State.Ok shared bitsStore) =
      .ok (EvmYul.Yul.State.Ok shared bitsStore,
        [FormalYul.word (FormalYul.evmShr 1 value)]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_shift_right_unsigned_dynamic_direct
        (bits := 1) (value := value) (fuel := fuel + 53)
        (shared := shared) (store := bitsStore) (hlookup := hlookup)
  have hCleanupResult :
      EvmYul.Yul.call (fuel + 95) [EvmYul.UInt256.ofNat (FormalYul.evmShr 1 value)]
        (.some "cleanup_t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok shared bitsStore) =
      .ok (EvmYul.Yul.State.Ok shared bitsStore,
        [EvmYul.UInt256.ofNat (FormalYul.evmShr 1 value)]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_cleanup_t_uint256_direct
        (v := FormalYul.word (FormalYul.evmShr 1 value)) (fuel := fuel + 75)
        (shared := shared) (store := bitsStore) (hlookup := hlookup)
  simp +decide [baseStore, bitsStore, hCleanupBits, hCleanupValue, hShift, hCleanupResult,
    EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

private theorem call_fun_clz_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [FormalYul.word x] (.some yulName_fun_clz)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmClz x)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_clz]
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

@[simp] private theorem call_fun_clz_4991_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 4991) [EvmYul.UInt256.ofNat x] (.some "fun_clz_6141")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmClz x)]) := by
  simpa [FormalYul.word, yulName_fun_clz, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_clz_direct (x := x) (fuel := fuel + 4931)
      (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_fun_unsafeDiv_direct
    (numerator denominator fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [FormalYul.word numerator, FormalYul.word denominator]
      (.some yulName_fun_unsafeDiv) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmDiv numerator denominator)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_unsafeDiv]
  simp only [yulFunction_fun_unsafeDiv, yulFunction_fun_unsafeDiv_5899,
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
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [FormalYul.word x, FormalYul.word b]
      (.some yulName_fun_unsafeDec) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmSub x (FormalYul.evmLt 0 b))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_unsafeDec]
  simp only [yulFunction_fun_unsafeDec, yulFunction_fun_unsafeDec_5854,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
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

private theorem call_fun_unsafeDec_uint256_direct
    (x b : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [x, b]
      (.some yulName_fun_unsafeDec) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [x - EvmYul.UInt256.lt (EvmYul.UInt256.ofNat 0) b]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_unsafeDec]
  simp only [yulFunction_fun_unsafeDec, yulFunction_fun_unsafeDec_5854,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 36)
      (shared := shared)
      (store := Finmap.insert "var_x_5845" x
        (Finmap.insert "var_b_5847" b
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup)]

@[simp] private theorem call_fun_unsafeDec_930_direct
    (x b : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 930) [x, b]
      (.some yulName_fun_unsafeDec) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [x - EvmYul.UInt256.lt (EvmYul.UInt256.ofNat 0) b]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_unsafeDec_uint256_direct
      (x := x) (b := b) (fuel := fuel + 870)
      (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_fun_unsafeDec_ofNat_uint256_direct
    (x : Nat) (b : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [EvmYul.UInt256.ofNat x, b]
      (.some yulName_fun_unsafeDec) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmSub x
        (FormalYul.evmLt 0 (FormalYul.wordNat b)))]) := by
  rw [call_fun_unsafeDec_uint256_direct
    (x := EvmYul.UInt256.ofNat x) (b := b) (fuel := fuel)
    (shared := shared) (store := store) (hlookup := hlookup)]
  congr
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_sub, FormalYul.Preservation.wordNat_ofNat,
    FormalYul.Preservation.wordNat_lt]
  simp [FormalYul.word, FormalYul.Preservation.evmSub_u256_left,
    FormalYul.Preservation.evmLt_u256_left]

private theorem call_wrapping_add_t_uint256_direct
    (x y fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 80) [FormalYul.word x, FormalYul.word y]
      (.some "wrapping_add_t_uint256") (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmAdd x y)]) := by
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
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hcleanup]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_add]
  simp [FormalYul.Preservation.evmAdd_u256_left, FormalYul.Preservation.evmAdd_u256_right]

@[simp] private theorem call_wrapping_add_t_uint256_986_direct
    (x y fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 986) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat y]
      (.some "wrapping_add_t_uint256") (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmAdd x y)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_wrapping_add_t_uint256_direct
      (x := x) (y := y) (fuel := fuel + 906)
      (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_fun_and_direct
    (a b fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [FormalYul.word a, FormalYul.word b]
      (.some yulName_fun_and) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmMul a (FormalYul.evmLt 0 b))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_and]
  simp only [yulFunction_fun_and, yulFunction_fun_and_5596,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
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
  simp only [FormalYul.Preservation.wordNat_mul]
  simp [FormalYul.Preservation.wordNat_lt, FormalYul.Preservation.evmMul_u256_left,
    FormalYul.Preservation.evmMul_u256_right, FormalYul.Preservation.evmLt_u256_left,
    FormalYul.Preservation.evmLt_u256_right]

private theorem call_fun_and_uint256_direct
    (a b : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [a, b]
      (.some yulName_fun_and) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [a * EvmYul.UInt256.lt (EvmYul.UInt256.ofNat 0) b]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_and]
  simp only [yulFunction_fun_and, yulFunction_fun_and_5596,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert,
    call_zero_value_for_split_t_bool_direct (fuel := fuel) (extra := 36)
      (shared := shared)
      (store := Finmap.insert "var_a_5587" a
        (Finmap.insert "var_b_5589" b
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup)]

@[simp] private theorem call_fun_and_932_direct
    (a b : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 932) [a, b]
      (.some yulName_fun_and) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [a * EvmYul.UInt256.lt (EvmYul.UInt256.ofNat 0) b]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_and_uint256_direct
      (a := a) (b := b) (fuel := fuel + 872)
      (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_fun_or_direct
    (a b fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [FormalYul.word a, FormalYul.word b]
      (.some yulName_fun_or) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmOr a b)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_or]
  simp only [yulFunction_fun_or, yulFunction_fun_or_5585,
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

private theorem call_fun_or_uint256_direct
    (a b : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [a, b]
      (.some yulName_fun_or) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.lor a b]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_or]
  simp only [yulFunction_fun_or, yulFunction_fun_or_5585,
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
    Finmap.lookup_insert,
    call_zero_value_for_split_t_bool_direct (fuel := fuel) (extra := 36)
      (shared := shared)
      (store := Finmap.insert "var_a_5576" a
        (Finmap.insert "var_b_5578" b
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup)]

@[simp] private theorem call_fun_or_931_direct
    (a b : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 931) [a, b]
      (.some yulName_fun_or) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.lor a b]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_or_uint256_direct
      (a := a) (b := b) (fuel := fuel + 871)
      (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_fun_toUint_direct
    (b fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [FormalYul.word b] (.some yulName_fun_toUint)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmLt 0 b)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_toUint]
  simp only [yulFunction_fun_toUint, yulFunction_fun_toUint_5616,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 36)
      (shared := shared)
      (store := Finmap.insert "var_b_5609" (EvmYul.UInt256.ofNat b)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp [FormalYul.Preservation.wordNat_lt, FormalYul.Preservation.wordNat_ofNat,
    FormalYul.Preservation.evmLt_u256_left, FormalYul.Preservation.evmLt_u256_right]

private theorem call_fun__gt_direct
    (xHi xLo yHi yLo fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 80)
      [FormalYul.word xHi, FormalYul.word xLo, FormalYul.word yHi, FormalYul.word yLo]
      (.some yulName_fun__gt) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmOr (FormalYul.evmGt xHi yHi)
        (FormalYul.evmAnd (FormalYul.evmEq xHi yHi) (FormalYul.evmGt xLo yLo)))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__gt]
  simp only [yulFunction_fun__gt, yulFunction_fun__gt_1766,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    call_zero_value_for_split_t_bool_direct (fuel := fuel) (extra := 56)
      (shared := shared)
      (store := Finmap.insert "var_x_hi_1753" (EvmYul.UInt256.ofNat xHi)
        (Finmap.insert "var_x_lo_1755" (EvmYul.UInt256.ofNat xLo)
          (Finmap.insert "var_y_hi_1757" (EvmYul.UInt256.ofNat yHi)
            (Finmap.insert "var_y_lo_1759" (EvmYul.UInt256.ofNat yLo)
              (Inhabited.default : EvmYul.Yul.VarStore)))))
      (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_or, FormalYul.Preservation.wordNat_and,
    FormalYul.Preservation.wordNat_gt, FormalYul.Preservation.wordNat_eq]
  simp [FormalYul.Preservation.evmGt_u256_left, FormalYul.Preservation.evmGt_u256_right,
    FormalYul.Preservation.evmEq_u256_left, FormalYul.Preservation.evmEq_u256_right]

private theorem call_fun__add_direct
    (xHi xLo y fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 80) [FormalYul.word xHi, FormalYul.word xLo, FormalYul.word y]
      (.some yulName_fun__add) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmAdd xHi (FormalYul.evmLt (FormalYul.evmAdd xLo y) xLo)),
       FormalYul.word (FormalYul.evmAdd xLo y)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__add]
  simp only [yulFunction_fun__add, yulFunction_fun__add_637,
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
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 56)
      (shared := shared)
      (store := Finmap.insert "var_x_hi_624" (EvmYul.UInt256.ofNat xHi)
        (Finmap.insert "var_x_lo_626" (EvmYul.UInt256.ofNat xLo)
          (Finmap.insert "var_y_628" (EvmYul.UInt256.ofNat y)
            (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup),
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 54)
      (shared := shared)
      (store := Finmap.insert "var_r_hi_631" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "zero_t_uint256_64" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "var_x_hi_624" (EvmYul.UInt256.ofNat xHi)
            (Finmap.insert "var_x_lo_626" (EvmYul.UInt256.ofNat xLo)
              (Finmap.insert "var_y_628" (EvmYul.UInt256.ofNat y)
                (Inhabited.default : EvmYul.Yul.VarStore))))))
      (hlookup := hlookup)]
  constructor
  · apply FormalYul.Preservation.eq_of_wordNat_eq
    simp only [FormalYul.Preservation.wordNat_add, FormalYul.Preservation.wordNat_lt]
    simp [FormalYul.Preservation.evmAdd_u256_left, FormalYul.Preservation.evmAdd_u256_right,
      FormalYul.Preservation.evmLt_u256_right]
  · apply FormalYul.Preservation.eq_of_wordNat_eq
    simp only [FormalYul.Preservation.wordNat_add]
    simp [FormalYul.Preservation.evmAdd_u256_left, FormalYul.Preservation.evmAdd_u256_right]

private theorem call_fun__mul_direct
    (x y fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100) [FormalYul.word x, FormalYul.word y]
      (.some yulName_fun__mul) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word
        (FormalYul.evmSub
          (FormalYul.evmSub (FormalYul.evmMulmod x y (FormalYul.evmNot 0)) (FormalYul.evmMul x y))
          (FormalYul.evmLt (FormalYul.evmMulmod x y (FormalYul.evmNot 0)) (FormalYul.evmMul x y))),
       FormalYul.word (FormalYul.evmMul x y)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__mul]
  simp only [yulFunction_fun__mul, yulFunction_fun__mul_1022,
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
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 76)
      (shared := shared)
      (store := Finmap.insert "var_x_1011" (EvmYul.UInt256.ofNat x)
        (Finmap.insert "var_y_1013" (EvmYul.UInt256.ofNat y)
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup),
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 74)
      (shared := shared)
      (store := Finmap.insert "var_r_hi_1016" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "zero_t_uint256_60" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "var_x_1011" (EvmYul.UInt256.ofNat x)
            (Finmap.insert "var_y_1013" (EvmYul.UInt256.ofNat y)
              (Inhabited.default : EvmYul.Yul.VarStore)))))
      (hlookup := hlookup)]
  constructor
  · apply FormalYul.Preservation.eq_of_wordNat_eq
    simp only [FormalYul.Preservation.wordNat_sub, FormalYul.Preservation.wordNat_mulMod,
      FormalYul.Preservation.wordNat_not, FormalYul.Preservation.wordNat_mul,
      FormalYul.Preservation.wordNat_lt]
    simp [FormalYul.Preservation.evmMulmod_u256_left,
      FormalYul.Preservation.evmMulmod_u256_middle,
      FormalYul.Preservation.evmMul_u256_left, FormalYul.Preservation.evmMul_u256_right]
  · apply FormalYul.Preservation.eq_of_wordNat_eq
    simp only [FormalYul.Preservation.wordNat_mul]
    simp [FormalYul.Preservation.evmMul_u256_left, FormalYul.Preservation.evmMul_u256_right]

private theorem call_fun__shl256_direct
    (xHi xLo s fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100) [FormalYul.word xHi, FormalYul.word xLo, FormalYul.word s]
      (.some yulName_fun__shl256) (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShr (FormalYul.evmSub 256 s) xHi),
       FormalYul.word (FormalYul.evmOr (FormalYul.evmShl s xHi)
         (FormalYul.evmShr (FormalYul.evmSub 256 s) xLo)),
       FormalYul.word (FormalYul.evmShl s xLo)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__shl256]
  simp only [yulFunction_fun__shl256, yulFunction_fun__shl256_3075,
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
        (Finmap.insert "zero_t_uint256_70" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "var_x_hi_3060" (EvmYul.UInt256.ofNat xHi)
            (Finmap.insert "var_x_lo_3062" (EvmYul.UInt256.ofNat xLo)
              (Finmap.insert "var_s_3064" (EvmYul.UInt256.ofNat s)
                (Inhabited.default : EvmYul.Yul.VarStore))))))
      (hlookup := hlookup),
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 72)
      (shared := shared)
      (store := Finmap.insert "var_r_hi_3069" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "zero_t_uint256_71" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "var_r_ex_3067" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "zero_t_uint256_70" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "var_x_hi_3060" (EvmYul.UInt256.ofNat xHi)
                (Finmap.insert "var_x_lo_3062" (EvmYul.UInt256.ofNat xLo)
                  (Finmap.insert "var_s_3064" (EvmYul.UInt256.ofNat s)
                    (Inhabited.default : EvmYul.Yul.VarStore))))))))
      (hlookup := hlookup)]
  constructor
  · apply FormalYul.Preservation.eq_of_wordNat_eq
    simp only [FormalYul.Preservation.wordNat_shiftRight, FormalYul.Preservation.wordNat_sub,
      FormalYul.Preservation.wordNat_ofNat]
    simp [FormalYul.Preservation.evmShr_u256_right, FormalYul.Preservation.evmSub_u256_right]
  · constructor
    · apply FormalYul.Preservation.eq_of_wordNat_eq
      simp only [FormalYul.Preservation.wordNat_or, FormalYul.Preservation.wordNat_shiftLeft,
        FormalYul.Preservation.wordNat_shiftRight, FormalYul.Preservation.wordNat_sub,
        FormalYul.Preservation.wordNat_ofNat]
      simp [FormalYul.Preservation.evmShl_u256_left, FormalYul.Preservation.evmShl_u256_right,
        FormalYul.Preservation.evmShr_u256_right, FormalYul.Preservation.evmSub_u256_right]
    · apply FormalYul.Preservation.eq_of_wordNat_eq
      simp only [FormalYul.Preservation.wordNat_shiftLeft]
      simp [FormalYul.Preservation.evmShl_u256_left, FormalYul.Preservation.evmShl_u256_right]

private theorem call_fun__sqrt_babylonianStep_direct
    (x r fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 140) [FormalYul.word x, FormalYul.word r]
      (.some yulName_fun__sqrt_babylonianStep) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShr 1 (FormalYul.evmAdd (FormalYul.evmDiv x r) r))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__sqrt_babylonianStep]
  simp only [yulFunction_fun__sqrt_babylonianStep, yulFunction_fun__sqrt_babylonianStep_4323,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hCallDiv :=
    call_fun_unsafeDiv_direct (numerator := x) (denominator := r) (fuel := fuel + 69)
      (shared := shared)
      (store := Finmap.insert "expr_4314" (EvmYul.UInt256.ofNat r)
        (Finmap.insert "_114" (EvmYul.UInt256.ofNat r)
          (Finmap.insert "expr_4313_self" (EvmYul.UInt256.ofNat x)
            (Finmap.insert "expr_4312" (EvmYul.UInt256.ofNat x)
              (Finmap.insert "_113" (EvmYul.UInt256.ofNat x)
                (Finmap.insert "var__4310" (EvmYul.UInt256.ofNat 0)
                  (Finmap.insert "zero_t_uint256_112" (EvmYul.UInt256.ofNat 0)
                    (Finmap.insert "var_x_4305" (EvmYul.UInt256.ofNat x)
                      (Finmap.insert "var_r_4307" (EvmYul.UInt256.ofNat r)
                        (Inhabited.default : EvmYul.Yul.VarStore))))))))))
      (hlookup := hlookup)
  simp [FormalYul.word, yulName_fun_unsafeDiv] at hCallDiv
  have hCallAdd :=
    call_wrapping_add_t_uint256_direct (x := FormalYul.evmDiv x r) (y := r)
      (fuel := fuel + 46) (shared := shared)
      (store := Finmap.insert "expr_4316" (EvmYul.UInt256.ofNat r)
        (Finmap.insert "_115" (EvmYul.UInt256.ofNat r)
          (Finmap.insert "expr_4315" (EvmYul.UInt256.ofNat (FormalYul.evmDiv x r))
            (Finmap.insert "expr_4314" (EvmYul.UInt256.ofNat r)
              (Finmap.insert "_114" (EvmYul.UInt256.ofNat r)
                (Finmap.insert "expr_4313_self" (EvmYul.UInt256.ofNat x)
                  (Finmap.insert "expr_4312" (EvmYul.UInt256.ofNat x)
                    (Finmap.insert "_113" (EvmYul.UInt256.ofNat x)
                      (Finmap.insert "var__4310" (EvmYul.UInt256.ofNat 0)
                        (Finmap.insert "zero_t_uint256_112" (EvmYul.UInt256.ofNat 0)
                          (Finmap.insert "var_x_4305" (EvmYul.UInt256.ofNat x)
                            (Finmap.insert "var_r_4307" (EvmYul.UInt256.ofNat r)
                              (Inhabited.default : EvmYul.Yul.VarStore)))))))))))))
      (hlookup := hlookup)
  simp [FormalYul.word] at hCallAdd
  have hCallConvert :=
    call_convert_t_rational_1_by_1_to_t_uint8_direct
      (value := 1) (fuel := fuel + 4) (shared := shared)
      (store := Finmap.insert "expr_4318" (EvmYul.UInt256.ofNat 1)
        (Finmap.insert "expr_4317" (EvmYul.UInt256.ofNat (FormalYul.evmAdd (FormalYul.evmDiv x r) r))
          (Finmap.insert "expr_4316" (EvmYul.UInt256.ofNat r)
            (Finmap.insert "_115" (EvmYul.UInt256.ofNat r)
              (Finmap.insert "expr_4315" (EvmYul.UInt256.ofNat (FormalYul.evmDiv x r))
                (Finmap.insert "expr_4314" (EvmYul.UInt256.ofNat r)
                  (Finmap.insert "_114" (EvmYul.UInt256.ofNat r)
                    (Finmap.insert "expr_4313_self" (EvmYul.UInt256.ofNat x)
                      (Finmap.insert "expr_4312" (EvmYul.UInt256.ofNat x)
                        (Finmap.insert "_113" (EvmYul.UInt256.ofNat x)
                          (Finmap.insert "var__4310" (EvmYul.UInt256.ofNat 0)
                            (Finmap.insert "zero_t_uint256_112" (EvmYul.UInt256.ofNat 0)
                              (Finmap.insert "var_x_4305" (EvmYul.UInt256.ofNat x)
                                (Finmap.insert "var_r_4307" (EvmYul.UInt256.ofNat r)
                                  (Inhabited.default : EvmYul.Yul.VarStore)))))))))))))))
      (hlookup := hlookup)
  simp [FormalYul.word] at hCallConvert
  have hCallShift :
      EvmYul.Yul.call (fuel + 123)
        [EvmYul.UInt256.ofNat (FormalYul.evmAdd (FormalYul.evmDiv x r) r),
          EvmYul.UInt256.ofNat (FormalYul.evmAnd 1 255)]
        (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
        (EvmYul.Yul.State.Ok shared
          (Finmap.insert "_116" (EvmYul.UInt256.ofNat (FormalYul.evmAnd 1 255))
            (Finmap.insert "expr_4318" (EvmYul.UInt256.ofNat 1)
              (Finmap.insert "expr_4317"
                (EvmYul.UInt256.ofNat (FormalYul.evmAdd (FormalYul.evmDiv x r) r))
                (Finmap.insert "expr_4316" (EvmYul.UInt256.ofNat r)
                  (Finmap.insert "_115" (EvmYul.UInt256.ofNat r)
                    (Finmap.insert "expr_4315" (EvmYul.UInt256.ofNat (FormalYul.evmDiv x r))
                      (Finmap.insert "expr_4314" (EvmYul.UInt256.ofNat r)
                        (Finmap.insert "_114" (EvmYul.UInt256.ofNat r)
                          (Finmap.insert "expr_4313_self" (EvmYul.UInt256.ofNat x)
                            (Finmap.insert "expr_4312" (EvmYul.UInt256.ofNat x)
                              (Finmap.insert "_113" (EvmYul.UInt256.ofNat x)
                                (Finmap.insert "var__4310" (EvmYul.UInt256.ofNat 0)
                                  (Finmap.insert "zero_t_uint256_112" (EvmYul.UInt256.ofNat 0)
                                    (Finmap.insert "var_x_4305" (EvmYul.UInt256.ofNat x)
                                      (Finmap.insert "var_r_4307" (EvmYul.UInt256.ofNat r)
                                        (Inhabited.default : EvmYul.Yul.VarStore))))))))))))))))) =
      .ok (EvmYul.Yul.State.Ok shared
          (Finmap.insert "_116" (EvmYul.UInt256.ofNat (FormalYul.evmAnd 1 255))
            (Finmap.insert "expr_4318" (EvmYul.UInt256.ofNat 1)
              (Finmap.insert "expr_4317"
                (EvmYul.UInt256.ofNat (FormalYul.evmAdd (FormalYul.evmDiv x r) r))
                (Finmap.insert "expr_4316" (EvmYul.UInt256.ofNat r)
                  (Finmap.insert "_115" (EvmYul.UInt256.ofNat r)
                    (Finmap.insert "expr_4315" (EvmYul.UInt256.ofNat (FormalYul.evmDiv x r))
                      (Finmap.insert "expr_4314" (EvmYul.UInt256.ofNat r)
                        (Finmap.insert "_114" (EvmYul.UInt256.ofNat r)
                          (Finmap.insert "expr_4313_self" (EvmYul.UInt256.ofNat x)
                            (Finmap.insert "expr_4312" (EvmYul.UInt256.ofNat x)
                              (Finmap.insert "_113" (EvmYul.UInt256.ofNat x)
                                (Finmap.insert "var__4310" (EvmYul.UInt256.ofNat 0)
                                  (Finmap.insert "zero_t_uint256_112" (EvmYul.UInt256.ofNat 0)
                                    (Finmap.insert "var_x_4305" (EvmYul.UInt256.ofNat x)
                                      (Finmap.insert "var_r_4307" (EvmYul.UInt256.ofNat r)
                                        (Inhabited.default : EvmYul.Yul.VarStore)))))))))))))))),
        [FormalYul.word
          (FormalYul.evmShr 1 (FormalYul.evmAdd (FormalYul.evmDiv x r) r))]) := by
    simpa [FormalYul.word, FormalYul.evmAnd] using
      call_shift_right_t_uint256_t_uint8_one_direct
        (value := FormalYul.evmAdd (FormalYul.evmDiv x r) r) (fuel := fuel + 23)
        (shared := shared)
        (store := Finmap.insert "_116" (EvmYul.UInt256.ofNat (FormalYul.evmAnd 1 255))
          (Finmap.insert "expr_4318" (EvmYul.UInt256.ofNat 1)
            (Finmap.insert "expr_4317"
              (EvmYul.UInt256.ofNat (FormalYul.evmAdd (FormalYul.evmDiv x r) r))
              (Finmap.insert "expr_4316" (EvmYul.UInt256.ofNat r)
                (Finmap.insert "_115" (EvmYul.UInt256.ofNat r)
                  (Finmap.insert "expr_4315" (EvmYul.UInt256.ofNat (FormalYul.evmDiv x r))
                    (Finmap.insert "expr_4314" (EvmYul.UInt256.ofNat r)
                      (Finmap.insert "_114" (EvmYul.UInt256.ofNat r)
                        (Finmap.insert "expr_4313_self" (EvmYul.UInt256.ofNat x)
                          (Finmap.insert "expr_4312" (EvmYul.UInt256.ofNat x)
                            (Finmap.insert "_113" (EvmYul.UInt256.ofNat x)
                              (Finmap.insert "var__4310" (EvmYul.UInt256.ofNat 0)
                                (Finmap.insert "zero_t_uint256_112" (EvmYul.UInt256.ofNat 0)
                                  (Finmap.insert "var_x_4305" (EvmYul.UInt256.ofNat x)
                                    (Finmap.insert "var_r_4307" (EvmYul.UInt256.ofNat r)
                                      (Inhabited.default : EvmYul.Yul.VarStore))))))))))))))))
        (hlookup := hlookup)
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hCallDiv, hCallAdd, hCallConvert, hCallShift,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 116)
      (shared := shared)
      (store := Finmap.insert "var_x_4305" (EvmYul.UInt256.ofNat x)
        (Finmap.insert "var_r_4307" (EvmYul.UInt256.ofNat r)
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup)]

private theorem call_fun__sqrt256_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 200) [FormalYul.word x] (.some yulName_fun__sqrt256)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (innerSqrt (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__sqrt256]
  simp only [yulFunction_fun__sqrt256, yulFunction_fun__sqrt_6169,
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
      (store := Finmap.insert "var_x_6162" (EvmYul.UInt256.ofNat x)
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

private theorem call_fun_sqrt256_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 360) [FormalYul.word x] (.some yulName_fun_sqrt256)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (floorSqrt (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_sqrt256]
  simp only [yulFunction_fun_sqrt256, yulFunction_fun_sqrt_6185,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hsqrtFuel : fuel + 352 = (fuel + 152) + 200 := by omega
  have hCallSqrt :=
    call_fun__sqrt256_direct (x := x) (fuel := fuel + 152) (shared := shared)
      (store := Finmap.insert "expr_6179"
        (EvmYul.UInt256.ofNat x)
        (Finmap.insert "_41"
          (EvmYul.UInt256.ofNat x)
          (Finmap.insert "var_z_6175" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "zero_t_uint256_40" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "var_x_6172" (EvmYul.UInt256.ofNat x)
                (Inhabited.default : EvmYul.Yul.VarStore))))))
      (hlookup := hlookup)
  simp [FormalYul.word, yulName_fun__sqrt256] at hCallSqrt
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
      (store := Finmap.insert "var_x_6172" (EvmYul.UInt256.ofNat x)
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

private theorem call_fun_sqrtUp256_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 420) [FormalYul.word x] (.some yulName_fun_sqrtUp256)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (sqrtUp256 (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_sqrtUp256]
  simp only [yulFunction_fun_sqrtUp256, yulFunction_fun_sqrtUp_6201,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hCallSqrt :=
    call_fun__sqrt256_direct (x := x) (fuel := fuel + 212) (shared := shared)
      (store := Finmap.insert "expr_6195"
        (EvmYul.UInt256.ofNat x)
        (Finmap.insert "_67"
          (EvmYul.UInt256.ofNat x)
          (Finmap.insert "var_z_6191" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "zero_t_uint256_66" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "var_x_6188" (EvmYul.UInt256.ofNat x)
                (Inhabited.default : EvmYul.Yul.VarStore))))))
      (hlookup := hlookup)
  simp [FormalYul.word, yulName_fun__sqrt256] at hCallSqrt
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
      (store := Finmap.insert "var_x_6188" (EvmYul.UInt256.ofNat x)
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

private theorem call_cleanup_t_rational_128_by_1_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v] (.some "cleanup_t_rational_128_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_cleanup_t_rational_128_by_1]
  simp only [yulFunction_cleanup_t_rational_128_by_1,
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

private theorem call_cleanup_t_rational_254_by_1_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v] (.some "cleanup_t_rational_254_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_cleanup_t_rational_254_by_1]
  simp only [yulFunction_cleanup_t_rational_254_by_1,
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

private theorem call_cleanup_t_rational_fixed_seed_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v]
      (.some "cleanup_t_rational_240615969168004511545033772477625056927_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions,
    lookup_cleanup_t_rational_240615969168004511545033772477625056927_by_1]
  simp only [yulFunction_cleanup_t_rational_240615969168004511545033772477625056927_by_1,
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

private theorem call_cleanup_t_rational_mask128_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v]
      (.some "cleanup_t_rational_340282366920938463463374607431768211455_by_1")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions,
    lookup_cleanup_t_rational_340282366920938463463374607431768211455_by_1]
  simp only [yulFunction_cleanup_t_rational_340282366920938463463374607431768211455_by_1,
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

private theorem call_convert_t_rational_128_by_1_to_t_uint8_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 120) [FormalYul.word value]
      (.some "convert_t_rational_128_by_1_to_t_uint8")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmAnd value 255)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_convert_t_rational_128_by_1_to_t_uint8]
  simp only [yulFunction_convert_t_rational_128_by_1_to_t_uint8,
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
  rw [call_cleanup_t_rational_128_by_1_direct
    (v := EvmYul.UInt256.ofNat value) (fuel := fuel + 92)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat value)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
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

private theorem call_convert_t_rational_128_by_1_to_t_uint8_128_991_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 991) [EvmYul.UInt256.ofNat 128]
      (.some "convert_t_rational_128_by_1_to_t_uint8")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 128]) := by
  simpa [FormalYul.word, FormalYul.evmAnd, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_128_by_1_to_t_uint8_direct
      (value := 128) (fuel := fuel + 871) (shared := shared) (store := store)
      (hlookup := hlookup)

private theorem call_convert_t_rational_128_by_1_to_t_uint8_128_977_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 977) [EvmYul.UInt256.ofNat 128]
      (.some "convert_t_rational_128_by_1_to_t_uint8")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 128]) := by
  simpa [FormalYul.word, FormalYul.evmAnd, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_128_by_1_to_t_uint8_direct
      (value := 128) (fuel := fuel + 857) (shared := shared) (store := store)
      (hlookup := hlookup)

private theorem call_convert_t_rational_128_by_1_to_t_uint8_128_971_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 971) [EvmYul.UInt256.ofNat 128]
      (.some "convert_t_rational_128_by_1_to_t_uint8")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 128]) := by
  simpa [FormalYul.word, FormalYul.evmAnd, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_128_by_1_to_t_uint8_direct
      (value := 128) (fuel := fuel + 851) (shared := shared) (store := store)
      (hlookup := hlookup)

private theorem call_convert_t_rational_128_by_1_to_t_uint8_128_965_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 965) [EvmYul.UInt256.ofNat 128]
      (.some "convert_t_rational_128_by_1_to_t_uint8")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 128]) := by
  simpa [FormalYul.word, FormalYul.evmAnd, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_128_by_1_to_t_uint8_direct
      (value := 128) (fuel := fuel + 845) (shared := shared) (store := store)
      (hlookup := hlookup)

private theorem call_convert_t_rational_128_by_1_to_t_uint8_128_959_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 959) [EvmYul.UInt256.ofNat 128]
      (.some "convert_t_rational_128_by_1_to_t_uint8")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 128]) := by
  simpa [FormalYul.word, FormalYul.evmAnd, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_128_by_1_to_t_uint8_direct
      (value := 128) (fuel := fuel + 839) (shared := shared) (store := store)
      (hlookup := hlookup)

private theorem call_convert_t_rational_128_by_1_to_t_uint8_128_953_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 953) [EvmYul.UInt256.ofNat 128]
      (.some "convert_t_rational_128_by_1_to_t_uint8")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 128]) := by
  simpa [FormalYul.word, FormalYul.evmAnd, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_128_by_1_to_t_uint8_direct
      (value := 128) (fuel := fuel + 833) (shared := shared) (store := store)
      (hlookup := hlookup)

private theorem call_convert_t_rational_128_by_1_to_t_uint8_128_947_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 947) [EvmYul.UInt256.ofNat 128]
      (.some "convert_t_rational_128_by_1_to_t_uint8")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 128]) := by
  simpa [FormalYul.word, FormalYul.evmAnd, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_128_by_1_to_t_uint8_direct
      (value := 128) (fuel := fuel + 827) (shared := shared) (store := store)
      (hlookup := hlookup)

private theorem call_convert_t_rational_254_by_1_to_t_uint256_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100) [FormalYul.word value]
      (.some "convert_t_rational_254_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word value]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_convert_t_rational_254_by_1_to_t_uint256]
  simp only [yulFunction_convert_t_rational_254_by_1_to_t_uint256,
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
  rw [call_cleanup_t_rational_254_by_1_direct
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

private theorem call_convert_t_rational_fixed_seed_to_t_uint256_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100)
      [FormalYul.word 240615969168004511545033772477625056927]
      (.some "convert_t_rational_240615969168004511545033772477625056927_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word 240615969168004511545033772477625056927]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions,
    lookup_convert_t_rational_240615969168004511545033772477625056927_by_1_to_t_uint256]
  simp only [yulFunction_convert_t_rational_240615969168004511545033772477625056927_by_1_to_t_uint256,
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
  rw [call_cleanup_t_rational_fixed_seed_direct
    (v := EvmYul.UInt256.ofNat 240615969168004511545033772477625056927) (fuel := fuel + 72)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 240615969168004511545033772477625056927)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide
  rw [call_identity_direct
    (v := EvmYul.UInt256.ofNat 240615969168004511545033772477625056927) (fuel := fuel + 74)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 240615969168004511545033772477625056927)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide
  rw [call_cleanup_t_uint256_direct
    (v := EvmYul.UInt256.ofNat 240615969168004511545033772477625056927) (fuel := fuel + 76)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 240615969168004511545033772477625056927)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide

private theorem call_convert_t_rational_fixed_seed_to_t_uint256_1391_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 1391)
      [EvmYul.UInt256.ofNat 240615969168004511545033772477625056927]
      (.some "convert_t_rational_240615969168004511545033772477625056927_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [EvmYul.UInt256.ofNat 240615969168004511545033772477625056927]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_fixed_seed_to_t_uint256_direct
      (fuel := fuel + 1291) (shared := shared) (store := store) (hlookup := hlookup)

private def sqrtBaseCaseStepEvm (x z : Nat) : Nat :=
  FormalYul.evmShr 1 (FormalYul.evmAdd (FormalYul.evmDiv x z) z)

@[simp] private theorem call_fun__sqrt_babylonianStep_1384_direct
    (x r fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 1384) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat r]
      (.some yulName_fun__sqrt_babylonianStep) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (sqrtBaseCaseStepEvm x r)]) := by
  simpa [FormalYul.word, sqrtBaseCaseStepEvm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun__sqrt_babylonianStep_direct
      (x := x) (r := r) (fuel := fuel + 1244)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun__sqrt_babylonianStep_1377_direct
    (x r fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 1377) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat r]
      (.some yulName_fun__sqrt_babylonianStep) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (sqrtBaseCaseStepEvm x r)]) := by
  simpa [FormalYul.word, sqrtBaseCaseStepEvm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun__sqrt_babylonianStep_direct
      (x := x) (r := r) (fuel := fuel + 1237)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun__sqrt_babylonianStep_1370_direct
    (x r fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 1370) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat r]
      (.some yulName_fun__sqrt_babylonianStep) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (sqrtBaseCaseStepEvm x r)]) := by
  simpa [FormalYul.word, sqrtBaseCaseStepEvm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun__sqrt_babylonianStep_direct
      (x := x) (r := r) (fuel := fuel + 1230)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun__sqrt_babylonianStep_1363_direct
    (x r fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 1363) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat r]
      (.some yulName_fun__sqrt_babylonianStep) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (sqrtBaseCaseStepEvm x r)]) := by
  simpa [FormalYul.word, sqrtBaseCaseStepEvm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun__sqrt_babylonianStep_direct
      (x := x) (r := r) (fuel := fuel + 1223)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun__sqrt_babylonianStep_1356_direct
    (x r fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 1356) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat r]
      (.some yulName_fun__sqrt_babylonianStep) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (sqrtBaseCaseStepEvm x r)]) := by
  simpa [FormalYul.word, sqrtBaseCaseStepEvm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun__sqrt_babylonianStep_direct
      (x := x) (r := r) (fuel := fuel + 1216)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun__sqrt_babylonianStep_1349_direct
    (x r fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 1349) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat r]
      (.some yulName_fun__sqrt_babylonianStep) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (sqrtBaseCaseStepEvm x r)]) := by
  simpa [FormalYul.word, sqrtBaseCaseStepEvm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun__sqrt_babylonianStep_direct
      (x := x) (r := r) (fuel := fuel + 1209)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun_unsafeDiv_1338_direct
    (numerator denominator fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 1338) [EvmYul.UInt256.ofNat numerator, EvmYul.UInt256.ofNat denominator]
      (.some "fun_unsafeDiv_5899") (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmDiv numerator denominator)]) := by
  simpa [FormalYul.word, yulName_fun_unsafeDiv, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_unsafeDiv_direct
      (numerator := numerator) (denominator := denominator) (fuel := fuel + 1278)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_cleanup_t_uint256_1333_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 1333) [v] (.some "cleanup_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_uint256_direct
      (v := v) (fuel := fuel + 1313) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_cleanup_t_uint256_1331_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 1331) [v] (.some "cleanup_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_uint256_direct
      (v := v) (fuel := fuel + 1311) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_fun_unsafeDec_1334_direct
    (x : Nat) (b : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 1334) [EvmYul.UInt256.ofNat x, b]
      (.some "fun_unsafeDec_5854") (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmSub x
        (FormalYul.evmLt 0 (FormalYul.wordNat b)))]) := by
  simpa [FormalYul.word, yulName_fun_unsafeDec, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_unsafeDec_ofNat_uint256_direct
      (x := x) (b := b) (fuel := fuel + 1274)
      (shared := shared) (store := store) (hlookup := hlookup)

private def sqrtBaseCaseEvm (x : Nat) : Nat × Nat :=
  let z1 := sqrtBaseCaseStepEvm x Sqrt512Cert.FIXED_SEED
  let z2 := sqrtBaseCaseStepEvm x z1
  let z3 := sqrtBaseCaseStepEvm x z2
  let z4 := sqrtBaseCaseStepEvm x z3
  let z5 := sqrtBaseCaseStepEvm x z4
  let z6 := sqrtBaseCaseStepEvm x z5
  let r := FormalYul.evmSub z6 (FormalYul.evmLt (FormalYul.evmDiv x z6) z6)
  (r, FormalYul.evmSub x (FormalYul.evmMul r r))

private theorem call_fun__sqrt_baseCase_direct
    (xHi fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 1400) [FormalYul.word xHi]
      (.some yulName_fun__sqrt_baseCase) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (sqrtBaseCaseEvm xHi).1, FormalYul.word (sqrtBaseCaseEvm xHi).2]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__sqrt_baseCase]
  simp only [yulFunction_fun__sqrt_baseCase, yulFunction_fun__sqrt_baseCase_4393,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 1376)
      (shared := shared)
      (store := Finmap.insert "var_x_hi_4326" (EvmYul.UInt256.ofNat xHi)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup),
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 1374)
      (shared := shared)
      (store := Finmap.insert "var_r_hi_4329" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "zero_t_uint256_73" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "var_x_hi_4326" (EvmYul.UInt256.ofNat xHi)
            (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup),
    call_convert_t_rational_fixed_seed_to_t_uint256_1391_direct (hlookup := hlookup),
    call_fun__sqrt_babylonianStep_1384_direct (hlookup := hlookup),
    call_fun__sqrt_babylonianStep_1377_direct (hlookup := hlookup),
    call_fun__sqrt_babylonianStep_1370_direct (hlookup := hlookup),
    call_fun__sqrt_babylonianStep_1363_direct (hlookup := hlookup),
    call_fun__sqrt_babylonianStep_1356_direct (hlookup := hlookup),
    call_fun__sqrt_babylonianStep_1349_direct (hlookup := hlookup),
    call_fun_unsafeDiv_1338_direct (hlookup := hlookup),
    call_cleanup_t_uint256_1333_direct (hlookup := hlookup),
    call_cleanup_t_uint256_1331_direct (hlookup := hlookup),
    call_fun_unsafeDec_1334_direct (hlookup := hlookup),
    FormalYul.word]
  constructor
  · apply FormalYul.Preservation.eq_of_wordNat_eq
    simp [sqrtBaseCaseEvm, sqrtBaseCaseStepEvm, Sqrt512Cert.FIXED_SEED]
  · apply FormalYul.Preservation.eq_of_wordNat_eq
    simp only [FormalYul.Preservation.wordNat_sub, FormalYul.Preservation.wordNat_mul,
      FormalYul.Preservation.wordNat_ofNat]
    simp [sqrtBaseCaseEvm, sqrtBaseCaseStepEvm, Sqrt512Cert.FIXED_SEED,
      FormalYul.Preservation.evmSub_u256_left]

private theorem call_convert_t_rational_mask128_to_t_uint256_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100)
      [FormalYul.word 340282366920938463463374607431768211455]
      (.some "convert_t_rational_340282366920938463463374607431768211455_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word 340282366920938463463374607431768211455]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions,
    lookup_convert_t_rational_340282366920938463463374607431768211455_by_1_to_t_uint256]
  simp only [yulFunction_convert_t_rational_340282366920938463463374607431768211455_by_1_to_t_uint256,
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
  rw [call_cleanup_t_rational_mask128_direct
    (v := EvmYul.UInt256.ofNat 340282366920938463463374607431768211455) (fuel := fuel + 72)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 340282366920938463463374607431768211455)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide
  rw [call_identity_direct
    (v := EvmYul.UInt256.ofNat 340282366920938463463374607431768211455) (fuel := fuel + 74)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 340282366920938463463374607431768211455)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide
  rw [call_cleanup_t_uint256_direct
    (v := EvmYul.UInt256.ofNat 340282366920938463463374607431768211455) (fuel := fuel + 76)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 340282366920938463463374607431768211455)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide

@[simp] private theorem call_convert_t_rational_mask128_to_t_uint256_939_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 939)
      [EvmYul.UInt256.ofNat 340282366920938463463374607431768211455]
      (.some "convert_t_rational_340282366920938463463374607431768211455_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word 340282366920938463463374607431768211455]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_mask128_to_t_uint256_direct
      (fuel := fuel + 839) (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_shift_left_dynamic_direct
    (bits value fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 40) [FormalYul.word bits, FormalYul.word value]
      (.some "shift_left_dynamic") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmShl bits value)]) := by
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

private theorem call_shift_left_t_uint256_t_uint8_direct
    (value bits fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
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

private theorem call_shift_right_t_uint256_t_uint8_direct
    (value bits fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
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

@[simp] private theorem call_shift_left_t_uint256_t_uint8_128_990_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 990) [EvmYul.UInt256.ofNat value, EvmYul.UInt256.ofNat 128]
      (.some "shift_left_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmShl 128 value)]) := by
  simpa +decide [FormalYul.word, FormalYul.evmAnd,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_left_t_uint256_t_uint8_direct
      (value := value) (bits := 128) (fuel := fuel + 890)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_shift_left_t_uint256_t_uint8_128_958_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 958) [EvmYul.UInt256.ofNat value, EvmYul.UInt256.ofNat 128]
      (.some "shift_left_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmShl 128 value)]) := by
  simpa +decide [FormalYul.word, FormalYul.evmAnd,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_left_t_uint256_t_uint8_direct
      (value := value) (bits := 128) (fuel := fuel + 858)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_shift_left_t_uint256_t_uint8_128_955_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 955) [EvmYul.UInt256.ofNat value, EvmYul.UInt256.ofNat 128]
      (.some "shift_left_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmShl 128 value)]) := by
  simpa +decide [FormalYul.word, FormalYul.evmAnd,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_left_t_uint256_t_uint8_direct
      (value := value) (bits := 128) (fuel := fuel + 855)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_shift_left_t_uint256_t_uint8_128_946_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 946) [EvmYul.UInt256.ofNat value, EvmYul.UInt256.ofNat 128]
      (.some "shift_left_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmShl 128 value)]) := by
  simpa +decide [FormalYul.word, FormalYul.evmAnd,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_left_t_uint256_t_uint8_direct
      (value := value) (bits := 128) (fuel := fuel + 846)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_shift_right_t_uint256_t_uint8_128_976_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 976) [EvmYul.UInt256.ofNat value, EvmYul.UInt256.ofNat 128]
      (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmShr 128 value)]) := by
  simpa +decide [FormalYul.word, FormalYul.evmAnd,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_right_t_uint256_t_uint8_direct
      (value := value) (bits := 128) (fuel := fuel + 876)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_shift_right_t_uint256_t_uint8_128_970_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 970) [EvmYul.UInt256.ofNat value, EvmYul.UInt256.ofNat 128]
      (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmShr 128 value)]) := by
  simpa +decide [FormalYul.word, FormalYul.evmAnd,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_right_t_uint256_t_uint8_direct
      (value := value) (bits := 128) (fuel := fuel + 870)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_shift_right_t_uint256_t_uint8_128_964_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 964) [EvmYul.UInt256.ofNat value, EvmYul.UInt256.ofNat 128]
      (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmShr 128 value)]) := by
  simpa +decide [FormalYul.word, FormalYul.evmAnd,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_right_t_uint256_t_uint8_direct
      (value := value) (bits := 128) (fuel := fuel + 864)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_shift_right_t_uint256_t_uint8_128_961_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 961) [EvmYul.UInt256.ofNat value, EvmYul.UInt256.ofNat 128]
      (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmShr 128 value)]) := by
  simpa +decide [FormalYul.word, FormalYul.evmAnd,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_right_t_uint256_t_uint8_direct
      (value := value) (bits := 128) (fuel := fuel + 861)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_shift_right_t_uint256_t_uint8_128_955_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 955) [EvmYul.UInt256.ofNat value, EvmYul.UInt256.ofNat 128]
      (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmShr 128 value)]) := by
  simpa +decide [FormalYul.word, FormalYul.evmAnd,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_right_t_uint256_t_uint8_direct
      (value := value) (bits := 128) (fuel := fuel + 855)
      (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_shift_right_t_uint256_t_uint256_direct
    (value bits fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100) [FormalYul.word value, FormalYul.word bits]
      (.some "shift_right_t_uint256_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmShr bits value)]) := by
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

private theorem call_wrapping_mul_t_uint256_direct
    (x y fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 80) [FormalYul.word x, FormalYul.word y]
      (.some "wrapping_mul_t_uint256") (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmMul x y)]) := by
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
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hcleanup]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_mul]
  simp [FormalYul.Preservation.evmMul_u256_left, FormalYul.Preservation.evmMul_u256_right]

@[simp] private theorem call_wrapping_mul_t_uint256_934_direct
    (x y fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 934) [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat y]
      (.some "wrapping_mul_t_uint256") (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmMul x y)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_wrapping_mul_t_uint256_direct
      (x := x) (y := y) (fuel := fuel + 854)
      (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_fun__sqrt_karatsubaQuotient_direct
    (res xLo rHi fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 300) [FormalYul.word res, FormalYul.word xLo, FormalYul.word rHi]
      (.some yulName_fun__sqrt_karatsubaQuotient) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    let n := FormalYul.evmOr (FormalYul.evmShl 128 res) (FormalYul.evmShr 128 xLo)
    let d := FormalYul.evmShl 1 rHi
    let q0 := FormalYul.evmDiv n d
    let rem0 := FormalYul.evmMod n d
    let c := FormalYul.evmShr 128 res
    let q1 := FormalYul.evmAdd q0 (FormalYul.evmDiv (FormalYul.evmNot 0) d)
    let rem1 := FormalYul.evmAdd rem0
      (FormalYul.evmAdd 1 (FormalYul.evmMod (FormalYul.evmNot 0) d))
    let q2 := FormalYul.evmAdd q1 (FormalYul.evmDiv rem1 d)
    let rem2 := FormalYul.evmMod rem1 d
    if c = 0 then
      .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word q0, FormalYul.word rem0])
    else
      .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word q2, FormalYul.word rem2]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__sqrt_karatsubaQuotient]
  simp only [yulFunction_fun__sqrt_karatsubaQuotient, yulFunction_fun__sqrt_karatsubaQuotient_4409,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    FormalYul.word,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 276)
      (shared := shared)
      (store := Finmap.insert "var_res_4396" (EvmYul.UInt256.ofNat res)
        (Finmap.insert "var_x_lo_4398" (EvmYul.UInt256.ofNat xLo)
          (Finmap.insert "var_r_hi_4400" (EvmYul.UInt256.ofNat rHi)
            (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup),
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 274)
      (shared := shared)
      (store := Finmap.insert "var_r_lo_4403" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "zero_t_uint256_92" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "var_res_4396" (EvmYul.UInt256.ofNat res)
            (Finmap.insert "var_x_lo_4398" (EvmYul.UInt256.ofNat xLo)
              (Finmap.insert "var_r_hi_4400" (EvmYul.UInt256.ofNat rHi)
                (Inhabited.default : EvmYul.Yul.VarStore))))))
      (hlookup := hlookup)]
  by_cases hc : FormalYul.evmShr 128 res = 0
  · have hcUInt :
        EvmYul.UInt256.shiftRight (EvmYul.UInt256.ofNat res) (EvmYul.UInt256.ofNat 128) =
          ({ val := 0 } : EvmYul.UInt256) := by
      apply FormalYul.Preservation.eq_of_wordNat_eq
      simpa [FormalYul.word] using hc
    simp +decide [hcUInt, hc, Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
    constructor
    · apply FormalYul.Preservation.eq_of_wordNat_eq
      simp +decide [FormalYul.Preservation.wordNat_div, FormalYul.Preservation.wordNat_or,
        FormalYul.Preservation.wordNat_shiftLeft, FormalYul.Preservation.wordNat_shiftRight,
        FormalYul.Preservation.wordNat_ofNat]
    · apply FormalYul.Preservation.eq_of_wordNat_eq
      simp +decide [FormalYul.Preservation.wordNat_or,
        FormalYul.Preservation.wordNat_shiftLeft, FormalYul.Preservation.wordNat_shiftRight,
        FormalYul.Preservation.wordNat_ofNat]
  · have hcUInt :
        EvmYul.UInt256.shiftRight (EvmYul.UInt256.ofNat res) (EvmYul.UInt256.ofNat 128) ≠
          ({ val := 0 } : EvmYul.UInt256) := by
      intro h
      apply hc
      have hw := congrArg FormalYul.wordNat h
      simpa [FormalYul.word] using hw
    simp +decide [hcUInt, hc, Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
    constructor
    · apply FormalYul.Preservation.eq_of_wordNat_eq
      simp +decide [FormalYul.Preservation.wordNat_add, FormalYul.Preservation.wordNat_div,
        FormalYul.Preservation.wordNat_not,
        FormalYul.Preservation.wordNat_or, FormalYul.Preservation.wordNat_shiftLeft,
        FormalYul.Preservation.wordNat_shiftRight, FormalYul.Preservation.wordNat_ofNat]
    · apply FormalYul.Preservation.eq_of_wordNat_eq
      simp +decide [FormalYul.Preservation.wordNat_add,
        FormalYul.Preservation.wordNat_not,
        FormalYul.Preservation.wordNat_or, FormalYul.Preservation.wordNat_shiftLeft,
        FormalYul.Preservation.wordNat_shiftRight, FormalYul.Preservation.wordNat_ofNat]

private theorem call_fun__sqrt_correction_direct
    (rHi rLo res xLo fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 1000)
      [FormalYul.word rHi, FormalYul.word rLo, FormalYul.word res, FormalYul.word xLo]
      (.some yulName_fun__sqrt_correction) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    let r := FormalYul.evmAdd (FormalYul.evmShl 128 rHi) rLo
    let hiRes := FormalYul.evmShr 128 res
    let hiRLo := FormalYul.evmShr 128 rLo
    let loRes := FormalYul.evmOr (FormalYul.evmShl 128 res)
      (FormalYul.evmAnd xLo 340282366920938463463374607431768211455)
    let loSq := FormalYul.evmMul rLo rLo
    let dec := FormalYul.evmOr (FormalYul.evmLt hiRes hiRLo)
      (FormalYul.evmAnd (FormalYul.evmEq hiRes hiRLo) (FormalYul.evmLt loRes loSq))
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmSub r dec)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__sqrt_correction]
  simp only [yulFunction_fun__sqrt_correction, yulFunction_fun__sqrt_correction_4477,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 976)
      (shared := shared)
      (store := Finmap.insert "var_r_hi_4412" (EvmYul.UInt256.ofNat rHi)
        (Finmap.insert "var_r_lo_4414" (EvmYul.UInt256.ofNat rLo)
          (Finmap.insert "var_res_4416" (EvmYul.UInt256.ofNat res)
            (Finmap.insert "var_x_lo_4418" (EvmYul.UInt256.ofNat xLo)
              (Inhabited.default : EvmYul.Yul.VarStore)))))
      (hlookup := hlookup),
    call_convert_t_rational_128_by_1_to_t_uint8_128_991_direct (hlookup := hlookup),
    call_convert_t_rational_128_by_1_to_t_uint8_128_977_direct (hlookup := hlookup),
    call_convert_t_rational_128_by_1_to_t_uint8_128_971_direct (hlookup := hlookup),
    call_convert_t_rational_128_by_1_to_t_uint8_128_959_direct (hlookup := hlookup),
    call_convert_t_rational_128_by_1_to_t_uint8_128_953_direct (hlookup := hlookup),
    call_convert_t_rational_128_by_1_to_t_uint8_128_947_direct (hlookup := hlookup),
    hlookup,
    call_shift_left_t_uint256_t_uint8_128_990_direct,
    call_shift_left_t_uint256_t_uint8_128_946_direct,
    call_shift_right_t_uint256_t_uint8_128_976_direct,
    call_shift_right_t_uint256_t_uint8_128_970_direct,
    call_shift_right_t_uint256_t_uint8_128_961_direct,
    call_shift_right_t_uint256_t_uint8_128_955_direct,
    call_wrapping_add_t_uint256_986_direct,
    call_cleanup_t_uint256_966_direct,
    call_cleanup_t_uint256_964_direct,
    call_cleanup_t_uint256_951_direct,
    call_cleanup_t_uint256_949_direct,
    call_cleanup_t_uint256_931_direct,
    call_cleanup_t_uint256_929_direct,
    call_convert_t_rational_mask128_to_t_uint256_939_direct,
    call_wrapping_mul_t_uint256_934_direct,
    call_fun_and_932_direct, call_fun_or_931_direct,
    call_fun_unsafeDec_930_direct,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne, FormalYul.word]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp +decide [FormalYul.Preservation.wordNat_sub,
    FormalYul.Preservation.wordNat_or, FormalYul.Preservation.wordNat_and,
    FormalYul.Preservation.wordNat_eq, FormalYul.Preservation.wordNat_lt,
    FormalYul.Preservation.wordNat_ofNat,
    FormalYul.Preservation.evmAnd_u256_left, FormalYul.Preservation.evmAnd_u256_right]

private theorem evmSub_eq_of_le (a b : Nat) (ha : a < FormalYul.WORD_MOD) (hb : b ≤ a) :
    FormalYul.evmSub a b = a - b := by
  have hb' : b < FormalYul.WORD_MOD := Nat.lt_of_le_of_lt hb ha
  have hab' : a - b < FormalYul.WORD_MOD := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
  unfold FormalYul.evmSub FormalYul.u256
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb']
  have hsplit : a + FormalYul.WORD_MOD - b = FormalYul.WORD_MOD + (a - b) := by omega
  rw [hsplit, Nat.add_mod, Nat.mod_eq_zero_of_dvd (Nat.dvd_refl FormalYul.WORD_MOD),
    Nat.zero_add, Nat.mod_mod_of_dvd, Nat.mod_eq_of_lt hab']
  exact Nat.dvd_refl FormalYul.WORD_MOD

private theorem evmDiv_eq_of_lt
    (a b : Nat) (ha : a < FormalYul.WORD_MOD) (hb : 0 < b) (hb' : b < FormalYul.WORD_MOD) :
    FormalYul.evmDiv a b = a / b := by
  unfold FormalYul.evmDiv
  simp [FormalYul.u256_eq_self_of_lt ha, FormalYul.u256_eq_self_of_lt hb', Nat.ne_of_gt hb]

private theorem evmMod_eq_of_lt
    (a b : Nat) (ha : a < FormalYul.WORD_MOD) (hb : 0 < b) (hb' : b < FormalYul.WORD_MOD) :
    FormalYul.evmMod a b = a % b := by
  unfold FormalYul.evmMod
  simp [FormalYul.u256_eq_self_of_lt ha, FormalYul.u256_eq_self_of_lt hb', Nat.ne_of_gt hb]

private theorem evmOr_eq_of_lt
    (a b : Nat) (ha : a < FormalYul.WORD_MOD) (hb : b < FormalYul.WORD_MOD) :
    FormalYul.evmOr a b = a ||| b := by
  unfold FormalYul.evmOr
  simp [FormalYul.u256_eq_self_of_lt ha, FormalYul.u256_eq_self_of_lt hb]

private theorem evmAnd_eq_of_lt
    (a b : Nat) (ha : a < FormalYul.WORD_MOD) (hb : b < FormalYul.WORD_MOD) :
    FormalYul.evmAnd a b = a &&& b := by
  unfold FormalYul.evmAnd
  simp [FormalYul.u256_eq_self_of_lt ha, FormalYul.u256_eq_self_of_lt hb]

private theorem evmShr_eq_of_lt
    (s v : Nat) (hs : s < 256) (hv : v < FormalYul.WORD_MOD) :
    FormalYul.evmShr s v = v / 2 ^ s := by
  have hs' : s < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    omega
  unfold FormalYul.evmShr
  simp [FormalYul.u256_eq_self_of_lt hs', FormalYul.u256_eq_self_of_lt hv, hs]

private theorem evmShl_eq_of_lt
    (s v : Nat) (hs : s < 256) (hv : v < FormalYul.WORD_MOD) :
    FormalYul.evmShl s v = (v * 2 ^ s) % FormalYul.WORD_MOD := by
  have hs' : s < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    omega
  unfold FormalYul.evmShl FormalYul.u256
  simp [Nat.mod_eq_of_lt hs', Nat.mod_eq_of_lt hv, hs]

private theorem evmAdd_eq_of_lt
    (a b : Nat) (ha : a < FormalYul.WORD_MOD) (hb : b < FormalYul.WORD_MOD)
    (hab : a + b < FormalYul.WORD_MOD) :
    FormalYul.evmAdd a b = a + b := by
  unfold FormalYul.evmAdd FormalYul.u256
  simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hab]

private theorem evmMul_eq_mod_of_lt
    (a b : Nat) (ha : a < FormalYul.WORD_MOD) (hb : b < FormalYul.WORD_MOD) :
    FormalYul.evmMul a b = (a * b) % FormalYul.WORD_MOD := by
  unfold FormalYul.evmMul FormalYul.u256
  simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

private theorem evmClz_eq_of_lt (v : Nat) (hv : v < FormalYul.WORD_MOD) :
    FormalYul.evmClz v = if v = 0 then 256 else 255 - Nat.log2 v := by
  unfold FormalYul.evmClz
  simp [FormalYul.u256_eq_self_of_lt hv]

private theorem evmLt_eq_of_lt
    (a b : Nat) (ha : a < FormalYul.WORD_MOD) (hb : b < FormalYul.WORD_MOD) :
    FormalYul.evmLt a b = if a < b then 1 else 0 := by
  unfold FormalYul.evmLt
  simp [FormalYul.u256_eq_self_of_lt ha, FormalYul.u256_eq_self_of_lt hb]

private theorem evmEq_eq_of_lt
    (a b : Nat) (ha : a < FormalYul.WORD_MOD) (hb : b < FormalYul.WORD_MOD) :
    FormalYul.evmEq a b = if a = b then 1 else 0 := by
  unfold FormalYul.evmEq
  simp [FormalYul.u256_eq_self_of_lt ha, FormalYul.u256_eq_self_of_lt hb]

private theorem evmNot_eq_of_lt (a : Nat) (ha : a < FormalYul.WORD_MOD) :
    FormalYul.evmNot a = FormalYul.WORD_MOD - 1 - a := by
  unfold FormalYul.evmNot
  simp [FormalYul.u256_eq_self_of_lt ha]

private theorem evmSub_evmAdd_eq_of_overflow (a b : Nat)
    (ha : a < FormalYul.WORD_MOD) (hb : b < FormalYul.WORD_MOD)
    (hab : a + b = FormalYul.WORD_MOD) :
    FormalYul.evmSub (FormalYul.evmAdd a b) 1 = FormalYul.WORD_MOD - 1 := by
  unfold FormalYul.evmAdd FormalYul.evmSub FormalYul.u256
  simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hab, Nat.mod_self]
  have h1 : (1 : Nat) < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    omega
  simp [Nat.mod_eq_of_lt h1]

private theorem mul_mod_sq (a n : Nat) (hn : 0 < n) :
    (a * n) % (n * n) = (a % n) * n := by
  have h := Nat.div_add_mod a n
  have ha : a * n = n * n * (a / n) + a % n * n := by
    have h2 : a * n = (n * (a / n) + a % n) * n := by rw [h]
    rw [h2, Nat.add_mul]
    congr 1
    rw [Nat.mul_assoc, Nat.mul_comm (a / n) n, ← Nat.mul_assoc]
  rw [ha, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (Nat.mul_lt_mul_of_pos_right (Nat.mod_lt a hn) hn)

private theorem mul_pow128_mod_word (a : Nat) :
    (a * 2 ^ 128) % FormalYul.WORD_MOD = (a % 2 ^ 128) * 2 ^ 128 := by
  have : FormalYul.WORD_MOD = 2 ^ 128 * 2 ^ 128 := by
    unfold FormalYul.WORD_MOD
    rw [← Nat.pow_add]
  rw [this]
  exact mul_mod_sq a (2 ^ 128) (Nat.two_pow_pos 128)

private theorem div_of_mul_add (d q r : Nat) (hd : 0 < d) :
    (d * q + r) / d = q + r / d := by
  rw [show d * q + r = r + q * d from by rw [Nat.mul_comm, Nat.add_comm],
    Nat.add_mul_div_right r q hd, Nat.add_comm]

private theorem mod_of_mul_add (d q r : Nat) :
    (d * q + r) % d = r % d := by
  rw [show d * q + r = r + q * d from by rw [Nat.mul_comm, Nat.add_comm]]
  exact Nat.add_mul_mod_self_right r q d

private theorem testBit_254_succ_of_lt_7 (i : Nat) (hi : i < 7) :
    (254 : Nat).testBit (i + 1) = true := by
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
    omega
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem testBit_mul_two_div_two_succ (n i : Nat) :
    (2 * (n / 2)).testBit (i + 1) = n.testBit (i + 1) := by
  rw [show 2 * (n / 2) = (n / 2) <<< 1 by
    rw [Nat.shiftLeft_eq]
    simp [Nat.mul_comm]]
  simp [Nat.testBit_shiftLeft, Nat.testBit_div_two]

private theorem testBit_mul_two_div_two_zero (n : Nat) :
    (2 * (n / 2)).testBit 0 = false := by
  rw [show 2 * (n / 2) = (n / 2) <<< 1 by
    rw [Nat.shiftLeft_eq]
    simp [Nat.mul_comm]]
  simp

private theorem and_shift_254 (n : Nat) (hn : n < 256) :
    n &&& 254 = 2 * (n / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
      rw [Nat.testBit_and, testBit_mul_two_div_two_zero]
      simp
  | succ i =>
      by_cases hi : i < 7
      · have hmask := testBit_254_succ_of_lt_7 i hi
        rw [Nat.testBit_and, hmask]
        simp [testBit_mul_two_div_two_succ]
      · have hi7 : 7 ≤ i := Nat.le_of_not_gt hi
        have hnbit : n.testBit (i + 1) = false := by
          apply Nat.testBit_lt_two_pow
          have hpow : 2 ^ 8 ≤ 2 ^ (i + 1) :=
            Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega)
          have h256 : 256 ≤ 2 ^ (i + 1) := by simpa using hpow
          omega
        rw [Nat.testBit_and, hnbit]
        simp [testBit_mul_two_div_two_succ, hnbit]

private theorem and_1_255 : (1 : Nat) &&& (255 : Nat) = 1 := by decide

private theorem or_eq_add_shl (a b s : Nat) (hb : b < 2 ^ s) :
    (a * 2 ^ s) ||| b = a * 2 ^ s + b := by
  rw [← Nat.shiftLeft_eq]
  exact (Nat.shiftLeft_add_eq_or_of_lt hb a).symm

private theorem shl512_hi (xHi xLo s : Nat) (hs : s ≤ 255) :
    (xHi * 2 ^ 256 + xLo) * 2 ^ s / 2 ^ 256 =
      xHi * 2 ^ s + xLo / 2 ^ (256 - s) := by
  have hrw : (xHi * 2 ^ 256 + xLo) * 2 ^ s =
      xLo * 2 ^ s + xHi * 2 ^ s * 2 ^ 256 := by
    rw [Nat.add_mul, Nat.mul_right_comm]
    omega
  rw [hrw, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 256), Nat.add_comm]
  congr 1
  have h256_split : 2 ^ 256 = 2 ^ (256 - s) * 2 ^ s := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [h256_split]
  exact Nat.mul_div_mul_right _ _ (Nat.two_pow_pos s)

private theorem shl512_lo (xHi xLo s : Nat) :
    (xHi * 2 ^ 256 + xLo) * 2 ^ s % 2 ^ 256 =
      (xLo * 2 ^ s) % 2 ^ 256 := by
  have hrw : (xHi * 2 ^ 256 + xLo) * 2 ^ s =
      xLo * 2 ^ s + xHi * 2 ^ s * 2 ^ 256 := by
    rw [Nat.add_mul, Nat.mul_right_comm]
    omega
  rw [hrw, Nat.add_mul_mod_self_right]

private theorem shl_no_overflow (xHi s : Nat) (h : xHi * 2 ^ s < 2 ^ 256) :
    (xHi * 2 ^ s) % 2 ^ 256 = xHi * 2 ^ s :=
  Nat.mod_eq_of_lt h

private theorem shl_or_shr (xHi xLo s : Nat) (hs : 0 < s) (hs' : s ≤ 255)
    (hxlo : xLo < 2 ^ 256) :
    (xHi * 2 ^ s) ||| (xLo / 2 ^ (256 - s)) =
      xHi * 2 ^ s + xLo / 2 ^ (256 - s) := by
  have hcarry : xLo / 2 ^ (256 - s) < 2 ^ s := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    calc
      xLo < 2 ^ 256 := hxlo
      _ = 2 ^ s * 2 ^ (256 - s) := by
        rw [← Nat.pow_add]
        congr 1
        omega
  exact or_eq_add_shl xHi (xLo / 2 ^ (256 - s)) s hcarry

private theorem shl512_hi_or (xHi xLo s : Nat) (hs : 0 < s) (hs' : s ≤ 255)
    (hxhi_shl : xHi * 2 ^ s < 2 ^ 256) (hxlo : xLo < 2 ^ 256) :
    ((xHi * 2 ^ s) % 2 ^ 256) ||| (xLo / 2 ^ (256 - s)) =
      (xHi * 2 ^ 256 + xLo) * 2 ^ s / 2 ^ 256 := by
  rw [shl_no_overflow xHi s hxhi_shl, shl_or_shr xHi xLo s hs hs' hxlo,
    shl512_hi xHi xLo s hs']

private theorem evmNormalization_correct (xHi xLo : Nat)
    (hxhi_pos : 0 < xHi) (hxhi_lt : xHi < 2 ^ 256) (hxlo_lt : xLo < 2 ^ 256) :
    let x := xHi * 2 ^ 256 + xLo
    let k := (255 - Nat.log2 xHi) / 2
    let shift := FormalYul.evmClz (FormalYul.u256 xHi)
    let dblK := FormalYul.evmAnd shift 254
    let xLo1 := FormalYul.evmShl dblK (FormalYul.u256 xLo)
    let xHi1 := FormalYul.evmOr (FormalYul.evmShl dblK (FormalYul.u256 xHi))
      (FormalYul.evmShr (FormalYul.evmSub 256 dblK) (FormalYul.u256 xLo))
    let kEvm := FormalYul.evmShr (FormalYul.evmAnd (FormalYul.evmAnd 1 255) 255) shift
    xHi1 = x * 4 ^ k / 2 ^ 256 ∧
    xLo1 = x * 4 ^ k % 2 ^ 256 ∧
    kEvm = k ∧
    2 ^ 254 ≤ xHi1 ∧
    xHi1 < 2 ^ 256 ∧
    xLo1 < 2 ^ 256 := by
  intro x k shift dblK xLo1 xHi1 kEvm
  have hxhi_wm : xHi < FormalYul.WORD_MOD := by
    simpa [FormalYul.WORD_MOD] using hxhi_lt
  have hxlo_wm : xLo < FormalYul.WORD_MOD := by
    simpa [FormalYul.WORD_MOD] using hxlo_lt
  have hxhi_ne : xHi ≠ 0 := Nat.ne_of_gt hxhi_pos
  have hlog_le : Nat.log2 xHi ≤ 255 := by
    have := (Nat.log2_lt hxhi_ne).2 hxhi_lt
    omega
  have hshift_eq : shift = 255 - Nat.log2 xHi := by
    dsimp [shift]
    rw [FormalYul.u256_eq_self_of_lt hxhi_wm, evmClz_eq_of_lt xHi hxhi_wm]
    simp [hxhi_ne]
  have hshift_wm : shift < FormalYul.WORD_MOD := by
    rw [hshift_eq]
    unfold FormalYul.WORD_MOD
    omega
  have hdblK : dblK = 2 * k := by
    dsimp [dblK]
    rw [evmAnd_eq_of_lt _ 254 hshift_wm (by unfold FormalYul.WORD_MOD; omega), hshift_eq]
    exact and_shift_254 (255 - Nat.log2 xHi) (by omega)
  have hdblK_lt : dblK < 256 := by omega
  have hsub_eq : FormalYul.evmSub 256 dblK = 256 - dblK :=
    evmSub_eq_of_le 256 dblK (by unfold FormalYul.WORD_MOD; omega) (by omega)
  have hkEvm_eq : kEvm = k := by
    dsimp [kEvm]
    have h1 : (1 : Nat) < FormalYul.WORD_MOD := by unfold FormalYul.WORD_MOD; omega
    have h255 : (255 : Nat) < FormalYul.WORD_MOD := by unfold FormalYul.WORD_MOD; omega
    rw [evmAnd_eq_of_lt 1 255 h1 h255, and_1_255,
      evmAnd_eq_of_lt 1 255 h1 h255, and_1_255]
    rw [evmShr_eq_of_lt 1 shift (by omega) hshift_wm, hshift_eq, Nat.pow_one]
  have hfour_eq : 4 ^ k = 2 ^ dblK := by
    rw [hdblK, show (4 : Nat) = 2 ^ 2 from by decide, ← Nat.pow_mul]
  have hsr := shift_range xHi hxhi_pos hxhi_lt
  have hxhi_shl_lt : xHi * 2 ^ dblK < 2 ^ 256 := by
    rw [← hfour_eq]
    exact hsr.2
  have hshl_xhi : FormalYul.evmShl dblK (FormalYul.u256 xHi) =
      (xHi * 2 ^ dblK) % FormalYul.WORD_MOD := by
    rw [FormalYul.u256_eq_self_of_lt hxhi_wm]
    exact evmShl_eq_of_lt dblK xHi hdblK_lt hxhi_wm
  by_cases hdblK_zero : dblK = 0
  · have hk_zero : k = 0 := by omega
    have hxHi1_eq : xHi1 = xHi := by
      dsimp [xHi1]
      rw [hdblK_zero, FormalYul.u256_eq_self_of_lt hxhi_wm, FormalYul.u256_eq_self_of_lt hxlo_wm]
      rw [evmShl_eq_of_lt 0 xHi (by omega) hxhi_wm, Nat.pow_zero, Nat.mul_one]
      unfold FormalYul.WORD_MOD
      rw [Nat.mod_eq_of_lt hxhi_lt]
      rw [evmSub_eq_of_le 256 0 (by unfold FormalYul.WORD_MOD; omega) (by omega)]
      have hshr : FormalYul.evmShr 256 xLo = 0 := by
        unfold FormalYul.evmShr FormalYul.u256 FormalYul.WORD_MOD
        simp
      rw [hshr, evmOr_eq_of_lt xHi 0 hxhi_wm (by unfold FormalYul.WORD_MOD; omega)]
      simp
    have hxLo1_eq : xLo1 = xLo := by
      dsimp [xLo1]
      rw [hdblK_zero, FormalYul.u256_eq_self_of_lt hxlo_wm,
        evmShl_eq_of_lt 0 xLo (by omega) hxlo_wm, Nat.pow_zero, Nat.mul_one]
      unfold FormalYul.WORD_MOD
      exact Nat.mod_eq_of_lt hxlo_lt
    have hxdiv : x / 2 ^ 256 = xHi := by
      dsimp [x]
      rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos 256), Nat.div_eq_of_lt hxlo_lt,
        Nat.add_zero]
    have hxmod : x % 2 ^ 256 = xLo := by
      dsimp [x]
      rw [Nat.mul_comm, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt hxlo_lt
    have h4k_one : 4 ^ k = 1 := by simp [hk_zero]
    refine ⟨?_, ?_, hkEvm_eq, ?_, ?_, ?_⟩
    · rw [hxHi1_eq, h4k_one, Nat.mul_one, hxdiv]
    · rw [hxLo1_eq, h4k_one, Nat.mul_one, hxmod]
    · rw [hxHi1_eq]
      have := hsr.1
      rw [h4k_one, Nat.mul_one] at this
      exact this
    · rw [hxHi1_eq]
      exact hxhi_lt
    · rw [hxLo1_eq]
      exact hxlo_lt
  · have hdblK_pos : 0 < dblK := by omega
    have hshr_xlo : FormalYul.evmShr (FormalYul.evmSub 256 dblK) (FormalYul.u256 xLo) =
        xLo / 2 ^ (256 - dblK) := by
      rw [FormalYul.u256_eq_self_of_lt hxlo_wm, hsub_eq]
      exact evmShr_eq_of_lt (256 - dblK) xLo (by omega) hxlo_wm
    have hshl_xlo : FormalYul.evmShl dblK (FormalYul.u256 xLo) =
        (xLo * 2 ^ dblK) % FormalYul.WORD_MOD := by
      rw [FormalYul.u256_eq_self_of_lt hxlo_wm]
      exact evmShl_eq_of_lt dblK xLo hdblK_lt hxlo_wm
    have hshl_xhi_wm : FormalYul.evmShl dblK (FormalYul.u256 xHi) < FormalYul.WORD_MOD := by
      rw [hshl_xhi]
      exact Nat.mod_lt _ (by unfold FormalYul.WORD_MOD; omega)
    have hshr_xlo_wm :
        FormalYul.evmShr (FormalYul.evmSub 256 dblK) (FormalYul.u256 xLo) < FormalYul.WORD_MOD := by
      rw [hshr_xlo]
      unfold FormalYul.WORD_MOD
      have : xLo / 2 ^ (256 - dblK) < 2 ^ dblK := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
        calc
          xLo < 2 ^ 256 := hxlo_lt
          _ = 2 ^ dblK * 2 ^ (256 - dblK) := by
            rw [← Nat.pow_add]
            congr 1
            omega
      exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) (by omega))
    have hxHi1_eq : xHi1 = x * 4 ^ k / 2 ^ 256 := by
      dsimp [xHi1]
      rw [evmOr_eq_of_lt _ _ hshl_xhi_wm hshr_xlo_wm, hshl_xhi, hshr_xlo]
      unfold FormalYul.WORD_MOD
      rw [shl512_hi_or xHi xLo dblK hdblK_pos (by omega) hxhi_shl_lt hxlo_lt]
      congr 1
      rw [← hfour_eq]
    have hxLo1_eq : xLo1 = x * 4 ^ k % 2 ^ 256 := by
      dsimp [xLo1]
      rw [hshl_xlo]
      unfold FormalYul.WORD_MOD
      rw [show x * 4 ^ k = (xHi * 2 ^ 256 + xLo) * 2 ^ dblK from by
        dsimp [x]
        rw [← hfour_eq]]
      exact (shl512_lo xHi xLo dblK).symm
    have hhi_eq : x * 4 ^ k / 2 ^ 256 =
        xHi * 2 ^ dblK + xLo / 2 ^ (256 - dblK) := by
      rw [show x * 4 ^ k = (xHi * 2 ^ 256 + xLo) * 2 ^ dblK from by
        dsimp [x]
        rw [← hfour_eq]]
      exact shl512_hi xHi xLo dblK (by omega)
    have hhi_lo_bound : 2 ^ 254 ≤ x * 4 ^ k / 2 ^ 256 := by
      rw [hhi_eq]
      have := hsr.1
      rw [hfour_eq] at this
      omega
    have hshr_xlo_val : xLo / 2 ^ (256 - dblK) < 2 ^ dblK := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      calc
        xLo < 2 ^ 256 := hxlo_lt
        _ = 2 ^ dblK * 2 ^ (256 - dblK) := by
          rw [← Nat.pow_add]
          congr 1
          omega
    have hhi_hi_bound : x * 4 ^ k / 2 ^ 256 < 2 ^ 256 := by
      rw [hhi_eq]
      have h2 : (xHi + 1) * 2 ^ dblK ≤ 2 ^ 256 := by
        rw [Nat.succ_mul]
        have h256 : 2 ^ 256 = 2 ^ dblK * 2 ^ (256 - dblK) := by
          rw [← Nat.pow_add]
          congr 1
          omega
        rw [h256] at hxhi_shl_lt ⊢
        have hxhi_lt_pow : xHi < 2 ^ (256 - dblK) := by
          rw [Nat.mul_comm] at hxhi_shl_lt
          exact Nat.lt_of_mul_lt_mul_left hxhi_shl_lt
        calc
          xHi * 2 ^ dblK + 2 ^ dblK = (xHi + 1) * 2 ^ dblK := by rw [Nat.succ_mul]
          _ ≤ 2 ^ (256 - dblK) * 2 ^ dblK := Nat.mul_le_mul_right _ hxhi_lt_pow
          _ = 2 ^ dblK * 2 ^ (256 - dblK) := Nat.mul_comm _ _
      calc
        xHi * 2 ^ dblK + xLo / 2 ^ (256 - dblK)
            < xHi * 2 ^ dblK + 2 ^ dblK := by omega
        _ = (xHi + 1) * 2 ^ dblK := by rw [Nat.succ_mul]
        _ ≤ 2 ^ 256 := h2
    have hlo1_bound : xLo1 < 2 ^ 256 := by
      rw [hxLo1_eq]
      exact Nat.mod_lt _ (by omega)
    exact ⟨hxHi1_eq, hxLo1_eq, hkEvm_eq, hxHi1_eq ▸ hhi_lo_bound,
      hxHi1_eq ▸ hhi_hi_bound, hlo1_bound⟩

private theorem fixedSeed_pos : 0 < Sqrt512Cert.FIXED_SEED := by
  unfold Sqrt512Cert.FIXED_SEED
  norm_num

private theorem fixedSeed_run6_error_254
    (x m : Nat)
    (hm : 0 < m)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hlo : Sqrt512Cert.lo254 ≤ m)
    (hhi : m ≤ Sqrt512Cert.hi254) :
    SqrtCertified.run6From x Sqrt512Cert.FIXED_SEED - m ≤ Sqrt512Cert.fd6_254 := by
  let z1 := bstep x Sqrt512Cert.FIXED_SEED
  let z2 := bstep x z1
  let z3 := bstep x z2
  let z4 := bstep x z3
  let z5 := bstep x z4
  let z6 := bstep x z5
  have hs : 0 < Sqrt512Cert.FIXED_SEED := fixedSeed_pos
  have hmz1 : m ≤ z1 := by
    dsimp [z1]
    exact babylon_step_floor_bound x Sqrt512Cert.FIXED_SEED m hs hmlo
  have hz1Pos : 0 < z1 := Nat.lt_of_lt_of_le hm hmz1
  have hd1 : z1 - m ≤ Sqrt512Cert.fd1_254 := by
    have h := SqrtBridge.d1_bound x m Sqrt512Cert.FIXED_SEED Sqrt512Cert.lo254
      Sqrt512Cert.hi254 hs hmlo hmhi hlo hhi
    simpa [z1, Sqrt512Cert.fd1_254, Sqrt512Cert.maxAbs254] using h
  have hd1m : Sqrt512Cert.fd1_254 ≤ m := Nat.le_trans Sqrt512Cert.fd1_254_le_lo hlo
  have hmz2 : m ≤ z2 := by
    dsimp [z2]
    exact babylon_step_floor_bound x z1 m hz1Pos hmlo
  have hz2Pos : 0 < z2 := Nat.lt_of_lt_of_le hm hmz2
  have hd2 : z2 - m ≤ Sqrt512Cert.fd2_254 := by
    have h := SqrtCertified.step_from_bound x m Sqrt512Cert.lo254 z1
      Sqrt512Cert.fd1_254 hm Sqrt512Cert.lo254_pos hlo hmhi hmz1 hd1 hd1m
    simpa [z2, Sqrt512Cert.fd2_254] using h
  have hd2m : Sqrt512Cert.fd2_254 ≤ m := Nat.le_trans Sqrt512Cert.fd2_254_le_lo hlo
  have hmz3 : m ≤ z3 := by
    dsimp [z3]
    exact babylon_step_floor_bound x z2 m hz2Pos hmlo
  have hz3Pos : 0 < z3 := Nat.lt_of_lt_of_le hm hmz3
  have hd3 : z3 - m ≤ Sqrt512Cert.fd3_254 := by
    have h := SqrtCertified.step_from_bound x m Sqrt512Cert.lo254 z2
      Sqrt512Cert.fd2_254 hm Sqrt512Cert.lo254_pos hlo hmhi hmz2 hd2 hd2m
    simpa [z3, Sqrt512Cert.fd3_254] using h
  have hd3m : Sqrt512Cert.fd3_254 ≤ m := Nat.le_trans Sqrt512Cert.fd3_254_le_lo hlo
  have hmz4 : m ≤ z4 := by
    dsimp [z4]
    exact babylon_step_floor_bound x z3 m hz3Pos hmlo
  have hz4Pos : 0 < z4 := Nat.lt_of_lt_of_le hm hmz4
  have hd4 : z4 - m ≤ Sqrt512Cert.fd4_254 := by
    have h := SqrtCertified.step_from_bound x m Sqrt512Cert.lo254 z3
      Sqrt512Cert.fd3_254 hm Sqrt512Cert.lo254_pos hlo hmhi hmz3 hd3 hd3m
    simpa [z4, Sqrt512Cert.fd4_254] using h
  have hd4m : Sqrt512Cert.fd4_254 ≤ m := Nat.le_trans Sqrt512Cert.fd4_254_le_lo hlo
  have hmz5 : m ≤ z5 := by
    dsimp [z5]
    exact babylon_step_floor_bound x z4 m hz4Pos hmlo
  have hz5Pos : 0 < z5 := Nat.lt_of_lt_of_le hm hmz5
  have hd5 : z5 - m ≤ Sqrt512Cert.fd5_254 := by
    have h := SqrtCertified.step_from_bound x m Sqrt512Cert.lo254 z4
      Sqrt512Cert.fd4_254 hm Sqrt512Cert.lo254_pos hlo hmhi hmz4 hd4 hd4m
    simpa [z5, Sqrt512Cert.fd5_254] using h
  have hd5m : Sqrt512Cert.fd5_254 ≤ m := Nat.le_trans Sqrt512Cert.fd5_254_le_lo hlo
  have hmz6 : m ≤ z6 := by
    dsimp [z6]
    exact babylon_step_floor_bound x z5 m hz5Pos hmlo
  have hd6 : z6 - m ≤ Sqrt512Cert.fd6_254 := by
    have h := SqrtCertified.step_from_bound x m Sqrt512Cert.lo254 z5
      Sqrt512Cert.fd5_254 hm Sqrt512Cert.lo254_pos hlo hmhi hmz5 hd5 hd5m
    simpa [z6, Sqrt512Cert.fd6_254] using h
  simpa [SqrtCertified.run6From, z1, z2, z3, z4, z5, z6] using hd6

private theorem fixedSeed_run6_error_255
    (x m : Nat)
    (hm : 0 < m)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hlo : Sqrt512Cert.lo255 ≤ m)
    (hhi : m ≤ Sqrt512Cert.hi255) :
    SqrtCertified.run6From x Sqrt512Cert.FIXED_SEED - m ≤ Sqrt512Cert.fd6_255 := by
  let z1 := bstep x Sqrt512Cert.FIXED_SEED
  let z2 := bstep x z1
  let z3 := bstep x z2
  let z4 := bstep x z3
  let z5 := bstep x z4
  let z6 := bstep x z5
  have hs : 0 < Sqrt512Cert.FIXED_SEED := fixedSeed_pos
  have hmz1 : m ≤ z1 := by
    dsimp [z1]
    exact babylon_step_floor_bound x Sqrt512Cert.FIXED_SEED m hs hmlo
  have hz1Pos : 0 < z1 := Nat.lt_of_lt_of_le hm hmz1
  have hd1 : z1 - m ≤ Sqrt512Cert.fd1_255 := by
    have h := SqrtBridge.d1_bound x m Sqrt512Cert.FIXED_SEED Sqrt512Cert.lo255
      Sqrt512Cert.hi255 hs hmlo hmhi hlo hhi
    simpa [z1, Sqrt512Cert.fd1_255, Sqrt512Cert.maxAbs255] using h
  have hd1m : Sqrt512Cert.fd1_255 ≤ m := Nat.le_trans Sqrt512Cert.fd1_255_le_lo hlo
  have hmz2 : m ≤ z2 := by
    dsimp [z2]
    exact babylon_step_floor_bound x z1 m hz1Pos hmlo
  have hz2Pos : 0 < z2 := Nat.lt_of_lt_of_le hm hmz2
  have hd2 : z2 - m ≤ Sqrt512Cert.fd2_255 := by
    have h := SqrtCertified.step_from_bound x m Sqrt512Cert.lo255 z1
      Sqrt512Cert.fd1_255 hm Sqrt512Cert.lo255_pos hlo hmhi hmz1 hd1 hd1m
    simpa [z2, Sqrt512Cert.fd2_255] using h
  have hd2m : Sqrt512Cert.fd2_255 ≤ m := Nat.le_trans Sqrt512Cert.fd2_255_le_lo hlo
  have hmz3 : m ≤ z3 := by
    dsimp [z3]
    exact babylon_step_floor_bound x z2 m hz2Pos hmlo
  have hz3Pos : 0 < z3 := Nat.lt_of_lt_of_le hm hmz3
  have hd3 : z3 - m ≤ Sqrt512Cert.fd3_255 := by
    have h := SqrtCertified.step_from_bound x m Sqrt512Cert.lo255 z2
      Sqrt512Cert.fd2_255 hm Sqrt512Cert.lo255_pos hlo hmhi hmz2 hd2 hd2m
    simpa [z3, Sqrt512Cert.fd3_255] using h
  have hd3m : Sqrt512Cert.fd3_255 ≤ m := Nat.le_trans Sqrt512Cert.fd3_255_le_lo hlo
  have hmz4 : m ≤ z4 := by
    dsimp [z4]
    exact babylon_step_floor_bound x z3 m hz3Pos hmlo
  have hz4Pos : 0 < z4 := Nat.lt_of_lt_of_le hm hmz4
  have hd4 : z4 - m ≤ Sqrt512Cert.fd4_255 := by
    have h := SqrtCertified.step_from_bound x m Sqrt512Cert.lo255 z3
      Sqrt512Cert.fd3_255 hm Sqrt512Cert.lo255_pos hlo hmhi hmz3 hd3 hd3m
    simpa [z4, Sqrt512Cert.fd4_255] using h
  have hd4m : Sqrt512Cert.fd4_255 ≤ m := Nat.le_trans Sqrt512Cert.fd4_255_le_lo hlo
  have hmz5 : m ≤ z5 := by
    dsimp [z5]
    exact babylon_step_floor_bound x z4 m hz4Pos hmlo
  have hz5Pos : 0 < z5 := Nat.lt_of_lt_of_le hm hmz5
  have hd5 : z5 - m ≤ Sqrt512Cert.fd5_255 := by
    have h := SqrtCertified.step_from_bound x m Sqrt512Cert.lo255 z4
      Sqrt512Cert.fd4_255 hm Sqrt512Cert.lo255_pos hlo hmhi hmz4 hd4 hd4m
    simpa [z5, Sqrt512Cert.fd5_255] using h
  have hd5m : Sqrt512Cert.fd5_255 ≤ m := Nat.le_trans Sqrt512Cert.fd5_255_le_lo hlo
  have hmz6 : m ≤ z6 := by
    dsimp [z6]
    exact babylon_step_floor_bound x z5 m hz5Pos hmlo
  have hd6 : z6 - m ≤ Sqrt512Cert.fd6_255 := by
    have h := SqrtCertified.step_from_bound x m Sqrt512Cert.lo255 z5
      Sqrt512Cert.fd5_255 hm Sqrt512Cert.lo255_pos hlo hmhi hmz5 hd5 hd5m
    simpa [z6, Sqrt512Cert.fd6_255] using h
  simpa [SqrtCertified.run6From, z1, z2, z3, z4, z5, z6] using hd6

private theorem fixedSeed_run6_lower (x m : Nat)
    (hm : 0 < m)
    (hmlo : m * m ≤ x) :
    m ≤ SqrtCertified.run6From x Sqrt512Cert.FIXED_SEED := by
  let z1 := bstep x Sqrt512Cert.FIXED_SEED
  let z2 := bstep x z1
  let z3 := bstep x z2
  let z4 := bstep x z3
  let z5 := bstep x z4
  let z6 := bstep x z5
  have hs : 0 < Sqrt512Cert.FIXED_SEED := fixedSeed_pos
  have hmz1 : m ≤ z1 := by
    dsimp [z1]
    exact babylon_step_floor_bound x Sqrt512Cert.FIXED_SEED m hs hmlo
  have hz1 : 0 < z1 := Nat.lt_of_lt_of_le hm hmz1
  have hmz2 : m ≤ z2 := by
    dsimp [z2]
    exact babylon_step_floor_bound x z1 m hz1 hmlo
  have hz2 : 0 < z2 := Nat.lt_of_lt_of_le hm hmz2
  have hmz3 : m ≤ z3 := by
    dsimp [z3]
    exact babylon_step_floor_bound x z2 m hz2 hmlo
  have hz3 : 0 < z3 := Nat.lt_of_lt_of_le hm hmz3
  have hmz4 : m ≤ z4 := by
    dsimp [z4]
    exact babylon_step_floor_bound x z3 m hz3 hmlo
  have hz4 : 0 < z4 := Nat.lt_of_lt_of_le hm hmz4
  have hmz5 : m ≤ z5 := by
    dsimp [z5]
    exact babylon_step_floor_bound x z4 m hz4 hmlo
  have hz5 : 0 < z5 := Nat.lt_of_lt_of_le hm hmz5
  have hmz6 : m ≤ z6 := by
    dsimp [z6]
    exact babylon_step_floor_bound x z5 m hz5 hmlo
  simpa [SqrtCertified.run6From, z1, z2, z3, z4, z5, z6] using hmz6

private theorem fixedSeed_run6_bracket
    (x : Nat) (hlo : 2 ^ 254 ≤ x) (hhi : x < 2 ^ 256) :
    natSqrt x ≤ SqrtCertified.run6From x Sqrt512Cert.FIXED_SEED ∧
      SqrtCertified.run6From x Sqrt512Cert.FIXED_SEED ≤ natSqrt x + 1 := by
  let m := natSqrt x
  have hmlo : m * m ≤ x := by simpa [m] using natSqrt_sq_le x
  have hmhi : x < (m + 1) * (m + 1) := by simpa [m] using natSqrt_lt_succ_sq x
  have hm : 0 < m := by
    by_cases hm0 : m = 0
    · have hx1 : 1 ≤ x := Nat.le_trans (by decide : (1 : Nat) ≤ 2 ^ 254) hlo
      have hlt1 : x < 1 := by simpa [m, hm0] using hmhi
      exact False.elim ((Nat.not_lt_of_ge hx1) hlt1)
    · exact Nat.pos_of_ne_zero hm0
  have hlower : m ≤ SqrtCertified.run6From x Sqrt512Cert.FIXED_SEED :=
    fixedSeed_run6_lower x m hm hmlo
  have hupper : SqrtCertified.run6From x Sqrt512Cert.FIXED_SEED ≤ m + 1 := by
    by_cases hx255 : x < 2 ^ 255
    · let i : Fin 256 := ⟨254, by omega⟩
      have hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1) := by
        simpa [i] using And.intro hlo hx255
      have hinterval : SqrtCert.loOf i ≤ m ∧ m ≤ SqrtCert.hiOf i :=
        m_within_cert_interval i x m hmlo hmhi hOct
      have herr := fixedSeed_run6_error_254 x m hm hmlo hmhi
        (by simpa [Sqrt512Cert.lo254, i] using hinterval.1)
        (by simpa [Sqrt512Cert.hi254, i] using hinterval.2)
      have hsub : SqrtCertified.run6From x Sqrt512Cert.FIXED_SEED - m ≤ 1 :=
        Nat.le_trans herr Sqrt512Cert.fd6_254_le_one
      omega
    · let i : Fin 256 := ⟨255, by omega⟩
      have hx255le : 2 ^ 255 ≤ x := Nat.le_of_not_gt hx255
      have hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1) := by
        simpa [i] using And.intro hx255le hhi
      have hinterval : SqrtCert.loOf i ≤ m ∧ m ≤ SqrtCert.hiOf i :=
        m_within_cert_interval i x m hmlo hmhi hOct
      have herr := fixedSeed_run6_error_255 x m hm hmlo hmhi
        (by simpa [Sqrt512Cert.lo255, i] using hinterval.1)
        (by simpa [Sqrt512Cert.hi255, i] using hinterval.2)
      have hsub : SqrtCertified.run6From x Sqrt512Cert.FIXED_SEED - m ≤ 1 :=
        Nat.le_trans herr Sqrt512Cert.fd6_255_le_one
      omega
  exact ⟨hlower, hupper⟩

private theorem fixedSeed_corrected_eq_natSqrt
    (x : Nat) (hlo : 2 ^ 254 ≤ x) (hhi : x < 2 ^ 256) :
    let z := SqrtCertified.run6From x Sqrt512Cert.FIXED_SEED
    (if x / z < z then z - 1 else z) = natSqrt x := by
  intro z
  have hbracket := fixedSeed_run6_bracket x hlo hhi
  have hzpos : 0 < z := by
    dsimp [z]
    have hmpos : 0 < natSqrt x := by
      by_cases hm0 : natSqrt x = 0
      · have hx1 : 1 ≤ x := Nat.le_trans (by decide : (1 : Nat) ≤ 2 ^ 254) hlo
        have hlt1 : x < 1 := by simpa [hm0] using natSqrt_lt_succ_sq x
        exact False.elim ((Nat.not_lt_of_ge hx1) hlt1)
      · exact Nat.pos_of_ne_zero hm0
    exact Nat.lt_of_lt_of_le hmpos hbracket.1
  have hcorr := correction_correct x z (by simpa [z] using hbracket.1) (by simpa [z] using hbracket.2)
  simpa [Nat.div_lt_iff_lt_mul hzpos] using hcorr

private theorem sqrtBaseCaseStepEvm_eq_bstep
    (x z : Nat) (hlo : 2 ^ 254 ≤ x) (hhi : x < 2 ^ 256)
    (hzlo : 2 ^ 127 ≤ z) (hzhi : z < 2 ^ 129) :
    sqrtBaseCaseStepEvm x z = bstep x z ∧
      2 ^ 127 ≤ bstep x z ∧ bstep x z < 2 ^ 129 := by
  have hxW : x < FormalYul.WORD_MOD := by
    simpa [FormalYul.WORD_MOD] using hhi
  have hzW : z < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    omega
  have hzPos : 0 < z := by omega
  have hdiv129 : x / z < 2 ^ 129 := by
    rw [Nat.div_lt_iff_lt_mul hzPos]
    calc
      x < 2 ^ 256 := hhi
      _ = 2 ^ 129 * 2 ^ 127 := by rw [← Nat.pow_add]
      _ ≤ 2 ^ 129 * z := Nat.mul_le_mul_left _ hzlo
  have hdivW : x / z < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    omega
  have hsumW : x / z + z < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    omega
  have heq : sqrtBaseCaseStepEvm x z = bstep x z := by
    unfold sqrtBaseCaseStepEvm bstep
    rw [evmDiv_eq_of_lt x z hxW hzPos hzW]
    rw [evmAdd_eq_of_lt (x / z) z hdivW hzW hsumW]
    rw [evmShr_eq_of_lt 1 (x / z + z) (by decide) hsumW, Nat.pow_one]
    rw [Nat.add_comm]
  refine ⟨heq, ?_, ?_⟩
  · unfold bstep
    have hsquare : (2 ^ 127) * (2 ^ 127) ≤ x := by
      rw [← Nat.pow_add]
      simpa using hlo
    exact babylon_step_floor_bound x z (2 ^ 127) hzPos hsquare
  · unfold bstep
    have hsum : z + x / z < 2 ^ 130 := by omega
    rw [Nat.div_lt_iff_lt_mul (by decide : (0 : Nat) < 2)]
    calc
      z + x / z < 2 ^ 130 := hsum
      _ = 2 ^ 129 * 2 := by
        rw [show (130 : Nat) = 129 + 1 by omega, Nat.pow_add]

private theorem natSqrt_lt_2_128_of_lt_2_256 (x : Nat) (hhi : x < 2 ^ 256) :
    natSqrt x < 2 ^ 128 := by
  by_contra hnot
  have hle : 2 ^ 128 ≤ natSqrt x := Nat.le_of_not_gt hnot
  have hsquare := natSqrt_sq_le x
  have hge : 2 ^ 256 ≤ x := by
    calc
      2 ^ 256 = 2 ^ 128 * 2 ^ 128 := by rw [← Nat.pow_add]
      _ ≤ natSqrt x * natSqrt x := Nat.mul_le_mul hle hle
      _ ≤ x := hsquare
  exact (not_le_of_gt hhi) hge

private theorem natSqrt_ge_2_127_of_ge_2_254 (x : Nat) (hlo : 2 ^ 254 ≤ x) :
    2 ^ 127 ≤ natSqrt x := by
  by_contra hnot
  have hlt : natSqrt x < 2 ^ 127 := Nat.lt_of_not_ge hnot
  have hsucc : natSqrt x + 1 ≤ 2 ^ 127 := hlt
  have hsquare := Nat.mul_le_mul hsucc hsucc
  have hupper := natSqrt_lt_succ_sq x
  have hpow : (2 : Nat) ^ 127 * 2 ^ 127 = 2 ^ 254 := by
    rw [← Nat.pow_add]
  omega

private theorem sqrtBaseCaseEvm_correct
    (x : Nat) (hlo : 2 ^ 254 ≤ x) (hhi : x < 2 ^ 256) :
    (sqrtBaseCaseEvm x).1 = natSqrt x ∧
      (sqrtBaseCaseEvm x).2 = x - natSqrt x * natSqrt x := by
  let z1 := bstep x Sqrt512Cert.FIXED_SEED
  let z2 := bstep x z1
  let z3 := bstep x z2
  let z4 := bstep x z3
  let z5 := bstep x z4
  let z6 := bstep x z5
  have hseedLo : 2 ^ 127 ≤ Sqrt512Cert.FIXED_SEED := by
    unfold Sqrt512Cert.FIXED_SEED
    norm_num
  have hseedHi : Sqrt512Cert.FIXED_SEED < 2 ^ 129 := by
    unfold Sqrt512Cert.FIXED_SEED
    norm_num
  have h1 := sqrtBaseCaseStepEvm_eq_bstep x Sqrt512Cert.FIXED_SEED hlo hhi hseedLo hseedHi
  have h2 := sqrtBaseCaseStepEvm_eq_bstep x z1 hlo hhi h1.2.1 h1.2.2
  have h3 := sqrtBaseCaseStepEvm_eq_bstep x z2 hlo hhi h2.2.1 h2.2.2
  have h4 := sqrtBaseCaseStepEvm_eq_bstep x z3 hlo hhi h3.2.1 h3.2.2
  have h5 := sqrtBaseCaseStepEvm_eq_bstep x z4 hlo hhi h4.2.1 h4.2.2
  have h6 := sqrtBaseCaseStepEvm_eq_bstep x z5 hlo hhi h5.2.1 h5.2.2
  have hz6_run : z6 = SqrtCertified.run6From x Sqrt512Cert.FIXED_SEED := by
    simp [z1, z2, z3, z4, z5, z6, SqrtCertified.run6From]
  have hz6W : z6 < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    omega
  have hz6Pos : 0 < z6 := by omega
  have hxW : x < FormalYul.WORD_MOD := by
    simpa [FormalYul.WORD_MOD] using hhi
  have hdivEq : FormalYul.evmDiv x z6 = x / z6 := by
    exact evmDiv_eq_of_lt x z6 hxW hz6Pos hz6W
  have hdivW : x / z6 < FormalYul.WORD_MOD :=
    Nat.lt_of_le_of_lt (Nat.div_le_self x z6) hxW
  have hltEq :
      FormalYul.evmLt (FormalYul.evmDiv x z6) z6 =
        if x / z6 < z6 then 1 else 0 := by
    rw [hdivEq]
    exact evmLt_eq_of_lt (x / z6) z6 hdivW hz6W
  have hsubEq :
      FormalYul.evmSub z6 (FormalYul.evmLt (FormalYul.evmDiv x z6) z6) =
        if x / z6 < z6 then z6 - 1 else z6 := by
    rw [hltEq]
    by_cases hlt : x / z6 < z6
    · simp [hlt]
      exact evmSub_eq_of_le z6 1 hz6W (by omega)
    · simp [hlt]
      exact evmSub_eq_of_le z6 0 hz6W (Nat.zero_le z6)
  have hcorr : (if x / z6 < z6 then z6 - 1 else z6) = natSqrt x := by
    rw [hz6_run]
    exact fixedSeed_corrected_eq_natSqrt x hlo hhi
  have hr : FormalYul.evmSub z6 (FormalYul.evmLt (FormalYul.evmDiv x z6) z6) = natSqrt x := by
    rw [hsubEq, hcorr]
  have hsqrtW : natSqrt x < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    have := natSqrt_lt_2_128_of_lt_2_256 x hhi
    omega
  have hsqrtSqLt : natSqrt x * natSqrt x < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    have hlt := natSqrt_lt_2_128_of_lt_2_256 x hhi
    calc
      natSqrt x * natSqrt x < 2 ^ 128 * 2 ^ 128 :=
        Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hlt) hlt (by omega)
      _ = 2 ^ 256 := by rw [← Nat.pow_add]
  have hmul :
      FormalYul.evmMul
        (FormalYul.evmSub z6 (FormalYul.evmLt (FormalYul.evmDiv x z6) z6))
        (FormalYul.evmSub z6 (FormalYul.evmLt (FormalYul.evmDiv x z6) z6)) =
        natSqrt x * natSqrt x := by
    rw [hr, evmMul_eq_mod_of_lt (natSqrt x) (natSqrt x) hsqrtW hsqrtW,
      Nat.mod_eq_of_lt hsqrtSqLt]
  have hres :
      FormalYul.evmSub x
        (FormalYul.evmMul
          (FormalYul.evmSub z6 (FormalYul.evmLt (FormalYul.evmDiv x z6) z6))
          (FormalYul.evmSub z6 (FormalYul.evmLt (FormalYul.evmDiv x z6) z6))) =
        x - natSqrt x * natSqrt x := by
    rw [hmul]
    exact evmSub_eq_of_le x (natSqrt x * natSqrt x) hxW (natSqrt_sq_le x)
  have hstep1 : sqrtBaseCaseStepEvm x Sqrt512Cert.FIXED_SEED = z1 := by
    simpa [z1] using h1.1
  have hstep2 : sqrtBaseCaseStepEvm x z1 = z2 := by
    simpa [z2] using h2.1
  have hstep3 : sqrtBaseCaseStepEvm x z2 = z3 := by
    simpa [z3] using h3.1
  have hstep4 : sqrtBaseCaseStepEvm x z3 = z4 := by
    simpa [z4] using h4.1
  have hstep5 : sqrtBaseCaseStepEvm x z4 = z5 := by
    simpa [z5] using h5.1
  have hstep6 : sqrtBaseCaseStepEvm x z5 = z6 := by
    simpa [z6] using h6.1
  constructor
  · simp [sqrtBaseCaseEvm, hstep1, hstep2, hstep3, hstep4, hstep5, hstep6, hr]
  · simp [sqrtBaseCaseEvm, hstep1, hstep2, hstep3, hstep4, hstep5, hstep6, hres]

private theorem karatsubaQuotientEvm_correct
    (res xLo rHi : Nat)
    (hres : res ≤ 2 * rHi)
    (hxlo : xLo < 2 ^ 256) (hrhi_lo : 2 ^ 127 ≤ rHi) (hrhi_hi : rHi < 2 ^ 128)
    (hres_lt : res < 2 ^ 256) :
    let nFull := res * 2 ^ 128 + xLo / 2 ^ 128
    let d := 2 * rHi
    let nEvm := FormalYul.evmOr (FormalYul.evmShl 128 res) (FormalYul.evmShr 128 xLo)
    let dEvm := FormalYul.evmShl 1 rHi
    let q0 := FormalYul.evmDiv nEvm dEvm
    let rem0 := FormalYul.evmMod nEvm dEvm
    let c := FormalYul.evmShr 128 res
    let q1 := FormalYul.evmAdd q0 (FormalYul.evmDiv (FormalYul.evmNot 0) dEvm)
    let rem1 := FormalYul.evmAdd rem0
      (FormalYul.evmAdd 1 (FormalYul.evmMod (FormalYul.evmNot 0) dEvm))
    let q2 := FormalYul.evmAdd q1 (FormalYul.evmDiv rem1 dEvm)
    let rem2 := FormalYul.evmMod rem1 dEvm
    let out : Nat × Nat := if c = 0 then (q0, rem0) else (q2, rem2)
    out.1 = nFull / d % FormalYul.WORD_MOD ∧
      out.2 = nFull % d % FormalYul.WORD_MOD := by
  intro nFull d nEvm dEvm q0 rem0 c q1 rem1 q2 rem2 out
  have hres_wm : res < FormalYul.WORD_MOD := by
    simpa [FormalYul.WORD_MOD] using hres_lt
  have hxlo_wm : xLo < FormalYul.WORD_MOD := by
    simpa [FormalYul.WORD_MOD] using hxlo
  have hrhi_wm : rHi < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    omega
  have hd_pos : 0 < d := by
    dsimp [d]
    omega
  have hd_ge : 2 ^ 128 ≤ d := by
    dsimp [d]
    omega
  have hd_wm : d < FormalYul.WORD_MOD := by
    dsimp [d]
    unfold FormalYul.WORD_MOD
    omega
  have h_wm_sq : FormalYul.WORD_MOD = 2 ^ 128 * 2 ^ 128 := by
    unfold FormalYul.WORD_MOD
    rw [← Nat.pow_add]
  have hxlo_hi : xLo / 2 ^ 128 < 2 ^ 128 :=
    Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hxlo)
  have hn_evm_lt : (res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128 < FormalYul.WORD_MOD := by
    have := Nat.mod_lt res (Nat.two_pow_pos 128)
    rw [h_wm_sq]
    omega
  have hd_eq : dEvm = d := by
    dsimp [dEvm, d]
    rw [evmShl_eq_of_lt 1 rHi (by omega) hrhi_wm, Nat.pow_one, Nat.mul_comm]
    exact Nat.mod_eq_of_lt (by unfold FormalYul.WORD_MOD; omega)
  have hshl_res : FormalYul.evmShl 128 res = (res % 2 ^ 128) * 2 ^ 128 := by
    rw [evmShl_eq_of_lt 128 res (by omega) hres_wm]
    exact mul_pow128_mod_word res
  have hshr_xlo : FormalYul.evmShr 128 xLo = xLo / 2 ^ 128 :=
    evmShr_eq_of_lt 128 xLo (by omega) hxlo_wm
  have hshl_wm : (res % 2 ^ 128) * 2 ^ 128 < FormalYul.WORD_MOD := by
    have := Nat.mod_lt res (Nat.two_pow_pos 128)
    rw [h_wm_sq]
    exact Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos 128)
  have hshr_wm : xLo / 2 ^ 128 < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    omega
  have hn_eq : nEvm = (res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128 := by
    dsimp [nEvm]
    rw [hshl_res, hshr_xlo, evmOr_eq_of_lt _ _ hshl_wm hshr_wm]
    exact or_eq_add_shl (res % 2 ^ 128) (xLo / 2 ^ 128) 128 hxlo_hi
  have hc_eq : c = res / 2 ^ 128 := by
    dsimp [c]
    exact evmShr_eq_of_lt 128 res (by omega) hres_wm
  by_cases hc_zero : c = 0
  · have hc_zero_nat : res / 2 ^ 128 = 0 := by
      rwa [hc_eq] at hc_zero
    have hres_128 : res < 2 ^ 128 := by
      by_contra hnot
      have hge : 2 ^ 128 ≤ res := Nat.le_of_not_gt hnot
      have hpos : 0 < res / 2 ^ 128 := Nat.div_pos hge (Nat.two_pow_pos 128)
      omega
    have hmod_res : res % 2 ^ 128 = res := Nat.mod_eq_of_lt hres_128
    have hn_or : nEvm = nFull := by
      rw [hn_eq, hmod_res]
    have hn_full_wm : nFull < FormalYul.WORD_MOD := by
      rw [← hn_or, hn_eq]
      exact hn_evm_lt
    have hq0 : q0 = nFull / d := by
      dsimp [q0]
      rw [hn_or, hd_eq]
      exact evmDiv_eq_of_lt nFull d hn_full_wm hd_pos hd_wm
    have hrem0 : rem0 = nFull % d := by
      dsimp [rem0]
      rw [hn_or, hd_eq]
      exact evmMod_eq_of_lt nFull d hn_full_wm hd_pos hd_wm
    simp [out, hc_zero, hq0, hrem0,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self nFull d) hn_full_wm),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt nFull hd_pos)
        (Nat.le_of_lt hd_wm))]
  · have hc_ne_nat : res / 2 ^ 128 ≠ 0 := by
      intro h
      apply hc_zero
      rw [hc_eq, h]
    have hn_div_evm : FormalYul.evmDiv nEvm dEvm =
        ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) / d := by
      rw [hn_eq, hd_eq]
      exact evmDiv_eq_of_lt _ d hn_evm_lt hd_pos hd_wm
    have hn_mod_evm : FormalYul.evmMod nEvm dEvm =
        ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d := by
      rw [hn_eq, hd_eq]
      exact evmMod_eq_of_lt _ d hn_evm_lt hd_pos hd_wm
    have hnot_zero : FormalYul.evmNot 0 = FormalYul.WORD_MOD - 1 := by
      exact evmNot_eq_of_lt 0 (by unfold FormalYul.WORD_MOD; omega)
    have hnot_wm : FormalYul.WORD_MOD - 1 < FormalYul.WORD_MOD := by
      unfold FormalYul.WORD_MOD
      omega
    have hwm_div : FormalYul.evmDiv (FormalYul.evmNot 0) dEvm =
        (FormalYul.WORD_MOD - 1) / d := by
      rw [hnot_zero, hd_eq]
      exact evmDiv_eq_of_lt _ d hnot_wm hd_pos hd_wm
    have hwm_mod : FormalYul.evmMod (FormalYul.evmNot 0) dEvm =
        (FormalYul.WORD_MOD - 1) % d := by
      rw [hnot_zero, hd_eq]
      exact evmMod_eq_of_lt _ d hnot_wm hd_pos hd_wm
    have hrw_lt : (FormalYul.WORD_MOD - 1) % d < d := Nat.mod_lt _ hd_pos
    have hrw_wm : (FormalYul.WORD_MOD - 1) % d < FormalYul.WORD_MOD :=
      Nat.lt_of_lt_of_le hrw_lt (Nat.le_of_lt hd_wm)
    have h1_wm : (1 : Nat) < FormalYul.WORD_MOD := by
      unfold FormalYul.WORD_MOD
      omega
    have h1rw_sum : 1 + (FormalYul.WORD_MOD - 1) % d < FormalYul.WORD_MOD :=
      Nat.lt_of_le_of_lt (by omega : 1 + (FormalYul.WORD_MOD - 1) % d ≤ d)
        hd_wm
    have hadd_1_rw :
        FormalYul.evmAdd 1 ((FormalYul.WORD_MOD - 1) % d) =
          1 + (FormalYul.WORD_MOD - 1) % d :=
      evmAdd_eq_of_lt 1 _ h1_wm hrw_wm h1rw_sum
    have hr0_lt : ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d < d :=
      Nat.mod_lt _ hd_pos
    have hr0_wm :
        ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d < FormalYul.WORD_MOD :=
      Nat.lt_of_lt_of_le hr0_lt (Nat.le_of_lt hd_wm)
    have hR_sum : ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
        (1 + (FormalYul.WORD_MOD - 1) % d) < FormalYul.WORD_MOD :=
      Nat.lt_of_lt_of_le (by omega : _ < 2 * d) (by unfold FormalYul.WORD_MOD; omega)
    have hstep2 :
        FormalYul.evmAdd (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d)
          (1 + (FormalYul.WORD_MOD - 1) % d) =
        ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
          (1 + (FormalYul.WORD_MOD - 1) % d) :=
      evmAdd_eq_of_lt _ _ hr0_wm h1rw_sum hR_sum
    have hR_lt2d : ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
        (1 + (FormalYul.WORD_MOD - 1) % d) < 2 * d := by
      omega
    have hdiv_R :
        FormalYul.evmDiv (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
          (1 + (FormalYul.WORD_MOD - 1) % d)) d =
        (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
          (1 + (FormalYul.WORD_MOD - 1) % d)) / d :=
      evmDiv_eq_of_lt _ d hR_sum hd_pos hd_wm
    have hmod_R :
        FormalYul.evmMod (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
          (1 + (FormalYul.WORD_MOD - 1) % d)) d =
        (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
          (1 + (FormalYul.WORD_MOD - 1) % d)) % d :=
      evmMod_eq_of_lt _ d hR_sum hd_pos hd_wm
    have hq0_wm : ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) / d <
        FormalYul.WORD_MOD :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn_evm_lt
    have hqw_wm : (FormalYul.WORD_MOD - 1) / d < FormalYul.WORD_MOD :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hnot_wm
    have hq0_128 : ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) / d < 2 ^ 128 :=
      (Nat.div_lt_iff_lt_mul hd_pos).mpr (Nat.lt_of_lt_of_le hn_evm_lt
        (by rw [h_wm_sq]; exact Nat.mul_le_mul_left _ hd_ge))
    have hqw_128 : (FormalYul.WORD_MOD - 1) / d < 2 ^ 128 :=
      (Nat.div_lt_iff_lt_mul hd_pos).mpr (Nat.lt_of_lt_of_le hnot_wm
        (by rw [h_wm_sq]; exact Nat.mul_le_mul_left _ hd_ge))
    have hq0qw_sum : ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) / d +
        (FormalYul.WORD_MOD - 1) / d < FormalYul.WORD_MOD :=
      Nat.lt_of_lt_of_le (by omega : _ < 2 ^ 129)
        (by unfold FormalYul.WORD_MOD; omega)
    have hstep1 :
        FormalYul.evmAdd (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) / d)
          ((FormalYul.WORD_MOD - 1) / d) =
        ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) / d +
          (FormalYul.WORD_MOD - 1) / d :=
      evmAdd_eq_of_lt _ _ hq0_wm hqw_wm hq0qw_sum
    have hR_div_le1 :
        (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
          (1 + (FormalYul.WORD_MOD - 1) % d)) / d ≤ 1 :=
      Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hd_pos).mpr hR_lt2d)
    have hR_div_wm :
        (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
          (1 + (FormalYul.WORD_MOD - 1) % d)) / d < FormalYul.WORD_MOD :=
      Nat.lt_of_le_of_lt hR_div_le1 (by unfold FormalYul.WORD_MOD; omega)
    have hfinal_sum : ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) / d +
        (FormalYul.WORD_MOD - 1) / d +
          (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
            (1 + (FormalYul.WORD_MOD - 1) % d)) / d < FormalYul.WORD_MOD :=
      Nat.lt_of_lt_of_le (by omega : _ < 2 ^ 129 + 1)
        (by unfold FormalYul.WORD_MOD; omega)
    have hstep3 :
        FormalYul.evmAdd
          (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) / d +
            (FormalYul.WORD_MOD - 1) / d)
          ((((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
            (1 + (FormalYul.WORD_MOD - 1) % d)) / d) =
        ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) / d +
          (FormalYul.WORD_MOD - 1) / d +
            (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
              (1 + (FormalYul.WORD_MOD - 1) % d)) / d :=
      evmAdd_eq_of_lt _ _ hq0qw_sum hR_div_wm hfinal_sum
    have hc_one : res / 2 ^ 128 = 1 := by
      have hc_pos : 0 < res / 2 ^ 128 := Nat.pos_of_ne_zero hc_ne_nat
      have hc_le : res / 2 ^ 128 ≤ 1 := by
        have : res / 2 ^ 128 < 2 :=
          (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 128)).mpr (by omega)
        omega
      omega
    have hn_full_eq :
        nFull = (res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128 + FormalYul.WORD_MOD := by
      dsimp [nFull]
      have h := Nat.div_add_mod res (2 ^ 128)
      rw [hc_one] at h
      rw [h_wm_sq]
      omega
    have hn_full_decomp :
        nFull =
          d * (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) / d +
            (FormalYul.WORD_MOD - 1) / d) +
          (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
            (1 + (FormalYul.WORD_MOD - 1) % d)) := by
      rw [hn_full_eq]
      have h1 := (Nat.div_add_mod ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) d).symm
      have h2 := (Nat.div_add_mod (FormalYul.WORD_MOD - 1) d).symm
      rw [Nat.mul_add]
      omega
    have hn_div_nat : nFull / d =
        ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) / d +
          (FormalYul.WORD_MOD - 1) / d +
            (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
              (1 + (FormalYul.WORD_MOD - 1) % d)) / d := by
      rw [hn_full_decomp]
      exact div_of_mul_add d _ _ hd_pos
    have hn_mod_nat : nFull % d =
        (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
          (1 + (FormalYul.WORD_MOD - 1) % d)) % d := by
      rw [hn_full_decomp]
      exact mod_of_mul_add d _ _
    have hn_full_mod_wm : nFull % d < FormalYul.WORD_MOD :=
      Nat.lt_of_lt_of_le (Nat.mod_lt nFull hd_pos) (Nat.le_of_lt hd_wm)
    have hq0_def : q0 = ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) / d := by
      dsimp [q0]
      exact hn_div_evm
    have hrem0_def : rem0 = ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d := by
      dsimp [rem0]
      exact hn_mod_evm
    have hq1_def :
        q1 = ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) / d +
          (FormalYul.WORD_MOD - 1) / d := by
      dsimp [q1]
      rw [hq0_def, hwm_div]
      exact hstep1
    have hrem1_def :
        rem1 = ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
          (1 + (FormalYul.WORD_MOD - 1) % d) := by
      dsimp [rem1]
      rw [hrem0_def, hwm_mod, hadd_1_rw]
      exact hstep2
    have hq2_def :
        q2 = ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) / d +
          (FormalYul.WORD_MOD - 1) / d +
            (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
              (1 + (FormalYul.WORD_MOD - 1) % d)) / d := by
      dsimp [q2]
      rw [hq1_def, hrem1_def, hd_eq, hdiv_R]
      exact hstep3
    have hrem2_def :
        rem2 = (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
          (1 + (FormalYul.WORD_MOD - 1) % d)) % d := by
      dsimp [rem2]
      rw [hrem1_def, hd_eq]
      exact hmod_R
    have hmod_q : nFull / d % FormalYul.WORD_MOD = nFull / d := by
      rw [hn_div_nat]
      exact Nat.mod_eq_of_lt hfinal_sum
    have hrem2_wm :
        (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
          (1 + (FormalYul.WORD_MOD - 1) % d)) % d < FormalYul.WORD_MOD :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ hd_pos) (Nat.le_of_lt hd_wm)
    simp [out, hc_zero, hq2_def, hrem2_def]
    constructor
    · rw [hn_div_nat]
      exact (Nat.mod_eq_of_lt hfinal_sum).symm
    · rw [hn_mod_nat]
      have hrem_norm :
          (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) +
              (1 + (FormalYul.WORD_MOD - 1) % d)) % d =
            (((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) % d +
              (1 + (FormalYul.WORD_MOD - 1) % d)) % d :=
        (Nat.mod_add_mod ((res % 2 ^ 128) * 2 ^ 128 + xLo / 2 ^ 128) d
          (1 + (FormalYul.WORD_MOD - 1) % d)).symm
      exact hrem_norm.trans (Nat.mod_eq_of_lt hrem2_wm).symm

private theorem sqrtCorrectionEvm_correct
    (rHi rLo rem xLo : Nat)
    (hrhi_lo : 2 ^ 127 ≤ rHi) (hrhi_hi : rHi < 2 ^ 128)
    (hrlo_le : rLo ≤ 2 ^ 128) (hrem : rem < 2 * rHi)
    (hxlo : xLo < 2 ^ 256)
    (hedge : rLo = 2 ^ 128 → rem < 2 ^ 128) :
    let r := FormalYul.evmAdd (FormalYul.evmShl 128 rHi) rLo
    let hiRem := FormalYul.evmShr 128 rem
    let hiRLo := FormalYul.evmShr 128 rLo
    let loRem := FormalYul.evmOr (FormalYul.evmShl 128 rem)
      (FormalYul.evmAnd xLo 340282366920938463463374607431768211455)
    let loSq := FormalYul.evmMul rLo rLo
    let dec := FormalYul.evmOr (FormalYul.evmLt hiRem hiRLo)
      (FormalYul.evmAnd (FormalYul.evmEq hiRem hiRLo) (FormalYul.evmLt loRem loSq))
    FormalYul.evmSub r dec =
      rHi * 2 ^ 128 + rLo -
        (if rem * 2 ^ 128 + xLo % 2 ^ 128 < rLo * rLo then 1 else 0) := by
  intro r hiRem hiRLo loRem loSq dec
  have hrhi_wm : rHi < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    omega
  have hrlo_wm : rLo < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    omega
  have hrem_wm : rem < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    omega
  have hxlo_wm : xLo < FormalYul.WORD_MOD := by
    simpa [FormalYul.WORD_MOD] using hxlo
  have hrem_129 : rem < 2 ^ 129 := by
    omega
  have h_wm_sq : FormalYul.WORD_MOD = 2 ^ 128 * 2 ^ 128 := by
    unfold FormalYul.WORD_MOD
    rw [← Nat.pow_add]
  have hmask : (340282366920938463463374607431768211455 : Nat) = 2 ^ 128 - 1 := by
    decide
  have hshl_rhi : FormalYul.evmShl 128 rHi = rHi * 2 ^ 128 := by
    rw [evmShl_eq_of_lt 128 rHi (by omega) hrhi_wm]
    exact Nat.mod_eq_of_lt (by
      rw [h_wm_sq]
      exact Nat.mul_lt_mul_of_pos_right hrhi_hi (Nat.two_pow_pos 128))
  have hshr_rem : FormalYul.evmShr 128 rem = rem / 2 ^ 128 :=
    evmShr_eq_of_lt 128 rem (by omega) hrem_wm
  have hshr_rlo : FormalYul.evmShr 128 rLo = rLo / 2 ^ 128 :=
    evmShr_eq_of_lt 128 rLo (by omega) hrlo_wm
  have hshl_rem : FormalYul.evmShl 128 rem = (rem % 2 ^ 128) * 2 ^ 128 := by
    rw [evmShl_eq_of_lt 128 rem (by omega) hrem_wm]
    exact mul_pow128_mod_word rem
  have hand_mask : FormalYul.evmAnd xLo (2 ^ 128 - 1) = xLo % 2 ^ 128 := by
    rw [evmAnd_eq_of_lt xLo (2 ^ 128 - 1) hxlo_wm
      (by unfold FormalYul.WORD_MOD; omega)]
    exact Nat.and_two_pow_sub_one_eq_mod xLo 128
  have hshl_rem_wm : (rem % 2 ^ 128) * 2 ^ 128 < FormalYul.WORD_MOD := by
    rw [h_wm_sq]
    exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt rem (Nat.two_pow_pos 128))
      (Nat.two_pow_pos 128)
  have hxlo_mod_lt : xLo % 2 ^ 128 < 2 ^ 128 := Nat.mod_lt xLo (Nat.two_pow_pos 128)
  have hxlo_mod_wm : xLo % 2 ^ 128 < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    omega
  have hor_concat : loRem = (rem % 2 ^ 128) * 2 ^ 128 + xLo % 2 ^ 128 := by
    dsimp [loRem]
    rw [hmask, hshl_rem, hand_mask, evmOr_eq_of_lt _ _ hshl_rem_wm hxlo_mod_wm,
      or_eq_add_shl (rem % 2 ^ 128) (xLo % 2 ^ 128) 128 hxlo_mod_lt]
    rfl
  have hmul_rlo : loSq = (rLo * rLo) % FormalYul.WORD_MOD := by
    dsimp [loSq]
    exact evmMul_eq_mod_of_lt rLo rLo hrlo_wm hrlo_wm
  have hrem_hi_wm : rem / 2 ^ 128 < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    omega
  have hrlo_hi_wm : rLo / 2 ^ 128 < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    omega
  have hconcat_wm : (rem % 2 ^ 128) * 2 ^ 128 + xLo % 2 ^ 128 < FormalYul.WORD_MOD := by
    rw [h_wm_sq]
    omega
  have hmul_wm : (rLo * rLo) % FormalYul.WORD_MOD < FormalYul.WORD_MOD :=
    Nat.mod_lt _ (by unfold FormalYul.WORD_MOD; omega)
  have hlt_hi : FormalYul.evmLt hiRem hiRLo =
      if rem / 2 ^ 128 < rLo / 2 ^ 128 then 1 else 0 := by
    dsimp [hiRem, hiRLo]
    rw [hshr_rem, hshr_rlo]
    exact evmLt_eq_of_lt _ _ hrem_hi_wm hrlo_hi_wm
  have heq_hi : FormalYul.evmEq hiRem hiRLo =
      if rem / 2 ^ 128 = rLo / 2 ^ 128 then 1 else 0 := by
    dsimp [hiRem, hiRLo]
    rw [hshr_rem, hshr_rlo]
    exact evmEq_eq_of_lt _ _ hrem_hi_wm hrlo_hi_wm
  have hlt_lo : FormalYul.evmLt loRem loSq =
      if (rem % 2 ^ 128) * 2 ^ 128 + xLo % 2 ^ 128 < (rLo * rLo) % FormalYul.WORD_MOD
      then 1 else 0 := by
    rw [hor_concat, hmul_rlo]
    exact evmLt_eq_of_lt _ _ hconcat_wm hmul_wm
  have hrem_hi_le : rem / 2 ^ 128 ≤ 1 :=
    Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 128)).mpr (by omega))
  have hrlo_hi_le : rLo / 2 ^ 128 ≤ 1 := by
    have : rLo / 2 ^ 128 < 2 :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 128)).mpr (by omega)
    omega
  have hrem_hi_cases : rem / 2 ^ 128 = 0 ∨ rem / 2 ^ 128 = 1 := by
    omega
  have hrlo_hi_cases : rLo / 2 ^ 128 = 0 ∨ rLo / 2 ^ 128 = 1 := by
    omega
  dsimp [r, dec]
  rw [hshl_rhi, hlt_hi, heq_hi, hlt_lo]
  rcases hrem_hi_cases with hremh | hremh <;> rcases hrlo_hi_cases with hrloh | hrloh <;>
    rw [hremh, hrloh]
  · have h00 : (if (0 : Nat) < 0 then 1 else 0) = 0 := by
      decide
    simp only [h00, ite_true]
    have hand1 : ∀ n : Nat, n ≤ 1 → FormalYul.evmAnd 1 n = n := by
      intro n hn
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl <;> decide
    have hor0 : ∀ n : Nat, n ≤ 1 → FormalYul.evmOr 0 n = n := by
      intro n hn
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl <;> decide
    have hrem_lt : rem < 2 ^ 128 := by
      omega
    have hrem_mod : rem % 2 ^ 128 = rem := Nat.mod_eq_of_lt hrem_lt
    have hrlo_lt : rLo < 2 ^ 128 := by
      omega
    have hrlo_sq_lt : rLo * rLo < FormalYul.WORD_MOD := by
      rw [h_wm_sq]
      exact Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hrlo_lt) hrlo_lt (by omega)
    have hmod_sq : rLo * rLo % FormalYul.WORD_MOD = rLo * rLo :=
      Nat.mod_eq_of_lt hrlo_sq_lt
    rw [hrem_mod, hmod_sq]
    have hcmp_le :
        (if rem * 2 ^ 128 + xLo % 2 ^ 128 < rLo * rLo then 1 else (0 : Nat)) ≤ 1 := by
      split <;> omega
    rw [hand1 _ hcmp_le, hor0 _ hcmp_le]
    have hrhi_mul_lt : rHi * 2 ^ 128 < FormalYul.WORD_MOD := by
      rw [h_wm_sq]
      exact Nat.mul_lt_mul_of_pos_right hrhi_hi (Nat.two_pow_pos 128)
    have hadd_lt : rHi * 2 ^ 128 + rLo < FormalYul.WORD_MOD := by
      omega
    have hcmp_le_sum :
        (if rem * 2 ^ 128 + xLo % 2 ^ 128 < rLo * rLo then 1 else 0) ≤
          rHi * 2 ^ 128 + rLo := by
      split <;> omega
    rw [evmAdd_eq_of_lt _ _ hrhi_mul_lt hrlo_wm hadd_lt,
      evmSub_eq_of_le _ _ hadd_lt hcmp_le_sum]
    rfl
  · have hrlo_eq : rLo = 2 ^ 128 := by
      omega
    have h01a : (if (0 : Nat) < 1 then 1 else 0) = 1 := by
      decide
    have h01b : (if (0 : Nat) = 1 then 1 else 0) = 0 := by
      decide
    simp only [h01a, h01b]
    have hand0 : ∀ x, FormalYul.evmAnd 0 x = 0 := by
      intro x
      unfold FormalYul.evmAnd FormalYul.u256
      simp
    simp only [hand0]
    have hor10 : FormalYul.evmOr 1 0 = 1 := by
      decide
    simp only [hor10]
    have hrem_lt : rem < 2 ^ 128 := by
      omega
    have hcmp_true : rem * 2 ^ 128 + xLo % 2 ^ 128 < rLo * rLo := by
      rw [hrlo_eq, show (2 : Nat) ^ 128 * 2 ^ 128 = 2 ^ 256 from by rw [← Nat.pow_add]]
      have := Nat.mod_lt xLo (Nat.two_pow_pos 128)
      omega
    rw [if_pos (by simpa using hcmp_true)]
    rw [hrlo_eq]
    by_cases hoverflow : rHi * 2 ^ 128 + 2 ^ 128 < FormalYul.WORD_MOD
    · rw [evmAdd_eq_of_lt _ _ (by omega) (by unfold FormalYul.WORD_MOD; omega) hoverflow,
        evmSub_eq_of_le _ 1 hoverflow (by omega)]
      rfl
    · have hsum_eq : rHi * 2 ^ 128 + 2 ^ 128 = FormalYul.WORD_MOD := by
        have : rHi * 2 ^ 128 + 2 ^ 128 ≤ FormalYul.WORD_MOD := by
          rw [h_wm_sq, ← Nat.succ_mul]
          exact Nat.mul_le_mul_right _ hrhi_hi
        omega
      rw [evmSub_evmAdd_eq_of_overflow _ _ (by omega) (by unfold FormalYul.WORD_MOD; omega)
        hsum_eq]
      omega
  · have h10a : (if (1 : Nat) < 0 then 1 else 0) = 0 := by
      decide
    have h10b : (if (1 : Nat) = 0 then 1 else 0) = 0 := by
      decide
    simp only [h10a, h10b]
    have hand0 : ∀ x, FormalYul.evmAnd 0 x = 0 := by
      intro x
      unfold FormalYul.evmAnd FormalYul.u256
      simp
    simp only [hand0]
    have hor00 : FormalYul.evmOr 0 0 = 0 := by
      decide
    simp only [hor00]
    have hrlo_lt : rLo < 2 ^ 128 := by
      omega
    have hcmp_false : ¬(rem * 2 ^ 128 + xLo % 2 ^ 128 < rLo * rLo) := by
      intro hlt
      have hrem_ge : 2 ^ 128 ≤ rem := by
        by_contra hnot
        have hlt_rem : rem < 2 ^ 128 := Nat.lt_of_not_ge hnot
        have hdiv0 : rem / 2 ^ 128 = 0 := Nat.div_eq_of_lt hlt_rem
        omega
      have lhs_ge : 2 ^ 256 ≤ rem * 2 ^ 128 + xLo % 2 ^ 128 := by
        calc
          2 ^ 256 = 2 ^ 128 * 2 ^ 128 := by rw [← Nat.pow_add]
          _ ≤ rem * 2 ^ 128 := Nat.mul_le_mul_right _ hrem_ge
          _ ≤ rem * 2 ^ 128 + xLo % 2 ^ 128 := Nat.le_add_right _ _
      have rhs_lt : rLo * rLo < 2 ^ 256 := by
        calc
          rLo * rLo < 2 ^ 128 * 2 ^ 128 :=
            Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hrlo_lt) hrlo_lt (by omega)
          _ = 2 ^ 256 := by rw [← Nat.pow_add]
      exact (not_le_of_gt (Nat.lt_trans hlt rhs_lt)) lhs_ge
    rw [if_neg (by simpa using hcmp_false)]
    simp only [Nat.sub_zero]
    have hrhi_mul_lt : rHi * 2 ^ 128 < FormalYul.WORD_MOD := by
      rw [h_wm_sq]
      exact Nat.mul_lt_mul_of_pos_right hrhi_hi (Nat.two_pow_pos 128)
    have hadd_lt : rHi * 2 ^ 128 + rLo < FormalYul.WORD_MOD := by
      omega
    rw [evmAdd_eq_of_lt _ _ hrhi_mul_lt hrlo_wm hadd_lt,
      evmSub_eq_of_le _ 0 hadd_lt (Nat.zero_le _)]
    omega
  · have hrlo_eq : rLo = 2 ^ 128 := by
      omega
    have hrem_lt : rem < 2 ^ 128 := hedge hrlo_eq
    exfalso
    omega

private theorem sub_if_one_eq_if {p q : Prop} [Decidable p] [Decidable q]
    (r : Nat) (h : p ↔ q) :
    r - (if q then 1 else 0) = (if p then r - 1 else r) := by
  by_cases hp : p
  · have hq : q := h.mp hp
    simp [hp, hq]
  · have hq : ¬ q := fun hq => hp (h.mpr hq)
    simp [hp, hq]

private theorem karatsubaCorrectedNat_eq_karatsubaFloor (xHi xLo : Nat) :
    let nNat := (xHi - natSqrt xHi * natSqrt xHi) * 2 ^ 128 + xLo / 2 ^ 128
    let dNat := 2 * natSqrt xHi
    natSqrt xHi * 2 ^ 128 + nNat / dNat -
        (if nNat % dNat * 2 ^ 128 + xLo % 2 ^ 128 < (nNat / dNat) * (nNat / dNat)
          then 1 else 0) =
      karatsubaFloor xHi xLo := by
  intro nNat dNat
  have hident :
      let q := nNat / dNat
      let rem := nNat % dNat
      let rr := natSqrt xHi * 2 ^ 128 + q
      xHi * (2 ^ 128 * 2 ^ 128) + xLo / 2 ^ 128 * 2 ^ 128 + xLo % 2 ^ 128 +
        q * q = rr * rr + rem * 2 ^ 128 + xLo % 2 ^ 128 := by
    dsimp [nNat, dNat]
    exact karatsuba_identity xHi (xLo / 2 ^ 128) (xLo % 2 ^ 128)
      (natSqrt xHi) (2 ^ 128) (natSqrt_sq_le xHi)
  have hequiv := correction_equiv
    (xHi * (2 ^ 128 * 2 ^ 128) + xLo / 2 ^ 128 * 2 ^ 128 + xLo % 2 ^ 128)
    (nNat / dNat)
    (natSqrt xHi * 2 ^ 128 + nNat / dNat)
    (nNat % dNat * 2 ^ 128)
    (xLo % 2 ^ 128)
    hident
  let p := xHi * (2 ^ 128 * 2 ^ 128) + xLo / 2 ^ 128 * 2 ^ 128 + xLo % 2 ^ 128 <
    (natSqrt xHi * 2 ^ 128 + nNat / dNat) * (natSqrt xHi * 2 ^ 128 + nNat / dNat)
  let q := nNat % dNat * 2 ^ 128 + xLo % 2 ^ 128 < (nNat / dNat) * (nNat / dNat)
  let rr := natSqrt xHi * 2 ^ 128 + nNat / dNat
  have hfloor : karatsubaFloor xHi xLo = (if p then rr - 1 else rr) := by
    unfold karatsubaFloor karatsubaR
    dsimp [p, rr, nNat, dNat]
  rw [hfloor]
  exact sub_if_one_eq_if rr hequiv

private theorem sqrtCorrectionFromQuotient_eq_karatsubaFloor (xHi xLo q rem : Nat)
    (hlo : 2 ^ 254 ≤ xHi) (hhi : xHi < 2 ^ 256) (hxlo : xLo < 2 ^ 256)
    (hq : q =
      ((xHi - natSqrt xHi * natSqrt xHi) * 2 ^ 128 + xLo / 2 ^ 128) /
        (2 * natSqrt xHi))
    (hrem : rem =
      ((xHi - natSqrt xHi * natSqrt xHi) * 2 ^ 128 + xLo / 2 ^ 128) %
        (2 * natSqrt xHi)) :
    let r := FormalYul.evmAdd (FormalYul.evmShl 128 (natSqrt xHi)) q
    let hiRem := FormalYul.evmShr 128 rem
    let hiRLo := FormalYul.evmShr 128 q
    let loRem := FormalYul.evmOr (FormalYul.evmShl 128 rem)
      (FormalYul.evmAnd xLo 340282366920938463463374607431768211455)
    let loSq := FormalYul.evmMul q q
    let dec := FormalYul.evmOr (FormalYul.evmLt hiRem hiRLo)
      (FormalYul.evmAnd (FormalYul.evmEq hiRem hiRLo) (FormalYul.evmLt loRem loSq))
    FormalYul.evmSub r dec = karatsubaFloor xHi xLo := by
  intro r hiRem hiRLo loRem loSq dec
  have hrhi_lo : 2 ^ 127 ≤ natSqrt xHi := natSqrt_ge_2_127_of_ge_2_254 xHi hlo
  have hrhi_hi : natSqrt xHi < 2 ^ 128 := natSqrt_lt_2_128_of_lt_2_256 xHi hhi
  have hres_le : xHi - natSqrt xHi * natSqrt xHi ≤ 2 * natSqrt xHi := by
    have hsq := natSqrt_sq_le xHi
    have hsucc := natSqrt_lt_succ_sq xHi
    have hadd := Nat.add_mul (natSqrt xHi) 1 (natSqrt xHi + 1)
    have hmul := Nat.mul_add (natSqrt xHi) (natSqrt xHi) 1
    omega
  have hres_lt : xHi - natSqrt xHi * natSqrt xHi < 2 ^ 256 := by
    omega
  have hd_pos : 0 < 2 * natSqrt xHi := by
    omega
  let nNat := (xHi - natSqrt xHi * natSqrt xHi) * 2 ^ 128 + xLo / 2 ^ 128
  let dNat := 2 * natSqrt xHi
  have hxlo_hi : xLo / 2 ^ 128 < 2 ^ 128 :=
    Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hxlo)
  have hq_le : nNat / dNat ≤ 2 ^ 128 := by
    rw [Nat.div_le_iff_le_mul_add_pred hd_pos]
    dsimp [nNat, dNat]
    omega
  have hq_lt_word : nNat / dNat < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    omega
  have hrem_lt_word : nNat % dNat < FormalYul.WORD_MOD := by
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hd_pos)
      (by unfold dNat FormalYul.WORD_MOD; omega)
  have hedge :
      nNat / dNat = 2 ^ 128 → nNat % dNat < 2 ^ 128 := by
    intro hq_eq
    have hid := (Nat.div_add_mod nNat dNat).symm
    rw [hq_eq] at hid
    have hres_eq_d : xHi - natSqrt xHi * natSqrt xHi = 2 * natSqrt xHi := by
      dsimp [nNat, dNat] at hid
      omega
    dsimp [nNat, dNat]
    rw [hres_eq_d]
    change (2 * natSqrt xHi * 2 ^ 128 + xLo / 2 ^ 128) %
        (2 * natSqrt xHi) < 2 ^ 128
    have hcomm : 2 * natSqrt xHi * 2 ^ 128 + xLo / 2 ^ 128 =
        xLo / 2 ^ 128 + 2 ^ 128 * (2 * natSqrt xHi) := by
      omega
    rw [hcomm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (by omega : xLo / 2 ^ 128 < 2 * natSqrt xHi)]
    exact hxlo_hi
  have hcorr := sqrtCorrectionEvm_correct (natSqrt xHi) (nNat / dNat) (nNat % dNat)
    xLo hrhi_lo hrhi_hi hq_le (Nat.mod_lt _ hd_pos) hxlo hedge
  have hcorr_out :
      FormalYul.evmSub r dec =
        natSqrt xHi * 2 ^ 128 + nNat / dNat -
          (if nNat % dNat * 2 ^ 128 + xLo % 2 ^ 128 < (nNat / dNat) * (nNat / dNat)
            then 1 else 0) := by
    dsimp [r, dec, hiRem, hiRLo, loRem, loSq]
    rw [hq, hrem]
    simpa [nNat, dNat] using hcorr
  rw [hcorr_out]
  exact karatsubaCorrectedNat_eq_karatsubaFloor xHi xLo

private theorem uint512_lt_512 (xHi xLo : Nat) :
    uint512 xHi xLo < 2 ^ 512 := by
  have hxHi : FormalYul.u256 xHi < 2 ^ 256 := by
    unfold FormalYul.u256 FormalYul.WORD_MOD
    exact Nat.mod_lt xHi (Nat.two_pow_pos 256)
  have hxLo : FormalYul.u256 xLo < 2 ^ 256 := by
    unfold FormalYul.u256 FormalYul.WORD_MOD
    exact Nat.mod_lt xLo (Nat.two_pow_pos 256)
  unfold uint512
  have hmul : FormalYul.u256 xHi * 2 ^ 256 < 2 ^ 256 * 2 ^ 256 :=
    Nat.mul_lt_mul_of_pos_right hxHi (Nat.two_pow_pos 256)
  have hpow : (2 : Nat) ^ 256 * 2 ^ 256 = 2 ^ 512 := by
    rw [← Nat.pow_add]
  omega

theorem sqrt512_uint512_eq_natSqrt (xHi xLo : Nat) :
    sqrt512 (uint512 xHi xLo) = natSqrt (uint512 xHi xLo) := by
  exact sqrt512_correct (uint512 xHi xLo) (uint512_lt_512 xHi xLo)

private theorem natSqrt_uint512_lt_word (xHi xLo : Nat) :
    natSqrt (uint512 xHi xLo) < FormalYul.WORD_MOD := by
  rw [FormalYul.WORD_MOD]
  by_contra hnot
  have hle : 2 ^ 256 ≤ natSqrt (uint512 xHi xLo) := Nat.le_of_not_gt hnot
  have hsquare := natSqrt_sq_le (uint512 xHi xLo)
  have hge : 2 ^ 512 ≤ uint512 xHi xLo := by
    calc
      2 ^ 512 = 2 ^ 256 * 2 ^ 256 := by rw [← Nat.pow_add]
      _ ≤ natSqrt (uint512 xHi xLo) * natSqrt (uint512 xHi xLo) :=
        Nat.mul_le_mul hle hle
      _ ≤ uint512 xHi xLo := hsquare
  exact not_le_of_gt (uint512_lt_512 xHi xLo) hge

private theorem karatsubaFloor_lt_word (xHi xLo : Nat)
    (hlo : 2 ^ 254 ≤ xHi) (hhi : xHi < 2 ^ 256) (hxlo : xLo < 2 ^ 256) :
    karatsubaFloor xHi xLo < FormalYul.WORD_MOD := by
  rw [karatsubaFloor_eq_natSqrt xHi xLo hlo hxlo]
  unfold FormalYul.WORD_MOD
  by_contra hnot
  have hle : 2 ^ 256 ≤ natSqrt (xHi * 2 ^ 256 + xLo) := Nat.le_of_not_gt hnot
  have hsquare := natSqrt_sq_le (xHi * 2 ^ 256 + xLo)
  have hge : 2 ^ 512 ≤ xHi * 2 ^ 256 + xLo := by
    calc
      2 ^ 512 = 2 ^ 256 * 2 ^ 256 := by rw [← Nat.pow_add]
      _ ≤ natSqrt (xHi * 2 ^ 256 + xLo) * natSqrt (xHi * 2 ^ 256 + xLo) :=
        Nat.mul_le_mul hle hle
      _ ≤ xHi * 2 ^ 256 + xLo := hsquare
  have hlt : xHi * 2 ^ 256 + xLo < 2 ^ 512 := by
    calc
      xHi * 2 ^ 256 + xLo < 2 ^ 256 * 2 ^ 256 := by
        have hmul := Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos 256)
        omega
      _ = 2 ^ 512 := by rw [← Nat.pow_add]
  exact not_le_of_gt hlt hge

private theorem sqrt512CoreFromQuotient_eq_natSqrt
    (xHi xLo xHi1 xLo1 k q rem : Nat)
    (hxHi1_lo : 2 ^ 254 ≤ xHi1) (hxHi1_hi : xHi1 < 2 ^ 256)
    (hxLo1 : xLo1 < 2 ^ 256) (hk : k < 256)
    (hHi : xHi1 = (xHi * 2 ^ 256 + xLo) * 4 ^ k / 2 ^ 256)
    (hLo : xLo1 = (xHi * 2 ^ 256 + xLo) * 4 ^ k % 2 ^ 256)
    (hq : q =
      ((xHi1 - natSqrt xHi1 * natSqrt xHi1) * 2 ^ 128 + xLo1 / 2 ^ 128) /
        (2 * natSqrt xHi1))
    (hrem : rem =
      ((xHi1 - natSqrt xHi1 * natSqrt xHi1) * 2 ^ 128 + xLo1 / 2 ^ 128) %
        (2 * natSqrt xHi1)) :
    let r := FormalYul.evmAdd (FormalYul.evmShl 128 (natSqrt xHi1)) q
    let hiRem := FormalYul.evmShr 128 rem
    let hiRLo := FormalYul.evmShr 128 q
    let loRem := FormalYul.evmOr (FormalYul.evmShl 128 rem)
      (FormalYul.evmAnd xLo1 340282366920938463463374607431768211455)
    let loSq := FormalYul.evmMul q q
    let dec := FormalYul.evmOr (FormalYul.evmLt hiRem hiRLo)
      (FormalYul.evmAnd (FormalYul.evmEq hiRem hiRLo) (FormalYul.evmLt loRem loSq))
    FormalYul.evmShr k (FormalYul.evmSub r dec) =
      natSqrt (xHi * 2 ^ 256 + xLo) := by
  intro r hiRem hiRLo loRem loSq dec
  have hcorr := sqrtCorrectionFromQuotient_eq_karatsubaFloor xHi1 xLo1 q rem
    hxHi1_lo hxHi1_hi hxLo1 hq hrem
  rw [hcorr]
  have hfloor_lt := karatsubaFloor_lt_word xHi1 xLo1 hxHi1_lo hxHi1_hi hxLo1
  rw [evmShr_eq_of_lt k (karatsubaFloor xHi1 xLo1) hk hfloor_lt]
  rw [karatsubaFloor_eq_natSqrt xHi1 xLo1 hxHi1_lo hxLo1]
  have hx_norm :
      xHi1 * 2 ^ 256 + xLo1 = (xHi * 2 ^ 256 + xLo) * 4 ^ k := by
    rw [hHi, hLo]
    have h := Nat.div_add_mod ((xHi * 2 ^ 256 + xLo) * 4 ^ k) (2 ^ 256)
    rw [Nat.mul_comm] at h
    exact h
  rw [hx_norm]
  exact natSqrt_shift_div (xHi * 2 ^ 256 + xLo) k

@[simp] private theorem call_convert_t_rational_254_by_1_to_t_uint256_4980_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 4980) [EvmYul.UInt256.ofNat 254]
      (.some "convert_t_rational_254_by_1_to_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 254]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_254_by_1_to_t_uint256_direct
      (value := 254) (fuel := fuel + 4880)
      (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_fun__shl256_uint256_direct
    (xHi xLo fuel : Nat) (s : EvmYul.UInt256)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100)
      [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo, s]
      (.some "fun__shl256_3075") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShr (FormalYul.evmSub 256 (FormalYul.wordNat s)) xHi),
       FormalYul.word (FormalYul.evmOr (FormalYul.evmShl (FormalYul.wordNat s) xHi)
         (FormalYul.evmShr (FormalYul.evmSub 256 (FormalYul.wordNat s)) xLo)),
       FormalYul.word (FormalYul.evmShl (FormalYul.wordNat s) xLo)]) := by
  have hs : s = FormalYul.word (FormalYul.wordNat s) := by
    apply FormalYul.Preservation.eq_of_wordNat_eq
    rw [FormalYul.Preservation.wordNat_word]
    unfold FormalYul.u256 FormalYul.WORD_MOD FormalYul.wordNat EvmYul.UInt256.toNat
    exact (Nat.mod_eq_of_lt s.val.2).symm
  rw [hs]
  simpa [FormalYul.word, yulName_fun__shl256, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using
    call_fun__shl256_direct (xHi := xHi) (xLo := xLo) (s := FormalYul.wordNat s)
      (fuel := fuel) (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun__shl256_4981_direct
    (xHi xLo fuel : Nat) (s : EvmYul.UInt256)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 4981)
      [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo, s]
      (.some "fun__shl256_3075") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShr (FormalYul.evmSub 256 (FormalYul.wordNat s)) xHi),
       FormalYul.word (FormalYul.evmOr (FormalYul.evmShl (FormalYul.wordNat s) xHi)
         (FormalYul.evmShr (FormalYul.evmSub 256 (FormalYul.wordNat s)) xLo)),
       FormalYul.word (FormalYul.evmShl (FormalYul.wordNat s) xLo)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun__shl256_uint256_direct (xHi := xHi) (xLo := xLo) (s := s)
      (fuel := fuel + 4881) (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_convert_t_rational_1_by_1_to_t_uint8_4977_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 4977) [EvmYul.UInt256.ofNat 1]
      (.some "convert_t_rational_1_by_1_to_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 1]) := by
  simpa [FormalYul.word, FormalYul.evmAnd, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using
    call_convert_t_rational_1_by_1_to_t_uint8_direct
      (value := 1) (fuel := fuel + 4857)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_shift_right_t_uint256_t_uint8_4975_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 4975) [EvmYul.UInt256.ofNat value, EvmYul.UInt256.ofNat 1]
      (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmShr 1 value)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_right_t_uint256_t_uint8_one_direct
      (value := value) (fuel := fuel + 4875)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun__sqrt_baseCase_4971_direct
    (xHi fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 4971) [EvmYul.UInt256.ofNat xHi]
      (.some "fun__sqrt_baseCase_4393") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (sqrtBaseCaseEvm xHi).1, FormalYul.word (sqrtBaseCaseEvm xHi).2]) := by
  simpa [FormalYul.word, yulName_fun__sqrt_baseCase, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using
    call_fun__sqrt_baseCase_direct (xHi := xHi) (fuel := fuel + 3571)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_zero_value_for_split_t_uint256_4967_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 4967) [] (.some "zero_value_for_split_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_zero_value_for_split_t_uint256_direct
      (fuel := fuel) (extra := 4947) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_fun__sqrt_karatsubaQuotient_4959_direct
    (res xLo rHi fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 4959)
      [EvmYul.UInt256.ofNat res, EvmYul.UInt256.ofNat xLo, EvmYul.UInt256.ofNat rHi]
      (.some "fun__sqrt_karatsubaQuotient_4409") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    let n := FormalYul.evmOr (FormalYul.evmShl 128 res) (FormalYul.evmShr 128 xLo)
    let d := FormalYul.evmShl 1 rHi
    let q0 := FormalYul.evmDiv n d
    let rem0 := FormalYul.evmMod n d
    let c := FormalYul.evmShr 128 res
    let q1 := FormalYul.evmAdd q0 (FormalYul.evmDiv (FormalYul.evmNot 0) d)
    let rem1 := FormalYul.evmAdd rem0
      (FormalYul.evmAdd 1 (FormalYul.evmMod (FormalYul.evmNot 0) d))
    let q2 := FormalYul.evmAdd q1 (FormalYul.evmDiv rem1 d)
    let rem2 := FormalYul.evmMod rem1 d
    let out : Nat × Nat := if c = 0 then (q0, rem0) else (q2, rem2)
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word out.1, FormalYul.word out.2]) := by
  by_cases hc : FormalYul.evmShr 128 res = 0
  · simpa [FormalYul.word, yulName_fun__sqrt_karatsubaQuotient, hc, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      call_fun__sqrt_karatsubaQuotient_direct
        (res := res) (xLo := xLo) (rHi := rHi) (fuel := fuel + 4659)
        (shared := shared) (store := store) (hlookup := hlookup)
  · simpa [FormalYul.word, yulName_fun__sqrt_karatsubaQuotient, hc, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      call_fun__sqrt_karatsubaQuotient_direct
        (res := res) (xLo := xLo) (rHi := rHi) (fuel := fuel + 4659)
        (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun__sqrt_correction_4948_direct
    (rHi rLo res xLo fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 4948)
      [EvmYul.UInt256.ofNat rHi, EvmYul.UInt256.ofNat rLo,
       EvmYul.UInt256.ofNat res, EvmYul.UInt256.ofNat xLo]
      (.some "fun__sqrt_correction_4477") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    let r := FormalYul.evmAdd (FormalYul.evmShl 128 rHi) rLo
    let hiRes := FormalYul.evmShr 128 res
    let hiRLo := FormalYul.evmShr 128 rLo
    let loRes := FormalYul.evmOr (FormalYul.evmShl 128 res)
      (FormalYul.evmAnd xLo 340282366920938463463374607431768211455)
    let loSq := FormalYul.evmMul rLo rLo
    let dec := FormalYul.evmOr (FormalYul.evmLt hiRes hiRLo)
      (FormalYul.evmAnd (FormalYul.evmEq hiRes hiRLo) (FormalYul.evmLt loRes loSq))
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmSub r dec)]) := by
  simpa [FormalYul.word, yulName_fun__sqrt_correction, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using
    call_fun__sqrt_correction_direct
      (rHi := rHi) (rLo := rLo) (res := res) (xLo := xLo) (fuel := fuel + 3948)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_shift_right_t_uint256_t_uint256_4941_direct
    (value bits fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 4941)
      [EvmYul.UInt256.ofNat value, EvmYul.UInt256.ofNat bits]
      (.some "shift_right_t_uint256_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmShr bits value)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_right_t_uint256_t_uint256_direct
      (value := value) (bits := bits) (fuel := fuel + 4841)
      (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_fun__sqrt512_raw_direct
    (xHi xLo fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (rawShift rawDblK rawXLo1 rawXHi1 rawK rawRHi rawRes rawN rawD
      rawQ0 rawRem0 rawC rawQ1 rawRem1 rawQ2 rawRem2 rawQ rawRem rawR
      rawHiRem rawHiRLo rawLoRem rawLoSq rawDec rawCorrected : Nat)
    (rawOut : Nat × Nat)
    (hrawShift : rawShift = FormalYul.evmClz xHi)
    (hrawDblK : rawDblK = FormalYul.evmAnd rawShift 254)
    (hrawXLo1 : rawXLo1 = FormalYul.evmShl rawDblK xLo)
    (hrawXHi1 : rawXHi1 =
      FormalYul.evmOr (FormalYul.evmShl rawDblK xHi)
        (FormalYul.evmShr (FormalYul.evmSub 256 rawDblK) xLo))
    (hrawK : rawK = FormalYul.evmShr 1 rawShift)
    (hrawRHi : rawRHi = (sqrtBaseCaseEvm rawXHi1).1)
    (hrawRes : rawRes = (sqrtBaseCaseEvm rawXHi1).2)
    (hrawN : rawN = FormalYul.evmOr (FormalYul.evmShl 128 rawRes)
      (FormalYul.evmShr 128 rawXLo1))
    (hrawD : rawD = FormalYul.evmShl 1 rawRHi)
    (hrawQ0 : rawQ0 = FormalYul.evmDiv rawN rawD)
    (hrawRem0 : rawRem0 = FormalYul.evmMod rawN rawD)
    (hrawC : rawC = FormalYul.evmShr 128 rawRes)
    (hrawQ1 : rawQ1 = FormalYul.evmAdd rawQ0
      (FormalYul.evmDiv (FormalYul.evmNot 0) rawD))
    (hrawRem1 : rawRem1 = FormalYul.evmAdd rawRem0
      (FormalYul.evmAdd 1 (FormalYul.evmMod (FormalYul.evmNot 0) rawD)))
    (hrawQ2 : rawQ2 = FormalYul.evmAdd rawQ1 (FormalYul.evmDiv rawRem1 rawD))
    (hrawRem2 : rawRem2 = FormalYul.evmMod rawRem1 rawD)
    (hrawOut : rawOut = if rawC = 0 then (rawQ0, rawRem0) else (rawQ2, rawRem2))
    (hrawQ : rawQ = rawOut.1)
    (hrawRem : rawRem = rawOut.2)
    (hrawR : rawR = FormalYul.evmAdd (FormalYul.evmShl 128 rawRHi) rawQ)
    (hrawHiRem : rawHiRem = FormalYul.evmShr 128 rawRem)
    (hrawHiRLo : rawHiRLo = FormalYul.evmShr 128 rawQ)
    (hrawLoRem : rawLoRem = FormalYul.evmOr (FormalYul.evmShl 128 rawRem)
      (FormalYul.evmAnd rawXLo1 340282366920938463463374607431768211455))
    (hrawLoSq : rawLoSq = FormalYul.evmMul rawQ rawQ)
    (hrawDec : rawDec = FormalYul.evmOr (FormalYul.evmLt rawHiRem rawHiRLo)
      (FormalYul.evmAnd (FormalYul.evmEq rawHiRem rawHiRLo)
        (FormalYul.evmLt rawLoRem rawLoSq)))
    (hrawCorrected : rawCorrected = FormalYul.evmSub rawR rawDec) :
    EvmYul.Yul.call (fuel + 5000) [FormalYul.word xHi, FormalYul.word xLo]
      (.some yulName_fun__sqrt512) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (FormalYul.evmShr rawK rawCorrected)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun__sqrt512]
  simp only [yulFunction_fun__sqrt512, yulFunction_fun__sqrt_4544,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup,
    EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
    ← hrawShift, ← hrawDblK, ← hrawXLo1, ← hrawXHi1, ← hrawK,
    ← hrawRHi, ← hrawRes, ← hrawN, ← hrawD, ← hrawQ0, ← hrawRem0,
    ← hrawC, ← hrawQ1, ← hrawRem1, ← hrawQ2, ← hrawRem2, ← hrawOut,
    ← hrawQ, ← hrawRem, ← hrawR, ← hrawHiRem, ← hrawHiRLo, ← hrawLoRem,
    ← hrawLoSq, ← hrawDec, ← hrawCorrected,
    call_zero_value_for_split_t_uint256_direct (fuel := fuel) (extra := 4976)
      (shared := shared)
      (store := Finmap.insert "var_x_hi_4479" (EvmYul.UInt256.ofNat xHi)
        (Finmap.insert "var_x_lo_4481" (EvmYul.UInt256.ofNat xLo)
          (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup),
    Finmap.lookup_insert, FormalYul.word]

private theorem sqrt512_raw_result_eq_natSqrt
    (xHi xLo : Nat) (hxHi_pos : 0 < FormalYul.u256 xHi)
    (rawShift rawDblK rawXLo1 rawXHi1 rawK rawRHi rawRes rawN rawD
      rawQ0 rawRem0 rawC rawQ1 rawRem1 rawQ2 rawRem2 rawQ rawRem rawR
      rawHiRem rawHiRLo rawLoRem rawLoSq rawDec rawCorrected : Nat)
    (rawOut : Nat × Nat)
    (hrawShift : rawShift = FormalYul.evmClz xHi)
    (hrawDblK : rawDblK = FormalYul.evmAnd rawShift 254)
    (hrawXLo1 : rawXLo1 = FormalYul.evmShl rawDblK xLo)
    (hrawXHi1 : rawXHi1 =
      FormalYul.evmOr (FormalYul.evmShl rawDblK xHi)
        (FormalYul.evmShr (FormalYul.evmSub 256 rawDblK) xLo))
    (hrawK : rawK = FormalYul.evmShr 1 rawShift)
    (hrawRHi : rawRHi = (sqrtBaseCaseEvm rawXHi1).1)
    (hrawRes : rawRes = (sqrtBaseCaseEvm rawXHi1).2)
    (hrawN : rawN = FormalYul.evmOr (FormalYul.evmShl 128 rawRes)
      (FormalYul.evmShr 128 rawXLo1))
    (hrawD : rawD = FormalYul.evmShl 1 rawRHi)
    (hrawQ0 : rawQ0 = FormalYul.evmDiv rawN rawD)
    (hrawRem0 : rawRem0 = FormalYul.evmMod rawN rawD)
    (hrawC : rawC = FormalYul.evmShr 128 rawRes)
    (hrawQ1 : rawQ1 = FormalYul.evmAdd rawQ0
      (FormalYul.evmDiv (FormalYul.evmNot 0) rawD))
    (hrawRem1 : rawRem1 = FormalYul.evmAdd rawRem0
      (FormalYul.evmAdd 1 (FormalYul.evmMod (FormalYul.evmNot 0) rawD)))
    (hrawQ2 : rawQ2 = FormalYul.evmAdd rawQ1 (FormalYul.evmDiv rawRem1 rawD))
    (hrawRem2 : rawRem2 = FormalYul.evmMod rawRem1 rawD)
    (hrawOut : rawOut = if rawC = 0 then (rawQ0, rawRem0) else (rawQ2, rawRem2))
    (hrawQ : rawQ = rawOut.1)
    (hrawRem : rawRem = rawOut.2)
    (hrawR : rawR = FormalYul.evmAdd (FormalYul.evmShl 128 rawRHi) rawQ)
    (hrawHiRem : rawHiRem = FormalYul.evmShr 128 rawRem)
    (hrawHiRLo : rawHiRLo = FormalYul.evmShr 128 rawQ)
    (hrawLoRem : rawLoRem = FormalYul.evmOr (FormalYul.evmShl 128 rawRem)
      (FormalYul.evmAnd rawXLo1 340282366920938463463374607431768211455))
    (hrawLoSq : rawLoSq = FormalYul.evmMul rawQ rawQ)
    (hrawDec : rawDec = FormalYul.evmOr (FormalYul.evmLt rawHiRem rawHiRLo)
      (FormalYul.evmAnd (FormalYul.evmEq rawHiRem rawHiRLo)
        (FormalYul.evmLt rawLoRem rawLoSq)))
    (hrawCorrected : rawCorrected = FormalYul.evmSub rawR rawDec) :
    FormalYul.evmShr rawK rawCorrected = natSqrt (uint512 xHi xLo) := by
  let xh := FormalYul.u256 xHi
  let xl := FormalYul.u256 xLo
  have hxh_lt : xh < 2 ^ 256 := by
    dsimp [xh]
    unfold FormalYul.u256 FormalYul.WORD_MOD
    exact Nat.mod_lt xHi (Nat.two_pow_pos 256)
  have hxl_lt : xl < 2 ^ 256 := by
    dsimp [xl]
    unfold FormalYul.u256 FormalYul.WORD_MOD
    exact Nat.mod_lt xLo (Nat.two_pow_pos 256)
  let shift := FormalYul.evmClz xh
  let dblK := FormalYul.evmAnd shift 254
  let xLo1 := FormalYul.evmShl dblK xl
  let xHi1 :=
    FormalYul.evmOr (FormalYul.evmShl dblK xh)
      (FormalYul.evmShr (FormalYul.evmSub 256 dblK) xl)
  let kNat := (255 - Nat.log2 xh) / 2
  let kEvm := FormalYul.evmShr (FormalYul.evmAnd (FormalYul.evmAnd 1 255) 255) shift
  have hnorm := evmNormalization_correct xh xl hxHi_pos hxh_lt hxl_lt
  have hnorm' :
      xHi1 = (xh * 2 ^ 256 + xl) * 4 ^ kNat / 2 ^ 256 ∧
      xLo1 = (xh * 2 ^ 256 + xl) * 4 ^ kNat % 2 ^ 256 ∧
      kEvm = kNat ∧
      2 ^ 254 ≤ xHi1 ∧ xHi1 < 2 ^ 256 ∧ xLo1 < 2 ^ 256 := by
    simpa [xh, xl, shift, dblK, xLo1, xHi1, kNat, kEvm,
      FormalYul.u256_u256] using hnorm
  rcases hnorm' with ⟨hHi, hLo, hk, hxHi1_lo, hxHi1_hi, hxLo1_lt⟩
  have hbase := sqrtBaseCaseEvm_correct xHi1 hxHi1_lo hxHi1_hi
  let rHi := (sqrtBaseCaseEvm xHi1).1
  let res := (sqrtBaseCaseEvm xHi1).2
  have hrHi : rHi = natSqrt xHi1 := by
    simpa [rHi] using hbase.1
  have hres : res = xHi1 - natSqrt xHi1 * natSqrt xHi1 := by
    simpa [res] using hbase.2
  have hrawShift_norm : rawShift = shift := by
    rw [hrawShift]
    simp [shift, xh, FormalYul.Preservation.evmClz_u256]
  have hrawDblK_norm : rawDblK = dblK := by
    simp [hrawDblK, dblK, hrawShift_norm]
  have hrawXLo1_norm : rawXLo1 = xLo1 := by
    simp [hrawXLo1, xLo1, hrawDblK_norm, xl, FormalYul.Preservation.evmShl_u256_right]
  have hrawXHi1_norm : rawXHi1 = xHi1 := by
    simp [hrawXHi1, xHi1, hrawDblK_norm, xh, xl,
      FormalYul.Preservation.evmShl_u256_right,
      FormalYul.Preservation.evmShr_u256_right]
  have hrawK_norm : rawK = kNat := by
    have hkRaw : rawK = kEvm := by
      simp +decide [hrawK, kEvm, hrawShift_norm, FormalYul.evmAnd]
    exact hkRaw.trans hk
  have hrawRHi_norm : rawRHi = rHi := by
    simp [hrawRHi, rHi, hrawXHi1_norm]
  have hrawRes_norm : rawRes = res := by
    simp [hrawRes, res, hrawXHi1_norm]
  have hrHi_lo : 2 ^ 127 ≤ rHi := by
    rw [hrHi]
    exact natSqrt_ge_2_127_of_ge_2_254 xHi1 hxHi1_lo
  have hrHi_hi : rHi < 2 ^ 128 := by
    rw [hrHi]
    exact natSqrt_lt_2_128_of_lt_2_256 xHi1 hxHi1_hi
  have hres_le : res ≤ 2 * rHi := by
    rw [hres, hrHi]
    have hsq := natSqrt_sq_le xHi1
    have hsucc := natSqrt_lt_succ_sq xHi1
    have hadd := Nat.add_mul (natSqrt xHi1) 1 (natSqrt xHi1 + 1)
    have hmul := Nat.mul_add (natSqrt xHi1) (natSqrt xHi1) 1
    omega
  have hres_lt : res < 2 ^ 256 := by
    rw [hres]
    omega
  have hrawRHi_lo : 2 ^ 127 ≤ rawRHi := by
    rwa [hrawRHi_norm]
  have hrawRHi_hi : rawRHi < 2 ^ 128 := by
    rwa [hrawRHi_norm]
  have hrawRes_le : rawRes ≤ 2 * rawRHi := by
    rw [hrawRes_norm, hrawRHi_norm]
    exact hres_le
  have hrawRes_lt : rawRes < 2 ^ 256 := by
    rwa [hrawRes_norm]
  have hrawXLo1_lt : rawXLo1 < 2 ^ 256 := by
    rwa [hrawXLo1_norm]
  have hquotRaw := karatsubaQuotientEvm_correct rawRes rawXLo1 rawRHi
    hrawRes_le hrawXLo1_lt hrawRHi_lo hrawRHi_hi hrawRes_lt
  let nNat := (xHi1 - natSqrt xHi1 * natSqrt xHi1) * 2 ^ 128 + xLo1 / 2 ^ 128
  let dNat := 2 * natSqrt xHi1
  have hdNat_pos : 0 < dNat := by
    dsimp [dNat]
    rw [← hrHi]
    omega
  have hxLo1_hi : xLo1 / 2 ^ 128 < 2 ^ 128 :=
    Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hxLo1_lt)
  have hq_le_128 : nNat / dNat ≤ 2 ^ 128 := by
    rw [Nat.div_le_iff_le_mul_add_pred hdNat_pos]
    dsimp [nNat, dNat]
    omega
  have hq_lt_word : nNat / dNat < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    omega
  have hrem_lt_word : nNat % dNat < FormalYul.WORD_MOD := by
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hdNat_pos)
      (by dsimp [dNat]; rw [← hrHi]; unfold FormalYul.WORD_MOD; omega)
  have hrawQ :
      rawQ =
        ((xHi1 - natSqrt xHi1 * natSqrt xHi1) * 2 ^ 128 + xLo1 / 2 ^ 128) /
          (2 * natSqrt xHi1) := by
    have hq_raw :
        rawQ =
          (rawRes * 2 ^ 128 + rawXLo1 / 2 ^ 128) / (2 * rawRHi) %
            FormalYul.WORD_MOD := by
      simpa [hrawQ, hrawOut, hrawQ0, hrawQ1, hrawQ2, hrawRem1, hrawRem0,
        hrawRem2, hrawN, hrawD, hrawC]
        using hquotRaw.1
    have hq_mod : rawQ = nNat / dNat % FormalYul.WORD_MOD := by
      simpa [nNat, dNat, hrawRHi_norm, hrawRes_norm, hrawXLo1_norm, hrHi, hres] using hq_raw
    rwa [Nat.mod_eq_of_lt hq_lt_word] at hq_mod
  have hrawRem :
      rawRem =
        ((xHi1 - natSqrt xHi1 * natSqrt xHi1) * 2 ^ 128 + xLo1 / 2 ^ 128) %
          (2 * natSqrt xHi1) := by
    have hrem_raw :
        rawRem =
          (rawRes * 2 ^ 128 + rawXLo1 / 2 ^ 128) % (2 * rawRHi) %
            FormalYul.WORD_MOD := by
      simpa [hrawRem, hrawOut, hrawQ0, hrawQ1, hrawQ2, hrawRem0, hrawRem1,
        hrawRem2, hrawN, hrawD, hrawC]
        using hquotRaw.2
    have hrem_mod : rawRem = nNat % dNat % FormalYul.WORD_MOD := by
      simpa [nNat, dNat, hrawRHi_norm, hrawRes_norm, hrawXLo1_norm, hrHi, hres] using hrem_raw
    rwa [Nat.mod_eq_of_lt hrem_lt_word] at hrem_mod
  have hkNat_lt : kNat < 256 := by
    dsimp [kNat]
    omega
  have hcore := sqrt512CoreFromQuotient_eq_natSqrt xh xl xHi1 xLo1 kNat rawQ rawRem
    hxHi1_lo hxHi1_hi hxLo1_lt hkNat_lt hHi hLo hrawQ hrawRem
  simpa [hrawCorrected, hrawR, hrawDec, hrawHiRem, hrawHiRLo, hrawLoRem,
    hrawLoSq, hrawRHi_norm, hrawXLo1_norm, hrawK_norm, hrHi, uint512, xh, xl]
    using hcore

private theorem call_fun__sqrt512_direct
    (xHi xLo fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hxHi_pos : 0 < FormalYul.u256 xHi) :
    EvmYul.Yul.call (fuel + 5000) [FormalYul.word xHi, FormalYul.word xLo]
      (.some yulName_fun__sqrt512) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (natSqrt (uint512 xHi xLo))]) := by
  let rawShift := FormalYul.evmClz xHi
  let rawDblK := FormalYul.evmAnd rawShift 254
  let rawXLo1 := FormalYul.evmShl rawDblK xLo
  let rawXHi1 :=
    FormalYul.evmOr (FormalYul.evmShl rawDblK xHi)
      (FormalYul.evmShr (FormalYul.evmSub 256 rawDblK) xLo)
  let rawK := FormalYul.evmShr 1 rawShift
  let rawRHi := (sqrtBaseCaseEvm rawXHi1).1
  let rawRes := (sqrtBaseCaseEvm rawXHi1).2
  let rawN := FormalYul.evmOr (FormalYul.evmShl 128 rawRes) (FormalYul.evmShr 128 rawXLo1)
  let rawD := FormalYul.evmShl 1 rawRHi
  let rawQ0 := FormalYul.evmDiv rawN rawD
  let rawRem0 := FormalYul.evmMod rawN rawD
  let rawC := FormalYul.evmShr 128 rawRes
  let rawQ1 := FormalYul.evmAdd rawQ0 (FormalYul.evmDiv (FormalYul.evmNot 0) rawD)
  let rawRem1 := FormalYul.evmAdd rawRem0
    (FormalYul.evmAdd 1 (FormalYul.evmMod (FormalYul.evmNot 0) rawD))
  let rawQ2 := FormalYul.evmAdd rawQ1 (FormalYul.evmDiv rawRem1 rawD)
  let rawRem2 := FormalYul.evmMod rawRem1 rawD
  let rawOut : Nat × Nat := if rawC = 0 then (rawQ0, rawRem0) else (rawQ2, rawRem2)
  let rawQ := rawOut.1
  let rawRem := rawOut.2
  let rawR := FormalYul.evmAdd (FormalYul.evmShl 128 rawRHi) rawQ
  let rawHiRem := FormalYul.evmShr 128 rawRem
  let rawHiRLo := FormalYul.evmShr 128 rawQ
  let rawLoRem := FormalYul.evmOr (FormalYul.evmShl 128 rawRem)
    (FormalYul.evmAnd rawXLo1 340282366920938463463374607431768211455)
  let rawLoSq := FormalYul.evmMul rawQ rawQ
  let rawDec := FormalYul.evmOr (FormalYul.evmLt rawHiRem rawHiRLo)
    (FormalYul.evmAnd (FormalYul.evmEq rawHiRem rawHiRLo)
      (FormalYul.evmLt rawLoRem rawLoSq))
  let rawCorrected := FormalYul.evmSub rawR rawDec
  rw [call_fun__sqrt512_raw_direct
    (xHi := xHi) (xLo := xLo) (fuel := fuel) (shared := shared)
    (store := store) (hlookup := hlookup)
    (rawShift := rawShift) (rawDblK := rawDblK) (rawXLo1 := rawXLo1)
    (rawXHi1 := rawXHi1) (rawK := rawK) (rawRHi := rawRHi) (rawRes := rawRes)
    (rawN := rawN) (rawD := rawD) (rawQ0 := rawQ0) (rawRem0 := rawRem0)
    (rawC := rawC) (rawQ1 := rawQ1) (rawRem1 := rawRem1) (rawQ2 := rawQ2)
    (rawRem2 := rawRem2) (rawQ := rawQ) (rawRem := rawRem) (rawR := rawR)
    (rawHiRem := rawHiRem) (rawHiRLo := rawHiRLo) (rawLoRem := rawLoRem)
    (rawLoSq := rawLoSq) (rawDec := rawDec) (rawCorrected := rawCorrected)
    (rawOut := rawOut)
    (hrawShift := rfl) (hrawDblK := rfl) (hrawXLo1 := rfl) (hrawXHi1 := rfl)
    (hrawK := rfl) (hrawRHi := rfl) (hrawRes := rfl) (hrawN := rfl)
    (hrawD := rfl) (hrawQ0 := rfl) (hrawRem0 := rfl) (hrawC := rfl)
    (hrawQ1 := rfl) (hrawRem1 := rfl) (hrawQ2 := rfl) (hrawRem2 := rfl)
    (hrawOut := rfl) (hrawQ := rfl) (hrawRem := rfl) (hrawR := rfl)
    (hrawHiRem := rfl) (hrawHiRLo := rfl) (hrawLoRem := rfl)
    (hrawLoSq := rfl) (hrawDec := rfl) (hrawCorrected := rfl)]
  exact congrArg
    (fun r => Except.ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word r]))
    (sqrt512_raw_result_eq_natSqrt xHi xLo hxHi_pos
      rawShift rawDblK rawXLo1 rawXHi1 rawK rawRHi rawRes rawN rawD rawQ0 rawRem0
      rawC rawQ1 rawRem1 rawQ2 rawRem2 rawQ rawRem rawR rawHiRem rawHiRLo
      rawLoRem rawLoSq rawDec rawCorrected rawOut rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

private theorem call_fun_tmp_128_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 40) [] (.some "fun_tmp_128") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_tmp_128]
  simp only [yulFunction_fun_tmp_128,
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
      EvmYul.Yul.call (fuel + 36) [] (.some "zero_value_for_split_t_userDefinedValueType$_uint512_$113")
        (.some yulContract) (EvmYul.Yul.State.Ok shared
          (Inhabited.default : EvmYul.Yul.VarStore)) =
      .ok (EvmYul.Yul.State.Ok shared (Inhabited.default : EvmYul.Yul.VarStore),
        [FormalYul.word 0]) := by
    simpa using hzero
  simp [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.multifill',
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill, EvmYul.Yul.State.lookup!,
    EvmYul.Yul.State.setStore, EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?, hzero', FormalYul.word]

private theorem call_fun_tmp_128_raw_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 40)) [] (.some "fun_tmp_128")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 0]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_tmp_128_direct (fuel := fuel + extra) (shared := shared)
      (store := store) (hlookup := hlookup)

private def sharedAfterFrom0 (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat) :
    EvmYul.SharedState .Yul :=
  { shared with
    toMachineState :=
      ((shared.toMachineState.mstore (FormalYul.word 0) (FormalYul.word xHi)).mstore
        (FormalYul.word 32) (FormalYul.word xLo)) }

private def sharedAfterFrom128 (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat) :
    EvmYul.SharedState .Yul :=
  { shared with
    toMachineState :=
      ((shared.toMachineState.mstore (FormalYul.word 128) (FormalYul.word xHi)).mstore
        (FormalYul.word 160) (FormalYul.word xLo)) }

private def sharedAfterAlloc128 (shared : EvmYul.SharedState .Yul) :
    EvmYul.SharedState .Yul :=
  { shared with
    toMachineState := shared.toMachineState.mstore (FormalYul.word 64) (FormalYul.word 192) }

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

private theorem sharedAfterFrom128_lookup
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    (sharedAfterFrom128 shared xHi xLo).accountMap.find?
        (sharedAfterFrom128 shared xHi xLo).executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract) := by
  simpa [sharedAfterFrom128] using
    FormalYul.Preservation.shared_mstore_two_words_lookup
      (shared := shared) (pos0 := FormalYul.word 128) (pos1 := FormalYul.word 160)
      (value0 := FormalYul.word xHi) (value1 := FormalYul.word xLo)
      (account := FormalYul.accountFor yulContract) hlookup

private theorem sharedAfterAlloc128_lookup
    (shared : EvmYul.SharedState .Yul)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    (sharedAfterAlloc128 shared).accountMap.find?
        (sharedAfterAlloc128 shared).executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract) := by
  simpa [sharedAfterAlloc128] using
    FormalYul.Preservation.shared_mstore_lookup
      (shared := shared) (pos := FormalYul.word 64) (value := FormalYul.word 192)
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

private theorem sharedAfterFrom0_mload0_active6
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hactive : shared.toMachineState.activeWords = FormalYul.word 6) :
    ((sharedAfterFrom0 shared xHi xLo).mload (FormalYul.word 0)).1 =
      FormalYul.word xHi := by
  simpa [sharedAfterFrom0] using
    FormalYul.Preservation.mload_two_word_write_first_active_6 shared.toMachineState
      (FormalYul.word xHi) (FormalYul.word xLo) hactive

private theorem sharedAfterFrom0_mload32_active6
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hactive : shared.toMachineState.activeWords = FormalYul.word 6) :
    ((sharedAfterFrom0 shared xHi xLo).mload (FormalYul.word 32)).1 =
      FormalYul.word xLo := by
  simpa [sharedAfterFrom0] using
    FormalYul.Preservation.mload_two_word_write_second_active_6 shared.toMachineState
      (FormalYul.word xHi) (FormalYul.word xLo) hactive

private theorem sharedAfterFrom0_mload0_state_active6
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hactive : shared.toMachineState.activeWords = FormalYul.word 6) :
    ((sharedAfterFrom0 shared xHi xLo).mload (FormalYul.word 0)).2 =
      (sharedAfterFrom0 shared xHi xLo).toMachineState := by
  simpa [sharedAfterFrom0] using
    FormalYul.Preservation.mload_two_word_write_first_state_active_6 shared.toMachineState
      (FormalYul.word xHi) (FormalYul.word xLo) hactive

private theorem sharedAfterFrom0_mload32_state_active6
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hactive : shared.toMachineState.activeWords = FormalYul.word 6) :
    ((sharedAfterFrom0 shared xHi xLo).mload (FormalYul.word 32)).2 =
      (sharedAfterFrom0 shared xHi xLo).toMachineState := by
  simpa [sharedAfterFrom0] using
    FormalYul.Preservation.mload_two_word_write_second_state_active_6 shared.toMachineState
      (FormalYul.word xHi) (FormalYul.word xLo) hactive

private theorem call_fun_from_156_zero_direct
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100) [FormalYul.word 0, FormalYul.word xHi, FormalYul.word xLo]
      (.some "fun_from_156") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [FormalYul.word 0]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_from_156]
  simp only [yulFunction_fun_from_156,
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
      EvmYul.Yul.call (fuel + 96) [] (.some "zero_value_for_split_t_userDefinedValueType$_uint512_$113")
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

@[simp] private theorem call_fun_from_156_zero_raw_direct
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100)
      [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
      (.some "fun_from_156") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [EvmYul.UInt256.ofNat 0]) := by
  simpa [FormalYul.word] using
    call_fun_from_156_zero_direct (xHi := xHi) (xLo := xLo) (fuel := fuel)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun_from_156_zero_raw_add_direct
    (xHi xLo : Nat) (fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 100))
      [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
      (.some "fun_from_156") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [EvmYul.UInt256.ofNat 0]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_from_156_zero_raw_direct (xHi := xHi) (xLo := xLo)
      (fuel := fuel + extra) (shared := shared) (store := store)
      (hlookup := hlookup)

private theorem call_fun_from_156_128_direct
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100)
      [FormalYul.word 128, FormalYul.word xHi, FormalYul.word xLo]
      (.some "fun_from_156") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom128 shared xHi xLo) store,
      [FormalYul.word 128]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_from_156]
  simp only [yulFunction_fun_from_156,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let zeroStore :=
    Finmap.insert "var_r_144" (EvmYul.UInt256.ofNat 128)
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
    hzero, sharedAfterFrom128, zeroStore, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  have haddr :
      EvmYul.UInt256.ofNat 32 + EvmYul.UInt256.ofNat 128 =
        EvmYul.UInt256.ofNat 160 := by
    decide
  rw [haddr]

private theorem call_fun_from_156_128_raw_direct
    (xHi xLo : Nat) (fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 100))
      [EvmYul.UInt256.ofNat 128, EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
      (.some "fun_from_156") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom128 shared xHi xLo) store,
      [EvmYul.UInt256.ofNat 128]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_from_156_128_direct (xHi := xHi) (xLo := xLo)
      (fuel := fuel + extra) (shared := shared) (store := store)
      (hlookup := hlookup)

private theorem call_fun_alloc_121_128_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hmload64 : (shared.mload (FormalYul.word 64)).1 = FormalYul.word 128)
    (hmload64_state : (shared.mload (FormalYul.word 64)).2 = shared.toMachineState) :
    EvmYul.Yul.call (fuel + 100) [] (.some "fun_alloc_121") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterAlloc128 shared) store,
      [FormalYul.word 128]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_alloc_121]
  simp only [yulFunction_fun_alloc_121,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hzero :
      EvmYul.Yul.call (fuel + 96) []
        (.some "zero_value_for_split_t_userDefinedValueType$_uint512_$113")
        (.some yulContract)
        (EvmYul.Yul.State.Ok shared (Inhabited.default : EvmYul.Yul.VarStore)) =
      .ok (EvmYul.Yul.State.Ok shared (Inhabited.default : EvmYul.Yul.VarStore),
        [FormalYul.word 0]) := by
    simpa using
      call_zero_value_for_split_t_userDefinedValueType_uint512_direct
        (fuel := fuel) (extra := 76) (shared := shared)
        (store := (Inhabited.default : EvmYul.Yul.VarStore)) (hlookup := hlookup)
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.eval.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.setMachineState, EvmYul.Yul.State.toMachineState,
    EvmYul.Yul.State.store,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    hzero, sharedAfterAlloc128, FormalYul.word, Finmap.lookup_insert]
  have hval :
      (shared.mload (EvmYul.UInt256.ofNat 64)).1 =
        EvmYul.UInt256.ofNat 128 := by
    simpa [FormalYul.word] using hmload64
  have hstate :
      (shared.mload (EvmYul.UInt256.ofNat 64)).2 =
        shared.toMachineState := by
    simpa [FormalYul.word] using hmload64_state
  rw [hstate, hval]
  constructor
  · have hadd :
        EvmYul.UInt256.ofNat 64 + EvmYul.UInt256.ofNat 128 =
          EvmYul.UInt256.ofNat 192 := by
      decide
    rw [hadd]
  · rfl

private theorem call_fun_alloc_121_128_raw_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hmload64 : (shared.mload (FormalYul.word 64)).1 = FormalYul.word 128)
    (hmload64_state : (shared.mload (FormalYul.word 64)).2 = shared.toMachineState) :
    EvmYul.Yul.call (fuel + (extra + 100)) [] (.some "fun_alloc_121")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterAlloc128 shared) store,
      [EvmYul.UInt256.ofNat 128]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_alloc_121_128_direct (fuel := fuel + extra) (shared := shared)
      (store := store) (hlookup := hlookup)
      (hmload64 := hmload64) (hmload64_state := hmload64_state)

private theorem call_fun_into_182_from0_direct
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    EvmYul.Yul.call (fuel + 120) [FormalYul.word 0]
      (.some "fun_into_182") (.some yulContract)
      (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [FormalYul.word xHi, FormalYul.word xLo]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [sharedAfterFrom0_lookup shared xHi xLo hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_into_182]
  simp only [yulFunction_fun_into_182,
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
      (Finmap.insert "zero_t_uint256_38" (EvmYul.UInt256.ofNat 0)
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

private theorem call_fun_into_182_from0_5591_raw_direct
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    EvmYul.Yul.call (fuel + 5591) [EvmYul.UInt256.ofNat 0]
      (.some "fun_into_182") (.some yulContract)
      (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_into_182_from0_direct (xHi := xHi) (xLo := xLo) (fuel := fuel + 5471)
      (shared := shared) (store := store) (hlookup := hlookup) (hactive := hactive)

private theorem evmEq_zero_eq_zero_iff (x : Nat) :
    FormalYul.evmEq x 0 = 0 ↔ FormalYul.u256 x ≠ 0 := by
  unfold FormalYul.evmEq
  simp

private theorem uint256_eq_ofNat_zero_struct_zero_iff (x : Nat) :
    (EvmYul.UInt256.eq (EvmYul.UInt256.ofNat x) (EvmYul.UInt256.ofNat 0) =
        ({ val := 0 } : EvmYul.UInt256)) ↔
      FormalYul.evmEq x 0 = 0 := by
  have hnat :
      FormalYul.wordNat
          (EvmYul.UInt256.eq (EvmYul.UInt256.ofNat x) (EvmYul.UInt256.ofNat 0)) =
        FormalYul.evmEq x 0 := by
    rw [FormalYul.Preservation.wordNat_eq]
    simp [FormalYul.Preservation.wordNat_ofNat,
      FormalYul.Preservation.evmEq_u256_left]
  constructor
  · intro h
    rw [h] at hnat
    simpa [FormalYul.wordNat] using hnat.symm
  · intro h
    apply FormalYul.Preservation.eq_of_wordNat_eq
    rw [hnat, h]
    rfl

private theorem uint256_eq_ofNat_zero_eq_one_of_u256_eq_zero (x : Nat)
    (h : FormalYul.u256 x = 0) :
    EvmYul.UInt256.eq (EvmYul.UInt256.ofNat x) (EvmYul.UInt256.ofNat 0) =
      EvmYul.UInt256.ofNat 1 := by
  apply FormalYul.Preservation.eq_of_wordNat_eq
  rw [FormalYul.Preservation.wordNat_eq]
  simp [FormalYul.Preservation.wordNat_ofNat, FormalYul.evmEq, h]

private theorem sqrt512_zero_high_eq_natSqrt (xHi xLo : Nat)
    (hhi : FormalYul.u256 xHi = 0) :
    floorSqrt (FormalYul.u256 xLo) = natSqrt (uint512 xHi xLo) := by
  have hxLo : FormalYul.u256 xLo < 2 ^ 256 := by
    unfold FormalYul.u256 FormalYul.WORD_MOD
    exact Nat.mod_lt xLo (Nat.two_pow_pos 256)
  rw [floorSqrt_eq_natSqrt_u256 _ hxLo]
  simp [uint512, hhi]

private theorem call_fun_sqrt256_5579_from0_raw_direct
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 5579) [EvmYul.UInt256.ofNat xLo] (.some yulName_fun_sqrt256)
      (.some yulContract) (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [EvmYul.UInt256.ofNat (floorSqrt (FormalYul.u256 xLo))]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_sqrt256_direct (x := xLo) (fuel := fuel + 5219)
      (shared := sharedAfterFrom0 shared xHi xLo) (store := store)
      (hlookup := sharedAfterFrom0_lookup shared xHi xLo hlookup)

private theorem call_fun__sqrt512_5579_from0_raw_direct
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hxHi_pos : 0 < FormalYul.u256 xHi) :
    EvmYul.Yul.call (fuel + 5579) [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
      (.some yulName_fun__sqrt512) (.some yulContract)
      (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [EvmYul.UInt256.ofNat (natSqrt (uint512 xHi xLo))]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun__sqrt512_direct (xHi := xHi) (xLo := xLo) (fuel := fuel + 579)
      (shared := sharedAfterFrom0 shared xHi xLo) (store := store)
      (hlookup := sharedAfterFrom0_lookup shared xHi xLo hlookup)
      (hxHi_pos := hxHi_pos)

private theorem call_cleanup_t_uint256_5581_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 5581) [v] (.some "cleanup_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_uint256_direct
      (v := v) (fuel := fuel + 5561) (shared := shared) (store := store)
      (hlookup := hlookup)

private theorem call_convert_t_rational_0_by_1_to_t_uint256_5583_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 5583) [EvmYul.UInt256.ofNat 0]
      (.some "convert_t_rational_0_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 0]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_0_by_1_to_t_uint256_direct
      (value := 0) (fuel := fuel + 5483)
      (shared := shared) (store := store) (hlookup := hlookup)

private theorem call_fun_sqrt512_from0_raw_direct
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    EvmYul.Yul.call (fuel + 5600) [EvmYul.UInt256.ofNat 0]
      (.some yulName_fun_sqrt512) (.some yulContract)
      (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [EvmYul.UInt256.ofNat (natSqrt (uint512 xHi xLo))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [sharedAfterFrom0_lookup shared xHi xLo hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_sqrt512]
  simp only [yulFunction_fun_sqrt512, yulFunction_fun_sqrt_4575,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let zeroStore :=
    Finmap.insert "var_x_4547" (EvmYul.UInt256.ofNat 0)
      (Inhabited.default : EvmYul.Yul.VarStore)
  have hzero :
      EvmYul.Yul.call (fuel + 5596) [] (.some "zero_value_for_split_t_uint256")
        (.some yulContract) (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo)
          zeroStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) zeroStore,
        [FormalYul.word 0]) := by
    simpa [zeroStore] using
      call_zero_value_for_split_t_uint256_direct
        (fuel := fuel) (extra := 5576) (shared := sharedAfterFrom0 shared xHi xLo)
        (store := zeroStore)
        (hlookup := sharedAfterFrom0_lookup shared xHi xLo hlookup)
  let intoStore :=
    Finmap.insert "expr_4557_self" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "expr_4556" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "_13" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "var__4550" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "zero_t_uint256_12" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "var_x_4547" (EvmYul.UInt256.ofNat 0)
                (Inhabited.default : EvmYul.Yul.VarStore))))))
  have hinto :=
    call_fun_into_182_from0_5591_raw_direct (xHi := xHi) (xLo := xLo)
      (fuel := fuel) (shared := shared) (store := intoStore)
      (hlookup := hlookup) (hactive := hactive)
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.store,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    hzero, hinto, zeroStore, intoStore, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    call_cleanup_t_uint256_5581_direct
      (fuel := fuel) (shared := sharedAfterFrom0 shared xHi xLo)
      (hlookup := sharedAfterFrom0_lookup shared xHi xLo hlookup),
    call_convert_t_rational_0_by_1_to_t_uint256_5583_direct
      (fuel := fuel) (shared := sharedAfterFrom0 shared xHi xLo)
      (hlookup := sharedAfterFrom0_lookup shared xHi xLo hlookup)]
  by_cases hcond : FormalYul.evmEq xHi 0 = 0
  · have hxHi_pos : 0 < FormalYul.u256 xHi := by
      exact Nat.pos_of_ne_zero ((evmEq_zero_eq_zero_iff xHi).mp hcond)
    have hcondUInt :
        EvmYul.UInt256.eq (EvmYul.UInt256.ofNat xHi) (EvmYul.UInt256.ofNat 0) =
          ({ val := 0 } : EvmYul.UInt256) :=
      (uint256_eq_ofNat_zero_struct_zero_iff xHi).2 hcond
    let sqrtStore :=
      Finmap.insert "expr_4571" (EvmYul.UInt256.ofNat xLo)
        (Finmap.insert "_17" (EvmYul.UInt256.ofNat xLo)
          (Finmap.insert "expr_4570" (EvmYul.UInt256.ofNat xHi)
            (Finmap.insert "_16" (EvmYul.UInt256.ofNat xHi)
              (Finmap.insert "expr_4562" ({ val := 0 } : EvmYul.UInt256)
                (Finmap.insert "expr_4561" (EvmYul.UInt256.ofNat 0)
                  (Finmap.insert "expr_4560" (EvmYul.UInt256.ofNat xHi)
                    (Finmap.insert "_14" (EvmYul.UInt256.ofNat xHi)
                      (Finmap.insert "var_x_lo_4555" (EvmYul.UInt256.ofNat xLo)
                        (Finmap.insert "var_x_hi_4553" (EvmYul.UInt256.ofNat xHi)
                          (Finmap.insert "expr_4558_component_1" (EvmYul.UInt256.ofNat xHi)
                            (Finmap.insert "expr_4558_component_2" (EvmYul.UInt256.ofNat xLo)
                              (Finmap.insert "expr_4557_self" (EvmYul.UInt256.ofNat 0)
                                (Finmap.insert "expr_4556" (EvmYul.UInt256.ofNat 0)
                                  (Finmap.insert "_13" (EvmYul.UInt256.ofNat 0)
                                    (Finmap.insert "var__4550" (EvmYul.UInt256.ofNat 0)
                                      (Finmap.insert "zero_t_uint256_12" (EvmYul.UInt256.ofNat 0)
                                        (Finmap.insert "var_x_4547" (EvmYul.UInt256.ofNat 0)
                                          (Inhabited.default : EvmYul.Yul.VarStore))))))))))))))))))
    have hcall :=
      call_fun__sqrt512_5579_from0_raw_direct (xHi := xHi) (xLo := xLo)
        (fuel := fuel) (shared := shared) (store := sqrtStore)
        (hlookup := hlookup) (hxHi_pos := hxHi_pos)
    simp +decide [hcondUInt, hcall, sqrtStore,
      EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
      Finmap.lookup_insert]
  · have hhi : FormalYul.u256 xHi = 0 := by
      by_contra hne
      exact hcond ((evmEq_zero_eq_zero_iff xHi).mpr hne)
    have hcondUInt :
        EvmYul.UInt256.eq (EvmYul.UInt256.ofNat xHi) (EvmYul.UInt256.ofNat 0) =
          EvmYul.UInt256.ofNat 1 :=
      uint256_eq_ofNat_zero_eq_one_of_u256_eq_zero xHi hhi
    have hbranch : floorSqrt (FormalYul.u256 xLo) = natSqrt (uint512 xHi xLo) :=
      sqrt512_zero_high_eq_natSqrt xHi xLo hhi
    let sqrtStore :=
      Finmap.insert "expr_4564_self" (EvmYul.UInt256.ofNat xLo)
        (Finmap.insert "expr_4563" (EvmYul.UInt256.ofNat xLo)
          (Finmap.insert "_15" (EvmYul.UInt256.ofNat xLo)
            (Finmap.insert "expr_4562" (EvmYul.UInt256.ofNat 1)
              (Finmap.insert "expr_4561" (EvmYul.UInt256.ofNat 0)
                (Finmap.insert "expr_4560" (EvmYul.UInt256.ofNat xHi)
                  (Finmap.insert "_14" (EvmYul.UInt256.ofNat xHi)
                    (Finmap.insert "var_x_lo_4555" (EvmYul.UInt256.ofNat xLo)
                      (Finmap.insert "var_x_hi_4553" (EvmYul.UInt256.ofNat xHi)
                        (Finmap.insert "expr_4558_component_1" (EvmYul.UInt256.ofNat xHi)
                          (Finmap.insert "expr_4558_component_2" (EvmYul.UInt256.ofNat xLo)
                            (Finmap.insert "expr_4557_self" (EvmYul.UInt256.ofNat 0)
                              (Finmap.insert "expr_4556" (EvmYul.UInt256.ofNat 0)
                                (Finmap.insert "_13" (EvmYul.UInt256.ofNat 0)
                                  (Finmap.insert "var__4550" (EvmYul.UInt256.ofNat 0)
                                    (Finmap.insert "zero_t_uint256_12" (EvmYul.UInt256.ofNat 0)
                                      (Finmap.insert "var_x_4547" (EvmYul.UInt256.ofNat 0)
                                        (Inhabited.default : EvmYul.Yul.VarStore)))))))))))))))))
    have hcall :=
      call_fun_sqrt256_5579_from0_raw_direct (xHi := xHi) (xLo := xLo)
        (fuel := fuel) (shared := shared) (store := sqrtStore)
        (hlookup := hlookup)
    simp +decide [hcondUInt, hcall, hbranch, sqrtStore,
      EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
      Finmap.lookup_insert,
      FormalYul.Preservation.call_on_checkpoint (fuel := fuel) (extra := 5578)]

private theorem call_fun_wrap_sqrt512_direct
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    EvmYul.Yul.call (fuel + 5800) [FormalYul.word xHi, FormalYul.word xLo]
      (.some yulName_fun_wrap_sqrt512) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [FormalYul.word (natSqrt (uint512 xHi xLo))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_wrap_sqrt512]
  simp only [yulFunction_fun_wrap_sqrt512, yulFunction_fun_wrap_sqrt512_6228,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let paramStore :=
    Finmap.insert "var_x_hi_6211" (EvmYul.UInt256.ofNat xHi)
      (Finmap.insert "var_x_lo_6213" (EvmYul.UInt256.ofNat xLo)
        (Inhabited.default : EvmYul.Yul.VarStore))
  have hzero :
      EvmYul.Yul.call (fuel + 5796) [] (.some "zero_value_for_split_t_uint256")
        (.some yulContract) (EvmYul.Yul.State.Ok shared paramStore) =
      .ok (EvmYul.Yul.State.Ok shared paramStore, [FormalYul.word 0]) := by
    simpa [paramStore] using
      call_zero_value_for_split_t_uint256_direct
        (fuel := fuel) (extra := 5776) (shared := shared) (store := paramStore)
        (hlookup := hlookup)
  let tmpStore :=
    Finmap.insert "var__6216" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "zero_t_uint256_1" (EvmYul.UInt256.ofNat 0) paramStore)
  have htmp :
      EvmYul.Yul.call (fuel + 5794) [] (.some "fun_tmp_128") (.some yulContract)
        (EvmYul.Yul.State.Ok shared tmpStore) =
      .ok (EvmYul.Yul.State.Ok shared tmpStore, [FormalYul.word 0]) := by
    simpa [tmpStore, FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_tmp_128_direct (fuel := fuel + 5754) (shared := shared)
        (store := tmpStore) (hlookup := hlookup)
  let fromStore :=
    Finmap.insert "expr_6222" (EvmYul.UInt256.ofNat xLo)
      (Finmap.insert "_3" (EvmYul.UInt256.ofNat xLo)
        (Finmap.insert "expr_6221" (EvmYul.UInt256.ofNat xHi)
          (Finmap.insert "_2" (EvmYul.UInt256.ofNat xHi)
            (Finmap.insert "expr_6220_self" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "expr_6219" (EvmYul.UInt256.ofNat 0) tmpStore)))))
  have hfrom :
      EvmYul.Yul.call (fuel + 5788)
        [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
        (.some "fun_from_156") (.some yulContract)
        (EvmYul.Yul.State.Ok shared fromStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) fromStore,
        [EvmYul.UInt256.ofNat 0]) := by
    simpa [fromStore, FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_from_156_zero_raw_direct (xHi := xHi) (xLo := xLo)
        (fuel := fuel + 5688) (shared := shared) (store := fromStore)
        (hlookup := hlookup)
  let sqrtStore :=
    Finmap.insert "expr_6224_self" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "expr_6223" (EvmYul.UInt256.ofNat 0) fromStore)
  have hsqrt :
      EvmYul.Yul.call (fuel + 5786) [EvmYul.UInt256.ofNat 0]
        (.some yulName_fun_sqrt512) (.some yulContract)
        (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) sqrtStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) sqrtStore,
        [EvmYul.UInt256.ofNat (natSqrt (uint512 xHi xLo))]) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_sqrt512_from0_raw_direct (xHi := xHi) (xLo := xLo)
        (fuel := fuel + 186) (shared := shared) (store := sqrtStore)
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
    hzero, htmp, hfrom, hsqrt, paramStore, tmpStore, fromStore, sqrtStore,
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

private theorem call_abi_encode_tuple_t_uint256_t_uint256__to_t_uint256_t_uint256__fromStack_direct
    (pos value0 value1 : EvmYul.UInt256) (fuel : Nat)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 220) [pos, value0, value1]
      (.some "abi_encode_tuple_t_uint256_t_uint256__to_t_uint256_t_uint256__fromStack")
      (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok
      ((EvmYul.Yul.State.Ok shared store).setMachineState
        (((EvmYul.Yul.State.Ok shared store).toMachineState.mstore pos value0).mstore
          (pos + EvmYul.UInt256.ofNat 32) value1),
        [pos + EvmYul.UInt256.ofNat 64]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_abi_encode_tuple_t_uint256_t_uint256__to_t_uint256_t_uint256__fromStack]
  simp only [yulFunction_abi_encode_tuple_t_uint256_t_uint256__to_t_uint256_t_uint256__fromStack,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let encStore : EvmYul.Yul.VarStore :=
    Finmap.insert "tail" (pos + EvmYul.UInt256.ofNat 64)
      (Finmap.insert "headStart" pos
        (Finmap.insert "value0" value0
          (Finmap.insert "value1" value1 (Inhabited.default : EvmYul.Yul.VarStore))))
  have hencode0 :
      EvmYul.Yul.call (fuel + 215) [value0, pos]
        (.some "abi_encode_t_uint256_to_t_uint256_fromStack") (.some yulContract)
        (EvmYul.Yul.State.Ok shared encStore) =
      .ok ((EvmYul.Yul.State.Ok shared encStore).setMachineState
          ((EvmYul.Yul.State.Ok shared encStore).toMachineState.mstore pos value0), []) := by
    simpa [encStore, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_abi_encode_t_uint256_to_t_uint256_fromStack_direct
        (value := value0) (pos := pos) (fuel := fuel + 135)
        (shared := shared) (store := encStore) (hlookup := hlookup)
  let firstShared : EvmYul.SharedState .Yul :=
    { shared with toMachineState := shared.toMachineState.mstore pos value0 }
  have hencode1 :
      EvmYul.Yul.call (fuel + 214) [value1, pos + EvmYul.UInt256.ofNat 32]
        (.some "abi_encode_t_uint256_to_t_uint256_fromStack") (.some yulContract)
        (EvmYul.Yul.State.Ok firstShared encStore) =
      .ok ((EvmYul.Yul.State.Ok firstShared encStore).setMachineState
          ((EvmYul.Yul.State.Ok firstShared encStore).toMachineState.mstore
            (pos + EvmYul.UInt256.ofNat 32) value1), []) := by
    simpa [firstShared, encStore, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_abi_encode_t_uint256_to_t_uint256_fromStack_direct
        (value := value1) (pos := pos + EvmYul.UInt256.ofNat 32) (fuel := fuel + 134)
        (shared := firstShared) (store := encStore)
        (hlookup := by simpa [firstShared] using hlookup)
  simp +decide [EvmYul.Yul.exec.eq_def, EvmYul.Yul.eval.eq_def,
    EvmYul.Yul.evalArgs.eq_def, EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.setMachineState, EvmYul.Yul.State.toMachineState,
    hencode0, hencode1, encStore, firstShared,
    Finmap.lookup_insert]

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

private def sqrt512SharedAfterFreePtr (xHi xLo : Nat) : EvmYul.SharedState .Yul :=
  let shared := FormalYul.sharedFor yulContract
    (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])
  { shared with toMachineState := shared.toMachineState.mstore (FormalYul.word 64) (FormalYul.word 128) }

private def osqrtUpSharedAfterFreePtr (xHi xLo : Nat) : EvmYul.SharedState .Yul :=
  let shared := FormalYul.sharedFor yulContract
    (selector_osqrtUp ++ FormalYul.encodeWords [xHi, xLo])
  { shared with toMachineState := shared.toMachineState.mstore (FormalYul.word 64) (FormalYul.word 128) }

private def osqrtUpSharedAfterAlloc (xHi xLo : Nat) : EvmYul.SharedState .Yul :=
  sharedAfterAlloc128 (osqrtUpSharedAfterFreePtr xHi xLo)

private def osqrtUpSharedAfterInput (xHi xLo : Nat) : EvmYul.SharedState .Yul :=
  sharedAfterFrom128 (osqrtUpSharedAfterAlloc xHi xLo) xHi xLo

private theorem sharedFor_inherited_mstore_mk_eq_sqrt512SharedAfterFreePtr
    (xHi xLo : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract
          (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])).toState
        ((FormalYul.sharedFor yulContract
          (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])).mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      sqrt512SharedAfterFreePtr xHi xLo := rfl

private theorem sharedFor_inherited_mstore_mk_eq_sqrt512SharedAfterFreePtr_raw
    (xHi xLo : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract
          (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])).toState
        ((FormalYul.sharedFor yulContract
          (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])).mstore
          (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128))) =
      sqrt512SharedAfterFreePtr xHi xLo := by
  simpa [FormalYul.word] using
    sharedFor_inherited_mstore_mk_eq_sqrt512SharedAfterFreePtr xHi xLo

private theorem sharedFor_inherited_mstore_mk_eq_osqrtUpSharedAfterFreePtr
    (xHi xLo : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract
          (selector_osqrtUp ++ FormalYul.encodeWords [xHi, xLo])).toState
        ((FormalYul.sharedFor yulContract
          (selector_osqrtUp ++ FormalYul.encodeWords [xHi, xLo])).mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      osqrtUpSharedAfterFreePtr xHi xLo := rfl

private theorem sharedFor_inherited_mstore_mk_eq_osqrtUpSharedAfterFreePtr_raw
    (xHi xLo : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract
          (selector_osqrtUp ++ FormalYul.encodeWords [xHi, xLo])).toState
        ((FormalYul.sharedFor yulContract
          (selector_osqrtUp ++ FormalYul.encodeWords [xHi, xLo])).mstore
          (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128))) =
      osqrtUpSharedAfterFreePtr xHi xLo := by
  simpa [FormalYul.word] using
    sharedFor_inherited_mstore_mk_eq_osqrtUpSharedAfterFreePtr xHi xLo

@[simp] private theorem sqrt512SharedAfterFreePtr_lookup (xHi xLo : Nat) :
    (sqrt512SharedAfterFreePtr xHi xLo).accountMap.find?
      (sqrt512SharedAfterFreePtr xHi xLo).executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract) := by
  simp [sqrt512SharedAfterFreePtr]

@[simp] private theorem osqrtUpSharedAfterFreePtr_lookup (xHi xLo : Nat) :
    (osqrtUpSharedAfterFreePtr xHi xLo).accountMap.find?
      (osqrtUpSharedAfterFreePtr xHi xLo).executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract) := by
  simp [osqrtUpSharedAfterFreePtr]

@[simp] private theorem sqrt512SharedAfterFreePtr_calldata (xHi xLo : Nat) :
    (sqrt512SharedAfterFreePtr xHi xLo).executionEnv.calldata =
      selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo] := by
  simp [sqrt512SharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp] private theorem osqrtUpSharedAfterFreePtr_calldata (xHi xLo : Nat) :
    (osqrtUpSharedAfterFreePtr xHi xLo).executionEnv.calldata =
      selector_osqrtUp ++ FormalYul.encodeWords [xHi, xLo] := by
  simp [osqrtUpSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp] private theorem sqrt512SharedAfterFreePtr_weiValue (xHi xLo : Nat) :
    (sqrt512SharedAfterFreePtr xHi xLo).executionEnv.weiValue =
      ({ val := 0 } : EvmYul.UInt256) := by
  simp [sqrt512SharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp] private theorem osqrtUpSharedAfterFreePtr_weiValue (xHi xLo : Nat) :
    (osqrtUpSharedAfterFreePtr xHi xLo).executionEnv.weiValue =
      ({ val := 0 } : EvmYul.UInt256) := by
  simp [osqrtUpSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp] private theorem sqrt512_calldata_size (xHi xLo : Nat) :
    (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo]).size = 68 := by
  have hHi : (FormalYul.encodeWord xHi).size = 32 := by
    change (FormalYul.encodeWord xHi).data.size = 32
    rw [← Array.length_toList]
    simp [FormalYul.Preservation.encodeWord_data_toList]
  have hLo : (FormalYul.encodeWord xLo).size = 32 := by
    change (FormalYul.encodeWord xLo).data.size = 32
    rw [← Array.length_toList]
    simp [FormalYul.Preservation.encodeWord_data_toList]
  simp [selector_sqrt512, FormalYul.encodeWords,
    FormalYul.bytes, ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
    hHi, hLo]

@[simp] private theorem osqrtUp_calldata_size (xHi xLo : Nat) :
    (selector_osqrtUp ++ FormalYul.encodeWords [xHi, xLo]).size = 68 := by
  have hHi : (FormalYul.encodeWord xHi).size = 32 := by
    change (FormalYul.encodeWord xHi).data.size = 32
    rw [← Array.length_toList]
    simp [FormalYul.Preservation.encodeWord_data_toList]
  have hLo : (FormalYul.encodeWord xLo).size = 32 := by
    change (FormalYul.encodeWord xLo).data.size = 32
    rw [← Array.length_toList]
    simp [FormalYul.Preservation.encodeWord_data_toList]
  simp [selector_osqrtUp, FormalYul.encodeWords,
    FormalYul.bytes, ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
    hHi, hLo]

@[simp] private theorem sqrt512SharedAfterFreePtr_activeWords (xHi xLo : Nat) :
    (sqrt512SharedAfterFreePtr xHi xLo).toMachineState.activeWords = FormalYul.word 3 := by
  simp [sqrt512SharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor,
    EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord, EvmYul.MachineState.M,
    FormalYul.word]
  decide

@[simp] private theorem osqrtUpSharedAfterFreePtr_activeWords (xHi xLo : Nat) :
    (osqrtUpSharedAfterFreePtr xHi xLo).toMachineState.activeWords = FormalYul.word 3 := by
  simp [osqrtUpSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor,
    EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord, EvmYul.MachineState.M,
    FormalYul.word]
  decide

@[simp] private theorem sqrt512SharedAfterFreePtr_mload64 (xHi xLo : Nat) :
    ((sqrt512SharedAfterFreePtr xHi xLo).mload (FormalYul.word 64)).1 =
      FormalYul.word 128 := by
  exact FormalYul.Preservation.sharedFor_mload_freePtr_after_mstore yulContract
    (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])

@[simp] private theorem osqrtUpSharedAfterFreePtr_mload64 (xHi xLo : Nat) :
    ((osqrtUpSharedAfterFreePtr xHi xLo).mload (FormalYul.word 64)).1 =
      FormalYul.word 128 := by
  exact FormalYul.Preservation.sharedFor_mload_freePtr_after_mstore yulContract
    (selector_osqrtUp ++ FormalYul.encodeWords [xHi, xLo])

@[simp] private theorem osqrtUpSharedAfterFreePtr_mload64_state (xHi xLo : Nat) :
    ((osqrtUpSharedAfterFreePtr xHi xLo).mload (FormalYul.word 64)).2 =
      (osqrtUpSharedAfterFreePtr xHi xLo).toMachineState := by
  simp [osqrtUpSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor,
    EvmYul.MachineState.mload, EvmYul.MachineState.mstore,
    EvmYul.MachineState.writeWord, EvmYul.writeBytes, EvmYul.MachineState.M,
    FormalYul.word]
  decide

@[simp] private theorem sharedAfterAlloc128_activeWords
    (shared : EvmYul.SharedState .Yul)
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    (sharedAfterAlloc128 shared).toMachineState.activeWords = FormalYul.word 3 := by
  simp [sharedAfterAlloc128, EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord,
    EvmYul.writeBytes, EvmYul.MachineState.M, FormalYul.word, hactive]
  decide

@[simp] private theorem osqrtUpSharedAfterAlloc_activeWords (xHi xLo : Nat) :
    (osqrtUpSharedAfterAlloc xHi xLo).toMachineState.activeWords = FormalYul.word 3 := by
  simp [osqrtUpSharedAfterAlloc]

@[simp] private theorem osqrtUpSharedAfterAlloc_memory_size (xHi xLo : Nat) :
    (osqrtUpSharedAfterAlloc xHi xLo).toMachineState.memory.size = 96 := by
  simp [osqrtUpSharedAfterAlloc, sharedAfterAlloc128, osqrtUpSharedAfterFreePtr,
    FormalYul.sharedFor, FormalYul.envFor, EvmYul.MachineState.mstore,
    EvmYul.MachineState.writeWord, EvmYul.writeBytes, ByteArray.write,
    ByteArray.size, FormalYul.word, EvmYul.UInt256.toNat, EvmYul.UInt256.ofNat,
    EvmYul.UInt256.size, Inhabited.default, EvmYul.UInt256.toByteArray]

@[simp] private theorem osqrtUpSharedAfterAlloc_read64 (xHi xLo : Nat) :
    (osqrtUpSharedAfterAlloc xHi xLo).toMachineState.memory.readWithPadding 64 32 =
      (FormalYul.word 192).toByteArray := by
  unfold osqrtUpSharedAfterAlloc sharedAfterAlloc128
  change ((FormalYul.word 192).toByteArray.write 0
      (osqrtUpSharedAfterFreePtr xHi xLo).memory 64 32).readWithPadding 64 32 =
    (FormalYul.word 192).toByteArray
  exact FormalYul.Preservation.readWithPadding_write_same_of_size
    (FormalYul.word 192).toByteArray (osqrtUpSharedAfterFreePtr xHi xLo).memory 64
    (by simp)

@[simp] private theorem osqrtUpSharedAfterInput_activeWords (xHi xLo : Nat) :
    (osqrtUpSharedAfterInput xHi xLo).toMachineState.activeWords = FormalYul.word 6 := by
  simpa [osqrtUpSharedAfterInput, sharedAfterFrom128] using
    FormalYul.Preservation.mstore_two_word_128_active_6
      (osqrtUpSharedAfterAlloc xHi xLo).toMachineState
      (FormalYul.word xHi) (FormalYul.word xLo)
      (osqrtUpSharedAfterAlloc_activeWords xHi xLo)

@[simp] private theorem osqrtUpSharedAfterInput_memory_size (xHi xLo : Nat) :
    (osqrtUpSharedAfterInput xHi xLo).toMachineState.memory.size = 192 := by
  unfold osqrtUpSharedAfterInput sharedAfterFrom128
  change (((osqrtUpSharedAfterAlloc xHi xLo).toMachineState.mstore (FormalYul.word 128)
      (FormalYul.word xHi)).mstore (FormalYul.word 160) (FormalYul.word xLo)).memory.size = 192
  unfold EvmYul.MachineState.mstore EvmYul.MachineState.writeWord EvmYul.writeBytes
  simp only [FormalYul.word]
  have hfirst :
      ((EvmYul.UInt256.ofNat xHi).toByteArray.write 0
        (osqrtUpSharedAfterAlloc xHi xLo).memory 128 32).size = 160 := by
    apply FormalYul.Preservation.write32_size_of_size_le_addr
    · simp
    · rw [osqrtUpSharedAfterAlloc_memory_size]
      omega
  apply FormalYul.Preservation.write32_size_of_size_le_addr
  · simp
  · change ((EvmYul.UInt256.ofNat xHi).toByteArray.write 0
        (osqrtUpSharedAfterAlloc xHi xLo).memory 128 32).size ≤ 160
    rw [hfirst]

@[simp] private theorem osqrtUpSharedAfterInput_read64 (xHi xLo : Nat) :
    (osqrtUpSharedAfterInput xHi xLo).toMachineState.memory.readWithPadding 64 32 =
      (FormalYul.word 192).toByteArray := by
  unfold osqrtUpSharedAfterInput sharedAfterFrom128
  change ((FormalYul.word xLo).toByteArray.write 0
      ((FormalYul.word xHi).toByteArray.write 0
        (osqrtUpSharedAfterAlloc xHi xLo).memory 128 32) 160 32).readWithPadding 64 32 =
    (FormalYul.word 192).toByteArray
  have hfirst :
      ((FormalYul.word xHi).toByteArray.write 0
        (osqrtUpSharedAfterAlloc xHi xLo).memory 128 32).size = 160 := by
    apply FormalYul.Preservation.write32_size_of_size_le_addr
    · simp
    · rw [osqrtUpSharedAfterAlloc_memory_size]
      omega
  rw [FormalYul.Preservation.readWithPadding_64_32_write160_preserve_of_size_160
    (FormalYul.word xLo).toByteArray
    ((FormalYul.word xHi).toByteArray.write 0
      (osqrtUpSharedAfterAlloc xHi xLo).memory 128 32)
    (by simp) hfirst]
  rw [FormalYul.Preservation.readWithPadding_64_32_write128_preserve_of_size_96
    (FormalYul.word xHi).toByteArray
    (osqrtUpSharedAfterAlloc xHi xLo).memory
    (by simp) (osqrtUpSharedAfterAlloc_memory_size xHi xLo)]
  exact osqrtUpSharedAfterAlloc_read64 xHi xLo

@[simp] private theorem osqrtUpSharedAfterInput_mload64 (xHi xLo : Nat) :
    ((osqrtUpSharedAfterInput xHi xLo).mload (FormalYul.word 64)).1 =
      FormalYul.word 192 := by
  unfold EvmYul.MachineState.mload EvmYul.MachineState.lookupMemory
  simp only [FormalYul.word]
  have hcond :
      ¬ ((EvmYul.UInt256.ofNat 64).toNat ≥
            (osqrtUpSharedAfterInput xHi xLo).toMachineState.memory.size ∨
          EvmYul.UInt256.ofNat 64 ≥
            (osqrtUpSharedAfterInput xHi xLo).toMachineState.activeWords *
              ({ val := 32 } : EvmYul.UInt256)) := by
    intro h
    cases h with
    | inl hmem =>
      rw [osqrtUpSharedAfterInput_memory_size] at hmem
      norm_num [EvmYul.UInt256.ofNat, EvmYul.UInt256.toNat, EvmYul.UInt256.size] at hmem
    | inr hactiveMem =>
      rw [osqrtUpSharedAfterInput_activeWords] at hactiveMem
      exact
        (by decide :
            ¬ (({ val := (64 : Fin EvmYul.UInt256.size) } : EvmYul.UInt256) ≥
              (({ val := 6 } : EvmYul.UInt256) * ({ val := 32 } : EvmYul.UInt256)))) hactiveMem
  rw [if_neg hcond]
  change EvmYul.UInt256.ofNat
      (EvmYul.fromByteArrayBigEndian
        ((osqrtUpSharedAfterInput xHi xLo).memory.readWithPadding 64 32)) =
    EvmYul.UInt256.ofNat 192
  rw [osqrtUpSharedAfterInput_read64]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  rw [FormalYul.Preservation.wordNat_ofNat]
  rw [EvmYul.UInt256.fromByteArrayBigEndian_toByteArray]
  rfl

@[simp] private theorem osqrtUpSharedAfterInput_mload64_state (xHi xLo : Nat) :
    ((osqrtUpSharedAfterInput xHi xLo).mload (FormalYul.word 64)).2 =
      (osqrtUpSharedAfterInput xHi xLo).toMachineState := by
  let m := (osqrtUpSharedAfterInput xHi xLo).toMachineState
  have hactive : m.activeWords = FormalYul.word 6 := by
    simp [m]
  change (m.mload (FormalYul.word 64)).2 = m
  exact FormalYul.Preservation.mload64_state_active_6 m hactive

@[simp] private theorem osqrtUpSharedAfterInput_mload128_state (xHi xLo : Nat) :
    ((osqrtUpSharedAfterInput xHi xLo).mload (FormalYul.word 128)).2 =
      (osqrtUpSharedAfterInput xHi xLo).toMachineState := by
  simpa [osqrtUpSharedAfterInput, sharedAfterFrom128] using
    FormalYul.Preservation.mload_two_word_write_128_first_state
      (osqrtUpSharedAfterAlloc xHi xLo).toMachineState
      (FormalYul.word xHi) (FormalYul.word xLo)
      (osqrtUpSharedAfterAlloc_activeWords xHi xLo)

@[simp] private theorem osqrtUpSharedAfterInput_mload160_state (xHi xLo : Nat) :
    ((osqrtUpSharedAfterInput xHi xLo).toMachineState.mload (FormalYul.word 160)).2 =
      (osqrtUpSharedAfterInput xHi xLo).toMachineState := by
  simpa [osqrtUpSharedAfterInput, sharedAfterFrom128] using
    FormalYul.Preservation.mload_two_word_write_128_second_state
      (osqrtUpSharedAfterAlloc xHi xLo).toMachineState
      (FormalYul.word xHi) (FormalYul.word xLo)
      (osqrtUpSharedAfterAlloc_activeWords xHi xLo)

@[simp] private theorem osqrtUpSharedAfterInput_mload128 (xHi xLo : Nat) :
    ((osqrtUpSharedAfterInput xHi xLo).mload (FormalYul.word 128)).1 =
      FormalYul.word xHi := by
  simpa [osqrtUpSharedAfterInput, sharedAfterFrom128] using
    FormalYul.Preservation.mload_two_word_write_128_first_of_size_le
      (osqrtUpSharedAfterAlloc xHi xLo).toMachineState
      (FormalYul.word xHi) (FormalYul.word xLo)
      (osqrtUpSharedAfterAlloc_activeWords xHi xLo)
      (osqrtUpSharedAfterAlloc_memory_size xHi xLo)

@[simp] private theorem osqrtUpSharedAfterInput_mload160 (xHi xLo : Nat) :
    ((osqrtUpSharedAfterInput xHi xLo).toMachineState.mload (FormalYul.word 160)).1 =
      FormalYul.word xLo := by
  simpa [osqrtUpSharedAfterInput, sharedAfterFrom128] using
    FormalYul.Preservation.mload_two_word_write_128_second_of_size_le
      (osqrtUpSharedAfterAlloc xHi xLo).toMachineState
      (FormalYul.word xHi) (FormalYul.word xLo)
      (osqrtUpSharedAfterAlloc_activeWords xHi xLo)

@[simp] private theorem osqrtUpSharedAfterInput_lookup (xHi xLo : Nat) :
    (osqrtUpSharedAfterInput xHi xLo).accountMap.find?
        (osqrtUpSharedAfterInput xHi xLo).executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract) := by
  simp [osqrtUpSharedAfterInput, osqrtUpSharedAfterAlloc, sharedAfterFrom128,
    sharedAfterAlloc128]

@[simp] private theorem sharedAfterFrom0_osqrt_activeWords (xHi xLo rHi rLo : Nat) :
    (sharedAfterFrom0 (osqrtUpSharedAfterInput xHi xLo) rHi rLo).toMachineState.activeWords =
      FormalYul.word 6 := by
  simpa [sharedAfterFrom0] using
    FormalYul.Preservation.mstore_two_word_active_6
      (osqrtUpSharedAfterInput xHi xLo).toMachineState
      (FormalYul.word rHi) (FormalYul.word rLo)
      (osqrtUpSharedAfterInput_activeWords xHi xLo)

@[simp] private theorem sharedAfterFrom0_osqrt_memory_size (xHi xLo rHi rLo : Nat) :
    (sharedAfterFrom0 (osqrtUpSharedAfterInput xHi xLo) rHi rLo).toMachineState.memory.size =
      192 := by
  unfold sharedAfterFrom0
  change (((osqrtUpSharedAfterInput xHi xLo).toMachineState.mstore (FormalYul.word 0)
      (FormalYul.word rHi)).mstore (FormalYul.word 32) (FormalYul.word rLo)).memory.size = 192
  unfold EvmYul.MachineState.mstore EvmYul.MachineState.writeWord EvmYul.writeBytes
  simp only [FormalYul.word]
  have hfirst :
      ((EvmYul.UInt256.ofNat rHi).toByteArray.write 0
        (osqrtUpSharedAfterInput xHi xLo).memory 0 32).size = 192 := by
    have h := FormalYul.Preservation.write32_size_of_addr_add_le_size
      (EvmYul.UInt256.ofNat rHi).toByteArray (osqrtUpSharedAfterInput xHi xLo).memory 0
      (by simp)
      (by rw [osqrtUpSharedAfterInput_memory_size]; omega)
    simpa using h
  have h := FormalYul.Preservation.write32_size_of_addr_add_le_size
    (EvmYul.UInt256.ofNat rLo).toByteArray
    ((EvmYul.UInt256.ofNat rHi).toByteArray.write 0
      (osqrtUpSharedAfterInput xHi xLo).memory 0 32) 32
    (by simp)
    (by rw [hfirst]; omega)
  change ((EvmYul.UInt256.ofNat rLo).toByteArray.write 0
      ((EvmYul.UInt256.ofNat rHi).toByteArray.write 0
        (osqrtUpSharedAfterInput xHi xLo).memory 0 32) 32 32).size = 192
  rw [h]
  exact hfirst

@[simp] private theorem sharedAfterFrom0_osqrt_read64 (xHi xLo rHi rLo : Nat) :
    (sharedAfterFrom0 (osqrtUpSharedAfterInput xHi xLo) rHi rLo).toMachineState.memory.readWithPadding
        64 32 =
      (FormalYul.word 192).toByteArray := by
  unfold sharedAfterFrom0
  change ((FormalYul.word rLo).toByteArray.write 0
      ((FormalYul.word rHi).toByteArray.write 0
        (osqrtUpSharedAfterInput xHi xLo).memory 0 32) 32 32).readWithPadding 64 32 =
    (FormalYul.word 192).toByteArray
  have hfirst :
      ((FormalYul.word rHi).toByteArray.write 0
        (osqrtUpSharedAfterInput xHi xLo).memory 0 32).size = 192 := by
    have h := FormalYul.Preservation.write32_size_of_addr_add_le_size
      (FormalYul.word rHi).toByteArray (osqrtUpSharedAfterInput xHi xLo).memory 0
      (by simp)
      (by rw [osqrtUpSharedAfterInput_memory_size]; omega)
    simpa [osqrtUpSharedAfterInput_memory_size xHi xLo] using h
  rw [FormalYul.Preservation.readWithPadding_64_32_write32_preserve_of_size_192
    (FormalYul.word rLo).toByteArray
    ((FormalYul.word rHi).toByteArray.write 0
      (osqrtUpSharedAfterInput xHi xLo).memory 0 32)
    (by simp) hfirst]
  rw [FormalYul.Preservation.readWithPadding_64_32_write0_preserve_of_size_192
    (FormalYul.word rHi).toByteArray
    (osqrtUpSharedAfterInput xHi xLo).memory
    (by simp) (osqrtUpSharedAfterInput_memory_size xHi xLo)]
  exact osqrtUpSharedAfterInput_read64 xHi xLo

@[simp] private theorem sharedAfterFrom0_osqrt_mload64 (xHi xLo rHi rLo : Nat) :
    ((sharedAfterFrom0 (osqrtUpSharedAfterInput xHi xLo) rHi rLo).mload
        (FormalYul.word 64)).1 =
      FormalYul.word 192 := by
  unfold EvmYul.MachineState.mload EvmYul.MachineState.lookupMemory
  simp only [FormalYul.word]
  have hcond :
      ¬ ((EvmYul.UInt256.ofNat 64).toNat ≥
            (sharedAfterFrom0 (osqrtUpSharedAfterInput xHi xLo) rHi rLo).toMachineState.memory.size ∨
          EvmYul.UInt256.ofNat 64 ≥
            (sharedAfterFrom0 (osqrtUpSharedAfterInput xHi xLo) rHi rLo).toMachineState.activeWords *
              ({ val := 32 } : EvmYul.UInt256)) := by
    intro h
    cases h with
    | inl hmem =>
      rw [sharedAfterFrom0_osqrt_memory_size] at hmem
      norm_num [EvmYul.UInt256.ofNat, EvmYul.UInt256.toNat, EvmYul.UInt256.size] at hmem
    | inr hactiveMem =>
      rw [sharedAfterFrom0_osqrt_activeWords] at hactiveMem
      exact
        (by decide :
            ¬ (({ val := (64 : Fin EvmYul.UInt256.size) } : EvmYul.UInt256) ≥
              (({ val := 6 } : EvmYul.UInt256) * ({ val := 32 } : EvmYul.UInt256)))) hactiveMem
  rw [if_neg hcond]
  change EvmYul.UInt256.ofNat
      (EvmYul.fromByteArrayBigEndian
        ((sharedAfterFrom0 (osqrtUpSharedAfterInput xHi xLo) rHi rLo).memory.readWithPadding
          64 32)) =
    EvmYul.UInt256.ofNat 192
  rw [sharedAfterFrom0_osqrt_read64]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  rw [FormalYul.Preservation.wordNat_ofNat]
  rw [EvmYul.UInt256.fromByteArrayBigEndian_toByteArray]
  rfl

@[simp] private theorem sharedAfterFrom0_osqrt_mload64_state (xHi xLo rHi rLo : Nat) :
    ((sharedAfterFrom0 (osqrtUpSharedAfterInput xHi xLo) rHi rLo).mload
        (FormalYul.word 64)).2 =
      (sharedAfterFrom0 (osqrtUpSharedAfterInput xHi xLo) rHi rLo).toMachineState := by
  let m := (sharedAfterFrom0 (osqrtUpSharedAfterInput xHi xLo) rHi rLo).toMachineState
  have hactive : m.activeWords = FormalYul.word 6 := by
    simp [m]
  change (m.mload (FormalYul.word 64)).2 = m
  exact FormalYul.Preservation.mload64_state_active_6 m hactive

private theorem call_fun_into_182_from128_osqrt_direct
    (xHi xLo fuel : Nat) (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.call (fuel + 120) [FormalYul.word 128]
      (.some "fun_into_182") (.some yulContract)
      (EvmYul.Yul.State.Ok (osqrtUpSharedAfterInput xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok (osqrtUpSharedAfterInput xHi xLo) store,
      [FormalYul.word xHi, FormalYul.word xLo]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [osqrtUpSharedAfterInput_lookup xHi xLo,
    Option.getD_some, yulContract_functions, lookup_fun_into_182]
  simp only [yulFunction_fun_into_182,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let hiZeroStore :=
    Finmap.insert "var_x_173" (EvmYul.UInt256.ofNat 128)
      (Inhabited.default : EvmYul.Yul.VarStore)
  have hzeroHi :
      EvmYul.Yul.call (fuel + 116) [] (.some "zero_value_for_split_t_uint256")
        (.some yulContract) (EvmYul.Yul.State.Ok (osqrtUpSharedAfterInput xHi xLo)
          hiZeroStore) =
      .ok (EvmYul.Yul.State.Ok (osqrtUpSharedAfterInput xHi xLo) hiZeroStore,
        [FormalYul.word 0]) := by
    simpa [hiZeroStore] using
      call_zero_value_for_split_t_uint256_direct
        (fuel := fuel) (extra := 96) (shared := osqrtUpSharedAfterInput xHi xLo)
        (store := hiZeroStore)
        (hlookup := osqrtUpSharedAfterInput_lookup xHi xLo)
  let loZeroStore :=
    Finmap.insert "var_r_hi_176" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "zero_t_uint256_38" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "var_x_173" (EvmYul.UInt256.ofNat 128)
          (Inhabited.default : EvmYul.Yul.VarStore)))
  have hzeroLo :
      EvmYul.Yul.call (fuel + 114) [] (.some "zero_value_for_split_t_uint256")
        (.some yulContract) (EvmYul.Yul.State.Ok (osqrtUpSharedAfterInput xHi xLo)
          loZeroStore) =
      .ok (EvmYul.Yul.State.Ok (osqrtUpSharedAfterInput xHi xLo) loZeroStore,
        [FormalYul.word 0]) := by
    simpa [loZeroStore] using
      call_zero_value_for_split_t_uint256_direct
        (fuel := fuel) (extra := 94) (shared := osqrtUpSharedAfterInput xHi xLo)
        (store := loZeroStore)
        (hlookup := osqrtUpSharedAfterInput_lookup xHi xLo)
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
  have haddr : EvmYul.UInt256.ofNat 32 + EvmYul.UInt256.ofNat 128 =
      EvmYul.UInt256.ofNat 160 := by
    decide
  have h128state :
      ((osqrtUpSharedAfterInput xHi xLo).mload (EvmYul.UInt256.ofNat 128)).2 =
        (osqrtUpSharedAfterInput xHi xLo).toMachineState := by
    simpa [FormalYul.word] using osqrtUpSharedAfterInput_mload128_state xHi xLo
  have h160state :
      ((osqrtUpSharedAfterInput xHi xLo).toMachineState.mload
          (EvmYul.UInt256.ofNat 160)).2 =
        (osqrtUpSharedAfterInput xHi xLo).toMachineState := by
    simpa [FormalYul.word] using osqrtUpSharedAfterInput_mload160_state xHi xLo
  have h128value :
      ((osqrtUpSharedAfterInput xHi xLo).mload (EvmYul.UInt256.ofNat 128)).1 =
        EvmYul.UInt256.ofNat xHi := by
    simpa [FormalYul.word] using osqrtUpSharedAfterInput_mload128 xHi xLo
  have h160value :
      ((osqrtUpSharedAfterInput xHi xLo).toMachineState.mload
          (EvmYul.UInt256.ofNat 160)).1 =
        EvmYul.UInt256.ofNat xLo := by
    simpa [FormalYul.word] using osqrtUpSharedAfterInput_mload160 xHi xLo
  constructor
  · rw [h128state, haddr, h160state]
  · constructor
    · exact h128value
    · rw [h128state, haddr]
      exact h160value

@[simp] private theorem call_fun_into_182_from128_osqrt_raw_direct
    (xHi xLo fuel extra : Nat) (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.call (fuel + (extra + 120)) [EvmYul.UInt256.ofNat 128]
      (.some "fun_into_182") (.some yulContract)
      (EvmYul.Yul.State.Ok (osqrtUpSharedAfterInput xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok (osqrtUpSharedAfterInput xHi xLo) store,
      [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_into_182_from128_osqrt_direct (xHi := xHi) (xLo := xLo)
      (fuel := fuel + extra) (store := store)

private theorem call_fun_into_182_from0_active6_raw_direct
    (xHi xLo fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hactive : shared.toMachineState.activeWords = FormalYul.word 6) :
    EvmYul.Yul.call (fuel + (extra + 120)) [EvmYul.UInt256.ofNat 0]
      (.some "fun_into_182") (.some yulContract)
      (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [sharedAfterFrom0_lookup shared xHi xLo hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_into_182]
  simp only [yulFunction_fun_into_182,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let hiZeroStore :=
    Finmap.insert "var_x_173" (EvmYul.UInt256.ofNat 0)
      (Inhabited.default : EvmYul.Yul.VarStore)
  have hzeroHi :
      EvmYul.Yul.call (fuel + (extra + 116)) [] (.some "zero_value_for_split_t_uint256")
        (.some yulContract) (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo)
          hiZeroStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) hiZeroStore,
        [FormalYul.word 0]) := by
    simpa [hiZeroStore, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_zero_value_for_split_t_uint256_direct
        (fuel := fuel) (extra := extra + 96) (shared := sharedAfterFrom0 shared xHi xLo)
        (store := hiZeroStore)
        (hlookup := sharedAfterFrom0_lookup shared xHi xLo hlookup)
  let loZeroStore :=
    Finmap.insert "var_r_hi_176" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "zero_t_uint256_38" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "var_x_173" (EvmYul.UInt256.ofNat 0)
          (Inhabited.default : EvmYul.Yul.VarStore)))
  have hzeroLo :
      EvmYul.Yul.call (fuel + (extra + 114)) [] (.some "zero_value_for_split_t_uint256")
        (.some yulContract) (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo)
          loZeroStore) =
      .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) loZeroStore,
        [FormalYul.word 0]) := by
    simpa [loZeroStore, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_zero_value_for_split_t_uint256_direct
        (fuel := fuel) (extra := extra + 94) (shared := sharedAfterFrom0 shared xHi xLo)
        (store := loZeroStore)
        (hlookup := sharedAfterFrom0_lookup shared xHi xLo hlookup)
  simp +decide [EvmYul.Yul.exec.eq_def,
    EvmYul.Yul.execCall.eq_def, EvmYul.Yul.eval.eq_def,
    EvmYul.Yul.evalArgs.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
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
    simpa [FormalYul.word] using sharedAfterFrom0_mload0_state_active6 shared xHi xLo hactive
  have h32state :
      ((sharedAfterFrom0 shared xHi xLo).mload (EvmYul.UInt256.ofNat 32)).2 =
        (sharedAfterFrom0 shared xHi xLo).toMachineState := by
    simpa [FormalYul.word] using sharedAfterFrom0_mload32_state_active6 shared xHi xLo hactive
  have h0value :
      ((sharedAfterFrom0 shared xHi xLo).mload (EvmYul.UInt256.ofNat 0)).1 =
        EvmYul.UInt256.ofNat xHi := by
    simpa [FormalYul.word] using sharedAfterFrom0_mload0_active6 shared xHi xLo hactive
  have h32value :
      ((sharedAfterFrom0 shared xHi xLo).mload (EvmYul.UInt256.ofNat 32)).1 =
        EvmYul.UInt256.ofNat xLo := by
    simpa [FormalYul.word] using sharedAfterFrom0_mload32_active6 shared xHi xLo hactive
  constructor
  · rw [h0state, h32state]
  · constructor
    · exact h0value
    · rw [h0state]
      exact h32value

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

@[simp] private theorem uint256_add_sub_self_64 (p : EvmYul.UInt256) :
    p + EvmYul.UInt256.ofNat 64 - p = EvmYul.UInt256.ofNat 64 := by
  apply FormalYul.Preservation.eq_of_wordNat_eq
  change FormalYul.wordNat (p + EvmYul.UInt256.ofNat 64 - p) =
    FormalYul.wordNat (EvmYul.UInt256.ofNat 64)
  simp only [FormalYul.Preservation.wordNat_sub, FormalYul.Preservation.wordNat_add,
    FormalYul.Preservation.wordNat_ofNat]
  unfold FormalYul.evmAdd FormalYul.evmSub FormalYul.u256 FormalYul.WORD_MOD
  let n := FormalYul.wordNat p
  have hn : n < 2 ^ 256 := by
    change FormalYul.wordNat p < 2 ^ 256
    simp [FormalYul.wordNat, EvmYul.UInt256.toNat, EvmYul.UInt256.size]
  have hM64 : 64 < 2 ^ 256 := by norm_num
  change (((n % 2 ^ 256 + 64 % 2 ^ 256 % 2 ^ 256) % 2 ^ 256 % 2 ^ 256 +
      2 ^ 256 - n % 2 ^ 256) % 2 ^ 256) = 64 % 2 ^ 256
  rw [Nat.mod_eq_of_lt hn]
  rw [Nat.mod_eq_of_lt hM64]
  by_cases h : n + 64 < 2 ^ 256
  · rw [Nat.mod_eq_of_lt h]
    rw [Nat.mod_eq_of_lt h]
    have hsum : n + 64 + 2 ^ 256 - n = 2 ^ 256 + 64 := by omega
    rw [hsum]
    rw [Nat.add_mod_left]
    exact Nat.mod_eq_of_lt hM64
  · have hge : n + 64 ≥ 2 ^ 256 := by omega
    rw [Nat.mod_eq_sub_mod hge]
    have hsmall : n + 64 - 2 ^ 256 < 2 ^ 256 := by omega
    rw [Nat.mod_eq_of_lt hsmall]
    rw [Nat.mod_eq_of_lt hsmall]
    have hsum : n + 64 - 2 ^ 256 + 2 ^ 256 - n = 64 := by omega
    rw [hsum]

private theorem external_fun_wrap_sqrt512_calldata_result_999989
    (xHi xLo : Nat) (store : EvmYul.Yul.VarStore) :
    ((match
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_sqrt512) (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) store)
    with
    | .error (.YulHalt state _) => FormalYul.resultWord (FormalYul.returnOf state)
    | .error .Revert => .error "revert"
    | .error err => .error (reprStr err)
    | .ok (state, _) => FormalYul.resultWord (FormalYul.returnOf state)) :
      Except String Nat) =
      .ok (natSqrt (uint512 xHi xLo)) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [
    sqrt512SharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_sqrt512]
  simp only [yulFunction_external_fun_wrap_sqrt512, yulFunction_external_fun_wrap_sqrt512_6228,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := natSqrt (uint512 xHi xLo)
  let paramStore : EvmYul.Yul.VarStore :=
    Finmap.insert "param_0" (FormalYul.word xHi)
      (Finmap.insert "param_1" (FormalYul.word xLo)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let baseStore : EvmYul.Yul.VarStore :=
    Finmap.insert "ret_0" (FormalYul.word ret) paramStore
  let wrapShared := sharedAfterFrom0 (sqrt512SharedAfterFreePtr xHi xLo) xHi xLo
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
      (a := 0x3f) (b := 0x51) (c := 0x62) (d := 0x8a)
      (xHi := xHi) (xLo := xLo) (fuel := 999824)
      (shared := sqrt512SharedAfterFreePtr xHi xLo)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := sqrt512SharedAfterFreePtr_lookup xHi xLo)
      (hdata := by
        rw [sqrt512SharedAfterFreePtr_calldata]
        rfl)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_sqrt512_direct (xHi := xHi) (xLo := xLo) (fuel := 994183)
      (shared := sqrt512SharedAfterFreePtr xHi xLo) (store := paramStore)
      (hlookup := sqrt512SharedAfterFreePtr_lookup xHi xLo)
      (hactive := sqrt512SharedAfterFreePtr_activeWords xHi xLo)
  simp [FormalYul.word, yulName_fun_wrap_sqrt512, paramStore] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999952) (shared := wrapShared)
      (store := baseStore)
      (hlookup := sharedAfterFrom0_lookup (sqrt512SharedAfterFreePtr xHi xLo) xHi xLo
        (sqrt512SharedAfterFreePtr_lookup xHi xLo))
  simp [FormalYul.word, baseStore, paramStore, ret, wrapShared] at halloc
  have hencode :=
    call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack_direct
      (pos := memPos) (value := FormalYul.word ret) (fuel := 999861)
      (shared := memShared) (store := encStore)
      (hlookup := by
        simp [memShared, wrapShared,
          sharedAfterFrom0_lookup (sqrt512SharedAfterFreePtr xHi xLo) xHi xLo
            (sqrt512SharedAfterFreePtr_lookup xHi xLo)])
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
    (((sharedAfterFrom0 (sqrt512SharedAfterFreePtr xHi xLo) xHi xLo).mload
      (EvmYul.UInt256.ofNat 64)).2)
    (((sharedAfterFrom0 (sqrt512SharedAfterFreePtr xHi xLo) xHi xLo).mload
      (EvmYul.UInt256.ofNat 64)).1)
    (EvmYul.UInt256.ofNat (natSqrt (uint512 xHi xLo)))
  simp [FormalYul.word] at hresult
  rw [hresult]
  have hnat :
      (EvmYul.UInt256.ofNat (natSqrt (uint512 xHi xLo))).toNat =
        natSqrt (uint512 xHi xLo) := by
    change FormalYul.wordNat (EvmYul.UInt256.ofNat (natSqrt (uint512 xHi xLo))) =
      natSqrt (uint512 xHi xLo)
    exact (FormalYul.Preservation.wordNat_ofNat (natSqrt (uint512 xHi xLo))).trans
      (u256_eq_of_lt _ (natSqrt_uint512_lt_word xHi xLo))
  rw [hnat]

private theorem external_fun_wrap_sqrt512_calldata_halts_999989
    (xHi xLo : Nat) (store : EvmYul.Yul.VarStore) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_sqrt512) (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) store) =
        .error (.YulHalt state value) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [
    sqrt512SharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_sqrt512]
  simp only [yulFunction_external_fun_wrap_sqrt512, yulFunction_external_fun_wrap_sqrt512_6228,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := natSqrt (uint512 xHi xLo)
  let paramStore : EvmYul.Yul.VarStore :=
    Finmap.insert "param_0" (FormalYul.word xHi)
      (Finmap.insert "param_1" (FormalYul.word xLo)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let baseStore : EvmYul.Yul.VarStore :=
    Finmap.insert "ret_0" (FormalYul.word ret) paramStore
  let wrapShared := sharedAfterFrom0 (sqrt512SharedAfterFreePtr xHi xLo) xHi xLo
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
      (a := 0x3f) (b := 0x51) (c := 0x62) (d := 0x8a)
      (xHi := xHi) (xLo := xLo) (fuel := 999824)
      (shared := sqrt512SharedAfterFreePtr xHi xLo)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := sqrt512SharedAfterFreePtr_lookup xHi xLo)
      (hdata := by
        rw [sqrt512SharedAfterFreePtr_calldata]
        rfl)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_sqrt512_direct (xHi := xHi) (xLo := xLo) (fuel := 994183)
      (shared := sqrt512SharedAfterFreePtr xHi xLo) (store := paramStore)
      (hlookup := sqrt512SharedAfterFreePtr_lookup xHi xLo)
      (hactive := sqrt512SharedAfterFreePtr_activeWords xHi xLo)
  simp [FormalYul.word, yulName_fun_wrap_sqrt512, paramStore] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999952) (shared := wrapShared)
      (store := baseStore)
      (hlookup := sharedAfterFrom0_lookup (sqrt512SharedAfterFreePtr xHi xLo) xHi xLo
        (sqrt512SharedAfterFreePtr_lookup xHi xLo))
  simp [FormalYul.word, baseStore, paramStore, ret, wrapShared] at halloc
  have hencode :=
    call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack_direct
      (pos := memPos) (value := FormalYul.word ret) (fuel := 999861)
      (shared := memShared) (store := encStore)
      (hlookup := by
        simp [memShared, wrapShared,
          sharedAfterFrom0_lookup (sqrt512SharedAfterFreePtr xHi xLo) xHi xLo
            (sqrt512SharedAfterFreePtr_lookup xHi xLo)])
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
    EvmYul.Yul.State.toMachineState,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    hdecode, hwrap, halloc, hencode]

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

@[simp] private theorem sqrt512_selector_afterFreePtr (xHi xLo : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 1062298250 := by
  have hselector :=
    FormalYul.Preservation.shiftRight_calldataload_selector_two_args_of_calldata
      (shared := sqrt512SharedAfterFreePtr xHi xLo)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (a := 0x3f) (b := 0x51) (c := 0x62) (d := 0x8a) (x := xHi) (y := xLo)
      (by simp [selector_sqrt512])
  simpa [EvmYul.fromBytesBigEndian, EvmYul.fromBytes', FormalYul.word] using hselector

@[simp] private theorem osqrtUp_selector_afterFreePtr (xHi xLo : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok (osqrtUpSharedAfterFreePtr xHi xLo)
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 2574136228 := by
  have hselector :=
    FormalYul.Preservation.shiftRight_calldataload_selector_two_args_of_calldata
      (shared := osqrtUpSharedAfterFreePtr xHi xLo)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (a := 0x99) (b := 0x6e) (c := 0x33) (d := 0xa4) (x := xHi) (y := xLo)
      (by simp [selector_osqrtUp])
  simpa [EvmYul.fromBytesBigEndian, EvmYul.fromBytes', FormalYul.word] using hselector

private theorem dispatcherReturn_sqrt512
    (xHi xLo : Nat) (haltState : EvmYul.Yul.State) (haltValue : EvmYul.Literal)
    (hhalt :
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_sqrt512) (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
          (Finmap.insert "selector" (FormalYul.word 1062298250)
            (Inhabited.default : EvmYul.Yul.VarStore))) =
        .error (.YulHalt haltState haltValue)) :
    FormalYul.Preservation.DispatcherReturn yulContract
      (FormalYul.calldata selector_sqrt512 [xHi, xLo]) 999998 (FormalYul.returnOf haltState) := by
  let start := FormalYul.stateFor yulContract
    (FormalYul.calldata selector_sqrt512 [xHi, xLo])
  let afterFreePtr : EvmYul.Yul.State :=
    EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
      (Inhabited.default : EvmYul.Yul.VarStore)
  let afterSelector : EvmYul.Yul.State :=
    EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
      (Finmap.insert "selector" (FormalYul.word 1062298250)
        (Inhabited.default : EvmYul.Yul.VarStore))
  apply FormalYul.Preservation.dispatcherReturn_of_execReturn
    (hdispatcher := yulContract_dispatcher)
  simpa [start, afterFreePtr, afterSelector, yulDispatcher, FormalYul.calldata,
      yulName_external_fun_wrap_sqrt512, yulName_external_fun_wrap_osqrtUp] using
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
        [(FormalYul.word 1062298250,
            [EvmYul.Yul.Ast.Stmt.ExprStmtCall
              (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_sqrt512) [])]),
          (FormalYul.word 2574136228,
            [EvmYul.Yul.Ast.Stmt.ExprStmtCall
              (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_osqrtUp) [])])])
      (defaultStmts := [])
      (fn := yulName_external_fun_wrap_sqrt512)
      (code := .some yulContract)
      (start := start)
      (afterFirst := afterFreePtr)
      (branchStart := afterFreePtr)
      (afterLet := afterSelector)
      (switchStart := afterSelector)
      (condValue := FormalYul.word 1)
      (selector := FormalYul.word 1062298250)
      (result := FormalYul.returnOf haltState)
      (hfirst := by
        simp +decide [start, afterFreePtr, FormalYul.stateFor, FormalYul.calldata,
          EvmYul.Yul.execPrimCall.eq_def,
          EvmYul.Yul.reverse', EvmYul.Yul.cons',
          EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
          EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
          EvmYul.Yul.State.toMachineState,
          sharedFor_inherited_mstore_mk_eq_sqrt512SharedAfterFreePtr_raw])
      (hcond := by
        simp +decide [afterFreePtr,
          EvmYul.Yul.evalPrimCall.eq_def,
          EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
          EvmYul.Yul.evalTail.eq_def,
          EvmYul.Yul.State.executionEnv, FormalYul.word,
          sqrt512SharedAfterFreePtr_calldata, sqrt512_calldata_size])
      (hcondNe := by decide)
      (hlet := by
        have hselector :
            ((EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
                (Inhabited.default : EvmYul.Yul.VarStore)).toState.calldataload
                (EvmYul.UInt256.ofNat 0)).shiftRight
              (EvmYul.UInt256.ofNat 224) =
              EvmYul.UInt256.ofNat 1062298250 := by
          simpa [FormalYul.word] using sqrt512_selector_afterFreePtr xHi xLo
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

theorem run_sqrt512_wrapper_evm_eq_natSqrt
    (xHi xLo : Nat) :
    run_sqrt512_wrapper_evm xHi xLo =
      .ok (natSqrt (uint512 xHi xLo)) := by
  let selectorStore :=
    Finmap.insert "selector" (FormalYul.word 1062298250)
      (Inhabited.default : EvmYul.Yul.VarStore)
  obtain ⟨haltState, haltValue, hhalt⟩ :=
    external_fun_wrap_sqrt512_calldata_halts_999989 xHi xLo selectorStore
  have hresult := external_fun_wrap_sqrt512_calldata_result_999989 xHi xLo selectorStore
  rw [hhalt] at hresult
  have hReturn :
      FormalYul.Preservation.DispatcherReturn yulContract
        (FormalYul.calldata selector_sqrt512 [xHi, xLo]) 999998
        (FormalYul.returnOf haltState) :=
    dispatcherReturn_sqrt512 xHi xLo haltState haltValue (by
      simpa [selectorStore] using hhalt)
  unfold run_sqrt512_wrapper_evm
  exact FormalYul.Preservation.callWord_ok_of_dispatcherReturn_result_1000000
    (contract := yulContract) (selector := selector_sqrt512) (args := [xHi, xLo])
    (hReturn := hReturn) hresult

private def osqrtUpRuntimePair (xHi xLo : Nat) : Nat × Nat :=
  let xh := FormalYul.u256 xHi
  let xl := FormalYul.u256 xLo
  if FormalYul.evmEq xh 0 = 0 then
    let r := natSqrt (uint512 xHi xLo)
    let r2Hi :=
      FormalYul.evmSub
        (FormalYul.evmSub
          (FormalYul.evmMulmod r r (FormalYul.evmNot 0))
          (FormalYul.evmMul r r))
        (FormalYul.evmLt
          (FormalYul.evmMulmod r r (FormalYul.evmNot 0))
          (FormalYul.evmMul r r))
    let r2Lo := FormalYul.evmMul r r
    let inc := FormalYul.evmOr (FormalYul.evmGt xh r2Hi)
      (FormalYul.evmAnd (FormalYul.evmEq xh r2Hi) (FormalYul.evmGt xl r2Lo))
    (FormalYul.evmAdd 0 (FormalYul.evmLt (FormalYul.evmAdd r inc) r),
      FormalYul.evmAdd r inc)
  else
    (0, sqrtUp256 xl)

private theorem evmNot_zero_eq_word_sub_one :
    FormalYul.evmNot 0 = FormalYul.WORD_MOD - 1 := by
  unfold FormalYul.evmNot FormalYul.u256
  simp

private theorem evmGt_eq_of_lt
    (a b : Nat) (ha : a < FormalYul.WORD_MOD) (hb : b < FormalYul.WORD_MOD) :
    FormalYul.evmGt a b = if a > b then 1 else 0 := by
  unfold FormalYul.evmGt
  simp [FormalYul.u256_eq_self_of_lt ha, FormalYul.u256_eq_self_of_lt hb]

private theorem mul512_high_word (r : Nat) (hr : r < FormalYul.WORD_MOD) :
    let mm := FormalYul.evmMulmod r r (FormalYul.evmNot 0)
    let m := FormalYul.evmMul r r
    FormalYul.evmSub (FormalYul.evmSub mm m) (FormalYul.evmLt mm m) =
      r * r / FormalYul.WORD_MOD := by
  simp only
  have hWM_pos : 0 < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    omega
  have hWM1_pos : 0 < FormalYul.WORD_MOD - 1 := by
    unfold FormalYul.WORD_MOD
    omega
  have hWM1_lt : FormalYul.WORD_MOD - 1 < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    omega
  have hmm :
      FormalYul.evmMulmod r r (FormalYul.evmNot 0) =
        (r * r) % (FormalYul.WORD_MOD - 1) := by
    unfold FormalYul.evmMulmod
    simp [FormalYul.u256_eq_self_of_lt hr, evmNot_zero_eq_word_sub_one,
      FormalYul.u256_eq_self_of_lt hWM1_lt, Nat.ne_of_gt hWM1_pos]
  have hm : FormalYul.evmMul r r = (r * r) % FormalYul.WORD_MOD :=
    evmMul_eq_mod_of_lt r r hr hr
  rw [hmm, hm]
  have hdecomp :
      r * r =
        r * r / FormalYul.WORD_MOD * FormalYul.WORD_MOD +
          r * r % FormalYul.WORD_MOD := by
    have := Nat.div_add_mod (r * r) FormalYul.WORD_MOD
    rw [Nat.mul_comm] at this
    exact this.symm
  have hq_bound : r * r / FormalYul.WORD_MOD < FormalYul.WORD_MOD := by
    have hsq : r * r < FormalYul.WORD_MOD * FormalYul.WORD_MOD :=
      Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hr) hr hWM_pos
    exact Nat.div_lt_of_lt_mul hsq
  have hlo_bound : r * r % FormalYul.WORD_MOD < FormalYul.WORD_MOD :=
    Nat.mod_lt _ hWM_pos
  have hhi_eq :
      (r * r) % (FormalYul.WORD_MOD - 1) =
        (r * r / FormalYul.WORD_MOD + r * r % FormalYul.WORD_MOD) %
          (FormalYul.WORD_MOD - 1) := by
    have hqW :
        r * r / FormalYul.WORD_MOD * FormalYul.WORD_MOD =
          (FormalYul.WORD_MOD - 1) * (r * r / FormalYul.WORD_MOD) +
            r * r / FormalYul.WORD_MOD := by
      have hsc :
          FormalYul.WORD_MOD - 1 + 1 = FormalYul.WORD_MOD :=
        Nat.sub_add_cancel (Nat.one_le_of_lt hWM_pos)
      have h :=
        Nat.mul_add (r * r / FormalYul.WORD_MOD) (FormalYul.WORD_MOD - 1) 1
      rw [hsc, Nat.mul_one] at h
      rw [h, Nat.mul_comm (r * r / FormalYul.WORD_MOD) (FormalYul.WORD_MOD - 1)]
    have hrr_eq :
        r * r =
          (FormalYul.WORD_MOD - 1) * (r * r / FormalYul.WORD_MOD) +
            (r * r / FormalYul.WORD_MOD + r * r % FormalYul.WORD_MOD) := by
      omega
    have step :=
      Nat.mul_add_mod (FormalYul.WORD_MOD - 1) (r * r / FormalYul.WORD_MOD)
        (r * r / FormalYul.WORD_MOD + r * r % FormalYul.WORD_MOD)
    rw [← hrr_eq] at step
    exact step
  by_cases hcase :
      r * r / FormalYul.WORD_MOD + r * r % FormalYul.WORD_MOD <
        FormalYul.WORD_MOD - 1
  · have hhi_val :
        (r * r) % (FormalYul.WORD_MOD - 1) =
          r * r / FormalYul.WORD_MOD + r * r % FormalYul.WORD_MOD := by
      rw [hhi_eq, Nat.mod_eq_of_lt hcase]
    have hhi_wm : (r * r) % (FormalYul.WORD_MOD - 1) < FormalYul.WORD_MOD := by
      have := Nat.mod_lt (r * r) hWM1_pos
      omega
    have hge :
        r * r % FormalYul.WORD_MOD ≤ (r * r) % (FormalYul.WORD_MOD - 1) := by
      rw [hhi_val]
      exact Nat.le_add_left _ _
    have hlt_eq :
        FormalYul.evmLt ((r * r) % (FormalYul.WORD_MOD - 1))
          (r * r % FormalYul.WORD_MOD) = 0 := by
      rw [evmLt_eq_of_lt _ _ hhi_wm hlo_bound]
      exact if_neg (Nat.not_lt.mpr hge)
    rw [hlt_eq]
    have hsub1 :
        FormalYul.evmSub ((r * r) % (FormalYul.WORD_MOD - 1))
            (r * r % FormalYul.WORD_MOD) =
          (r * r) % (FormalYul.WORD_MOD - 1) - r * r % FormalYul.WORD_MOD :=
      evmSub_eq_of_le _ _ hhi_wm hge
    rw [hsub1]
    have hq_eq :
        (r * r) % (FormalYul.WORD_MOD - 1) - r * r % FormalYul.WORD_MOD =
          r * r / FormalYul.WORD_MOD := by
      omega
    rw [hq_eq]
    exact evmSub_eq_of_le _ 0 hq_bound (Nat.zero_le _)
  · have hcase' :
        FormalYul.WORD_MOD - 1 ≤
          r * r / FormalYul.WORD_MOD + r * r % FormalYul.WORD_MOD :=
      Nat.not_lt.mp hcase
    have hq_le : r * r / FormalYul.WORD_MOD ≤ FormalYul.WORD_MOD - 2 := by
      have hr' : r ≤ FormalYul.WORD_MOD - 1 := by omega
      have hrsq : r * r ≤ (FormalYul.WORD_MOD - 1) * (FormalYul.WORD_MOD - 1) :=
        Nat.mul_le_mul hr' hr'
      have h1 :
          r * r / FormalYul.WORD_MOD ≤
            (FormalYul.WORD_MOD - 1) * (FormalYul.WORD_MOD - 1) /
              FormalYul.WORD_MOD :=
        Nat.div_le_div_right hrsq
      suffices
          (FormalYul.WORD_MOD - 1) * (FormalYul.WORD_MOD - 1) /
              FormalYul.WORD_MOD =
            FormalYul.WORD_MOD - 2 by
        omega
      unfold FormalYul.WORD_MOD
      omega
    have hql_lt :
        r * r / FormalYul.WORD_MOD + r * r % FormalYul.WORD_MOD <
          2 * (FormalYul.WORD_MOD - 1) := by
      omega
    have hhi_val :
        (r * r) % (FormalYul.WORD_MOD - 1) =
          r * r / FormalYul.WORD_MOD + r * r % FormalYul.WORD_MOD -
            (FormalYul.WORD_MOD - 1) := by
      rw [hhi_eq, Nat.mod_eq_sub_mod hcase',
        Nat.mod_eq_of_lt (by omega)]
    have hlt_lo :
        (r * r) % (FormalYul.WORD_MOD - 1) < r * r % FormalYul.WORD_MOD := by
      rw [hhi_val]
      omega
    have hhi_wm : (r * r) % (FormalYul.WORD_MOD - 1) < FormalYul.WORD_MOD := by
      have := Nat.mod_lt (r * r) hWM1_pos
      omega
    have hlt_eq :
        FormalYul.evmLt ((r * r) % (FormalYul.WORD_MOD - 1))
          (r * r % FormalYul.WORD_MOD) = 1 := by
      rw [evmLt_eq_of_lt _ _ hhi_wm hlo_bound]
      exact if_pos hlt_lo
    rw [hlt_eq]
    have hsub1 :
        FormalYul.evmSub ((r * r) % (FormalYul.WORD_MOD - 1))
            (r * r % FormalYul.WORD_MOD) =
          (r * r) % (FormalYul.WORD_MOD - 1) + FormalYul.WORD_MOD -
            r * r % FormalYul.WORD_MOD := by
      unfold FormalYul.evmSub FormalYul.u256
      simp [Nat.mod_eq_of_lt hhi_wm, Nat.mod_eq_of_lt hlo_bound]
      exact Nat.mod_eq_of_lt (show
        (r * r) % (FormalYul.WORD_MOD - 1) + FormalYul.WORD_MOD -
            r * r % FormalYul.WORD_MOD <
          FormalYul.WORD_MOD by
        rw [hhi_val]
        omega)
    rw [hsub1]
    have hval :
        (r * r) % (FormalYul.WORD_MOD - 1) + FormalYul.WORD_MOD -
            r * r % FormalYul.WORD_MOD <
          FormalYul.WORD_MOD := by
      rw [hhi_val]
      omega
    have hsub2 :
        FormalYul.evmSub
            ((r * r) % (FormalYul.WORD_MOD - 1) + FormalYul.WORD_MOD -
              r * r % FormalYul.WORD_MOD) 1 =
          (r * r) % (FormalYul.WORD_MOD - 1) + FormalYul.WORD_MOD -
            r * r % FormalYul.WORD_MOD - 1 :=
      evmSub_eq_of_le _ 1 hval (by
        rw [hhi_val]
        omega)
    rw [hsub2, hhi_val]
    omega

private theorem mul512_low_word (r : Nat) (hr : r < FormalYul.WORD_MOD) :
    FormalYul.evmMul r r = r * r % FormalYul.WORD_MOD :=
  evmMul_eq_mod_of_lt r r hr hr

private theorem gt512_correct (xHi xLo sqHi sqLo : Nat)
    (hxhi : xHi < FormalYul.WORD_MOD) (hxlo : xLo < FormalYul.WORD_MOD)
    (hsqhi : sqHi < FormalYul.WORD_MOD) (hsqlo : sqLo < FormalYul.WORD_MOD) :
    let cmp := FormalYul.evmOr (FormalYul.evmGt xHi sqHi)
      (FormalYul.evmAnd (FormalYul.evmEq xHi sqHi) (FormalYul.evmGt xLo sqLo))
    (cmp ≠ 0) ↔
      xHi * FormalYul.WORD_MOD + xLo > sqHi * FormalYul.WORD_MOD + sqLo := by
  simp only
  have hgtHi : FormalYul.evmGt xHi sqHi = if xHi > sqHi then 1 else 0 :=
    evmGt_eq_of_lt xHi sqHi hxhi hsqhi
  have heqHi : FormalYul.evmEq xHi sqHi = if xHi = sqHi then 1 else 0 :=
    evmEq_eq_of_lt xHi sqHi hxhi hsqhi
  have hgtLo : FormalYul.evmGt xLo sqLo = if xLo > sqLo then 1 else 0 :=
    evmGt_eq_of_lt xLo sqLo hxlo hsqlo
  rw [hgtHi, heqHi, hgtLo]
  by_cases hgt : xHi > sqHi
  · have hneq : ¬ xHi = sqHi := by omega
    simp only [hgt, if_true, hneq, if_false]
    have hor_nz : ∀ v, FormalYul.evmOr 1 (FormalYul.evmAnd 0 v) ≠ 0 := by
      intro v
      unfold FormalYul.evmOr FormalYul.evmAnd FormalYul.u256 FormalYul.WORD_MOD
      simp
    constructor
    · intro _
      have h1 : sqHi * FormalYul.WORD_MOD + FormalYul.WORD_MOD ≤
          xHi * FormalYul.WORD_MOD := by
        have := Nat.mul_le_mul_right FormalYul.WORD_MOD hgt
        rwa [Nat.succ_mul] at this
      omega
    · intro _
      exact hor_nz _
  · by_cases heq : xHi = sqHi
    · subst heq
      simp only [gt_iff_lt, lt_self_iff_false, if_false, if_true]
      by_cases hgtlo : xLo > sqLo
      · simp only [hgtlo, if_true]
        constructor
        · intro _
          omega
        · intro _
          unfold FormalYul.evmOr FormalYul.evmAnd FormalYul.u256 FormalYul.WORD_MOD
          simp
      · simp only [hgtlo, if_false]
        have hor_z : FormalYul.evmOr 0 (FormalYul.evmAnd 1 0) = 0 := by
          unfold FormalYul.evmOr FormalYul.evmAnd FormalYul.u256 FormalYul.WORD_MOD
          simp
        constructor
        · intro h
          exact absurd hor_z h
        · intro h
          omega
    · have hlt : xHi < sqHi := by omega
      have hng : ¬ xHi > sqHi := by omega
      simp only [hng, if_false, heq, gt_iff_lt]
      have hor_z : ∀ v, FormalYul.evmOr 0 (FormalYul.evmAnd 0 v) = 0 := by
        intro v
        unfold FormalYul.evmOr FormalYul.evmAnd FormalYul.u256 FormalYul.WORD_MOD
        simp
      constructor
      · intro h
        exact absurd (hor_z _) h
      · intro h
        have h1 : xHi * FormalYul.WORD_MOD + FormalYul.WORD_MOD ≤
            sqHi * FormalYul.WORD_MOD := by
          have := Nat.mul_le_mul_right FormalYul.WORD_MOD hlt
          rwa [Nat.succ_mul] at this
        omega

private theorem add_with_carry (r needsUp : Nat) (hr : r < FormalYul.WORD_MOD)
    (hn : needsUp = 0 ∨ needsUp = 1) :
    let rLo := FormalYul.evmAdd r needsUp
    let rHi := FormalYul.evmLt (FormalYul.evmAdd r needsUp) r
    rHi * FormalYul.WORD_MOD + rLo = r + needsUp := by
  simp only
  have hn_bound : needsUp < FormalYul.WORD_MOD := by
    rcases hn with h | h <;> rw [h] <;> unfold FormalYul.WORD_MOD <;> omega
  by_cases hov : r + needsUp < FormalYul.WORD_MOD
  · have hadd : FormalYul.evmAdd r needsUp = r + needsUp :=
      evmAdd_eq_of_lt r needsUp hr hn_bound hov
    rw [hadd]
    have hge : r ≤ r + needsUp := Nat.le_add_right r needsUp
    have hlt_eq : FormalYul.evmLt (r + needsUp) r = 0 := by
      rw [evmLt_eq_of_lt _ _ hov hr]
      exact if_neg (Nat.not_lt.mpr hge)
    rw [hlt_eq]
    simp
  · have hov' : FormalYul.WORD_MOD ≤ r + needsUp := Nat.not_lt.mp hov
    have hn1 : needsUp = 1 := by
      rcases hn with h | h <;> omega
    subst hn1
    have hrMax : r = FormalYul.WORD_MOD - 1 := by
      omega
    subst hrMax
    have hadd : FormalYul.evmAdd (FormalYul.WORD_MOD - 1) 1 = 0 := by
      unfold FormalYul.evmAdd FormalYul.u256 FormalYul.WORD_MOD
      simp
    rw [hadd]
    have hlt_eq : FormalYul.evmLt 0 (FormalYul.WORD_MOD - 1) = 1 := by
      unfold FormalYul.evmLt FormalYul.u256 FormalYul.WORD_MOD
      simp
    rw [hlt_eq]
    unfold FormalYul.WORD_MOD
    omega

private theorem sqrtUp256_eq_sqrtUp512_of_lt (x : Nat) (hx : x < 2 ^ 256) :
    sqrtUp256 x = sqrtUp512 x := by
  have hx512 : x < 2 ^ 512 :=
    Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : Nat)) (by omega))
  unfold sqrtUp256 sqrtUp512
  rw [sqrt512_correct x hx512, floorSqrt_eq_natSqrt_u256 x hx]

private theorem sqrtUp512Pair_zero_high (xHi xLo : Nat)
    (hhi : FormalYul.u256 xHi = 0) :
    (0, sqrtUp256 (FormalYul.u256 xLo)) = sqrtUp512Pair xHi xLo := by
  unfold sqrtUp512Pair uint512
  rw [hhi, Nat.zero_mul, Nat.zero_add]
  rw [sqrtUp256_eq_sqrtUp512_of_lt (FormalYul.u256 xLo)]
  · let r := sqrtUp512 (FormalYul.u256 xLo)
    have hr : r < 2 ^ 256 := by
      have hle : r ≤ 2 ^ 128 := by
        unfold r sqrtUp512
        rw [sqrt512_correct (FormalYul.u256 xLo)
          (Nat.lt_of_lt_of_le
            (by
              unfold FormalYul.u256 FormalYul.WORD_MOD
              exact Nat.mod_lt xLo (Nat.two_pow_pos 256))
            (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : Nat)) (by omega)))]
        have hx : FormalYul.u256 xLo < FormalYul.WORD_MOD := by
          unfold FormalYul.u256 FormalYul.WORD_MOD
          exact Nat.mod_lt xLo (Nat.two_pow_pos 256)
        rw [FormalYul.WORD_MOD] at hx
        have hm128 := m_lt_pow128_of_u256 (natSqrt (FormalYul.u256 xLo))
          (FormalYul.u256 xLo) (natSqrt_sq_le (FormalYul.u256 xLo)) (by
            simpa [FormalYul.WORD_MOD] using hx)
        by_cases hlt :
            natSqrt (FormalYul.u256 xLo) * natSqrt (FormalYul.u256 xLo) <
              FormalYul.u256 xLo
        · simp [hlt]
          omega
        · simp [hlt]
          omega
      omega
    change (0, r) = (r / 2 ^ 256, r % 2 ^ 256)
    rw [Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr]
  · unfold FormalYul.u256 FormalYul.WORD_MOD
    exact Nat.mod_lt xLo (Nat.two_pow_pos 256)

private theorem sqrtUp512_uint512_le_word (xHi xLo : Nat) :
    sqrtUp512 (uint512 xHi xLo) ≤ 2 ^ 256 := by
  have hcorrect := sqrtUp512_correct (uint512 xHi xLo) (uint512_lt_512 xHi xLo)
  exact hcorrect.2 (2 ^ 256) (by
    have hx : uint512 xHi xLo < 2 ^ 512 := uint512_lt_512 xHi xLo
    have hpow : (2 : Nat) ^ 256 * 2 ^ 256 = 2 ^ 512 := by
      rw [← Nat.pow_add]
    omega)

private theorem osqrtUpRuntimePair_eq_sqrtUp512Pair (xHi xLo : Nat) :
    osqrtUpRuntimePair xHi xLo = sqrtUp512Pair xHi xLo := by
  let xh := FormalYul.u256 xHi
  let xl := FormalYul.u256 xLo
  have hxh : xh < FormalYul.WORD_MOD := by
    dsimp [xh]
    unfold FormalYul.u256 FormalYul.WORD_MOD
    exact Nat.mod_lt xHi (Nat.two_pow_pos 256)
  have hxl : xl < FormalYul.WORD_MOD := by
    dsimp [xl]
    unfold FormalYul.u256 FormalYul.WORD_MOD
    exact Nat.mod_lt xLo (Nat.two_pow_pos 256)
  by_cases hcond : FormalYul.evmEq xh 0 = 0
  · have hxh_pos : 0 < xh := by
      have hne : xh ≠ 0 := by
        intro hz
        unfold FormalYul.evmEq at hcond
        simp [hz] at hcond
      exact Nat.pos_of_ne_zero hne
    have hwm : FormalYul.WORD_MOD = 2 ^ 256 := rfl
    have huint : uint512 xHi xLo = xh * FormalYul.WORD_MOD + xl := by
      dsimp [uint512, xh, xl]
      rw [FormalYul.WORD_MOD]
    have hx_lt : xh * FormalYul.WORD_MOD + xl < 2 ^ 512 := by
      rw [hwm]
      have hxhmul : xh * 2 ^ 256 < 2 ^ 256 * 2 ^ 256 :=
        Nat.mul_lt_mul_of_pos_right (by simpa [hwm] using hxh) (Nat.two_pow_pos 256)
      have hpow : 2 ^ 256 * 2 ^ 256 = 2 ^ 512 := by rw [← Nat.pow_add]
      omega
    let r := natSqrt (uint512 xHi xLo)
    have hr : r < FormalYul.WORD_MOD := by
      simpa [r] using natSqrt_uint512_lt_word xHi xLo
    have hmulHi :
        FormalYul.evmSub
            (FormalYul.evmSub (FormalYul.evmMulmod r r (FormalYul.evmNot 0))
              (FormalYul.evmMul r r))
            (FormalYul.evmLt (FormalYul.evmMulmod r r (FormalYul.evmNot 0))
              (FormalYul.evmMul r r)) =
          r * r / FormalYul.WORD_MOD := by
      simpa using mul512_high_word r hr
    have hmulLo : FormalYul.evmMul r r = r * r % FormalYul.WORD_MOD :=
      mul512_low_word r hr
    have hmulHiAfterLow :
        FormalYul.evmSub
            (FormalYul.evmSub (FormalYul.evmMulmod r r (FormalYul.evmNot 0))
              (r * r % FormalYul.WORD_MOD))
            (FormalYul.evmLt (FormalYul.evmMulmod r r (FormalYul.evmNot 0))
              (r * r % FormalYul.WORD_MOD)) =
          r * r / FormalYul.WORD_MOD := by
      simpa [hmulLo] using hmulHi
    have hsqhi : r * r / FormalYul.WORD_MOD < FormalYul.WORD_MOD := by
      have hsq : r * r < FormalYul.WORD_MOD * FormalYul.WORD_MOD :=
        Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hr) hr (by unfold FormalYul.WORD_MOD; omega)
      exact Nat.div_lt_of_lt_mul hsq
    have hsqlo : r * r % FormalYul.WORD_MOD < FormalYul.WORD_MOD :=
      Nat.mod_lt _ (by unfold FormalYul.WORD_MOD; omega)
    let needsUp :=
      FormalYul.evmOr (FormalYul.evmGt xh (r * r / FormalYul.WORD_MOD))
        (FormalYul.evmAnd (FormalYul.evmEq xh (r * r / FormalYul.WORD_MOD))
          (FormalYul.evmGt xl (r * r % FormalYul.WORD_MOD)))
    have hneeds_01 : needsUp = 0 ∨ needsUp = 1 := by
      dsimp [needsUp]
      have hgt01 : ∀ a b : Nat, a < FormalYul.WORD_MOD → b < FormalYul.WORD_MOD →
          FormalYul.evmGt a b = 0 ∨ FormalYul.evmGt a b = 1 := by
        intro a b ha hb
        rw [evmGt_eq_of_lt a b ha hb]
        split <;> simp
      have heq01 : ∀ a b : Nat, a < FormalYul.WORD_MOD → b < FormalYul.WORD_MOD →
          FormalYul.evmEq a b = 0 ∨ FormalYul.evmEq a b = 1 := by
        intro a b ha hb
        rw [evmEq_eq_of_lt a b ha hb]
        split <;> simp
      have hand01 : ∀ a b : Nat, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) →
          FormalYul.evmAnd a b = 0 ∨ FormalYul.evmAnd a b = 1 := by
        intro a b ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
          unfold FormalYul.evmAnd FormalYul.u256 FormalYul.WORD_MOD <;> simp
      have hor01 : ∀ a b : Nat, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) →
          FormalYul.evmOr a b = 0 ∨ FormalYul.evmOr a b = 1 := by
        intro a b ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
          unfold FormalYul.evmOr FormalYul.u256 FormalYul.WORD_MOD <;> simp
      exact hor01 _ _
        (hgt01 xh (r * r / FormalYul.WORD_MOD) hxh hsqhi)
        (hand01 _ _
          (heq01 xh (r * r / FormalYul.WORD_MOD) hxh hsqhi)
          (hgt01 xl (r * r % FormalYul.WORD_MOD) hxl hsqlo))
    have hneeds_iff :
        (needsUp ≠ 0) ↔ xh * FormalYul.WORD_MOD + xl > r * r := by
      dsimp [needsUp]
      have h := gt512_correct xh xl (r * r / FormalYul.WORD_MOD)
        (r * r % FormalYul.WORD_MOD) hxh hxl hsqhi hsqlo
      have hdm :
          r * r / FormalYul.WORD_MOD * FormalYul.WORD_MOD +
              r * r % FormalYul.WORD_MOD =
            r * r := by
        rw [Nat.mul_comm]
        exact Nat.div_add_mod ..
      rw [hdm] at h
      exact h
    have hcarry := add_with_carry r needsUp hr hneeds_01
    simp only at hcarry
    have hfst :
        FormalYul.evmAdd 0 (FormalYul.evmLt (FormalYul.evmAdd r needsUp) r) =
          FormalYul.evmLt (FormalYul.evmAdd r needsUp) r := by
      have hlt01 :
          FormalYul.evmLt (FormalYul.evmAdd r needsUp) r = 0 ∨
            FormalYul.evmLt (FormalYul.evmAdd r needsUp) r = 1 := by
        unfold FormalYul.evmLt
        split <;> simp
      rcases hlt01 with h | h <;>
        rw [h] <;> unfold FormalYul.evmAdd FormalYul.u256 FormalYul.WORD_MOD <;> simp
    have hresult :
        FormalYul.evmLt (FormalYul.evmAdd r needsUp) r * FormalYul.WORD_MOD +
            FormalYul.evmAdd r needsUp =
          if r * r < uint512 xHi xLo then r + 1 else r := by
      rw [hcarry]
      by_cases hlt : r * r < uint512 xHi xLo
      · simp [hlt]
        have hnz : needsUp ≠ 0 := hneeds_iff.mpr (by
          rw [← huint]
          exact hlt)
        rcases hneeds_01 with hz | ho
        · exact absurd hz hnz
        · rw [ho]
      · simp [hlt]
        have hz : needsUp = 0 := by
          rcases hneeds_01 with hz | ho
          · exact hz
          · exfalso
            have hgt := hneeds_iff.mp (by rw [ho]; omega)
            rw [← huint] at hgt
            omega
        rw [hz]
    have hresLe : (if r * r < uint512 xHi xLo then r + 1 else r) ≤ 2 ^ 256 := by
      have hle := sqrtUp512_uint512_le_word xHi xLo
      unfold sqrtUp512 at hle
      rw [sqrt512_correct (uint512 xHi xLo) (uint512_lt_512 xHi xLo)] at hle
      exact hle
    have hHiLo :
        FormalYul.evmLt (FormalYul.evmAdd r needsUp) r =
          (if r * r < uint512 xHi xLo then r + 1 else r) / 2 ^ 256 ∧
        FormalYul.evmAdd r needsUp =
          (if r * r < uint512 xHi xLo then r + 1 else r) % 2 ^ 256 := by
      have hhiLt :
          FormalYul.evmLt (FormalYul.evmAdd r needsUp) r < 2 := by
        unfold FormalYul.evmLt
        split <;> omega
      have hloLt : FormalYul.evmAdd r needsUp < FormalYul.WORD_MOD := by
        unfold FormalYul.evmAdd FormalYul.u256
        exact Nat.mod_lt _ (by unfold FormalYul.WORD_MOD; omega)
      have hdiv :
          (FormalYul.evmLt (FormalYul.evmAdd r needsUp) r *
              FormalYul.WORD_MOD + FormalYul.evmAdd r needsUp) / FormalYul.WORD_MOD =
            FormalYul.evmLt (FormalYul.evmAdd r needsUp) r := by
        calc
          (FormalYul.evmLt (FormalYul.evmAdd r needsUp) r *
              FormalYul.WORD_MOD + FormalYul.evmAdd r needsUp) / FormalYul.WORD_MOD
              = FormalYul.evmAdd r needsUp / FormalYul.WORD_MOD +
                  FormalYul.evmLt (FormalYul.evmAdd r needsUp) r := by
                    rw [Nat.add_comm,
                      Nat.add_mul_div_right _ _ (by unfold FormalYul.WORD_MOD; omega)]
          _ = 0 + FormalYul.evmLt (FormalYul.evmAdd r needsUp) r := by
            rw [Nat.div_eq_of_lt hloLt]
          _ = FormalYul.evmLt (FormalYul.evmAdd r needsUp) r := by
            simp
      have hmod :
          (FormalYul.evmLt (FormalYul.evmAdd r needsUp) r *
              FormalYul.WORD_MOD + FormalYul.evmAdd r needsUp) % FormalYul.WORD_MOD =
            FormalYul.evmAdd r needsUp := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt hloLt
      constructor
      · rw [← hresult]
        simpa [FormalYul.WORD_MOD] using hdiv.symm
      · rw [← hresult]
        simpa [FormalYul.WORD_MOD] using hmod.symm
    have hpair :
        (FormalYul.evmLt (FormalYul.evmAdd r needsUp) r,
            FormalYul.evmAdd r needsUp) =
          sqrtUp512Pair xHi xLo := by
      unfold sqrtUp512Pair sqrtUp512
      rw [sqrt512_correct (uint512 xHi xLo) (uint512_lt_512 xHi xLo)]
      change
        (FormalYul.evmLt (FormalYul.evmAdd r needsUp) r,
            FormalYul.evmAdd r needsUp) =
          ((if r * r < uint512 xHi xLo then r + 1 else r) / 2 ^ 256,
            (if r * r < uint512 xHi xLo then r + 1 else r) % 2 ^ 256)
      exact Prod.ext hHiLo.1 hHiLo.2
    have hpairWithAddZero :
        (FormalYul.evmAdd 0 (FormalYul.evmLt (FormalYul.evmAdd r needsUp) r),
            FormalYul.evmAdd r needsUp) =
          sqrtUp512Pair xHi xLo := by
      rw [hfst]
      exact hpair
    unfold osqrtUpRuntimePair
    simpa [xh, xl, hcond, r, hmulLo, hmulHiAfterLow, needsUp] using hpairWithAddZero
  · have hhi : xh = 0 := by
      by_contra hne
      have hEq0 : FormalYul.evmEq xh 0 = 0 := by
        unfold FormalYul.evmEq
        simp [FormalYul.u256_eq_self_of_lt hxh, hne]
      exact hcond hEq0
    have hcondFalse : ¬ FormalYul.evmEq (FormalYul.u256 xHi) 0 = 0 := by
      intro h
      exact hcond (by simpa [xh] using h)
    unfold osqrtUpRuntimePair
    rw [if_neg hcondFalse]
    simpa [xl] using sqrtUp512Pair_zero_high xHi xLo (by simpa [xh] using hhi)

private theorem sqrtUp512Pair_u256_components (xHi xLo : Nat) :
    (FormalYul.u256 (sqrtUp512Pair xHi xLo).1,
      FormalYul.u256 (sqrtUp512Pair xHi xLo).2) =
      sqrtUp512Pair xHi xLo := by
  unfold sqrtUp512Pair
  let r := sqrtUp512 (uint512 xHi xLo)
  have hr : r ≤ 2 ^ 256 := by
    simpa [r] using sqrtUp512_uint512_le_word xHi xLo
  have hhi : r / 2 ^ 256 < FormalYul.WORD_MOD := by
    rw [FormalYul.WORD_MOD]
    have hle : r / 2 ^ 256 ≤ 1 := by
      exact Nat.div_le_of_le_mul (by simpa using hr)
    omega
  have hlo : r % 2 ^ 256 < FormalYul.WORD_MOD := by
    rw [FormalYul.WORD_MOD]
    exact Nat.mod_lt r (Nat.two_pow_pos 256)
  change
    (FormalYul.u256 (r / 2 ^ 256), FormalYul.u256 (r % 2 ^ 256)) =
      (r / 2 ^ 256, r % 2 ^ 256)
  apply Prod.ext
  · exact FormalYul.u256_eq_self_of_lt hhi
  · exact FormalYul.u256_eq_self_of_lt hlo

@[simp] private theorem call_fun__sqrt512_osqrt_raw_direct
    (xHi xLo fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract))
    (hxHi_pos : 0 < FormalYul.u256 xHi) :
    EvmYul.Yul.call (fuel + (extra + 5000))
      [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
      (.some yulName_fun__sqrt512) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [EvmYul.UInt256.ofNat (natSqrt (uint512 xHi xLo))]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun__sqrt512_direct (xHi := xHi) (xLo := xLo)
      (fuel := fuel + extra) (shared := shared) (store := store)
      (hlookup := hlookup) (hxHi_pos := hxHi_pos)

@[simp] private theorem call_fun__mul_osqrt_raw_direct
    (x y fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 100))
      [EvmYul.UInt256.ofNat x, EvmYul.UInt256.ofNat y]
      (.some yulName_fun__mul) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word
        (FormalYul.evmSub
          (FormalYul.evmSub (FormalYul.evmMulmod x y (FormalYul.evmNot 0))
            (FormalYul.evmMul x y))
          (FormalYul.evmLt (FormalYul.evmMulmod x y (FormalYul.evmNot 0))
            (FormalYul.evmMul x y))),
       FormalYul.word (FormalYul.evmMul x y)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun__mul_direct (x := x) (y := y) (fuel := fuel + extra)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun__gt_osqrt_raw_direct
    (xHi xLo yHi yLo fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 80))
      [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo,
        EvmYul.UInt256.ofNat yHi, EvmYul.UInt256.ofNat yLo]
      (.some yulName_fun__gt) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmOr (FormalYul.evmGt xHi yHi)
        (FormalYul.evmAnd (FormalYul.evmEq xHi yHi) (FormalYul.evmGt xLo yLo)))]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun__gt_direct (xHi := xHi) (xLo := xLo) (yHi := yHi) (yLo := yLo)
      (fuel := fuel + extra) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_fun_toUint_osqrt_raw_direct
    (b fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 60)) [EvmYul.UInt256.ofNat b]
      (.some yulName_fun_toUint) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmLt 0 b)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_toUint_direct (b := b) (fuel := fuel + extra)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_fun__add_osqrt_raw_direct
    (xHi xLo y fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 80))
      [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo, EvmYul.UInt256.ofNat y]
      (.some yulName_fun__add) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmAdd xHi (FormalYul.evmLt (FormalYul.evmAdd xLo y) xLo)),
       FormalYul.word (FormalYul.evmAdd xLo y)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun__add_direct (xHi := xHi) (xLo := xLo) (y := y)
      (fuel := fuel + extra) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_fun_sqrtUp256_osqrt_raw_direct
    (x fuel extra : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 420)) [EvmYul.UInt256.ofNat x]
      (.some yulName_fun_sqrtUp256) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (sqrtUp256 (FormalYul.u256 x))]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_sqrtUp256_direct (x := x) (fuel := fuel + extra)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp] private theorem call_cleanup_t_uint256_6975_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 6975) [v] (.some "cleanup_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_uint256_direct
      (v := v) (fuel := fuel + 6955) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_convert_t_rational_0_by_1_to_t_uint256_6977_direct
    (value fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 6977) [EvmYul.UInt256.ofNat value]
      (.some "convert_t_rational_0_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat value]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_0_by_1_to_t_uint256_direct
      (value := value) (fuel := fuel + 6877) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_convert_t_rational_0_by_1_to_t_uint256_6948_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 6948) [EvmYul.UInt256.ofNat 0]
      (.some "convert_t_rational_0_by_1_to_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 0]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_0_by_1_to_t_uint256_direct
      (value := 0) (fuel := fuel + 6848) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_fun__add_osqrt_6947_direct
    (xHi xLo y fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup :
      shared.accountMap.find? shared.executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 6947)
      [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo, EvmYul.UInt256.ofNat y]
      (.some yulName_fun__add) (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (FormalYul.evmAdd xHi (FormalYul.evmLt (FormalYul.evmAdd xLo y) xLo)),
       FormalYul.word (FormalYul.evmAdd xLo y)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun__add_direct (xHi := xHi) (xLo := xLo) (y := y)
      (fuel := fuel + 6867) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp] private theorem call_fun_from_156_zero_osqrt_runtime_6970_direct
    (xHi xLo fuel : Nat) (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.call (fuel + 6970)
      [EvmYul.UInt256.ofNat 0,
       EvmYul.UInt256.ofNat (osqrtUpRuntimePair xHi xLo).1,
       EvmYul.UInt256.ofNat (osqrtUpRuntimePair xHi xLo).2]
      (.some "fun_from_156") (.some yulContract)
      (EvmYul.Yul.State.Ok (osqrtUpSharedAfterInput xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok
        (sharedAfterFrom0 (osqrtUpSharedAfterInput xHi xLo)
          (osqrtUpRuntimePair xHi xLo).1 (osqrtUpRuntimePair xHi xLo).2)
        store,
      [EvmYul.UInt256.ofNat 0]) := by
  rw [show fuel + 6970 = (fuel + 6870) + 100 by omega]
  exact
    call_fun_from_156_zero_raw_direct
      (xHi := (osqrtUpRuntimePair xHi xLo).1)
      (xLo := (osqrtUpRuntimePair xHi xLo).2)
      (fuel := fuel + 6870) (shared := osqrtUpSharedAfterInput xHi xLo)
      (store := store) (hlookup := osqrtUpSharedAfterInput_lookup xHi xLo)

private theorem call_fun_osqrtUp_direct
    (xHi xLo fuel : Nat) (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.call (fuel + 7000) [FormalYul.word 0, FormalYul.word 128]
      (.some yulName_fun_osqrtUp) (.some yulContract)
      (EvmYul.Yul.State.Ok (osqrtUpSharedAfterInput xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok
        (sharedAfterFrom0 (osqrtUpSharedAfterInput xHi xLo)
          (osqrtUpRuntimePair xHi xLo).1 (osqrtUpRuntimePair xHi xLo).2)
        store,
      [FormalYul.word 0]) := by
  by_cases hcond : FormalYul.evmEq xHi 0 = 0
  · have hxHi_pos : 0 < FormalYul.u256 xHi := by
      exact Nat.pos_of_ne_zero ((evmEq_zero_eq_zero_iff xHi).mp hcond)
    have hswitch :
        EvmYul.UInt256.eq (EvmYul.UInt256.ofNat xHi) (EvmYul.UInt256.ofNat 0) =
          ({ val := 0 } : EvmYul.UInt256) :=
      (uint256_eq_ofNat_zero_struct_zero_iff xHi).2 hcond
    rw [EvmYul.Yul.call.eq_def]
    simp +decide [osqrtUpSharedAfterInput_lookup xHi xLo,
      Option.getD_some, yulContract_functions]
    simp +decide [yulFunction_fun_osqrtUp_4653,
      FormalYul.Preservation.functionDefinition_params_def,
      FormalYul.Preservation.functionDefinition_rets_def,
      FormalYul.Preservation.functionDefinition_body_def,
      EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
    simp +decide [hcond, hswitch, hxHi_pos,
      EvmYul.Yul.selectSwitchCase,
      EvmYul.Yul.exec.eq_def,
      EvmYul.Yul.execCall.eq_def,
      EvmYul.Yul.evalCall.eq_def,
      EvmYul.Yul.execPrimCall.eq_def,
      EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
      EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
      EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
      EvmYul.Yul.State.store,
      GetElem?.getElem!, decidableGetElem?,
      EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
      EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
      EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
      call_zero_value_for_split_t_userDefinedValueType_uint512_direct,
      osqrtUpRuntimePair, FormalYul.word,
      FormalYul.Preservation.evmEq_u256_left,
      Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  · have hhi : FormalYul.u256 xHi = 0 := by
      by_contra hne
      exact hcond ((evmEq_zero_eq_zero_iff xHi).mpr hne)
    have hswitch : ¬ EvmYul.UInt256.ofNat 0 =
        EvmYul.UInt256.eq (EvmYul.UInt256.ofNat xHi) (EvmYul.UInt256.ofNat 0) := by
      intro hzero
      have hzero' :
          EvmYul.UInt256.eq (EvmYul.UInt256.ofNat xHi) (EvmYul.UInt256.ofNat 0) =
            ({ val := 0 } : EvmYul.UInt256) := by
        simpa [eq_comm] using hzero
      exact hcond ((uint256_eq_ofNat_zero_struct_zero_iff xHi).1 hzero')
    rw [EvmYul.Yul.call.eq_def]
    simp +decide [osqrtUpSharedAfterInput_lookup xHi xLo,
      Option.getD_some, yulContract_functions]
    simp +decide [yulFunction_fun_osqrtUp_4653,
      FormalYul.Preservation.functionDefinition_params_def,
      FormalYul.Preservation.functionDefinition_rets_def,
      FormalYul.Preservation.functionDefinition_body_def,
      EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
    simp +decide [hswitch, hhi,
      EvmYul.Yul.selectSwitchCase,
      EvmYul.Yul.execCall.eq_def,
      EvmYul.Yul.evalCall.eq_def,
      EvmYul.Yul.execPrimCall.eq_def,
      EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
      EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
      EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
      EvmYul.Yul.State.store,
      GetElem?.getElem!, decidableGetElem?,
      EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
      EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
      EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
      call_zero_value_for_split_t_userDefinedValueType_uint512_direct,
      osqrtUpRuntimePair, FormalYul.word,
      Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

private theorem call_fun_osqrtUp_raw_direct
    (xHi xLo fuel extra : Nat) (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.call (fuel + (extra + 7000))
      [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 128]
      (.some yulName_fun_osqrtUp) (.some yulContract)
      (EvmYul.Yul.State.Ok (osqrtUpSharedAfterInput xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok
        (sharedAfterFrom0 (osqrtUpSharedAfterInput xHi xLo)
          (osqrtUpRuntimePair xHi xLo).1 (osqrtUpRuntimePair xHi xLo).2)
        store,
      [EvmYul.UInt256.ofNat 0]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_osqrtUp_direct (xHi := xHi) (xLo := xLo)
      (fuel := fuel + extra) (store := store)

private theorem call_fun_wrap_osqrtUp_direct
    (xHi xLo fuel : Nat) (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.call (fuel + 7600)
      [FormalYul.word xHi, FormalYul.word xLo]
      (.some yulName_fun_wrap_osqrtUp) (.some yulContract)
      (EvmYul.Yul.State.Ok (osqrtUpSharedAfterFreePtr xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok
        (sharedAfterFrom0 (osqrtUpSharedAfterInput xHi xLo)
          (osqrtUpRuntimePair xHi xLo).1 (osqrtUpRuntimePair xHi xLo).2)
        store,
      [FormalYul.word (osqrtUpRuntimePair xHi xLo).1,
       FormalYul.word (osqrtUpRuntimePair xHi xLo).2]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [osqrtUpSharedAfterFreePtr_lookup xHi xLo,
    Option.getD_some, yulContract_functions, lookup_fun_wrap_osqrtUp]
  simp only [yulFunction_fun_wrap_osqrtUp, yulFunction_fun_wrap_osqrtUp_6261,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let paramStore : EvmYul.Yul.VarStore :=
    Finmap.insert "var_x_hi_6230" (EvmYul.UInt256.ofNat xHi)
      (Finmap.insert "var_x_lo_6232" (EvmYul.UInt256.ofNat xLo)
        (Inhabited.default : EvmYul.Yul.VarStore))
  have hzero4 :
      EvmYul.Yul.call (fuel + 7596) [] (.some "zero_value_for_split_t_uint256")
        (.some yulContract)
        (EvmYul.Yul.State.Ok (osqrtUpSharedAfterFreePtr xHi xLo) paramStore) =
      .ok (EvmYul.Yul.State.Ok (osqrtUpSharedAfterFreePtr xHi xLo) paramStore,
        [FormalYul.word 0]) := by
    exact
      call_zero_value_for_split_t_uint256_direct
        (fuel := fuel) (extra := 7576)
        (shared := osqrtUpSharedAfterFreePtr xHi xLo) (store := paramStore)
        (hlookup := osqrtUpSharedAfterFreePtr_lookup xHi xLo)
  let zero4Store : EvmYul.Yul.VarStore :=
    Finmap.insert "var__6235" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "zero_t_uint256_4" (EvmYul.UInt256.ofNat 0) paramStore)
  have hzero5 :
      EvmYul.Yul.call (fuel + 7594) [] (.some "zero_value_for_split_t_uint256")
        (.some yulContract)
        (EvmYul.Yul.State.Ok (osqrtUpSharedAfterFreePtr xHi xLo) zero4Store) =
      .ok (EvmYul.Yul.State.Ok (osqrtUpSharedAfterFreePtr xHi xLo) zero4Store,
        [FormalYul.word 0]) := by
    exact
      call_zero_value_for_split_t_uint256_direct
        (fuel := fuel) (extra := 7574)
        (shared := osqrtUpSharedAfterFreePtr xHi xLo) (store := zero4Store)
        (hlookup := osqrtUpSharedAfterFreePtr_lookup xHi xLo)
  let zero5Store : EvmYul.Yul.VarStore :=
    Finmap.insert "var__6237" (EvmYul.UInt256.ofNat 0)
      (Finmap.insert "zero_t_uint256_5" (EvmYul.UInt256.ofNat 0) zero4Store)
  have halloc :
      EvmYul.Yul.call (fuel + 7592) [] (.some "fun_alloc_121")
        (.some yulContract)
        (EvmYul.Yul.State.Ok (osqrtUpSharedAfterFreePtr xHi xLo) zero5Store) =
      .ok (EvmYul.Yul.State.Ok (osqrtUpSharedAfterAlloc xHi xLo) zero5Store,
        [EvmYul.UInt256.ofNat 128]) := by
    simpa [osqrtUpSharedAfterAlloc, zero5Store, zero4Store, FormalYul.word,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_alloc_121_128_raw_direct
        (fuel := fuel) (extra := 7492)
        (shared := osqrtUpSharedAfterFreePtr xHi xLo) (store := zero5Store)
        (hlookup := osqrtUpSharedAfterFreePtr_lookup xHi xLo)
        (hmload64 := osqrtUpSharedAfterFreePtr_mload64 xHi xLo)
        (hmload64_state := osqrtUpSharedAfterFreePtr_mload64_state xHi xLo)
  let fromStore : EvmYul.Yul.VarStore :=
    Finmap.insert "expr_6249" (EvmYul.UInt256.ofNat xLo)
      (Finmap.insert "_8" (EvmYul.UInt256.ofNat xLo)
        (Finmap.insert "expr_6248" (EvmYul.UInt256.ofNat xHi)
          (Finmap.insert "_7" (EvmYul.UInt256.ofNat xHi)
            (Finmap.insert "expr_6247_self" (EvmYul.UInt256.ofNat 128)
              (Finmap.insert "expr_6245" (EvmYul.UInt256.ofNat 128)
                (Finmap.insert "_6" (EvmYul.UInt256.ofNat 128)
                  (Finmap.insert "var_x_6241" (EvmYul.UInt256.ofNat 128)
                    (Finmap.insert "expr_6243" (EvmYul.UInt256.ofNat 128)
                      zero5Store))))))))
  have hfrom :
      EvmYul.Yul.call (fuel + 7583)
        [EvmYul.UInt256.ofNat 128, EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
        (.some "fun_from_156") (.some yulContract)
        (EvmYul.Yul.State.Ok (osqrtUpSharedAfterAlloc xHi xLo) fromStore) =
      .ok (EvmYul.Yul.State.Ok (osqrtUpSharedAfterInput xHi xLo) fromStore,
        [EvmYul.UInt256.ofNat 128]) := by
    simpa [osqrtUpSharedAfterInput, fromStore, zero5Store, zero4Store,
      FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_from_156_128_raw_direct (xHi := xHi) (xLo := xLo)
        (fuel := fuel) (extra := 7483)
        (shared := osqrtUpSharedAfterAlloc xHi xLo) (store := fromStore)
        (hlookup := sharedAfterAlloc128_lookup (osqrtUpSharedAfterFreePtr xHi xLo)
          (osqrtUpSharedAfterFreePtr_lookup xHi xLo))
  simp +decide [
    EvmYul.Yul.exec.eq_def,
    EvmYul.Yul.execCall.eq_def, EvmYul.Yul.eval.eq_def,
    EvmYul.Yul.evalArgs.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
    hzero4, hzero5, halloc, hfrom,
    call_fun_tmp_128_raw_direct,
    call_fun_osqrtUp_raw_direct,
    call_fun_into_182_from0_active6_raw_direct,
    paramStore, zero4Store, zero5Store, fromStore,
    osqrtUpRuntimePair, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

private theorem external_fun_wrap_osqrtUp_calldata_halts_999989
    (xHi xLo : Nat) (store : EvmYul.Yul.VarStore) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_osqrtUp) (.some yulContract)
        (EvmYul.Yul.State.Ok (osqrtUpSharedAfterFreePtr xHi xLo) store) =
        .error (.YulHalt state value) ∧
      FormalYul.returnOf state =
        FormalYul.Preservation.abiPairResult
          (osqrtUpRuntimePair xHi xLo).1 (osqrtUpRuntimePair xHi xLo).2 := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [
    osqrtUpSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_osqrtUp]
  simp only [yulFunction_external_fun_wrap_osqrtUp,
    yulFunction_external_fun_wrap_osqrtUp_6261,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let rHi := (osqrtUpRuntimePair xHi xLo).1
  let rLo := (osqrtUpRuntimePair xHi xLo).2
  let paramStore : EvmYul.Yul.VarStore :=
    Finmap.insert "param_0" (FormalYul.word xHi)
      (Finmap.insert "param_1" (FormalYul.word xLo)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let baseStore : EvmYul.Yul.VarStore :=
    Finmap.insert "ret_0" (FormalYul.word rHi)
      (Finmap.insert "ret_1" (FormalYul.word rLo) paramStore)
  let wrapShared :=
    sharedAfterFrom0 (osqrtUpSharedAfterInput xHi xLo) rHi rLo
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
      (a := 0x99) (b := 0x6e) (c := 0x33) (d := 0xa4)
      (xHi := xHi) (xLo := xLo) (fuel := 999824)
      (shared := osqrtUpSharedAfterFreePtr xHi xLo)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := osqrtUpSharedAfterFreePtr_lookup xHi xLo)
      (hdata := by
        rw [osqrtUpSharedAfterFreePtr_calldata]
        rfl)
  simp [FormalYul.word] at hdecode
  have hwrap :
      EvmYul.Yul.call 999983 [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
        (.some "fun_wrap_osqrtUp_6261") (.some yulContract)
        (EvmYul.Yul.State.Ok (osqrtUpSharedAfterFreePtr xHi xLo) paramStore) =
      .ok (EvmYul.Yul.State.Ok wrapShared paramStore,
        [FormalYul.word rHi, FormalYul.word rLo]) := by
    simpa [wrapShared, rHi, rLo, paramStore, FormalYul.word,
      yulName_fun_wrap_osqrtUp, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_wrap_osqrtUp_direct
        (xHi := xHi) (xLo := xLo) (fuel := 992383)
        (store := paramStore)
  simp [FormalYul.word, paramStore, wrapShared, rHi, rLo] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999952) (shared := wrapShared)
      (store := baseStore)
      (hlookup := sharedAfterFrom0_lookup (osqrtUpSharedAfterInput xHi xLo) rHi rLo
        (osqrtUpSharedAfterInput_lookup xHi xLo))
  simp [FormalYul.word, baseStore, paramStore, rHi, rLo, wrapShared] at halloc
  have hencode :=
    call_abi_encode_tuple_t_uint256_t_uint256__to_t_uint256_t_uint256__fromStack_direct
      (pos := memPos) (value0 := FormalYul.word rHi) (value1 := FormalYul.word rLo)
      (fuel := 999761) (shared := memShared) (store := encStore)
      (hlookup := by
        simp [memShared, wrapShared,
          sharedAfterFrom0_lookup (osqrtUpSharedAfterInput xHi xLo) rHi rLo
            (osqrtUpSharedAfterInput_lookup xHi xLo)])
  simp [FormalYul.word, memShared, encStore, memPos, baseStore, paramStore, rHi, rLo,
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
    FormalYul.Preservation.abiPairResult,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    hdecode, hwrap, halloc, hencode]
  have hloadPos :
      ((sharedAfterFrom0 (osqrtUpSharedAfterInput xHi xLo)
          (osqrtUpRuntimePair xHi xLo).1 (osqrtUpRuntimePair xHi xLo).2).mload
        (EvmYul.UInt256.ofNat 64)).1 =
      EvmYul.UInt256.ofNat 192 := by
    simpa [FormalYul.word] using
      sharedAfterFrom0_osqrt_mload64 xHi xLo
        (osqrtUpRuntimePair xHi xLo).1 (osqrtUpRuntimePair xHi xLo).2
  have hloadState :
      ((sharedAfterFrom0 (osqrtUpSharedAfterInput xHi xLo)
          (osqrtUpRuntimePair xHi xLo).1 (osqrtUpRuntimePair xHi xLo).2).mload
        (EvmYul.UInt256.ofNat 64)).2 =
      (sharedAfterFrom0 (osqrtUpSharedAfterInput xHi xLo)
        (osqrtUpRuntimePair xHi xLo).1 (osqrtUpRuntimePair xHi xLo).2).toMachineState := by
    simpa [FormalYul.word] using
      sharedAfterFrom0_osqrt_mload64_state xHi xLo
        (osqrtUpRuntimePair xHi xLo).1 (osqrtUpRuntimePair xHi xLo).2
  rw [hloadState, hloadPos]
  exact FormalYul.Preservation.evmReturn_mstore_two_words_H_return_of_size
    (mstate :=
      (sharedAfterFrom0 (osqrtUpSharedAfterInput xHi xLo)
        (osqrtUpRuntimePair xHi xLo).1 (osqrtUpRuntimePair xHi xLo).2).toMachineState)
    (pos := FormalYul.word 192)
    (value0 := FormalYul.word (osqrtUpRuntimePair xHi xLo).1)
    (value1 := FormalYul.word (osqrtUpRuntimePair xHi xLo).2)
    (hmem := by
      exact sharedAfterFrom0_osqrt_memory_size xHi xLo
        (osqrtUpRuntimePair xHi xLo).1 (osqrtUpRuntimePair xHi xLo).2)
    (hpos := by rfl)

private theorem dispatcherReturn_osqrtUp
    (xHi xLo : Nat) (haltState : EvmYul.Yul.State) (haltValue : EvmYul.Literal)
    (hhalt :
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_osqrtUp) (.some yulContract)
        (EvmYul.Yul.State.Ok (osqrtUpSharedAfterFreePtr xHi xLo)
          (Finmap.insert "selector" (FormalYul.word 2574136228)
            (Inhabited.default : EvmYul.Yul.VarStore))) =
        .error (.YulHalt haltState haltValue)) :
    FormalYul.Preservation.DispatcherReturn yulContract
      (FormalYul.calldata selector_osqrtUp [xHi, xLo]) 999998 (FormalYul.returnOf haltState) := by
  let start := FormalYul.stateFor yulContract
    (FormalYul.calldata selector_osqrtUp [xHi, xLo])
  let afterFreePtr : EvmYul.Yul.State :=
    EvmYul.Yul.State.Ok (osqrtUpSharedAfterFreePtr xHi xLo)
      (Inhabited.default : EvmYul.Yul.VarStore)
  let afterSelector : EvmYul.Yul.State :=
    EvmYul.Yul.State.Ok (osqrtUpSharedAfterFreePtr xHi xLo)
      (Finmap.insert "selector" (FormalYul.word 2574136228)
        (Inhabited.default : EvmYul.Yul.VarStore))
  apply FormalYul.Preservation.dispatcherReturn_of_execReturn
    (hdispatcher := yulContract_dispatcher)
  simpa [start, afterFreePtr, afterSelector, yulDispatcher, FormalYul.calldata,
      yulName_external_fun_wrap_sqrt512, yulName_external_fun_wrap_osqrtUp] using
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
        [(FormalYul.word 1062298250,
            [EvmYul.Yul.Ast.Stmt.ExprStmtCall
              (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_sqrt512) [])]),
          (FormalYul.word 2574136228,
            [EvmYul.Yul.Ast.Stmt.ExprStmtCall
              (EvmYul.Yul.Ast.Expr.Call (Sum.inr yulName_external_fun_wrap_osqrtUp) [])])])
      (defaultStmts := [])
      (fn := yulName_external_fun_wrap_osqrtUp)
      (code := .some yulContract)
      (start := start)
      (afterFirst := afterFreePtr)
      (branchStart := afterFreePtr)
      (afterLet := afterSelector)
      (switchStart := afterSelector)
      (condValue := FormalYul.word 1)
      (selector := FormalYul.word 2574136228)
      (result := FormalYul.returnOf haltState)
      (hfirst := by
        simp +decide [start, afterFreePtr, FormalYul.stateFor, FormalYul.calldata,
          EvmYul.Yul.execPrimCall.eq_def,
          EvmYul.Yul.reverse', EvmYul.Yul.cons',
          EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
          EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
          EvmYul.Yul.State.toMachineState,
          sharedFor_inherited_mstore_mk_eq_osqrtUpSharedAfterFreePtr_raw])
      (hcond := by
        simp +decide [afterFreePtr,
          EvmYul.Yul.evalPrimCall.eq_def,
          EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
          EvmYul.Yul.evalTail.eq_def,
          EvmYul.Yul.State.executionEnv, FormalYul.word,
          osqrtUpSharedAfterFreePtr_calldata, osqrtUp_calldata_size])
      (hcondNe := by decide)
      (hlet := by
        have hselector :
            ((EvmYul.Yul.State.Ok (osqrtUpSharedAfterFreePtr xHi xLo)
                (Inhabited.default : EvmYul.Yul.VarStore)).toState.calldataload
                (EvmYul.UInt256.ofNat 0)).shiftRight
              (EvmYul.UInt256.ofNat 224) =
              EvmYul.UInt256.ofNat 2574136228 := by
          simpa [FormalYul.word] using osqrtUp_selector_afterFreePtr xHi xLo
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

theorem run_osqrtUp_evm_eq_sqrtUp512Pair
    (xHi xLo : Nat) :
    run_osqrtUp_evm xHi xLo =
      .ok (sqrtUp512Pair xHi xLo) := by
  let selectorStore :=
    Finmap.insert "selector" (FormalYul.word 2574136228)
      (Inhabited.default : EvmYul.Yul.VarStore)
  obtain ⟨haltState, haltValue, hhalt, hret⟩ :=
    external_fun_wrap_osqrtUp_calldata_halts_999989 xHi xLo selectorStore
  have hReturn :
      FormalYul.Preservation.DispatcherReturn yulContract
        (FormalYul.calldata selector_osqrtUp [xHi, xLo]) 999998
        (FormalYul.returnOf haltState) :=
    dispatcherReturn_osqrtUp xHi xLo haltState haltValue (by
      simpa [selectorStore] using hhalt)
  have hReturnPair :
      FormalYul.Preservation.DispatcherReturn yulContract
        (FormalYul.calldata selector_osqrtUp [xHi, xLo]) 999998
        (FormalYul.Preservation.abiPairResult
          (osqrtUpRuntimePair xHi xLo).1 (osqrtUpRuntimePair xHi xLo).2) := by
    simpa [hret] using hReturn
  have hModel :
      (FormalYul.u256 (osqrtUpRuntimePair xHi xLo).1,
        FormalYul.u256 (osqrtUpRuntimePair xHi xLo).2) =
        sqrtUp512Pair xHi xLo := by
    rw [osqrtUpRuntimePair_eq_sqrtUp512Pair]
    exact sqrtUp512Pair_u256_components xHi xLo
  unfold run_osqrtUp_evm
  exact FormalYul.Preservation.callPair_ok_of_dispatcherReturn_two_words_1000000
    (contract := yulContract) (selector := selector_osqrtUp) (args := [xHi, xLo])
    (hReturn := hReturnPair) hModel

end Sqrt512Yul
