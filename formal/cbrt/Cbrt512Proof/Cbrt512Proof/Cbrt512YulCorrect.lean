import Cbrt512Proof.Cbrt512YulProof
import Cbrt512Proof.Cbrt512Correct

set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024
set_option linter.style.nameCheck false

namespace Cbrt512Yul

open FormalYul

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
