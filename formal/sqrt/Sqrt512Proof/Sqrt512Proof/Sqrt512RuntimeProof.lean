import Sqrt512Proof.Sqrt512YulProof
import SqrtProof.SqrtYul
import Sqrt512Proof.SqrtWrapperSpec

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 512
set_option linter.unusedSimpArgs false
set_option linter.style.nameCheck false

namespace Sqrt512Yul

open scoped EvmYul.Yul.Notation

@[simp] theorem bridge_u256 (x : Nat) : Sqrt512Yul.u256 x = FormalYul.u256 x := rfl
@[simp] theorem bridge_add (a b : Nat) : Sqrt512Yul.evmAdd a b = FormalYul.evmAdd a b := rfl
@[simp] theorem bridge_sub (a b : Nat) : Sqrt512Yul.evmSub a b = FormalYul.evmSub a b := rfl
@[simp] theorem bridge_mul (a b : Nat) : Sqrt512Yul.evmMul a b = FormalYul.evmMul a b := rfl
@[simp] theorem bridge_div (a b : Nat) : Sqrt512Yul.evmDiv a b = FormalYul.evmDiv a b := rfl
@[simp] theorem bridge_mod (a b : Nat) : Sqrt512Yul.evmMod a b = FormalYul.evmMod a b := rfl
@[simp] theorem bridge_shl (a b : Nat) : Sqrt512Yul.evmShl a b = FormalYul.evmShl a b := rfl
@[simp] theorem bridge_shr (a b : Nat) : Sqrt512Yul.evmShr a b = FormalYul.evmShr a b := rfl
@[simp] theorem bridge_clz (a : Nat) : Sqrt512Yul.evmClz a = FormalYul.evmClz a := rfl
@[simp] theorem bridge_lt (a b : Nat) : Sqrt512Yul.evmLt a b = FormalYul.evmLt a b := rfl
@[simp] theorem bridge_gt (a b : Nat) : Sqrt512Yul.evmGt a b = FormalYul.evmGt a b := rfl
@[simp] theorem bridge_eq (a b : Nat) : Sqrt512Yul.evmEq a b = FormalYul.evmEq a b := rfl
@[simp] theorem bridge_iszero (a : Nat) : Sqrt512Yul.evmIszero a = FormalYul.evmIszero a := rfl
@[simp] theorem bridge_and (a b : Nat) : Sqrt512Yul.evmAnd a b = FormalYul.evmAnd a b := rfl
@[simp] theorem bridge_or (a b : Nat) : Sqrt512Yul.evmOr a b = FormalYul.evmOr a b := rfl
@[simp] theorem bridge_mulmod (a b n : Nat) : Sqrt512Yul.evmMulmod a b n = FormalYul.evmMulmod a b n := rfl

@[simp] theorem u256_idem (x : Nat) : Sqrt512Yul.u256 (Sqrt512Yul.u256 x) = Sqrt512Yul.u256 x := by
  simp [Sqrt512Yul.u256, Sqrt512Yul.WORD_MOD]

theorem uint256_ofNat_toNat_eq_formal_u256 (x : Nat) :
    (EvmYul.UInt256.ofNat x).toNat = FormalYul.u256 x := by
  exact FormalYul.Preservation.wordNat_ofNat x

@[simp]
theorem model_sqrt512_evm_u256_args (xHi xLo : Nat) :
    model_sqrt512_evm (FormalYul.u256 xHi) (FormalYul.u256 xLo) =
      model_sqrt512_evm xHi xLo := by
  simp [model_sqrt512_evm, FormalYul.u256, Sqrt512Yul.u256,
    FormalYul.WORD_MOD, Sqrt512Yul.WORD_MOD]

@[simp]
theorem model_sqrt256_floor_evm_u256_arg (x : Nat) :
    model_sqrt256_floor_evm (FormalYul.u256 x) = model_sqrt256_floor_evm x := by
  simp [model_sqrt256_floor_evm, FormalYul.u256, Sqrt512Yul.u256,
    FormalYul.WORD_MOD, Sqrt512Yul.WORD_MOD]

@[simp]
theorem model_sqrt512_wrapper_evm_u256_args (xHi xLo : Nat) :
    model_sqrt512_wrapper_evm (FormalYul.u256 xHi) (FormalYul.u256 xLo) =
      model_sqrt512_wrapper_evm xHi xLo := by
  simp [model_sqrt512_wrapper_evm, FormalYul.u256, Sqrt512Yul.u256,
    FormalYul.WORD_MOD, Sqrt512Yul.WORD_MOD]

theorem model_sqrt512_wrapper_evm_lt_word (xHi xLo : Nat) :
    model_sqrt512_wrapper_evm xHi xLo < FormalYul.WORD_MOD := by
  have hxHi : Sqrt512Yul.u256 xHi < 2 ^ 256 := by
    unfold Sqrt512Yul.u256 Sqrt512Yul.WORD_MOD
    exact Nat.mod_lt xHi (Nat.two_pow_pos 256)
  have hxLo : Sqrt512Yul.u256 xLo < 2 ^ 256 := by
    unfold Sqrt512Yul.u256 Sqrt512Yul.WORD_MOD
    exact Nat.mod_lt xLo (Nat.two_pow_pos 256)
  have hcorrect := Sqrt512Spec.model_sqrt512_wrapper_evm_correct
    (Sqrt512Yul.u256 xHi) (Sqrt512Yul.u256 xLo) hxHi hxLo
  have harg :
      model_sqrt512_wrapper_evm (Sqrt512Yul.u256 xHi) (Sqrt512Yul.u256 xLo) =
        model_sqrt512_wrapper_evm xHi xLo := by
    simpa [bridge_u256] using model_sqrt512_wrapper_evm_u256_args xHi xLo
  rw [← harg, hcorrect]
  rw [FormalYul.WORD_MOD]
  suffices natSqrt (Sqrt512Yul.u256 xHi * 2 ^ 256 + Sqrt512Yul.u256 xLo) < 2 ^ 256 by
    exact this
  by_contra hnot
  have hsquare := natSqrt_sq_le (Sqrt512Yul.u256 xHi * 2 ^ 256 + Sqrt512Yul.u256 xLo)
  have hge : 2 ^ 512 ≤
      Sqrt512Yul.u256 xHi * 2 ^ 256 + Sqrt512Yul.u256 xLo := by
    have hle : 2 ^ 256 ≤ natSqrt (Sqrt512Yul.u256 xHi * 2 ^ 256 + Sqrt512Yul.u256 xLo) :=
      Nat.le_of_not_gt hnot
    calc
      2 ^ 512 = 2 ^ 256 * 2 ^ 256 := by
        rw [show (512 : Nat) = 256 + 256 by omega, Nat.pow_add]
      _ ≤ natSqrt (Sqrt512Yul.u256 xHi * 2 ^ 256 + Sqrt512Yul.u256 xLo) *
          natSqrt (Sqrt512Yul.u256 xHi * 2 ^ 256 + Sqrt512Yul.u256 xLo) :=
            Nat.mul_le_mul hle hle
      _ ≤ Sqrt512Yul.u256 xHi * 2 ^ 256 + Sqrt512Yul.u256 xLo := hsquare
  have hlt : Sqrt512Yul.u256 xHi * 2 ^ 256 + Sqrt512Yul.u256 xLo < 2 ^ 512 := by
    have hmul : Sqrt512Yul.u256 xHi * 2 ^ 256 < 2 ^ 256 * 2 ^ 256 :=
      Nat.mul_lt_mul_of_pos_right hxHi (Nat.two_pow_pos 256)
    have hpow : 2 ^ 256 * 2 ^ 256 = 2 ^ 512 := by
      rw [← Nat.pow_add]
    omega
  omega

@[simp]
theorem call_checkpoint_succ
    (fuel : Nat) (args : List EvmYul.Literal)
    (fn : Option EvmYul.Yul.Ast.YulFunctionName)
    (code : Option EvmYul.Yul.Ast.YulContract)
    (jump : EvmYul.Yul.Jump) :
    EvmYul.Yul.call (Nat.succ fuel) args fn code (EvmYul.Yul.State.Checkpoint jump) =
      .ok (EvmYul.Yul.State.Checkpoint jump, [⟨0⟩]) := by
  rw [EvmYul.Yul.call.eq_def]

@[simp] theorem formal_evmNot_zero :
    FormalYul.evmNot 0 =
      115792089237316195423570985008687907853269984665640564039457584007913129639935 := by
  norm_num [FormalYul.evmNot, FormalYul.u256, FormalYul.WORD_MOD]

@[simp]
theorem uint256_eq_ofNat_zero_eq_zero_iff (x : Nat) :
    (EvmYul.UInt256.eq (EvmYul.UInt256.ofNat x) (EvmYul.UInt256.ofNat 0) =
        EvmYul.UInt256.ofNat 0) ↔
      FormalYul.evmEq x 0 = 0 := by
  have hnat0 : (EvmYul.UInt256.ofNat x).toNat = FormalYul.u256 x := by
    exact FormalYul.Preservation.wordNat_ofNat x
  have hzero : (EvmYul.UInt256.ofNat 0).toNat = 0 := rfl
  have hnat :
      FormalYul.wordNat
          (EvmYul.UInt256.eq (EvmYul.UInt256.ofNat x) (EvmYul.UInt256.ofNat 0)) =
        FormalYul.evmEq x 0 := by
    rw [FormalYul.Preservation.wordNat_eq]
    simp [FormalYul.wordNat, hnat0, hzero, FormalYul.evmEq, FormalYul.u256]
  constructor
  · intro h
    rw [h] at hnat
    exact hnat.symm
  · intro h
    apply FormalYul.Preservation.eq_of_wordNat_eq
    rw [hnat]
    simpa [FormalYul.wordNat, EvmYul.UInt256.ofNat] using h

@[simp]
theorem uint256_eq_ofNat_zero_struct_zero_iff (x : Nat) :
    (EvmYul.UInt256.eq (EvmYul.UInt256.ofNat x) (EvmYul.UInt256.ofNat 0) =
        ({ val := 0 } : EvmYul.UInt256)) ↔
      FormalYul.evmEq x 0 = 0 := by
  simpa [EvmYul.UInt256.ofNat] using uint256_eq_ofNat_zero_eq_zero_iff x

theorem read_two_word_write_first_data
    (a b dest : ByteArray) (ha : a.size = 32) :
    ((b.write 0 (a.write 0 dest 0 32) 32 32).readWithPadding 0 32).data.toList =
      a.data.toList := by
  simp [ByteArray.size] at ha
  simp [ByteArray.write, ByteArray.readWithPadding, ByteArray.readWithoutPadding,
    ByteArray.size, ha, ffi.ByteArray.zeroes]

theorem read_two_word_write_second_data
    (a b dest : ByteArray) (ha : a.size = 32) (hb : b.size = 32) :
    ((b.write 0 (a.write 0 dest 0 32) 32 32).readWithPadding 32 32).data.toList =
      b.data.toList := by
  simp [ByteArray.size] at ha hb
  simp [ByteArray.write, ByteArray.readWithPadding, ByteArray.readWithoutPadding,
    ByteArray.size, ha, hb, ffi.ByteArray.zeroes]

theorem fromByteArrayBigEndian_eq_of_data_toList_eq
    {a b : ByteArray} (h : a.data.toList = b.data.toList) :
    EvmYul.fromByteArrayBigEndian a = EvmYul.fromByteArrayBigEndian b := by
  unfold EvmYul.fromByteArrayBigEndian
  rw [h]

theorem write32_size_ge (source dest : ByteArray) (destAddr : Nat) :
    destAddr + 32 ≤ (source.write 0 dest destAddr 32).size := by
  simp [ByteArray.write, ByteArray.size]
  omega

theorem two_word_write_size_ge_64
    (a b dest : ByteArray) :
    64 ≤ (b.write 0 (a.write 0 dest 0 32) 32 32).size := by
  have h := write32_size_ge b (a.write 0 dest 0 32) 32
  simpa using h

theorem mload_two_word_write_first (m : EvmYul.MachineState) (xHi xLo : EvmYul.UInt256)
    (hactive : m.activeWords = FormalYul.word 3) :
    (((m.mstore (FormalYul.word 0) xHi).mstore (FormalYul.word 32) xLo).mload (FormalYul.word 0)).1 =
      xHi := by
  unfold EvmYul.MachineState.mload EvmYul.MachineState.lookupMemory
  have hsize : 64 ≤ (xLo.toByteArray.write 0 (xHi.toByteArray.write 0 m.memory 0 32) 32 32).size :=
    two_word_write_size_ge_64 xHi.toByteArray xLo.toByteArray m.memory
  have hsize' :
      64 ≤ (xLo.toByteArray.write 0 (xHi.toByteArray.write 0 m.memory (EvmYul.UInt256.ofNat 0).toNat 32)
        (EvmYul.UInt256.ofNat 32).toNat 32).size := by
    simpa using hsize
  have hzero : (EvmYul.UInt256.ofNat 0).toNat = 0 := rfl
  have hcond :
      ¬ ((xLo.toByteArray.write 0 (xHi.toByteArray.write 0 m.memory (EvmYul.UInt256.ofNat 0).toNat 32)
                (EvmYul.UInt256.ofNat 32).toNat 32).size ≤
            (EvmYul.UInt256.ofNat 0).toNat ∨
          EvmYul.UInt256.ofNat
                (max
                  (EvmYul.UInt256.ofNat
                      (max (EvmYul.UInt256.ofNat 3).toNat (((EvmYul.UInt256.ofNat 0).toNat + 32 + 31) / 32))).toNat
                  (((EvmYul.UInt256.ofNat 32).toNat + 32 + 31) / 32)) *
              { val := 32 } ≤
            EvmYul.UInt256.ofNat 0) := by
    intro h
    cases h with
    | inl hmem =>
        have hgt :
            (EvmYul.UInt256.ofNat 0).toNat <
              (xLo.toByteArray.write 0
                (xHi.toByteArray.write 0 m.memory (EvmYul.UInt256.ofNat 0).toNat 32)
                (EvmYul.UInt256.ofNat 32).toNat 32).size := by
          rw [hzero]
          omega
        exact (not_le_of_gt hgt) hmem
    | inr hactiveMem =>
        norm_num [EvmYul.MachineState.M, EvmYul.UInt256.ofNat, EvmYul.UInt256.mul,
          EvmYul.UInt256.toNat, EvmYul.UInt256.size] at hactiveMem
        exact
          (by decide :
            ¬ ((({ val := 3 } : EvmYul.UInt256) * ({ val := 32 } : EvmYul.UInt256)) ≤
              ({ val := (0 : Fin EvmYul.UInt256.size) } : EvmYul.UInt256))) hactiveMem
  simp [FormalYul.word, EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord,
    hactive,
    EvmYul.writeBytes, EvmYul.fromByteArrayBigEndian, EvmYul.MachineState.M,
    hcond]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp
  have hread :
      ((xLo.toByteArray.write 0 (xHi.toByteArray.write 0 m.memory (EvmYul.UInt256.ofNat 0).toNat 32)
            (EvmYul.UInt256.ofNat 32).toNat 32).readWithPadding
          (EvmYul.UInt256.ofNat 0).toNat 32).data.toList =
        xHi.toByteArray.data.toList := by
    simpa using
      read_two_word_write_first_data xHi.toByteArray xLo.toByteArray m.memory
        (EvmYul.UInt256.toByteArray_size xHi)
  rw [hread]
  change FormalYul.u256 (EvmYul.fromByteArrayBigEndian xHi.toByteArray) = FormalYul.wordNat xHi
  simp [FormalYul.u256, FormalYul.WORD_MOD, FormalYul.wordNat]
  exact xHi.val.isLt

theorem mload_two_word_write_second (m : EvmYul.MachineState) (xHi xLo : EvmYul.UInt256)
    (hactive : m.activeWords = FormalYul.word 3) :
    (((m.mstore (FormalYul.word 0) xHi).mstore (FormalYul.word 32) xLo).mload (FormalYul.word 32)).1 =
      xLo := by
  unfold EvmYul.MachineState.mload EvmYul.MachineState.lookupMemory
  have hsize : 64 ≤ (xLo.toByteArray.write 0 (xHi.toByteArray.write 0 m.memory 0 32) 32 32).size :=
    two_word_write_size_ge_64 xHi.toByteArray xLo.toByteArray m.memory
  have hsize' :
      64 ≤ (xLo.toByteArray.write 0 (xHi.toByteArray.write 0 m.memory (EvmYul.UInt256.ofNat 0).toNat 32)
        (EvmYul.UInt256.ofNat 32).toNat 32).size := by
    simpa using hsize
  have h32 : (EvmYul.UInt256.ofNat 32).toNat = 32 := rfl
  have hcond :
      ¬ ((xLo.toByteArray.write 0 (xHi.toByteArray.write 0 m.memory (EvmYul.UInt256.ofNat 0).toNat 32)
                (EvmYul.UInt256.ofNat 32).toNat 32).size ≤
            (EvmYul.UInt256.ofNat 32).toNat ∨
          EvmYul.UInt256.ofNat
                (max
                  (EvmYul.UInt256.ofNat
                      (max (EvmYul.UInt256.ofNat 3).toNat (((EvmYul.UInt256.ofNat 0).toNat + 32 + 31) / 32))).toNat
                  (((EvmYul.UInt256.ofNat 32).toNat + 32 + 31) / 32)) *
              { val := 32 } ≤
            EvmYul.UInt256.ofNat 32) := by
    intro h
    cases h with
    | inl hmem =>
        have hgt :
            (EvmYul.UInt256.ofNat 32).toNat <
              (xLo.toByteArray.write 0
                (xHi.toByteArray.write 0 m.memory (EvmYul.UInt256.ofNat 0).toNat 32)
                (EvmYul.UInt256.ofNat 32).toNat 32).size := by
          rw [h32]
          omega
        exact (not_le_of_gt hgt) hmem
    | inr hactiveMem =>
        norm_num [EvmYul.MachineState.M, EvmYul.UInt256.ofNat, EvmYul.UInt256.mul,
          EvmYul.UInt256.toNat, EvmYul.UInt256.size] at hactiveMem
        exact
          (by decide :
            ¬ ((({ val := 3 } : EvmYul.UInt256) * ({ val := 32 } : EvmYul.UInt256)) ≤
              ({ val := (32 : Fin EvmYul.UInt256.size) } : EvmYul.UInt256))) hactiveMem
  simp [FormalYul.word, EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord,
    hactive,
    EvmYul.writeBytes, EvmYul.fromByteArrayBigEndian, EvmYul.MachineState.M,
    hcond]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp
  have hread :
      ((xLo.toByteArray.write 0 (xHi.toByteArray.write 0 m.memory (EvmYul.UInt256.ofNat 0).toNat 32)
            (EvmYul.UInt256.ofNat 32).toNat 32).readWithPadding
          (EvmYul.UInt256.ofNat 32).toNat 32).data.toList =
        xLo.toByteArray.data.toList := by
    simpa using
      read_two_word_write_second_data xHi.toByteArray xLo.toByteArray m.memory
        (EvmYul.UInt256.toByteArray_size xHi) (EvmYul.UInt256.toByteArray_size xLo)
  rw [hread]
  change FormalYul.u256 (EvmYul.fromByteArrayBigEndian xLo.toByteArray) = FormalYul.wordNat xLo
  simp [FormalYul.u256, FormalYul.WORD_MOD, FormalYul.wordNat]
  exact xLo.val.isLt

theorem mstore_two_word_active_3 (m : EvmYul.MachineState) (xHi xLo : EvmYul.UInt256)
    (hactive : m.activeWords = FormalYul.word 3) :
    ((m.mstore (FormalYul.word 0) xHi).mstore (FormalYul.word 32) xLo).activeWords =
      FormalYul.word 3 := by
  cases m
  simp [EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord, EvmYul.writeBytes,
    EvmYul.MachineState.M, FormalYul.word, hactive]
  decide

theorem mload_two_word_write_first_state (m : EvmYul.MachineState) (xHi xLo : EvmYul.UInt256)
    (hactive : m.activeWords = FormalYul.word 3) :
    (((m.mstore (FormalYul.word 0) xHi).mstore (FormalYul.word 32) xLo).mload (FormalYul.word 0)).2 =
      ((m.mstore (FormalYul.word 0) xHi).mstore (FormalYul.word 32) xLo) := by
  cases m
  simp [EvmYul.MachineState.mload, EvmYul.MachineState.mstore,
    EvmYul.MachineState.writeWord, EvmYul.writeBytes, EvmYul.MachineState.M,
    FormalYul.word, hactive]
  decide

theorem mload_two_word_write_second_state (m : EvmYul.MachineState) (xHi xLo : EvmYul.UInt256)
    (hactive : m.activeWords = FormalYul.word 3) :
    (((m.mstore (FormalYul.word 0) xHi).mstore (FormalYul.word 32) xLo).mload (FormalYul.word 32)).2 =
      ((m.mstore (FormalYul.word 0) xHi).mstore (FormalYul.word 32) xLo) := by
  cases m
  simp [EvmYul.MachineState.mload, EvmYul.MachineState.mstore,
    EvmYul.MachineState.writeWord, EvmYul.writeBytes, EvmYul.MachineState.M,
    FormalYul.word, hactive]
  decide


@[simp] theorem sqrt_bridge_u256 (x : Nat) : SqrtYul.u256 x = FormalYul.u256 x := rfl
@[simp] theorem sqrt_bridge_add (a b : Nat) : SqrtYul.evmAdd a b = FormalYul.evmAdd a b := rfl
@[simp] theorem sqrt_bridge_sub (a b : Nat) : SqrtYul.evmSub a b = FormalYul.evmSub a b := rfl
@[simp] theorem sqrt_bridge_mul (a b : Nat) : SqrtYul.evmMul a b = FormalYul.evmMul a b := rfl
@[simp] theorem sqrt_bridge_div (a b : Nat) : SqrtYul.evmDiv a b = FormalYul.evmDiv a b := rfl
@[simp] theorem sqrt_bridge_shl (a b : Nat) : SqrtYul.evmShl a b = FormalYul.evmShl a b := rfl
@[simp] theorem sqrt_bridge_shr (a b : Nat) : SqrtYul.evmShr a b = FormalYul.evmShr a b := rfl
@[simp] theorem sqrt_bridge_clz (a : Nat) : SqrtYul.evmClz a = FormalYul.evmClz a := rfl
@[simp] theorem sqrt_bridge_lt (a b : Nat) : SqrtYul.evmLt a b = FormalYul.evmLt a b := rfl
@[simp] theorem sqrt_bridge_gt (a b : Nat) : SqrtYul.evmGt a b = FormalYul.evmGt a b := rfl

@[simp]
theorem call_zero_value_for_split_t_uint256 (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 10) [] (.some "zero_value_for_split_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_zero_value_for_split_t_uint256]
  simp only [yulFunction_zero_value_for_split_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_zero_value_for_split_t_bool (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 10) [] (.some "zero_value_for_split_t_bool") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_zero_value_for_split_t_bool]
  simp only [yulFunction_zero_value_for_split_t_bool,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_fun__mul_1022
    (x y : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 80) [FormalYul.word x, FormalYul.word y]
      (.some "fun__mul_1022") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (evmSub (evmSub (evmMulmod x y
        115792089237316195423570985008687907853269984665640564039457584007913129639935)
        (evmMul x y))
        (evmLt (evmMulmod x y
          115792089237316195423570985008687907853269984665640564039457584007913129639935)
          (evmMul x y))),
       FormalYul.word (evmMul x y)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__mul_1022]
  simp only [yulFunction_fun__mul_1022,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_zero_value_for_split_t_uint256,
    FormalYul.word, Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  constructor
  · apply FormalYul.Preservation.eq_of_wordNat_eq
    simp [FormalYul.Preservation.wordNat_sub, FormalYul.Preservation.wordNat_mulMod,
      FormalYul.Preservation.wordNat_mul, FormalYul.Preservation.wordNat_lt,
      FormalYul.Preservation.wordNat_not, formal_evmNot_zero]
  · apply FormalYul.Preservation.eq_of_wordNat_eq
    simp [FormalYul.Preservation.wordNat_mul]

@[simp]
theorem call_fun__gt_1766
    (xHi xLo yHi yLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 70)
      [FormalYul.word xHi, FormalYul.word xLo, FormalYul.word yHi, FormalYul.word yLo]
      (.some "fun__gt_1766") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (evmOr (evmGt xHi yHi) (evmAnd (evmEq xHi yHi) (evmGt xLo yLo)))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__gt_1766]
  simp only [yulFunction_fun__gt_1766,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_zero_value_for_split_t_bool,
    FormalYul.word, Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp [FormalYul.Preservation.wordNat_gt, FormalYul.Preservation.wordNat_or,
    FormalYul.Preservation.wordNat_and, FormalYul.Preservation.wordNat_eq]

@[simp]
theorem call_fun_toUint_5616
    (b : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 50) [FormalYul.word b]
      (.some "fun_toUint_5616") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word b]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_toUint_5616]
  simp only [yulFunction_fun_toUint_5616,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_zero_value_for_split_t_uint256,
    FormalYul.word, Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_fun__add_637
    (xHi xLo y : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 70)
      [FormalYul.word xHi, FormalYul.word xLo, FormalYul.word y]
      (.some "fun__add_637") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (evmAdd xHi (evmLt (evmAdd xLo y) xLo)),
       FormalYul.word (evmAdd xLo y)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__add_637]
  simp only [yulFunction_fun__add_637,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_zero_value_for_split_t_uint256,
    FormalYul.word, Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  constructor
  · apply FormalYul.Preservation.eq_of_wordNat_eq
    simp [FormalYul.Preservation.wordNat_add, FormalYul.Preservation.wordNat_lt]
  · apply FormalYul.Preservation.eq_of_wordNat_eq
    simp [FormalYul.Preservation.wordNat_add]

@[simp]
theorem call_fun__sqrt_6169
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 220) [FormalYul.word x] (.some "fun__sqrt_6169") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (SqrtYul.model_sqrt_evm x)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__sqrt_6169]
  simp only [yulFunction_fun__sqrt_6169,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp [SqrtYul.model_sqrt_evm, FormalYul.word]

end Sqrt512Yul

namespace Sqrt512Yul

@[simp]
theorem call_zero_value_for_split_t_userDefinedValueType__uint512__113
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 10) [] (.some "zero_value_for_split_t_userDefinedValueType$_uint512_$113") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_zero_value_for_split_t_userDefinedValueType__uint512__113]
  simp only [yulFunction_zero_value_for_split_t_userDefinedValueType__uint512__113,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_fun_tmp_128
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 40) [] (.some "fun_tmp_128") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_tmp_128]
  simp only [yulFunction_fun_tmp_128,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_zero_value_for_split_t_userDefinedValueType__uint512__113,
    FormalYul.word, Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

end Sqrt512Yul

namespace Sqrt512Yul

def sharedAfterFrom0 (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat) :
    EvmYul.SharedState .Yul :=
  { shared with
    toMachineState :=
      ((shared.toMachineState.mstore (FormalYul.word 0) (FormalYul.word xHi)).mstore
        (FormalYul.word 32) (FormalYul.word xLo)) }

def sharedAfterFrom128 (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat) :
    EvmYul.SharedState .Yul :=
  { shared with
    toMachineState :=
      ((shared.toMachineState.mstore (FormalYul.word 128) (FormalYul.word xHi)).mstore
        (FormalYul.word 160) (FormalYul.word xLo)) }

@[simp]
theorem sharedAfterFrom0_lookup
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    (sharedAfterFrom0 shared xHi xLo).accountMap.find?
        (sharedAfterFrom0 shared xHi xLo).executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract) := by
  simpa [sharedAfterFrom0] using hlookup

@[simp]
theorem sharedAfterFrom128_lookup
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    (sharedAfterFrom128 shared xHi xLo).accountMap.find?
        (sharedAfterFrom128 shared xHi xLo).executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract) := by
  simpa [sharedAfterFrom128] using hlookup

theorem sharedState_eta (shared : EvmYul.SharedState .Yul) :
    { toState := shared.toState, toMachineState := shared.toMachineState } = shared := by
  cases shared
  rfl

@[simp]
theorem sharedAfterFrom0_mload0
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    ((sharedAfterFrom0 shared xHi xLo).toMachineState.mload (FormalYul.word 0)).1 =
      FormalYul.word xHi := by
  simpa [sharedAfterFrom0] using
    mload_two_word_write_first shared.toMachineState (FormalYul.word xHi) (FormalYul.word xLo)
      hactive

@[simp]
theorem sharedAfterFrom0_mload32
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    ((sharedAfterFrom0 shared xHi xLo).toMachineState.mload (FormalYul.word 32)).1 =
      FormalYul.word xLo := by
  simpa [sharedAfterFrom0] using
    mload_two_word_write_second shared.toMachineState (FormalYul.word xHi) (FormalYul.word xLo)
      hactive

@[simp]
theorem sharedAfterFrom0_mload0_state
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    ((sharedAfterFrom0 shared xHi xLo).toMachineState.mload (FormalYul.word 0)).2 =
      (sharedAfterFrom0 shared xHi xLo).toMachineState := by
  simpa [sharedAfterFrom0] using
    mload_two_word_write_first_state shared.toMachineState (FormalYul.word xHi) (FormalYul.word xLo)
      hactive

@[simp]
theorem sharedAfterFrom0_mload32_state
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    ((sharedAfterFrom0 shared xHi xLo).toMachineState.mload (FormalYul.word 32)).2 =
      (sharedAfterFrom0 shared xHi xLo).toMachineState := by
  simpa [sharedAfterFrom0] using
    mload_two_word_write_second_state shared.toMachineState (FormalYul.word xHi) (FormalYul.word xLo)
      hactive

@[simp]
theorem sharedAfterFrom0_mload0_inherited
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    ((sharedAfterFrom0 shared xHi xLo).mload (FormalYul.word 0)).1 =
      FormalYul.word xHi := by
  simpa using sharedAfterFrom0_mload0 shared xHi xLo hactive

@[simp]
theorem sharedAfterFrom0_mload32_inherited
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    ((sharedAfterFrom0 shared xHi xLo).mload (FormalYul.word 32)).1 =
      FormalYul.word xLo := by
  simpa using sharedAfterFrom0_mload32 shared xHi xLo hactive

@[simp]
theorem sharedAfterFrom0_mload0_state_inherited
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    ((sharedAfterFrom0 shared xHi xLo).mload (FormalYul.word 0)).2 =
      (sharedAfterFrom0 shared xHi xLo).toMachineState := by
  simpa using sharedAfterFrom0_mload0_state shared xHi xLo hactive

@[simp]
theorem sharedAfterFrom0_mload32_state_inherited
    (shared : EvmYul.SharedState .Yul) (xHi xLo : Nat)
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    ((sharedAfterFrom0 shared xHi xLo).mload (FormalYul.word 32)).2 =
      (sharedAfterFrom0 shared xHi xLo).toMachineState := by
  simpa using sharedAfterFrom0_mload32_state shared xHi xLo hactive

@[simp]
theorem call_fun_from_156_zero
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100) [FormalYul.word 0, FormalYul.word xHi, FormalYul.word xLo]
      (.some "fun_from_156") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store, [FormalYul.word 0]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_from_156]
  simp only [yulFunction_fun_from_156,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, sharedAfterFrom0, EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.setMachineState, EvmYul.Yul.State.toMachineState,
    call_zero_value_for_split_t_userDefinedValueType__uint512__113,
    FormalYul.word, Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_fun_from_156_128
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100) [FormalYul.word 128, FormalYul.word xHi, FormalYul.word xLo]
      (.some "fun_from_156") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom128 shared xHi xLo) store, [FormalYul.word 128]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_from_156]
  simp only [yulFunction_fun_from_156,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, sharedAfterFrom128, EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.setMachineState, EvmYul.Yul.State.toMachineState,
    call_zero_value_for_split_t_userDefinedValueType__uint512__113,
    FormalYul.word, Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  have haddr : EvmYul.UInt256.ofNat 32 + EvmYul.UInt256.ofNat 128 =
      EvmYul.UInt256.ofNat 160 := by
    decide
  rw [haddr]

@[simp]
theorem call_fun_into_182_from0
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract))
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    EvmYul.Yul.call (fuel + 120) [FormalYul.word 0]
      (.some "fun_into_182") (.some yulContract)
      (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [FormalYul.word xHi, FormalYul.word xLo]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv,
    sharedAfterFrom0_lookup shared xHi xLo hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_into_182]
  simp only [yulFunction_fun_into_182,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, hactive, sharedAfterFrom0_lookup,
    sharedAfterFrom0_mload0, sharedAfterFrom0_mload32,
    sharedAfterFrom0_mload0_state, sharedAfterFrom0_mload32_state,
    EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.setMachineState, EvmYul.Yul.State.toMachineState,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_zero_value_for_split_t_uint256,
    FormalYul.word, Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  have h0state :
      ((sharedAfterFrom0 shared xHi xLo).mload (EvmYul.UInt256.ofNat 0)).2 =
        (sharedAfterFrom0 shared xHi xLo).toMachineState := by
    simpa [FormalYul.word] using
      sharedAfterFrom0_mload0_state_inherited shared xHi xLo hactive
  have h32state :
      ((sharedAfterFrom0 shared xHi xLo).toMachineState.mload (EvmYul.UInt256.ofNat 32)).2 =
        (sharedAfterFrom0 shared xHi xLo).toMachineState := by
    simpa [FormalYul.word] using
      sharedAfterFrom0_mload32_state shared xHi xLo hactive
  have h0value :
      ((sharedAfterFrom0 shared xHi xLo).mload (EvmYul.UInt256.ofNat 0)).1 =
        EvmYul.UInt256.ofNat xHi := by
    simpa [FormalYul.word] using
      sharedAfterFrom0_mload0_inherited shared xHi xLo hactive
  have h32value :
      ((sharedAfterFrom0 shared xHi xLo).toMachineState.mload (EvmYul.UInt256.ofNat 32)).1 =
        EvmYul.UInt256.ofNat xLo := by
    simpa [FormalYul.word] using
      sharedAfterFrom0_mload32 shared xHi xLo hactive
  constructor
  · rw [h0state, h32state]
  · constructor
    · exact h0value
    · rw [h0state]
      exact h32value

@[simp]
theorem call_fun_into_182_from0_5591
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract))
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    EvmYul.Yul.call (fuel + 5591) [FormalYul.word 0]
      (.some "fun_into_182") (.some yulContract)
      (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [FormalYul.word xHi, FormalYul.word xLo]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_into_182_from0 (xHi := xHi) (xLo := xLo) (fuel := fuel + 5471)
      (shared := shared) (store := store) (hlookup := hlookup) (hactive := hactive)

@[simp]
theorem call_fun_into_182_from0_5591_raw
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract))
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    EvmYul.Yul.call (fuel + 5591) [EvmYul.UInt256.ofNat 0]
      (.some "fun_into_182") (.some yulContract)
      (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]) := by
  simpa [FormalYul.word] using
    call_fun_into_182_from0_5591 (xHi := xHi) (xLo := xLo) (fuel := fuel)
      (shared := shared) (store := store) (hlookup := hlookup) (hactive := hactive)

end Sqrt512Yul

namespace Sqrt512Yul

@[simp]
theorem call_cleanup_t_rational_0_by_1
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 10) [v] (.some "cleanup_t_rational_0_by_1") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_cleanup_t_rational_0_by_1]
  simp only [yulFunction_cleanup_t_rational_0_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_fun_sqrt_6185
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 260) [FormalYul.word x] (.some "fun_sqrt_6185") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (model_sqrt256_floor_evm x)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_sqrt_6185]
  simp only [yulFunction_fun_sqrt_6185,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_fun__sqrt_6169 (x := x) (fuel := fuel + 187) (shared := shared),
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp [model_sqrt256_floor_evm, SqrtYul.model_sqrt_evm, FormalYul.word]

@[simp]
theorem call_fun_sqrtUp_6201
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 260) [FormalYul.word x] (.some "fun_sqrtUp_6201") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (model_sqrt256_up_evm x)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_sqrtUp_6201]
  simp only [yulFunction_fun_sqrtUp_6201,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_fun__sqrt_6169 (x := x) (fuel := fuel + 187) (shared := shared),
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp [model_sqrt256_up_evm, SqrtYul.model_sqrt_evm, FormalYul.word]

end Sqrt512Yul

namespace Sqrt512Yul


@[simp]
theorem call_cleanup_t_uint256
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 10) [v] (.some "cleanup_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_cleanup_t_uint256]
  simp only [yulFunction_cleanup_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_fun_clz_6141
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 40) [FormalYul.word x] (.some "fun_clz_6141") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmClz x)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_clz_6141]
  simp only [yulFunction_fun_clz_6141,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp [FormalYul.word]

@[simp]
theorem call_fun_unsafeDiv_5899
    (a b : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 40) [FormalYul.word a, FormalYul.word b] (.some "fun_unsafeDiv_5899") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmDiv a b)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_unsafeDiv_5899]
  simp only [yulFunction_fun_unsafeDiv_5899,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp [FormalYul.word]

@[simp]
theorem call_fun_unsafeDec_5854
    (x : Nat) (b : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 40) [FormalYul.word x, b] (.some "fun_unsafeDec_5854") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmSub x (FormalYul.wordNat b))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_unsafeDec_5854]
  simp only [yulFunction_fun_unsafeDec_5854,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_zero_value_for_split_t_uint256,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp [FormalYul.word, FormalYul.Preservation.wordNat_sub]

@[simp]
theorem call_fun_unsafeDec_5854_1334
    (x : Nat) (b : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 1334) [FormalYul.word x, b] (.some "fun_unsafeDec_5854") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmSub x (FormalYul.wordNat b))]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_unsafeDec_5854 (x := x) (b := b) (fuel := fuel + 1294)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_wrapping_add_t_uint256
    (a b : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 40) [FormalYul.word a, FormalYul.word b] (.some "wrapping_add_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmAdd a b)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_wrapping_add_t_uint256]
  simp only [yulFunction_wrapping_add_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp [FormalYul.word]

@[simp]
theorem call_wrapping_mul_t_uint256
    (a b : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 40) [FormalYul.word a, FormalYul.word b] (.some "wrapping_mul_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmMul a b)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_wrapping_mul_t_uint256]
  simp only [yulFunction_wrapping_mul_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_cleanup_t_uint256,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp [FormalYul.word]

@[simp]
theorem call_fun_and_5596
    (a b : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 40) [FormalYul.word a, FormalYul.word b] (.some "fun_and_5596") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmAnd a b)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_and_5596]
  simp only [yulFunction_fun_and_5596,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_zero_value_for_split_t_bool,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp [FormalYul.word]

@[simp]
theorem call_fun_and_5596_u256
    (a b : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 40) [a, b] (.some "fun_and_5596") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (evmAnd (FormalYul.wordNat a) (FormalYul.wordNat b))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_and_5596]
  simp only [yulFunction_fun_and_5596,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_zero_value_for_split_t_bool,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp [FormalYul.word]

@[simp]
theorem call_fun_and_5596_u256_932
    (a b : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 932) [a, b] (.some "fun_and_5596") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (evmAnd (FormalYul.wordNat a) (FormalYul.wordNat b))]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_and_5596_u256 (a := a) (b := b) (fuel := fuel + 892)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_fun_or_5585
    (a b : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 40) [FormalYul.word a, FormalYul.word b] (.some "fun_or_5585") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmOr a b)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_or_5585]
  simp only [yulFunction_fun_or_5585,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_zero_value_for_split_t_bool,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp [FormalYul.word]

@[simp]
theorem call_fun_or_5585_u256
    (a b : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 40) [a, b] (.some "fun_or_5585") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (evmOr (FormalYul.wordNat a) (FormalYul.wordNat b))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_or_5585]
  simp only [yulFunction_fun_or_5585,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_zero_value_for_split_t_bool,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp [FormalYul.word]

@[simp]
theorem call_fun_or_5585_u256_928
    (a b : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 928) [a, b] (.some "fun_or_5585") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (evmOr (FormalYul.wordNat a) (FormalYul.wordNat b))]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_or_5585_u256 (a := a) (b := b) (fuel := fuel + 888)
      (shared := shared) (store := store) (hlookup := hlookup)

end Sqrt512Yul

namespace Sqrt512Yul

@[simp]
theorem call_cleanup_t_uint8_one
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 10) [FormalYul.word 1] (.some "cleanup_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 1]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_cleanup_t_uint8]
  simp only [yulFunction_cleanup_t_uint8,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_cleanup_t_uint8_128
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 10) [FormalYul.word 128] (.some "cleanup_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 128]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_cleanup_t_uint8]
  simp only [yulFunction_cleanup_t_uint8,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_shift_right_unsigned_dynamic
    (bits value : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [FormalYul.word bits, FormalYul.word value]
      (.some "shift_right_unsigned_dynamic") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmShr bits value)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_shift_right_unsigned_dynamic]
  simp only [yulFunction_shift_right_unsigned_dynamic,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp [FormalYul.word]

@[simp]
theorem call_shift_left_dynamic
    (bits value : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [FormalYul.word bits, FormalYul.word value]
      (.some "shift_left_dynamic") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmShl bits value)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_shift_left_dynamic]
  simp only [yulFunction_shift_left_dynamic,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp [FormalYul.word]

@[simp]
theorem call_shift_right_t_uint256_t_uint8_one
    (value : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 80) [FormalYul.word value, FormalYul.word 1]
      (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmShr 1 value)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_shift_right_t_uint256_t_uint8]
  simp only [yulFunction_shift_right_t_uint256_t_uint8,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_cleanup_t_uint8_one, call_cleanup_t_uint256, call_shift_right_unsigned_dynamic,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_shift_right_t_uint256_t_uint256
    (value bits : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 80) [FormalYul.word value, FormalYul.word bits]
      (.some "shift_right_t_uint256_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmShr bits value)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_shift_right_t_uint256_t_uint256]
  simp only [yulFunction_shift_right_t_uint256_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_cleanup_t_uint256, call_shift_right_unsigned_dynamic,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_fun__shl256_3075
    (xHi xLo s : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 120) [FormalYul.word xHi, FormalYul.word xLo, FormalYul.word s]
      (.some "fun__shl256_3075") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (evmShr (evmSub 256 s) xHi),
       FormalYul.word (evmOr (evmShl s xHi) (evmShr (evmSub 256 s) xLo)),
       FormalYul.word (evmShl s xLo)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__shl256_3075]
  simp only [yulFunction_fun__shl256_3075,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  constructor
  · apply FormalYul.Preservation.eq_of_wordNat_eq
    simp [FormalYul.word]
  · constructor
    · apply FormalYul.Preservation.eq_of_wordNat_eq
      simp [FormalYul.word]
    · apply FormalYul.Preservation.eq_of_wordNat_eq
      simp [FormalYul.word]

@[simp]
theorem call_fun__shl256_3075_4981
    (xHi xLo s : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 4981) [FormalYul.word xHi, FormalYul.word xLo, FormalYul.word s]
      (.some "fun__shl256_3075") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (evmShr (evmSub 256 s) xHi),
       FormalYul.word (evmOr (evmShl s xHi) (evmShr (evmSub 256 s) xLo)),
       FormalYul.word (evmShl s xLo)]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun__shl256_3075 (xHi := xHi) (xLo := xLo) (s := s)
      (fuel := fuel + 4861) (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_fun__shl256_3075_u256
    (xHi xLo : Nat) (s : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 120) [FormalYul.word xHi, FormalYul.word xLo, s]
      (.some "fun__shl256_3075") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (evmShr (evmSub 256 (FormalYul.wordNat s)) xHi),
       FormalYul.word (evmOr (evmShl (FormalYul.wordNat s) xHi)
        (evmShr (evmSub 256 (FormalYul.wordNat s)) xLo)),
       FormalYul.word (evmShl (FormalYul.wordNat s) xLo)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__shl256_3075]
  simp only [yulFunction_fun__shl256_3075,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  constructor
  · apply FormalYul.Preservation.eq_of_wordNat_eq
    simp [FormalYul.word]
  · constructor
    · apply FormalYul.Preservation.eq_of_wordNat_eq
      simp [FormalYul.word]
    · apply FormalYul.Preservation.eq_of_wordNat_eq
      simp [FormalYul.word]

@[simp]
theorem call_fun__shl256_3075_u256_4981
    (xHi xLo : Nat) (s : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 4981) [FormalYul.word xHi, FormalYul.word xLo, s]
      (.some "fun__shl256_3075") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (evmShr (evmSub 256 (FormalYul.wordNat s)) xHi),
       FormalYul.word (evmOr (evmShl (FormalYul.wordNat s) xHi)
        (evmShr (evmSub 256 (FormalYul.wordNat s)) xLo)),
       FormalYul.word (evmShl (FormalYul.wordNat s) xLo)]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun__shl256_3075_u256 (xHi := xHi) (xLo := xLo) (s := s)
      (fuel := fuel + 4861) (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_shift_left_t_uint256_t_uint8_128
    (value : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 80) [FormalYul.word value, FormalYul.word 128]
      (.some "shift_left_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmShl 128 value)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_shift_left_t_uint256_t_uint8]
  simp only [yulFunction_shift_left_t_uint256_t_uint8,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_cleanup_t_uint8_128, call_cleanup_t_uint256, call_shift_left_dynamic,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_shift_left_t_uint256_t_uint8_128_990
    (value : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 990) [FormalYul.word value, EvmYul.UInt256.ofNat 128]
      (.some "shift_left_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmShl 128 value)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_left_t_uint256_t_uint8_128 (value := value) (fuel := fuel + 910)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_shift_left_t_uint256_t_uint8_128_958
    (value : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 958) [FormalYul.word value, EvmYul.UInt256.ofNat 128]
      (.some "shift_left_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmShl 128 value)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_left_t_uint256_t_uint8_128 (value := value) (fuel := fuel + 878)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_shift_left_t_uint256_t_uint8_128_955
    (value : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 955) [FormalYul.word value, EvmYul.UInt256.ofNat 128]
      (.some "shift_left_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmShl 128 value)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_left_t_uint256_t_uint8_128 (value := value) (fuel := fuel + 875)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_shift_left_t_uint256_t_uint8_128_946
    (value : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 946) [FormalYul.word value, EvmYul.UInt256.ofNat 128]
      (.some "shift_left_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmShl 128 value)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_left_t_uint256_t_uint8_128 (value := value) (fuel := fuel + 866)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_shift_right_t_uint256_t_uint8_128
    (value : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 80) [FormalYul.word value, FormalYul.word 128]
      (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmShr 128 value)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_shift_right_t_uint256_t_uint8]
  simp only [yulFunction_shift_right_t_uint256_t_uint8,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_cleanup_t_uint8_128, call_cleanup_t_uint256, call_shift_right_unsigned_dynamic,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_shift_right_t_uint256_t_uint8_128_976
    (value : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 976) [FormalYul.word value, EvmYul.UInt256.ofNat 128]
      (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmShr 128 value)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_right_t_uint256_t_uint8_128 (value := value) (fuel := fuel + 896)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_shift_right_t_uint256_t_uint8_128_970
    (value : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 970) [FormalYul.word value, EvmYul.UInt256.ofNat 128]
      (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmShr 128 value)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_right_t_uint256_t_uint8_128 (value := value) (fuel := fuel + 890)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_shift_right_t_uint256_t_uint8_128_964
    (value : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 964) [FormalYul.word value, EvmYul.UInt256.ofNat 128]
      (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmShr 128 value)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_right_t_uint256_t_uint8_128 (value := value) (fuel := fuel + 884)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_shift_right_t_uint256_t_uint8_128_961
    (value : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 961) [FormalYul.word value, EvmYul.UInt256.ofNat 128]
      (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmShr 128 value)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_right_t_uint256_t_uint8_128 (value := value) (fuel := fuel + 881)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_shift_right_t_uint256_t_uint8_128_955
    (value : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 955) [FormalYul.word value, EvmYul.UInt256.ofNat 128]
      (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmShr 128 value)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_right_t_uint256_t_uint8_128 (value := value) (fuel := fuel + 875)
      (shared := shared) (store := store) (hlookup := hlookup)

end Sqrt512Yul


namespace Sqrt512Yul



@[simp]
theorem call_cleanup_t_rational_1_by_1
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 10) [v] (.some "cleanup_t_rational_1_by_1") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_cleanup_t_rational_1_by_1]
  simp only [yulFunction_cleanup_t_rational_1_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_identity
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 10) [v] (.some "identity") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_identity]
  simp only [yulFunction_identity,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_convert_t_rational_0_by_1_to_t_uint256
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [v] (.some "convert_t_rational_0_by_1_to_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_convert_t_rational_0_by_1_to_t_uint256]
  simp only [yulFunction_convert_t_rational_0_by_1_to_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_cleanup_t_uint256, call_cleanup_t_rational_0_by_1, call_identity,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]


@[simp]
theorem call_cleanup_t_rational_1_by_1_12
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 12) [v] (.some "cleanup_t_rational_1_by_1") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_rational_1_by_1 (v := v) (fuel := fuel + 2) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp]
theorem call_cleanup_t_rational_240615969168004511545033772477625056927_by_1
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 10) [v]
      (.some "cleanup_t_rational_240615969168004511545033772477625056927_by_1") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_cleanup_t_rational_240615969168004511545033772477625056927_by_1]
  simp only [yulFunction_cleanup_t_rational_240615969168004511545033772477625056927_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_cleanup_t_rational_240615969168004511545033772477625056927_by_1_12
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 12) [v]
      (.some "cleanup_t_rational_240615969168004511545033772477625056927_by_1") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_rational_240615969168004511545033772477625056927_by_1
      (v := v) (fuel := fuel + 2) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp]
theorem call_cleanup_t_rational_128_by_1
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 10) [v] (.some "cleanup_t_rational_128_by_1") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_cleanup_t_rational_128_by_1]
  simp only [yulFunction_cleanup_t_rational_128_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_cleanup_t_rational_128_by_1_12
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 12) [v] (.some "cleanup_t_rational_128_by_1") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_rational_128_by_1 (v := v) (fuel := fuel + 2)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_cleanup_t_rational_254_by_1
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 10) [v] (.some "cleanup_t_rational_254_by_1") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_cleanup_t_rational_254_by_1]
  simp only [yulFunction_cleanup_t_rational_254_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_cleanup_t_rational_254_by_1_12
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 12) [v] (.some "cleanup_t_rational_254_by_1") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_rational_254_by_1 (v := v) (fuel := fuel + 2)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_cleanup_t_rational_340282366920938463463374607431768211455_by_1
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 10) [v]
      (.some "cleanup_t_rational_340282366920938463463374607431768211455_by_1") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_cleanup_t_rational_340282366920938463463374607431768211455_by_1]
  simp only [yulFunction_cleanup_t_rational_340282366920938463463374607431768211455_by_1,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_cleanup_t_rational_340282366920938463463374607431768211455_by_1_12
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 12) [v]
      (.some "cleanup_t_rational_340282366920938463463374607431768211455_by_1") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_rational_340282366920938463463374607431768211455_by_1
      (v := v) (fuel := fuel + 2) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp]
theorem call_identity_14
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 14) [v] (.some "identity") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_identity (v := v) (fuel := fuel + 4) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp]
theorem call_cleanup_t_uint256_16
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 16) [v] (.some "cleanup_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_uint256 (v := v) (fuel := fuel + 6) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp]
theorem call_cleanup_t_uint8_one_16
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 16) [FormalYul.word 1] (.some "cleanup_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 1]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_uint8_one (fuel := fuel + 6) (shared := shared) (store := store)
      (hlookup := hlookup)


@[simp]
theorem call_cleanup_t_uint8_one_16_raw
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 16) [EvmYul.UInt256.ofNat 1] (.some "cleanup_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 1]) := by
  simpa [FormalYul.word] using
    call_cleanup_t_uint8_one_16 (fuel := fuel) (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_cleanup_t_uint8_128_16
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 16) [FormalYul.word 128] (.some "cleanup_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 128]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_cleanup_t_uint8_128 (fuel := fuel + 6) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp]
theorem call_cleanup_t_uint8_128_16_raw
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 16) [EvmYul.UInt256.ofNat 128] (.some "cleanup_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 128]) := by
  simpa [FormalYul.word] using
    call_cleanup_t_uint8_128_16 (fuel := fuel) (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_convert_t_rational_1_by_1_to_t_uint8_one
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [FormalYul.word 1]
      (.some "convert_t_rational_1_by_1_to_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 1]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_convert_t_rational_1_by_1_to_t_uint8]
  simp only [yulFunction_convert_t_rational_1_by_1_to_t_uint8,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  rw [call_cleanup_t_rational_1_by_1_12 (v := EvmYul.UInt256.ofNat 1) (fuel := fuel)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 1)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide [EvmYul.Yul.head', EvmYul.Yul.reverse', EvmYul.Yul.cons']
  rw [call_identity_14 (v := EvmYul.UInt256.ofNat 1) (fuel := fuel)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 1)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide [EvmYul.Yul.head', EvmYul.Yul.reverse', EvmYul.Yul.cons']
  rw [call_cleanup_t_uint8_one_16_raw (fuel := fuel) (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 1)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide [EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]


@[simp]
theorem call_convert_t_rational_128_by_1_to_t_uint8_128
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [FormalYul.word 128]
      (.some "convert_t_rational_128_by_1_to_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 128]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_convert_t_rational_128_by_1_to_t_uint8]
  simp only [yulFunction_convert_t_rational_128_by_1_to_t_uint8,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  rw [call_cleanup_t_rational_128_by_1_12 (v := EvmYul.UInt256.ofNat 128) (fuel := fuel)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 128)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide [EvmYul.Yul.head', EvmYul.Yul.reverse', EvmYul.Yul.cons']
  rw [call_identity_14 (v := EvmYul.UInt256.ofNat 128) (fuel := fuel)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 128)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide [EvmYul.Yul.head', EvmYul.Yul.reverse', EvmYul.Yul.cons']
  rw [call_cleanup_t_uint8_128_16_raw (fuel := fuel) (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 128)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide [EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]


@[simp]
theorem call_convert_t_rational_128_by_1_to_t_uint8_128_991
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 991) [EvmYul.UInt256.ofNat 128]
      (.some "convert_t_rational_128_by_1_to_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 128]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_128_by_1_to_t_uint8_128
      (fuel := fuel + 971) (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_convert_t_rational_128_by_1_to_t_uint8_128_977
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 977) [EvmYul.UInt256.ofNat 128]
      (.some "convert_t_rational_128_by_1_to_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 128]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_128_by_1_to_t_uint8_128
      (fuel := fuel + 957) (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_convert_t_rational_128_by_1_to_t_uint8_128_971
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 971) [EvmYul.UInt256.ofNat 128]
      (.some "convert_t_rational_128_by_1_to_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 128]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_128_by_1_to_t_uint8_128
      (fuel := fuel + 951) (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_convert_t_rational_128_by_1_to_t_uint8_128_965
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 965) [EvmYul.UInt256.ofNat 128]
      (.some "convert_t_rational_128_by_1_to_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 128]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_128_by_1_to_t_uint8_128
      (fuel := fuel + 945) (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_convert_t_rational_128_by_1_to_t_uint8_128_959
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 959) [EvmYul.UInt256.ofNat 128]
      (.some "convert_t_rational_128_by_1_to_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 128]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_128_by_1_to_t_uint8_128
      (fuel := fuel + 939) (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_convert_t_rational_128_by_1_to_t_uint8_128_956
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 956) [EvmYul.UInt256.ofNat 128]
      (.some "convert_t_rational_128_by_1_to_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 128]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_128_by_1_to_t_uint8_128
      (fuel := fuel + 936) (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_convert_t_rational_128_by_1_to_t_uint8_128_947
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 947) [EvmYul.UInt256.ofNat 128]
      (.some "convert_t_rational_128_by_1_to_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 128]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_128_by_1_to_t_uint8_128
      (fuel := fuel + 927) (shared := shared) (store := store) (hlookup := hlookup)


@[simp]
theorem call_convert_t_rational_240615969168004511545033772477625056927_by_1_to_t_uint256
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [FormalYul.word 240615969168004511545033772477625056927]
      (.some "convert_t_rational_240615969168004511545033772477625056927_by_1_to_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word 240615969168004511545033772477625056927]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions,
    lookup_convert_t_rational_240615969168004511545033772477625056927_by_1_to_t_uint256]
  simp only [yulFunction_convert_t_rational_240615969168004511545033772477625056927_by_1_to_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  rw [call_cleanup_t_rational_240615969168004511545033772477625056927_by_1_12
    (v := EvmYul.UInt256.ofNat 240615969168004511545033772477625056927) (fuel := fuel)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 240615969168004511545033772477625056927)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide [EvmYul.Yul.head', EvmYul.Yul.reverse', EvmYul.Yul.cons']
  rw [call_identity_14 (v := EvmYul.UInt256.ofNat 240615969168004511545033772477625056927) (fuel := fuel)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 240615969168004511545033772477625056927)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide [EvmYul.Yul.head', EvmYul.Yul.reverse', EvmYul.Yul.cons']
  rw [call_cleanup_t_uint256_16
    (v := EvmYul.UInt256.ofNat 240615969168004511545033772477625056927) (fuel := fuel)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 240615969168004511545033772477625056927)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide [EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]


@[simp]
theorem call_convert_t_rational_340282366920938463463374607431768211455_by_1_to_t_uint256
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [FormalYul.word 340282366920938463463374607431768211455]
      (.some "convert_t_rational_340282366920938463463374607431768211455_by_1_to_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word 340282366920938463463374607431768211455]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions,
    lookup_convert_t_rational_340282366920938463463374607431768211455_by_1_to_t_uint256]
  simp only [yulFunction_convert_t_rational_340282366920938463463374607431768211455_by_1_to_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  rw [call_cleanup_t_rational_340282366920938463463374607431768211455_by_1_12
    (v := EvmYul.UInt256.ofNat 340282366920938463463374607431768211455) (fuel := fuel)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 340282366920938463463374607431768211455)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide [EvmYul.Yul.head', EvmYul.Yul.reverse', EvmYul.Yul.cons']
  rw [call_identity_14 (v := EvmYul.UInt256.ofNat 340282366920938463463374607431768211455) (fuel := fuel)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 340282366920938463463374607431768211455)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide [EvmYul.Yul.head', EvmYul.Yul.reverse', EvmYul.Yul.cons']
  rw [call_cleanup_t_uint256_16
    (v := EvmYul.UInt256.ofNat 340282366920938463463374607431768211455) (fuel := fuel)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 340282366920938463463374607431768211455)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide [EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_convert_t_rational_340282366920938463463374607431768211455_by_1_to_t_uint256_939
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 939) [EvmYul.UInt256.ofNat 340282366920938463463374607431768211455]
      (.some "convert_t_rational_340282366920938463463374607431768211455_by_1_to_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [EvmYul.UInt256.ofNat 340282366920938463463374607431768211455]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_340282366920938463463374607431768211455_by_1_to_t_uint256
      (fuel := fuel + 919) (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_convert_t_rational_254_by_1_to_t_uint256_254
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [FormalYul.word 254]
      (.some "convert_t_rational_254_by_1_to_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 254]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_convert_t_rational_254_by_1_to_t_uint256]
  simp only [yulFunction_convert_t_rational_254_by_1_to_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  rw [call_cleanup_t_rational_254_by_1_12 (v := EvmYul.UInt256.ofNat 254) (fuel := fuel)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 254)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide [EvmYul.Yul.head', EvmYul.Yul.reverse', EvmYul.Yul.cons']
  rw [call_identity_14 (v := EvmYul.UInt256.ofNat 254) (fuel := fuel)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 254)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide [EvmYul.Yul.head', EvmYul.Yul.reverse', EvmYul.Yul.cons']
  rw [call_cleanup_t_uint256_16 (v := EvmYul.UInt256.ofNat 254) (fuel := fuel)
    (shared := shared)
    (store := Finmap.insert "value" (EvmYul.UInt256.ofNat 254)
      (Inhabited.default : EvmYul.Yul.VarStore))
    (hlookup := hlookup)]
  simp +decide [EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_convert_t_rational_254_by_1_to_t_uint256_254_4980
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 4980) [EvmYul.UInt256.ofNat 254]
      (.some "convert_t_rational_254_by_1_to_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 254]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_254_by_1_to_t_uint256_254
      (fuel := fuel + 4960) (shared := shared) (store := store) (hlookup := hlookup)


@[simp]
theorem call_convert_t_rational_240615969168004511545033772477625056927_by_1_to_t_uint256_1391
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 1391) [EvmYul.UInt256.ofNat 240615969168004511545033772477625056927]
      (.some "convert_t_rational_240615969168004511545033772477625056927_by_1_to_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [EvmYul.UInt256.ofNat 240615969168004511545033772477625056927]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_240615969168004511545033772477625056927_by_1_to_t_uint256
      (fuel := fuel + 1371) (shared := shared) (store := store) (hlookup := hlookup)


@[simp]
theorem call_convert_t_rational_1_by_1_to_t_uint8_one_164
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 164) [EvmYul.UInt256.ofNat 1]
      (.some "convert_t_rational_1_by_1_to_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 1]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_1_by_1_to_t_uint8_one (fuel := fuel + 144) (shared := shared) (store := store)
      (hlookup := hlookup)

@[simp]
theorem call_convert_t_rational_1_by_1_to_t_uint8_one_4977
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 4977) [EvmYul.UInt256.ofNat 1]
      (.some "convert_t_rational_1_by_1_to_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat 1]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_convert_t_rational_1_by_1_to_t_uint8_one
      (fuel := fuel + 4957) (shared := shared) (store := store) (hlookup := hlookup)


@[simp]
theorem call_shift_right_t_uint256_t_uint8_one_163
    (value : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 163) [FormalYul.word value, EvmYul.UInt256.ofNat 1]
      (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmShr 1 value)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_right_t_uint256_t_uint8_one (value := value) (fuel := fuel + 83)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_shift_right_t_uint256_t_uint8_one_4975
    (value : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 4975) [FormalYul.word value, EvmYul.UInt256.ofNat 1]
      (.some "shift_right_t_uint256_t_uint8") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (evmShr 1 value)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_shift_right_t_uint256_t_uint8_one (value := value) (fuel := fuel + 4895)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_fun__sqrt_babylonianStep_4323
    (x r : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 180) [FormalYul.word x, FormalYul.word r]
      (.some "fun__sqrt_babylonianStep_4323") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word (model_bstep_evm x r)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__sqrt_babylonianStep_4323]
  simp only [yulFunction_fun__sqrt_babylonianStep_4323,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
    call_fun_unsafeDiv_5899, call_wrapping_add_t_uint256,
    call_shift_right_t_uint256_t_uint8_one,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp [model_bstep_evm, FormalYul.word]

@[simp]
theorem call_fun__sqrt_babylonianStep_4323_1384_const
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 1384)
      [FormalYul.word x, EvmYul.UInt256.ofNat 240615969168004511545033772477625056927]
      (.some "fun__sqrt_babylonianStep_4323") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (model_bstep_evm x 240615969168004511545033772477625056927)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun__sqrt_babylonianStep_4323
      (x := x) (r := 240615969168004511545033772477625056927)
      (fuel := fuel + 1204) (shared := shared) (store := store) (hlookup := hlookup)

end Sqrt512Yul

namespace Sqrt512Yul

@[simp]
theorem call_fun__sqrt_baseCase_4393
    (xHi : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 1400) [FormalYul.word xHi]
      (.some "fun__sqrt_baseCase_4393") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (model_innerSqrt_evm xHi).1, FormalYul.word (model_innerSqrt_evm xHi).2]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__sqrt_baseCase_4393]
  simp only [yulFunction_fun__sqrt_baseCase_4393,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
    call_fun__sqrt_babylonianStep_4323,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  constructor
  · apply FormalYul.Preservation.eq_of_wordNat_eq
    simp [model_innerSqrt_evm, model_bstep_evm, FormalYul.word]
  · apply FormalYul.Preservation.eq_of_wordNat_eq
    simp [model_innerSqrt_evm, model_bstep_evm, FormalYul.word]

end Sqrt512Yul

namespace Sqrt512Yul

@[simp]
theorem call_fun__sqrt_karatsubaQuotient_4409
    (res xLo rHi : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 300) [FormalYul.word res, FormalYul.word xLo, FormalYul.word rHi]
      (.some "fun__sqrt_karatsubaQuotient_4409") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (model_karatsubaQuotient_evm res xLo rHi).1,
       FormalYul.word (model_karatsubaQuotient_evm res xLo rHi).2]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__sqrt_karatsubaQuotient_4409]
  simp only [yulFunction_fun__sqrt_karatsubaQuotient_4409,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.UInt256.eq0, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  by_cases hc : evmShr 128 res = 0
  · have hcUInt :
        (EvmYul.UInt256.shiftRight (EvmYul.UInt256.ofNat res) (EvmYul.UInt256.ofNat 128)) =
          { val := 0 } := by
      apply FormalYul.Preservation.eq_of_wordNat_eq
      simpa [FormalYul.word] using hc
    have hcF : FormalYul.evmShr 128 res = 0 := by
      simpa using hc
    simp [hcUInt, hc, EvmYul.Yul.State.revive, Finmap.lookup_insert,
      Finmap.lookup_insert_of_ne]
    constructor
    · apply FormalYul.Preservation.eq_of_wordNat_eq
      simp +decide [model_karatsubaQuotient_evm, hc, hcF, FormalYul.word,
        formal_evmNot_zero,
        Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
    · apply FormalYul.Preservation.eq_of_wordNat_eq
      simp +decide [model_karatsubaQuotient_evm, hc, hcF, FormalYul.word,
        formal_evmNot_zero,
        Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  · have hcUInt :
        (EvmYul.UInt256.shiftRight (EvmYul.UInt256.ofNat res) (EvmYul.UInt256.ofNat 128)) ≠
          { val := 0 } := by
      intro h
      apply hc
      have hw := congrArg FormalYul.wordNat h
      simpa [FormalYul.word] using hw
    have hcF : FormalYul.evmShr 128 res ≠ 0 := by
      intro h
      apply hc
      simpa using h
    simp [hcUInt, hc, EvmYul.Yul.State.revive, Finmap.lookup_insert,
      Finmap.lookup_insert_of_ne]
    constructor
    · apply FormalYul.Preservation.eq_of_wordNat_eq
      simp +decide [model_karatsubaQuotient_evm, hc, hcF, FormalYul.word,
        formal_evmNot_zero,
        Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
    · apply FormalYul.Preservation.eq_of_wordNat_eq
      simp +decide [model_karatsubaQuotient_evm, hc, hcF, FormalYul.word,
        formal_evmNot_zero,
        Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

end Sqrt512Yul

namespace Sqrt512Yul

@[simp]
theorem call_fun__sqrt_correction_4477
    (rHi rLo res xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 1000)
      [FormalYul.word rHi, FormalYul.word rLo, FormalYul.word res, FormalYul.word xLo]
      (.some "fun__sqrt_correction_4477") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (model_sqrtCorrection_evm rHi rLo res xLo)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__sqrt_correction_4477]
  simp only [yulFunction_fun__sqrt_correction_4477,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    call_convert_t_rational_128_by_1_to_t_uint8_128,
    call_shift_left_t_uint256_t_uint8_128,
    call_shift_right_t_uint256_t_uint8_128,
    call_wrapping_add_t_uint256,
    call_convert_t_rational_340282366920938463463374607431768211455_by_1_to_t_uint256,
    call_wrapping_mul_t_uint256,
    call_fun_and_5596, call_fun_or_5585, call_fun_unsafeDec_5854,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp +decide [model_sqrtCorrection_evm, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

end Sqrt512Yul

namespace Sqrt512Yul

@[simp]
theorem call_fun__sqrt_4544
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 5000) [FormalYul.word xHi, FormalYul.word xLo]
      (.some "fun__sqrt_4544") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (model_sqrt512_evm xHi xLo)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun__sqrt_4544]
  simp only [yulFunction_fun__sqrt_4544,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
    call_fun_clz_6141,
    call_convert_t_rational_254_by_1_to_t_uint256_254,
    call_fun__shl256_3075,
    call_convert_t_rational_1_by_1_to_t_uint8_one,
    call_shift_right_t_uint256_t_uint8_one,
    call_fun__sqrt_baseCase_4393,
    call_fun__sqrt_karatsubaQuotient_4409,
    call_fun__sqrt_correction_4477,
    call_shift_right_t_uint256_t_uint256,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp +decide [model_sqrt512_evm, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

end Sqrt512Yul

namespace Sqrt512Yul

@[simp]
theorem call_fun_sqrt_6185_5579_raw
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 5579) [EvmYul.UInt256.ofNat x] (.some "fun_sqrt_6185") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat (model_sqrt256_floor_evm x)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun_sqrt_6185 (x := x) (fuel := fuel + 5319)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_fun__sqrt_4544_5579_raw
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 5579) [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
      (.some "fun__sqrt_4544") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [EvmYul.UInt256.ofNat (model_sqrt512_evm xHi xLo)]) := by
  simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_fun__sqrt_4544 (xHi := xHi) (xLo := xLo) (fuel := fuel + 579)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_fun_sqrt_6185_5579_from0
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 5579) [EvmYul.UInt256.ofNat xLo] (.some "fun_sqrt_6185") (.some yulContract)
      (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [EvmYul.UInt256.ofNat (model_sqrt256_floor_evm xLo)]) := by
  simpa using
    call_fun_sqrt_6185_5579_raw (x := xLo) (fuel := fuel)
      (shared := sharedAfterFrom0 shared xHi xLo) (store := store)
      (hlookup := sharedAfterFrom0_lookup shared xHi xLo hlookup)

@[simp]
theorem call_fun__sqrt_4544_5579_from0
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 5579) [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
      (.some "fun__sqrt_4544") (.some yulContract)
      (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [EvmYul.UInt256.ofNat (model_sqrt512_evm xHi xLo)]) := by
  simpa using
    call_fun__sqrt_4544_5579_raw (xHi := xHi) (xLo := xLo) (fuel := fuel)
      (shared := sharedAfterFrom0 shared xHi xLo) (store := store)
      (hlookup := sharedAfterFrom0_lookup shared xHi xLo hlookup)

@[simp]
theorem call_fun_sqrt_4575_from0
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract))
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    EvmYul.Yul.call (fuel + 5600) [FormalYul.word 0]
      (.some "fun_sqrt_4575") (.some yulContract)
      (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv,
    sharedAfterFrom0_lookup shared xHi xLo hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_sqrt_4575]
  simp only [yulFunction_fun_sqrt_4575,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, hactive, sharedAfterFrom0_lookup,
    EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.setMachineState, EvmYul.Yul.State.toMachineState,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
    call_zero_value_for_split_t_uint256,
    call_fun_into_182_from0,
    call_cleanup_t_uint256,
    call_convert_t_rational_0_by_1_to_t_uint256,
    call_fun_sqrt_6185,
    call_fun__sqrt_4544,
    model_sqrt512_wrapper_evm, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  by_cases hcond : FormalYul.evmEq xHi 0 = 0
  · simp +decide [hcond, model_sqrt512_wrapper_evm, FormalYul.word,
      call_fun__sqrt_4544_5579_from0 (xHi := xHi) (xLo := xLo) (fuel := fuel)
        (shared := shared) (hlookup := hlookup),
      EvmYul.Yul.State.revive, Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  · simp +decide [hcond, model_sqrt512_wrapper_evm, FormalYul.word,
      call_fun_sqrt_6185_5579_from0 (xHi := xHi) (xLo := xLo) (fuel := fuel)
        (shared := shared) (hlookup := hlookup),
      EvmYul.Yul.State.revive, Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_fun_from_156_zero_raw
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 100)
      [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
      (.some "fun_from_156") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [EvmYul.UInt256.ofNat 0]) := by
  simpa [FormalYul.word] using
    call_fun_from_156_zero (xHi := xHi) (xLo := xLo) (fuel := fuel)
      (shared := shared) (store := store) (hlookup := hlookup)

@[simp]
theorem call_fun_sqrt_4575_from0_raw
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract))
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    EvmYul.Yul.call (fuel + 5600) [EvmYul.UInt256.ofNat 0]
      (.some "fun_sqrt_4575") (.some yulContract)
      (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [EvmYul.UInt256.ofNat (model_sqrt512_wrapper_evm xHi xLo)]) := by
  simpa [FormalYul.word] using
    call_fun_sqrt_4575_from0 (xHi := xHi) (xLo := xLo) (fuel := fuel)
      (shared := shared) (store := store) (hlookup := hlookup) (hactive := hactive)

@[simp]
theorem call_fun_wrap_sqrt512_6228
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner = some (FormalYul.accountFor yulContract))
    (hactive : shared.toMachineState.activeWords = FormalYul.word 3) :
    EvmYul.Yul.call (fuel + 5800) [FormalYul.word xHi, FormalYul.word xLo]
      (.some "fun_wrap_sqrt512_6228") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok (sharedAfterFrom0 shared xHi xLo) store,
      [FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_fun_wrap_sqrt512_6228]
  simp only [yulFunction_fun_wrap_sqrt512_6228,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, hactive, EvmYul.Yul.exec.eq_def,
    EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.setMachineState, EvmYul.Yul.State.toMachineState,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
    call_zero_value_for_split_t_uint256,
    call_fun_tmp_128,
    call_fun_from_156_zero_raw,
    call_fun_sqrt_4575_from0_raw,
    model_sqrt512_wrapper_evm, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_validator_revert_t_uint256
    (v : EvmYul.UInt256) (fuel : Nat)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 30) [v] (.some "validator_revert_t_uint256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, []) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_validator_revert_t_uint256]
  simp only [yulFunction_validator_revert_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_allocate_unbounded
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
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_allocate_unbounded]
  simp only [yulFunction_allocate_unbounded,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.toMachineState, FormalYul.word,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_abi_encode_t_uint256_to_t_uint256_fromStack
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
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions,
    lookup_abi_encode_t_uint256_to_t_uint256_fromStack]
  simp only [yulFunction_abi_encode_t_uint256_to_t_uint256_fromStack,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.toMachineState, FormalYul.word,
    call_cleanup_t_uint256,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem call_abi_encode_tuple_t_uint256__to_t_uint256__fromStack
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
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions,
    lookup_abi_encode_tuple_t_uint256__to_t_uint256__fromStack]
  simp only [yulFunction_abi_encode_tuple_t_uint256__to_t_uint256__fromStack,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.toMachineState, FormalYul.word,
    call_abi_encode_t_uint256_to_t_uint256_fromStack,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem readBytes_selector_two_args_first (a b c d x y : Nat) :
    ByteArray.readBytes (FormalYul.bytes [a, b, c, d] ++ FormalYul.encodeWords [x, y]) 4 32 =
      FormalYul.encodeWord x := by
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simp [ByteArray.readBytes, FormalYul.bytes, ByteArray.push, ByteArray.empty,
    ByteArray.emptyWithCapacity, ByteArray.size, ffi.ByteArray.zeroes,
    List.range, List.range.loop, FormalYul.encodeWords]

@[simp]
theorem readBytes_selector_two_args_second (a b c d x y : Nat) :
    ByteArray.readBytes (FormalYul.bytes [a, b, c, d] ++ FormalYul.encodeWords [x, y]) 36 32 =
      FormalYul.encodeWord y := by
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simp [ByteArray.readBytes, FormalYul.bytes, ByteArray.push, ByteArray.empty,
    ByteArray.emptyWithCapacity, ByteArray.size, ffi.ByteArray.zeroes,
    List.range, List.range.loop, FormalYul.encodeWords]

@[simp]
theorem calldataload_sqrt512_arg0_of_calldata
    (xHi xLo : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hdata : shared.executionEnv.calldata = selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo]) :
    EvmYul.State.calldataload
      (EvmYul.Yul.State.Ok shared store).toState (FormalYul.word 4) =
      FormalYul.word xHi := by
  simp [EvmYul.State.calldataload, EvmYul.Yul.State.toState, hdata,
    selector_sqrt512, FormalYul.Preservation.uInt256OfByteArray_encodeWord]

@[simp]
theorem calldataload_sqrt512_arg1_of_calldata
    (xHi xLo : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hdata : shared.executionEnv.calldata = selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo]) :
    EvmYul.State.calldataload
      (EvmYul.Yul.State.Ok shared store).toState (FormalYul.word 36) =
      FormalYul.word xLo := by
  change EvmYul.uInt256OfByteArray
      (shared.executionEnv.calldata.readBytes (FormalYul.word 36).toNat 32) =
    FormalYul.word xLo
  have h36 : (FormalYul.word 36).toNat = 36 := rfl
  rw [hdata, h36]
  simp [selector_sqrt512, FormalYul.Preservation.uInt256OfByteArray_encodeWord]

@[simp]
theorem call_abi_decode_t_uint256_sqrt512_arg0_of_calldata
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo]) :
    EvmYul.Yul.call (fuel + 50) [FormalYul.word 4, FormalYul.word 68]
      (.some "abi_decode_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word xHi]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_abi_decode_t_uint256]
  simp only [yulFunction_abi_decode_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hdata, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  rw [calldataload_sqrt512_arg0_of_calldata xHi xLo shared
    (Finmap.insert "offset" (FormalYul.word 4)
      (Finmap.insert "end" (FormalYul.word 68) (Inhabited.default : EvmYul.Yul.VarStore)))
    hdata]
  simp [call_validator_revert_t_uint256 (FormalYul.word xHi) (fuel + 15) shared _ hlookup]

@[simp]
theorem call_abi_decode_t_uint256_sqrt512_arg1_of_calldata
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo]) :
    EvmYul.Yul.call (fuel + 50) [FormalYul.word 36, FormalYul.word 68]
      (.some "abi_decode_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word xLo]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_abi_decode_t_uint256]
  simp only [yulFunction_abi_decode_t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hdata, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  rw [calldataload_sqrt512_arg1_of_calldata xHi xLo shared
    (Finmap.insert "offset" (FormalYul.word 36)
      (Finmap.insert "end" (FormalYul.word 68) (Inhabited.default : EvmYul.Yul.VarStore)))
    hdata]
  simp [call_validator_revert_t_uint256 (FormalYul.word xLo) (fuel + 15) shared _ hlookup]

@[simp]
theorem call_abi_decode_t_uint256_sqrt512_arg0_raw
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo]) :
    EvmYul.Yul.call (fuel + 50) [EvmYul.UInt256.ofNat 4, EvmYul.UInt256.ofNat 68]
      (.some "abi_decode_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat xHi]) := by
  simpa [FormalYul.word] using
    call_abi_decode_t_uint256_sqrt512_arg0_of_calldata
      (xHi := xHi) (xLo := xLo) (fuel := fuel) (shared := shared)
      (store := store) (hlookup := hlookup) (hdata := hdata)

@[simp]
theorem call_abi_decode_t_uint256_sqrt512_arg1_raw
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo]) :
    EvmYul.Yul.call (fuel + 50) [EvmYul.UInt256.ofNat 36, EvmYul.UInt256.ofNat 68]
      (.some "abi_decode_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat xLo]) := by
  simpa [FormalYul.word] using
    call_abi_decode_t_uint256_sqrt512_arg1_of_calldata
      (xHi := xHi) (xLo := xLo) (fuel := fuel) (shared := shared)
      (store := store) (hlookup := hlookup) (hdata := hdata)

@[simp]
theorem call_abi_decode_t_uint256_sqrt512_arg0_153
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo]) :
    EvmYul.Yul.call (fuel + 153) [EvmYul.UInt256.ofNat 4, EvmYul.UInt256.ofNat 68]
      (.some "abi_decode_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat xHi]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_abi_decode_t_uint256_sqrt512_arg0_raw
      (xHi := xHi) (xLo := xLo) (fuel := fuel + 103) (shared := shared)
      (store := store) (hlookup := hlookup) (hdata := hdata)

@[simp]
theorem call_abi_decode_t_uint256_sqrt512_arg1_152
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo]) :
    EvmYul.Yul.call (fuel + 152) [EvmYul.UInt256.ofNat 36, EvmYul.UInt256.ofNat 68]
      (.some "abi_decode_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [EvmYul.UInt256.ofNat xLo]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_abi_decode_t_uint256_sqrt512_arg1_raw
      (xHi := xHi) (xLo := xLo) (fuel := fuel + 102) (shared := shared)
      (store := store) (hlookup := hlookup) (hdata := hdata)

@[simp]
theorem call_abi_decode_t_uint256_sqrt512_arg0_153_formal
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo]) :
    EvmYul.Yul.call (fuel + 153) [FormalYul.word 4, FormalYul.word 68]
      (.some "abi_decode_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word xHi]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_abi_decode_t_uint256_sqrt512_arg0_of_calldata
      (xHi := xHi) (xLo := xLo) (fuel := fuel + 103) (shared := shared)
      (store := store) (hlookup := hlookup) (hdata := hdata)

@[simp]
theorem call_abi_decode_t_uint256_sqrt512_arg1_152_formal
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo]) :
    EvmYul.Yul.call (fuel + 152) [FormalYul.word 36, FormalYul.word 68]
      (.some "abi_decode_t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word xLo]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    call_abi_decode_t_uint256_sqrt512_arg1_of_calldata
      (xHi := xHi) (xLo := xLo) (fuel := fuel + 102) (shared := shared)
      (store := store) (hlookup := hlookup) (hdata := hdata)

@[simp]
theorem lookup_headStart_after_decode_value0 (shared : EvmYul.SharedState .Yul) (xHi : Nat) :
    EvmYul.Yul.State.lookup! "headStart" (EvmYul.Yul.State.Ok shared
      (Finmap.insert "offset" (EvmYul.UInt256.ofNat 32)
        (Finmap.insert "value0" (EvmYul.UInt256.ofNat xHi)
          (Finmap.insert "offset" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "headStart" (EvmYul.UInt256.ofNat 4)
              (Finmap.insert "dataEnd" (EvmYul.UInt256.ofNat 68)
                (Inhabited.default : EvmYul.Yul.VarStore))))))) =
      EvmYul.UInt256.ofNat 4 := by
  simp only [EvmYul.Yul.State.lookup!]
  rw [Finmap.lookup_insert_of_ne _ (by decide : "headStart" ≠ "offset")]
  rw [Finmap.lookup_insert_of_ne _ (by decide : "headStart" ≠ "value0")]
  rw [Finmap.lookup_insert_of_ne _ (by decide : "headStart" ≠ "offset")]
  rw [Finmap.lookup_insert]
  rfl

@[simp]
theorem lookup_dataEnd_after_decode_value0 (shared : EvmYul.SharedState .Yul) (xHi : Nat) :
    EvmYul.Yul.State.lookup! "dataEnd" (EvmYul.Yul.State.Ok shared
      (Finmap.insert "offset" (EvmYul.UInt256.ofNat 32)
        (Finmap.insert "value0" (EvmYul.UInt256.ofNat xHi)
          (Finmap.insert "offset" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "headStart" (EvmYul.UInt256.ofNat 4)
              (Finmap.insert "dataEnd" (EvmYul.UInt256.ofNat 68)
                (Inhabited.default : EvmYul.Yul.VarStore))))))) =
      EvmYul.UInt256.ofNat 68 := by
  simp only [EvmYul.Yul.State.lookup!]
  rw [Finmap.lookup_insert_of_ne _ (by decide : "dataEnd" ≠ "offset")]
  rw [Finmap.lookup_insert_of_ne _ (by decide : "dataEnd" ≠ "value0")]
  rw [Finmap.lookup_insert_of_ne _ (by decide : "dataEnd" ≠ "offset")]
  rw [Finmap.lookup_insert_of_ne _ (by decide : "dataEnd" ≠ "headStart")]
  rw [Finmap.lookup_insert]
  rfl

@[simp]
theorem call_abi_decode_tuple_t_uint256t_uint256_sqrt512_of_calldata
    (xHi xLo : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo]) :
    EvmYul.Yul.call (fuel + 160) [FormalYul.word 4, FormalYul.word 68]
      (.some "abi_decode_tuple_t_uint256t_uint256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word xHi, FormalYul.word xLo]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_abi_decode_tuple_t_uint256t_uint256]
  simp only [yulFunction_abi_decode_tuple_t_uint256t_uint256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [hlookup, hdata, EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  rw [call_abi_decode_t_uint256_sqrt512_arg0_153_formal
      xHi xLo fuel shared _ hlookup hdata]
  simp +decide only [GetElem?.getElem!, instGetElem?OfGetElemOfDecidable,
    GetElem.getElem, EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    decidableGetElem?, EvmYul.Yul.multifill', EvmYul.Yul.State.lookup!,
    EvmYul.Yul.State.store, List.zip,
    List.zipWith_cons_cons, List.zipWith_nil_left, List.zipWith_nil_right,
    List.foldr, List.foldl, EvmYul.Yul.State.insert,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne, Finmap.mem_insert,
    dite_true, dif_pos, Option.get!, Option.getD]
  rw [Finmap.lookup_insert_of_ne _ (by decide : "headStart" ≠ "offset")]
  rw [Finmap.lookup_insert_of_ne _ (by decide : "headStart" ≠ "value0")]
  rw [Finmap.lookup_insert_of_ne _ (by decide : "headStart" ≠ "offset")]
  rw [Finmap.lookup_insert]
  rw [Finmap.lookup_insert_of_ne _ (by decide : "dataEnd" ≠ "offset")]
  rw [Finmap.lookup_insert_of_ne _ (by decide : "dataEnd" ≠ "value0")]
  rw [Finmap.lookup_insert_of_ne _ (by decide : "dataEnd" ≠ "offset")]
  rw [Finmap.lookup_insert_of_ne _ (by decide : "dataEnd" ≠ "headStart")]
  rw [Finmap.lookup_insert]
  simp only [FormalYul.word, Option.get!, Option.getD]
  have hadd : EvmYul.UInt256.ofNat 4 + EvmYul.UInt256.ofNat 32 = EvmYul.UInt256.ofNat 36 := by
    decide
  rw [hadd]
  rw [call_abi_decode_t_uint256_sqrt512_arg1_152
      xHi xLo fuel shared _ hlookup hdata]
  simp +decide [EvmYul.Yul.multifill', EvmYul.Yul.State.lookup!, FormalYul.word,
    List.zip, List.zipWith_cons_cons, List.zipWith_nil_left, List.zipWith_nil_right,
    List.foldr, EvmYul.Yul.State.insert,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne, Option.get!, Option.getD]

def sqrt512SharedAfterFreePtr (xHi xLo : Nat) : EvmYul.SharedState .Yul :=
  let shared := FormalYul.sharedFor yulContract (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])
  { shared with toMachineState := shared.toMachineState.mstore (FormalYul.word 64) (FormalYul.word 128) }

theorem sharedFor_mstore_eq_sqrt512SharedAfterFreePtr (xHi xLo : Nat) :
    { (FormalYul.sharedFor yulContract (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])) with
      toMachineState :=
        (FormalYul.sharedFor yulContract (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])).toMachineState.mstore
          (FormalYul.word 64) (FormalYul.word 128) } =
      sqrt512SharedAfterFreePtr xHi xLo := rfl

theorem sharedFor_mstore_mk_eq_sqrt512SharedAfterFreePtr (xHi xLo : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])).toState
        ((FormalYul.sharedFor yulContract (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])).toMachineState.mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      sqrt512SharedAfterFreePtr xHi xLo := rfl

theorem sharedFor_inherited_mstore_mk_eq_sqrt512SharedAfterFreePtr (xHi xLo : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])).toState
        ((FormalYul.sharedFor yulContract (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])).mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      sqrt512SharedAfterFreePtr xHi xLo := rfl

theorem sharedFor_inherited_mstore_mk_eq_sqrt512SharedAfterFreePtr_raw (xHi xLo : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])).toState
        ((FormalYul.sharedFor yulContract (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])).mstore
          (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128))) =
      sqrt512SharedAfterFreePtr xHi xLo := by
  simpa [FormalYul.word] using sharedFor_inherited_mstore_mk_eq_sqrt512SharedAfterFreePtr xHi xLo

@[simp]
theorem sqrt512SharedAfterFreePtr_lookup (xHi xLo : Nat) :
    (sqrt512SharedAfterFreePtr xHi xLo).accountMap.find?
      (sqrt512SharedAfterFreePtr xHi xLo).executionEnv.codeOwner =
        some (FormalYul.accountFor yulContract) := by
  simp [sqrt512SharedAfterFreePtr]

@[simp]
theorem sqrt512SharedAfterFreePtr_calldata (xHi xLo : Nat) :
    (sqrt512SharedAfterFreePtr xHi xLo).executionEnv.calldata =
      selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo] := by
  simp [sqrt512SharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
theorem sqrt512SharedAfterFreePtr_callvalue (xHi xLo : Nat) :
    (sqrt512SharedAfterFreePtr xHi xLo).executionEnv.weiValue =
      ({ val := 0 } : EvmYul.UInt256) := by
  simp [sqrt512SharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
theorem encodeWord_size (x : Nat) : (FormalYul.encodeWord x).size = 32 := by
  change (FormalYul.encodeWord x).data.size = 32
  rw [← Array.length_toList]
  simp [FormalYul.Preservation.encodeWord_data_toList]

@[simp]
theorem uint256_add_sub_self_32 (p : EvmYul.UInt256) :
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
    simpa [FormalYul.wordNat, EvmYul.UInt256.toNat, EvmYul.UInt256.size] using p.val.isLt
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

@[simp]
theorem sqrt512_calldata_size (xHi xLo : Nat) :
    (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo]).size = 68 := by
  simp [selector_sqrt512, FormalYul.encodeWords,
    FormalYul.bytes, ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty]

@[simp]
theorem readBytes_selector_two_args_word0 (xHi xLo : Nat) :
    (ByteArray.readBytes (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo]) 0 32).data.toList =
      [UInt8.ofNat 63, UInt8.ofNat 81, UInt8.ofNat 98, UInt8.ofNat 138] ++
        List.take 28 (FormalYul.encodeWord xHi).data.toList := by
  simp [ByteArray.readBytes, selector_sqrt512, FormalYul.bytes, FormalYul.encodeWords,
    ByteArray.push, ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.size,
    ffi.ByteArray.zeroes, encodeWord_size]

@[simp]
theorem calldataload_sqrt512_selector_wordNat (xHi xLo : Nat) :
    FormalYul.wordNat
      (EvmYul.State.calldataload
        (FormalYul.sharedFor yulContract (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])).toState
        (EvmYul.UInt256.ofNat 0)) =
      FormalYul.u256 (EvmYul.fromBytesBigEndian
        ([UInt8.ofNat 63, UInt8.ofNat 81, UInt8.ofNat 98, UInt8.ofNat 138] ++
          List.take 28 (FormalYul.encodeWord xHi).data.toList)) := by
  change FormalYul.wordNat
      (EvmYul.uInt256OfByteArray
        (ByteArray.readBytes (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])
          (EvmYul.UInt256.ofNat 0).toNat 32)) =
      FormalYul.u256 (EvmYul.fromBytesBigEndian
        ([UInt8.ofNat 63, UInt8.ofNat 81, UInt8.ofNat 98, UInt8.ofNat 138] ++
          List.take 28 (FormalYul.encodeWord xHi).data.toList))
  simp only [EvmYul.UInt256.toNat, EvmYul.UInt256.ofNat]
  change FormalYul.wordNat
      (EvmYul.uInt256OfByteArray
        (ByteArray.readBytes (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo]) 0 32)) =
      FormalYul.u256 (EvmYul.fromBytesBigEndian
        ([UInt8.ofNat 63, UInt8.ofNat 81, UInt8.ofNat 98, UInt8.ofNat 138] ++
          List.take 28 (FormalYul.encodeWord xHi).data.toList))
  unfold EvmYul.uInt256OfByteArray EvmYul.fromBytesBigEndian FormalYul.wordNat
    FormalYul.u256 FormalYul.WORD_MOD
  rw [readBytes_selector_two_args_word0 xHi xLo]
  rfl

@[simp]
theorem selector_sqrt512_evmShr_prefix
    (tail : List UInt8) (htail_len : tail.length = 28) :
    FormalYul.evmShr 224
      (FormalYul.u256 (EvmYul.fromBytesBigEndian
        ([UInt8.ofNat 63, UInt8.ofNat 81, UInt8.ofNat 98, UInt8.ofNat 138] ++ tail))) =
      1062298250 := by
  let sel : List UInt8 := [UInt8.ofNat 63, UInt8.ofNat 81, UInt8.ofNat 98, UInt8.ofNat 138]
  change FormalYul.evmShr 224 (FormalYul.u256 (EvmYul.fromBytesBigEndian (sel ++ tail))) =
    1062298250
  unfold FormalYul.evmShr
  simp only [FormalYul.Preservation.u256_two_twenty_four, Nat.reduceLT, if_true,
    FormalYul.Preservation.u256_u256]
  have hsel : EvmYul.fromBytesBigEndian sel = 1062298250 := by decide
  have htail_lt : EvmYul.fromBytesBigEndian tail < 256 ^ 28 := by
    simpa [htail_len] using FormalYul.Preservation.fromBytesBigEndian_lt_pow_length tail
  rw [FormalYul.Preservation.fromBytesBigEndian_append]
  rw [hsel, htail_len]
  have hpow : 2 ^ 224 = 256 ^ 28 := by decide
  have hval_lt :
      1062298250 * 256 ^ 28 + EvmYul.fromBytesBigEndian tail < FormalYul.WORD_MOD := by
    unfold FormalYul.WORD_MOD
    have hsel_lt : 1062298250 < 256 ^ 4 := by decide
    calc
      1062298250 * 256 ^ 28 + EvmYul.fromBytesBigEndian tail
          < (1062298250 + 1) * 256 ^ 28 := by nlinarith
      _ ≤ 256 ^ 4 * 256 ^ 28 := by
          apply Nat.mul_le_mul_right
          omega
      _ = 256 ^ (4 + 28) := by rw [← Nat.pow_add]
      _ = 2 ^ 256 := by decide
  rw [FormalYul.Preservation.u256_eq_self_of_lt hval_lt]
  rw [hpow]
  have hdiv :
      (1062298250 * 256 ^ 28 + EvmYul.fromBytesBigEndian tail) / 256 ^ 28 =
        1062298250 := by
    rw [Nat.add_comm]
    rw [Nat.add_mul_div_right _ _ (by decide : 0 < 256 ^ 28)]
    rw [Nat.div_eq_of_lt htail_lt]
  rw [hdiv]

@[simp]
theorem selector_sqrt512_shifted_calldataload0 (xHi xLo : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (FormalYul.sharedFor yulContract (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])).toState
        (EvmYul.UInt256.ofNat 0))
      (EvmYul.UInt256.ofNat 224) = EvmYul.UInt256.ofNat 1062298250 := by
  let tail : List UInt8 := List.take 28 (FormalYul.encodeWord xHi).data.toList
  apply FormalYul.Preservation.eq_of_wordNat_eq
  change FormalYul.wordNat
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (FormalYul.sharedFor yulContract (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224)) =
    FormalYul.wordNat (EvmYul.UInt256.ofNat 1062298250)
  rw [FormalYul.Preservation.wordNat_shiftRight]
  rw [calldataload_sqrt512_selector_wordNat xHi xLo]
  change FormalYul.evmShr (FormalYul.wordNat (EvmYul.UInt256.ofNat 224))
      (FormalYul.u256 (EvmYul.fromBytesBigEndian
        ([UInt8.ofNat 63, UInt8.ofNat 81, UInt8.ofNat 98, UInt8.ofNat 138] ++ tail))) =
    FormalYul.wordNat (EvmYul.UInt256.ofNat 1062298250)
  simp only [FormalYul.Preservation.wordNat_ofNat,
    FormalYul.Preservation.u256_two_twenty_four]
  have htail_len : tail.length = 28 := by
    simp [tail, encodeWord_size, ByteArray.size]
  rw [selector_sqrt512_evmShr_prefix tail htail_len]
  rw [FormalYul.Preservation.u256_eq_self_of_lt (by
    unfold FormalYul.WORD_MOD
    decide)]

@[simp]
theorem call_shift_right_224_unsigned
    (value : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [value] (.some "shift_right_224_unsigned")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [EvmYul.UInt256.shiftRight value (EvmYul.UInt256.ofNat 224)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv, hlookup,
    Option.getD_some, yulContract_functions, lookup_shift_right_224_unsigned]
  simp only [yulFunction_shift_right_224_unsigned,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk, EvmYul.Yul.State.insert,
    EvmYul.Yul.State.multifill, EvmYul.Yul.State.lookup!,
    EvmYul.Yul.State.setStore, EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?, Finmap.lookup_insert, Finmap.lookup_insert_of_ne]

@[simp]
theorem sqrt512SharedAfterFreePtr_calldata_size (xHi xLo : Nat) :
    (sqrt512SharedAfterFreePtr xHi xLo).executionEnv.calldata.size = 68 := by
  simp [sqrt512SharedAfterFreePtr_calldata]

@[simp]
theorem sqrt512SharedAfterFreePtr_activeWords (xHi xLo : Nat) :
    (sqrt512SharedAfterFreePtr xHi xLo).toMachineState.activeWords = FormalYul.word 3 := by
  simp [sqrt512SharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor,
    EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord, EvmYul.MachineState.M,
    FormalYul.word]
  decide

@[simp]
theorem sqrt512SharedAfterFreePtr_mload64 (xHi xLo : Nat) :
    ((sqrt512SharedAfterFreePtr xHi xLo).mload (FormalYul.word 64)).1 =
      FormalYul.word 128 := by
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp [sqrt512SharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor,
    FormalYul.wordNat, FormalYul.word,
    EvmYul.UInt256.toNat, EvmYul.UInt256.ofNat, EvmYul.UInt256.size,
    Inhabited.default, EvmYul.MachineState.mload, EvmYul.MachineState.lookupMemory,
    EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord, EvmYul.writeBytes,
    ByteArray.write, ByteArray.readWithPadding, ByteArray.readWithoutPadding,
    ByteArray.size, EvmYul.MachineState.M, EvmYul.UInt256.toByteArray]
  have hle :
      ¬ (({ val := (3 : Fin EvmYul.UInt256.size) } : EvmYul.UInt256) *
          { val := (32 : Fin EvmYul.UInt256.size) } ≤
          ({ val := (64 : Fin EvmYul.UInt256.size) } : EvmYul.UInt256)) := by
    decide
  simp [hle, EvmYul.fromByteArrayBigEndian, EvmYul.fromBytesBigEndian,
    EvmYul.fromBytes', ffi.ByteArray.zeroes]
  norm_num [UInt8.size, EvmYul.UInt256.size]

@[simp]
theorem call_external_fun_wrap_sqrt512_6228_returnOf
    (xHi xLo fuel : Nat)
    (store : EvmYul.Yul.VarStore := (Inhabited.default : EvmYul.Yul.VarStore)) :
    (match EvmYul.Yul.call (fuel + 6200) [] (.some "external_fun_wrap_sqrt512_6228")
        (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) store) with
      | Except.ok (state, _) => Except.ok (FormalYul.returnOf state)
      | Except.error (.YulHalt state _) => Except.ok (FormalYul.returnOf state)
      | Except.error .Revert => Except.error "revert"
      | Except.error err => Except.error (reprStr err)) =
      Except.ok { returndata := (FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)).toByteArray } := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv,
    sqrt512SharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_sqrt512_6228]
  simp only [yulFunction_external_fun_wrap_sqrt512_6228,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [sqrt512SharedAfterFreePtr_lookup, sqrt512SharedAfterFreePtr_calldata,
    sqrt512SharedAfterFreePtr_calldata_size, sqrt512SharedAfterFreePtr_callvalue,
    sqrt512SharedAfterFreePtr_activeWords,
    EvmYul.Yul.exec.eq_def,
    EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.setMachineState, EvmYul.Yul.State.toMachineState,
    EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  have hdecode :
      EvmYul.Yul.call (fuel + 6195) [EvmYul.UInt256.ofNat 4, EvmYul.UInt256.ofNat 68]
        (.some "abi_decode_tuple_t_uint256t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
          (Inhabited.default : EvmYul.Yul.VarStore)) =
      .ok (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
          (Inhabited.default : EvmYul.Yul.VarStore),
        [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_abi_decode_tuple_t_uint256t_uint256_sqrt512_of_calldata
        (xHi := xHi) (xLo := xLo) (fuel := fuel + 6035)
        (shared := sqrt512SharedAfterFreePtr xHi xLo)
        (store := (Inhabited.default : EvmYul.Yul.VarStore))
        (hlookup := sqrt512SharedAfterFreePtr_lookup xHi xLo)
        (hdata := sqrt512SharedAfterFreePtr_calldata xHi xLo)
  rw [hdecode]
  simp +decide [EvmYul.Yul.multifill', EvmYul.Yul.State.lookup!,
    EvmYul.Yul.State.insert, List.zip, List.zipWith_cons_cons,
    List.zipWith_nil_left, List.zipWith_nil_right, List.foldr,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    FormalYul.word, Option.get!, Option.getD]
  let paramStore : EvmYul.Yul.VarStore :=
    Finmap.insert "param_0" (EvmYul.UInt256.ofNat xHi)
      (Finmap.insert "param_1" (EvmYul.UInt256.ofNat xLo)
        (Inhabited.default : EvmYul.Yul.VarStore))
  have hwrap :
      EvmYul.Yul.call (fuel + 6194) [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
        (.some "fun_wrap_sqrt512_6228") (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) paramStore) =
      .ok (EvmYul.Yul.State.Ok
          (sharedAfterFrom0 (sqrt512SharedAfterFreePtr xHi xLo) xHi xLo) paramStore,
        [EvmYul.UInt256.ofNat (model_sqrt512_wrapper_evm xHi xLo)]) := by
    simpa [paramStore, FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_wrap_sqrt512_6228
        (xHi := xHi) (xLo := xLo) (fuel := fuel + 394)
        (shared := sqrt512SharedAfterFreePtr xHi xLo)
        (store := paramStore)
        (hlookup := sqrt512SharedAfterFreePtr_lookup xHi xLo)
        (hactive := sqrt512SharedAfterFreePtr_activeWords xHi xLo)
  rw [hwrap]
  simp +decide [paramStore, EvmYul.Yul.multifill', EvmYul.Yul.State.lookup!,
    EvmYul.Yul.State.insert, List.zip, List.zipWith_cons_cons,
    List.zipWith_nil_left, List.zipWith_nil_right, List.foldr,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    FormalYul.word, Option.get!, Option.getD]
  simp [FormalYul.returnOf, EvmYul.Yul.State.toMachineState,
    uint256_add_sub_self_32]
  let mload64 :=
    (sharedAfterFrom0 (sqrt512SharedAfterFreePtr xHi xLo) xHi xLo).mload
      (EvmYul.UInt256.ofNat 64)
  change ((mload64.2.mstore mload64.1
      (EvmYul.UInt256.ofNat (model_sqrt512_wrapper_evm xHi xLo))).evmReturn
      mload64.1 (EvmYul.UInt256.ofNat 32)).H_return =
    (EvmYul.UInt256.ofNat (model_sqrt512_wrapper_evm xHi xLo)).toByteArray
  simpa [FormalYul.word] using
    FormalYul.Preservation.evmReturn_mstore_word_H_return
      mload64.2 mload64.1 (EvmYul.UInt256.ofNat (model_sqrt512_wrapper_evm xHi xLo))

theorem call_external_fun_wrap_sqrt512_6228_halt
    (xHi xLo fuel : Nat)
    (store : EvmYul.Yul.VarStore := (Inhabited.default : EvmYul.Yul.VarStore)) :
    ∃ state value,
      EvmYul.Yul.call (fuel + 6200) [] (.some "external_fun_wrap_sqrt512_6228")
        (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) store) =
        .error (EvmYul.Yul.Exception.YulHalt state value) ∧
      FormalYul.returnOf state =
        { returndata := (FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)).toByteArray } := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv,
    sqrt512SharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_sqrt512_6228]
  simp only [yulFunction_external_fun_wrap_sqrt512_6228,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [sqrt512SharedAfterFreePtr_lookup, sqrt512SharedAfterFreePtr_calldata,
    sqrt512SharedAfterFreePtr_calldata_size, sqrt512SharedAfterFreePtr_callvalue,
    sqrt512SharedAfterFreePtr_activeWords,
    EvmYul.Yul.exec.eq_def,
    EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.setMachineState, EvmYul.Yul.State.toMachineState,
    EvmYul.Yul.State.sharedState, EvmYul.Yul.State.executionEnv,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.setLeave, EvmYul.Yul.State.revive,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
  have hdecode :
      EvmYul.Yul.call (fuel + 6195) [EvmYul.UInt256.ofNat 4, EvmYul.UInt256.ofNat 68]
        (.some "abi_decode_tuple_t_uint256t_uint256") (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
          (Inhabited.default : EvmYul.Yul.VarStore)) =
      .ok (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
          (Inhabited.default : EvmYul.Yul.VarStore),
        [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]) := by
    simpa [FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_abi_decode_tuple_t_uint256t_uint256_sqrt512_of_calldata
        (xHi := xHi) (xLo := xLo) (fuel := fuel + 6035)
        (shared := sqrt512SharedAfterFreePtr xHi xLo)
        (store := (Inhabited.default : EvmYul.Yul.VarStore))
        (hlookup := sqrt512SharedAfterFreePtr_lookup xHi xLo)
        (hdata := sqrt512SharedAfterFreePtr_calldata xHi xLo)
  rw [hdecode]
  simp +decide [EvmYul.Yul.multifill', EvmYul.Yul.State.lookup!,
    EvmYul.Yul.State.insert, List.zip, List.zipWith_cons_cons,
    List.zipWith_nil_left, List.zipWith_nil_right, List.foldr,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    FormalYul.word, Option.get!, Option.getD]
  let paramStore : EvmYul.Yul.VarStore :=
    Finmap.insert "param_0" (EvmYul.UInt256.ofNat xHi)
      (Finmap.insert "param_1" (EvmYul.UInt256.ofNat xLo)
        (Inhabited.default : EvmYul.Yul.VarStore))
  have hwrap :
      EvmYul.Yul.call (fuel + 6194) [EvmYul.UInt256.ofNat xHi, EvmYul.UInt256.ofNat xLo]
        (.some "fun_wrap_sqrt512_6228") (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) paramStore) =
      .ok (EvmYul.Yul.State.Ok
          (sharedAfterFrom0 (sqrt512SharedAfterFreePtr xHi xLo) xHi xLo) paramStore,
        [EvmYul.UInt256.ofNat (model_sqrt512_wrapper_evm xHi xLo)]) := by
    simpa [paramStore, FormalYul.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_fun_wrap_sqrt512_6228
        (xHi := xHi) (xLo := xLo) (fuel := fuel + 394)
        (shared := sqrt512SharedAfterFreePtr xHi xLo)
        (store := paramStore)
        (hlookup := sqrt512SharedAfterFreePtr_lookup xHi xLo)
        (hactive := sqrt512SharedAfterFreePtr_activeWords xHi xLo)
  rw [hwrap]
  simp +decide [paramStore, EvmYul.Yul.multifill', EvmYul.Yul.State.lookup!,
    EvmYul.Yul.State.insert, List.zip, List.zipWith_cons_cons,
    List.zipWith_nil_left, List.zipWith_nil_right, List.foldr,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    FormalYul.word, Option.get!, Option.getD]
  simp [FormalYul.returnOf, EvmYul.Yul.State.toMachineState,
    uint256_add_sub_self_32]
  let mload64 :=
    (sharedAfterFrom0 (sqrt512SharedAfterFreePtr xHi xLo) xHi xLo).mload
      (EvmYul.UInt256.ofNat 64)
  change ((mload64.2.mstore mload64.1
      (EvmYul.UInt256.ofNat (model_sqrt512_wrapper_evm xHi xLo))).evmReturn
      mload64.1 (EvmYul.UInt256.ofNat 32)).H_return =
    (EvmYul.UInt256.ofNat (model_sqrt512_wrapper_evm xHi xLo)).toByteArray
  simpa [FormalYul.word] using
    FormalYul.Preservation.evmReturn_mstore_word_H_return
      mload64.2 mload64.1 (EvmYul.UInt256.ofNat (model_sqrt512_wrapper_evm xHi xLo))

def dispatcherMstore : EvmYul.Yul.Ast.Stmt :=
  <s mstore(64, 128)>

def dispatcherCond : EvmYul.Yul.Ast.Expr :=
  <<iszero(lt(calldatasize(), 4))>>

def dispatcherSelectorLet : EvmYul.Yul.Ast.Stmt :=
  <s let selector := shift_right_224_unsigned(calldataload(0))>

def dispatcherSwitch : EvmYul.Yul.Ast.Stmt :=
  <s switch selector
      case 0x3f51628a { external_fun_wrap_sqrt512_6228() }
      case 0x996e33a4 { external_fun_wrap_osqrtUp_6261() }
      default {}>

def dispatcherIf : EvmYul.Yul.Ast.Stmt :=
  <s if iszero(lt(calldatasize(), 4)) {
      let selector := shift_right_224_unsigned(calldataload(0))
      switch selector
      case 0x3f51628a { external_fun_wrap_sqrt512_6228() }
      case 0x996e33a4 { external_fun_wrap_osqrtUp_6261() }
      default {}
    }>

def dispatcherRevert : EvmYul.Yul.Ast.Stmt :=
  <s revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()>

def selectorStore : EvmYul.Yul.VarStore :=
  Finmap.insert "selector" (EvmYul.UInt256.ofNat 1062298250)
    (Inhabited.default : EvmYul.Yul.VarStore)

theorem yulDispatcher_sqrt512_shape :
    yulDispatcher =
      EvmYul.Yul.Ast.Stmt.Block [dispatcherMstore, dispatcherIf, dispatcherRevert] := by
  rfl

@[simp]
theorem exec_dispatcherMstore_sqrt512 (xHi xLo : Nat) :
    EvmYul.Yul.exec 999997 dispatcherMstore (.some yulContract)
      (FormalYul.stateFor yulContract (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])) =
    .ok (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
      (Inhabited.default : EvmYul.Yul.VarStore)) := by
  simp +decide [dispatcherMstore, FormalYul.stateFor, FormalYul.sharedFor,
    FormalYul.envFor, FormalYul.accountMapFor, FormalYul.accountFor,
    EvmYul.Yul.exec.eq_def, EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.evalArgs.eq_def, EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill',
    EvmYul.Yul.State.setMachineState, EvmYul.Yul.State.toMachineState,
    EvmYul.Yul.State.mkOk, EvmYul.Yul.State.initcall,
    sqrt512SharedAfterFreePtr, FormalYul.word]

@[simp]
theorem eval_dispatcherCond_sqrt512 (xHi xLo : Nat) :
    EvmYul.Yul.eval 999995 dispatcherCond (.some yulContract)
      (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
        (Inhabited.default : EvmYul.Yul.VarStore)) =
    .ok (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
        (Inhabited.default : EvmYul.Yul.VarStore), EvmYul.UInt256.ofNat 1) := by
  simp +decide [dispatcherCond, EvmYul.Yul.eval.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.evalArgs.eq_def,
    EvmYul.Yul.evalTail.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.State.executionEnv,
    sqrt512SharedAfterFreePtr_calldata_size, FormalYul.word]

@[simp]
theorem selector_sqrt512_shifted_calldataload0_afterFreePtr (xHi xLo : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (sqrt512SharedAfterFreePtr xHi xLo).toState
        (EvmYul.UInt256.ofNat 0))
      (EvmYul.UInt256.ofNat 224) = EvmYul.UInt256.ofNat 1062298250 := by
  simpa [sqrt512SharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor] using
    selector_sqrt512_shifted_calldataload0 xHi xLo

theorem evalArgs_dispatcherSelectorLet_sqrt512 (xHi xLo : Nat) :
    EvmYul.Yul.reverse'
      (EvmYul.Yul.evalArgs 999993
        [EvmYul.Yul.Ast.Expr.Call
          (Sum.inl (EvmYul.Operation.CALLDATALOAD : EvmYul.Operation .Yul))
          [EvmYul.Yul.Ast.Expr.Lit (EvmYul.UInt256.ofNat 0)]].reverse
        (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
          (Inhabited.default : EvmYul.Yul.VarStore))) =
    .ok (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
          (Inhabited.default : EvmYul.Yul.VarStore),
      [EvmYul.State.calldataload (sqrt512SharedAfterFreePtr xHi xLo).toState
        (EvmYul.UInt256.ofNat 0)]) := by
  simp +decide [EvmYul.Yul.evalArgs.eq_def, EvmYul.Yul.eval.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.State.toState]

@[simp]
theorem exec_dispatcherSelectorLet_sqrt512 (xHi xLo : Nat) :
    EvmYul.Yul.exec 999994 dispatcherSelectorLet (.some yulContract)
      (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
        (Inhabited.default : EvmYul.Yul.VarStore)) =
    .ok (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) selectorStore) := by
  rw [EvmYul.Yul.exec.eq_def]
  simp only [dispatcherSelectorLet]
  rw [evalArgs_dispatcherSelectorLet_sqrt512 xHi xLo]
  rw [EvmYul.Yul.execCall.eq_def]
  simp only [Nat.reduceAdd, reduceCtorEq]
  change EvmYul.Yul.multifill' ["selector"]
      (EvmYul.Yul.call 999992
        [EvmYul.State.calldataload (sqrt512SharedAfterFreePtr xHi xLo).toState
          (EvmYul.UInt256.ofNat 0)]
        (.some "shift_right_224_unsigned") (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
          (Inhabited.default : EvmYul.Yul.VarStore))) =
    .ok (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) selectorStore)
  have hcall :
      EvmYul.Yul.call 999992
        [EvmYul.State.calldataload (sqrt512SharedAfterFreePtr xHi xLo).toState
          (EvmYul.UInt256.ofNat 0)]
        (.some "shift_right_224_unsigned") (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
          (Inhabited.default : EvmYul.Yul.VarStore)) =
      .ok (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
          (Inhabited.default : EvmYul.Yul.VarStore),
        [EvmYul.UInt256.ofNat 1062298250]) := by
    simpa [selector_sqrt512_shifted_calldataload0_afterFreePtr,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      call_shift_right_224_unsigned
        (value := EvmYul.State.calldataload (sqrt512SharedAfterFreePtr xHi xLo).toState
          (EvmYul.UInt256.ofNat 0))
        (fuel := 999972) (shared := sqrt512SharedAfterFreePtr xHi xLo)
        (store := (Inhabited.default : EvmYul.Yul.VarStore))
        (hlookup := sqrt512SharedAfterFreePtr_lookup xHi xLo)
  rw [hcall]
  simp [selectorStore, EvmYul.Yul.multifill', EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.insert]

@[simp]
theorem selectSwitchCase_dispatcherSwitch_sqrt512 (xHi xLo : Nat) :
    EvmYul.Yul.selectSwitchCase
        (EvmYul.Yul.State.lookup! "selector"
          (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) selectorStore))
        [(EvmYul.UInt256.ofNat 1062298250,
            [<s external_fun_wrap_sqrt512_6228()>]),
          (EvmYul.UInt256.ofNat 2574136228,
            [<s external_fun_wrap_osqrtUp_6261()>])] =
      some [<s external_fun_wrap_sqrt512_6228()>] := by
  simp +decide [EvmYul.Yul.selectSwitchCase, selectorStore,
    EvmYul.Yul.State.lookup!, Finmap.lookup_insert]

@[simp]
theorem exec_dispatcherSwitch_sqrt512_returnOf (xHi xLo : Nat) :
    (match EvmYul.Yul.exec 999993 dispatcherSwitch (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) selectorStore) with
      | Except.ok state => Except.ok (FormalYul.returnOf state)
      | Except.error (.YulHalt state _) => Except.ok (FormalYul.returnOf state)
      | Except.error .Revert => Except.error "revert"
      | Except.error err => Except.error (reprStr err)) =
      Except.ok { returndata := (FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)).toByteArray } := by
  rw [EvmYul.Yul.exec.eq_def]
  simp only [dispatcherSwitch]
  simp only [EvmYul.Yul.eval.eq_def]
  change (match
        (match EvmYul.Yul.selectSwitchCase
          (EvmYul.Yul.State.lookup! "selector"
            (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) selectorStore))
          [(EvmYul.UInt256.ofNat 1062298250,
              [<s external_fun_wrap_sqrt512_6228()>]),
            (EvmYul.UInt256.ofNat 2574136228,
              [<s external_fun_wrap_osqrtUp_6261()>])] with
        | some stmts =>
            EvmYul.Yul.exec 999992 (EvmYul.Yul.Ast.Stmt.Block stmts) (.some yulContract)
              (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) selectorStore)
        | none =>
            EvmYul.Yul.exec 999992 (EvmYul.Yul.Ast.Stmt.Block []) (.some yulContract)
              (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) selectorStore)) with
      | Except.ok state => Except.ok (FormalYul.returnOf state)
      | Except.error (.YulHalt state _) => Except.ok (FormalYul.returnOf state)
      | Except.error .Revert => Except.error "revert"
      | Except.error err => Except.error (reprStr err)) =
      Except.ok { returndata := (FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)).toByteArray }
  rw [selectSwitchCase_dispatcherSwitch_sqrt512 xHi xLo]
  simp only
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  change (match (match
      EvmYul.Yul.exec 999991 (<s external_fun_wrap_sqrt512_6228()>) (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) selectorStore) with
    | Except.error e => Except.error e
    | Except.ok state =>
        EvmYul.Yul.exec (Nat.succ 999990) (EvmYul.Yul.Ast.Stmt.Block [])
          (.some yulContract) state) with
    | Except.ok state => Except.ok (FormalYul.returnOf state)
    | Except.error (.YulHalt state _) => Except.ok (FormalYul.returnOf state)
    | Except.error .Revert => Except.error "revert"
    | Except.error err => Except.error (reprStr err)) =
      Except.ok { returndata := (FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)).toByteArray }
  refine Eq.trans (b := (match
      EvmYul.Yul.exec 999991 (<s external_fun_wrap_sqrt512_6228()>)
        (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) selectorStore) with
    | Except.ok state => Except.ok (FormalYul.returnOf state)
    | Except.error (.YulHalt state _) => Except.ok (FormalYul.returnOf state)
    | Except.error .Revert => Except.error "revert"
    | Except.error err => Except.error (reprStr err))) ?_ ?_
  · exact FormalYul.Preservation.returnOf_exec_block_nil
      (fuel := 999990) (code := (.some yulContract))
      (r := EvmYul.Yul.exec 999991 (<s external_fun_wrap_sqrt512_6228()>)
        (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) selectorStore))
  · rw [EvmYul.Yul.exec.eq_def]
    simp only [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalArgs.eq_def,
      List.reverse_nil, EvmYul.Yul.reverse']
    refine Eq.trans (b := (match
        EvmYul.Yul.call 999989 [] (.some "external_fun_wrap_sqrt512_6228")
          (.some yulContract)
          (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) selectorStore) with
      | Except.ok (state, _) => Except.ok (FormalYul.returnOf state)
      | Except.error (.YulHalt state _) => Except.ok (FormalYul.returnOf state)
      | Except.error .Revert => Except.error "revert"
      | Except.error err => Except.error (reprStr err))) ?_ ?_
    · exact FormalYul.Preservation.returnOf_multifill_nil
        (r := EvmYul.Yul.call 999989 [] (.some "external_fun_wrap_sqrt512_6228")
          (.some yulContract)
          (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) selectorStore))
    · exact call_external_fun_wrap_sqrt512_6228_returnOf
        (xHi := xHi) (xLo := xLo) (fuel := 993789) (store := selectorStore)

theorem exec_dispatcherSwitch_sqrt512_halt (xHi xLo : Nat) :
    ∃ state value,
      EvmYul.Yul.exec 999993 dispatcherSwitch (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) selectorStore) =
        .error (EvmYul.Yul.Exception.YulHalt state value) ∧
      FormalYul.returnOf state =
        { returndata := (FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)).toByteArray } := by
  rw [EvmYul.Yul.exec.eq_def]
  simp only [dispatcherSwitch]
  simp only [EvmYul.Yul.eval.eq_def]
  change ∃ state value,
    (match EvmYul.Yul.selectSwitchCase
          (EvmYul.Yul.State.lookup! "selector"
            (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) selectorStore))
          [(EvmYul.UInt256.ofNat 1062298250,
              [<s external_fun_wrap_sqrt512_6228()>]),
            (EvmYul.UInt256.ofNat 2574136228,
              [<s external_fun_wrap_osqrtUp_6261()>])] with
      | some stmts =>
          EvmYul.Yul.exec 999992 (EvmYul.Yul.Ast.Stmt.Block stmts) (.some yulContract)
            (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) selectorStore)
      | none =>
          EvmYul.Yul.exec 999992 (EvmYul.Yul.Ast.Stmt.Block []) (.some yulContract)
            (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) selectorStore)) =
        .error (EvmYul.Yul.Exception.YulHalt state value) ∧
      FormalYul.returnOf state =
        { returndata := (FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)).toByteArray }
  rw [selectSwitchCase_dispatcherSwitch_sqrt512 xHi xLo]
  simp only
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  rw [EvmYul.Yul.exec.eq_def]
  simp only [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalArgs.eq_def,
    List.reverse_nil, EvmYul.Yul.reverse']
  rcases call_external_fun_wrap_sqrt512_6228_halt
      (xHi := xHi) (xLo := xLo) (fuel := 993789) (store := selectorStore) with
    ⟨state, value, hcall, hret⟩
  rw [hcall]
  exact ⟨state, value, rfl, hret⟩

@[simp]
theorem exec_dispatcherIf_sqrt512_returnOf (xHi xLo : Nat) :
    (match EvmYul.Yul.exec 999996 dispatcherIf (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
          (Inhabited.default : EvmYul.Yul.VarStore)) with
      | Except.ok state => Except.ok (FormalYul.returnOf state)
      | Except.error (.YulHalt state _) => Except.ok (FormalYul.returnOf state)
      | Except.error .Revert => Except.error "revert"
      | Except.error err => Except.error (reprStr err)) =
      Except.ok { returndata := (FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)).toByteArray } := by
  rw [EvmYul.Yul.exec.eq_def]
  simp only [dispatcherIf]
  change (match (match EvmYul.Yul.eval 999995 dispatcherCond (.some yulContract)
      (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
        (Inhabited.default : EvmYul.Yul.VarStore)) with
    | Except.error e => Except.error e
    | Except.ok (s, cond) =>
        if cond ≠ (EvmYul.UInt256.ofNat 0) then
          EvmYul.Yul.exec 999995
            (EvmYul.Yul.Ast.Stmt.Block [dispatcherSelectorLet, dispatcherSwitch])
            (.some yulContract) s
        else Except.ok s) with
    | Except.ok state => Except.ok (FormalYul.returnOf state)
    | Except.error (.YulHalt state _) => Except.ok (FormalYul.returnOf state)
    | Except.error .Revert => Except.error "revert"
    | Except.error err => Except.error (reprStr err)) =
      Except.ok { returndata := (FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)).toByteArray }
  rw [eval_dispatcherCond_sqrt512 xHi xLo]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ↓reduceIte]
  change (match EvmYul.Yul.exec 999995
        (EvmYul.Yul.Ast.Stmt.Block [dispatcherSelectorLet, dispatcherSwitch]) (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
          (Inhabited.default : EvmYul.Yul.VarStore)) with
      | Except.ok state => Except.ok (FormalYul.returnOf state)
      | Except.error (.YulHalt state _) => Except.ok (FormalYul.returnOf state)
      | Except.error .Revert => Except.error "revert"
      | Except.error err => Except.error (reprStr err)) =
      Except.ok { returndata := (FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)).toByteArray }
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  rw [exec_dispatcherSelectorLet_sqrt512 xHi xLo]
  simp only
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  change (match (match
      EvmYul.Yul.exec 999993 dispatcherSwitch (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) selectorStore) with
    | Except.error e => Except.error e
    | Except.ok state =>
        EvmYul.Yul.exec (Nat.succ 999992) (EvmYul.Yul.Ast.Stmt.Block [])
          (.some yulContract) state) with
    | Except.ok state => Except.ok (FormalYul.returnOf state)
    | Except.error (.YulHalt state _) => Except.ok (FormalYul.returnOf state)
    | Except.error .Revert => Except.error "revert"
    | Except.error err => Except.error (reprStr err)) =
      Except.ok { returndata := (FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)).toByteArray }
  refine Eq.trans (b := (match
      EvmYul.Yul.exec 999993 dispatcherSwitch (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) selectorStore) with
    | Except.ok state => Except.ok (FormalYul.returnOf state)
    | Except.error (.YulHalt state _) => Except.ok (FormalYul.returnOf state)
    | Except.error .Revert => Except.error "revert"
    | Except.error err => Except.error (reprStr err))) ?_ ?_
  · exact FormalYul.Preservation.returnOf_exec_block_nil
      (fuel := 999992) (code := (.some yulContract))
      (r := EvmYul.Yul.exec 999993 dispatcherSwitch (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo) selectorStore))
  · exact exec_dispatcherSwitch_sqrt512_returnOf xHi xLo

theorem exec_dispatcherIf_sqrt512_halt (xHi xLo : Nat) :
    ∃ state value,
      EvmYul.Yul.exec 999996 dispatcherIf (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
          (Inhabited.default : EvmYul.Yul.VarStore)) =
        .error (EvmYul.Yul.Exception.YulHalt state value) ∧
      FormalYul.returnOf state =
        { returndata := (FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)).toByteArray } := by
  rw [EvmYul.Yul.exec.eq_def]
  simp only [dispatcherIf]
  change ∃ state value,
    (match EvmYul.Yul.eval 999995 dispatcherCond (.some yulContract)
      (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
        (Inhabited.default : EvmYul.Yul.VarStore)) with
    | Except.error e => Except.error e
    | Except.ok (s, cond) =>
        if cond ≠ (EvmYul.UInt256.ofNat 0) then
          EvmYul.Yul.exec 999995
            (EvmYul.Yul.Ast.Stmt.Block [dispatcherSelectorLet, dispatcherSwitch])
            (.some yulContract) s
        else Except.ok s) =
        .error (EvmYul.Yul.Exception.YulHalt state value) ∧
      FormalYul.returnOf state =
        { returndata := (FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)).toByteArray }
  rw [eval_dispatcherCond_sqrt512 xHi xLo]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ↓reduceIte]
  change ∃ state value,
    EvmYul.Yul.exec 999995
        (EvmYul.Yul.Ast.Stmt.Block [dispatcherSelectorLet, dispatcherSwitch]) (.some yulContract)
        (EvmYul.Yul.State.Ok (sqrt512SharedAfterFreePtr xHi xLo)
          (Inhabited.default : EvmYul.Yul.VarStore)) =
        .error (EvmYul.Yul.Exception.YulHalt state value) ∧
      FormalYul.returnOf state =
        { returndata := (FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)).toByteArray }
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  rw [exec_dispatcherSelectorLet_sqrt512 xHi xLo]
  simp only
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  rcases exec_dispatcherSwitch_sqrt512_halt xHi xLo with ⟨state, value, hswitch, hret⟩
  rw [hswitch]
  exact ⟨state, value, rfl, hret⟩

theorem exec_yulDispatcher_sqrt512_halt (xHi xLo : Nat) :
    ∃ state value,
      EvmYul.Yul.exec 999998 yulDispatcher (.some yulContract)
        (FormalYul.stateFor yulContract (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])) =
        .error (EvmYul.Yul.Exception.YulHalt state value) ∧
      FormalYul.returnOf state =
        { returndata := (FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)).toByteArray } := by
  rw [yulDispatcher_sqrt512_shape]
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  rw [exec_dispatcherMstore_sqrt512 xHi xLo]
  simp only
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  rcases exec_dispatcherIf_sqrt512_halt xHi xLo with ⟨state, value, hif, hret⟩
  rw [hif]
  exact ⟨state, value, rfl, hret⟩

@[simp]
theorem callDispatcher_sqrt512_returnOf (xHi xLo : Nat) :
    (match EvmYul.Yul.callDispatcher 1000000 (.some yulContract)
        (FormalYul.stateFor yulContract (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])) with
      | Except.ok (state, _) => Except.ok (FormalYul.returnOf state)
      | Except.error (.YulHalt state _) => Except.ok (FormalYul.returnOf state)
      | Except.error .Revert => Except.error "revert"
      | Except.error err => Except.error (reprStr err)) =
      Except.ok { returndata := (FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)).toByteArray } := by
  rw [EvmYul.Yul.callDispatcher.eq_def]
  simp only [FormalYul.stateFor, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.executionEnv, yulContract_dispatcher,
    FormalYul.sharedFor, FormalYul.envFor, FormalYul.accountMapFor,
    FormalYul.accountFor, EvmYul.Yul.State.multifill, EvmYul.Yul.State.setStore,
    List.zip_nil_left, List.foldr_nil,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def]
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  rcases exec_yulDispatcher_sqrt512_halt xHi xLo with ⟨state, value, hdisp, hret⟩
  have hdisp' :
      EvmYul.Yul.exec 999998 yulDispatcher (.some yulContract)
        (EvmYul.Yul.State.Ok
          { (Inhabited.default : EvmYul.SharedState .Yul) with
            accountMap := FormalYul.accountMapFor yulContract
            executionEnv := FormalYul.envFor yulContract
              (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo])
            gasAvailable := .ofNat 1000000000 }
          (Inhabited.default : EvmYul.Yul.VarStore)) =
        .error (EvmYul.Yul.Exception.YulHalt state value) := by
    simpa [FormalYul.stateFor, FormalYul.sharedFor] using hdisp
  have hdisp'' :
      EvmYul.Yul.exec 999998 yulDispatcher (.some yulContract)
        (EvmYul.Yul.State.Ok
          { accountMap := FormalYul.accountMapFor yulContract,
            σ₀ := (Inhabited.default : EvmYul.SharedState .Yul).σ₀,
            totalGasUsedInBlock := (Inhabited.default : EvmYul.SharedState .Yul).totalGasUsedInBlock,
            transactionReceipts := (Inhabited.default : EvmYul.SharedState .Yul).transactionReceipts,
            substate := (Inhabited.default : EvmYul.SharedState .Yul).substate,
            executionEnv := FormalYul.envFor yulContract
              (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo]),
            blocks := (Inhabited.default : EvmYul.SharedState .Yul).blocks,
            genesisBlockHeader := (Inhabited.default : EvmYul.SharedState .Yul).genesisBlockHeader,
            createdAccounts := (Inhabited.default : EvmYul.SharedState .Yul).createdAccounts,
            gasAvailable := EvmYul.UInt256.ofNat 1000000000,
            activeWords := (Inhabited.default : EvmYul.SharedState .Yul).activeWords,
            memory := (Inhabited.default : EvmYul.SharedState .Yul).memory,
            returnData := (Inhabited.default : EvmYul.SharedState .Yul).returnData,
            H_return := (Inhabited.default : EvmYul.SharedState .Yul).H_return }
          (Inhabited.default : EvmYul.Yul.VarStore)) =
        .error (EvmYul.Yul.Exception.YulHalt state value) := by
    simpa using hdisp'
  have hdisp''' :
      EvmYul.Yul.exec 999998 yulDispatcher (.some yulContract)
        (EvmYul.Yul.State.Ok
          { accountMap := Batteries.RBMap.insert ∅ FormalYul.contractOwner
              { (Inhabited.default : EvmYul.Account .Yul) with code := yulContract },
            σ₀ := (Inhabited.default : EvmYul.SharedState .Yul).σ₀,
            totalGasUsedInBlock := (Inhabited.default : EvmYul.SharedState .Yul).totalGasUsedInBlock,
            transactionReceipts := (Inhabited.default : EvmYul.SharedState .Yul).transactionReceipts,
            substate := (Inhabited.default : EvmYul.SharedState .Yul).substate,
            executionEnv := { (Inhabited.default : EvmYul.ExecutionEnv .Yul) with
              calldata := selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo]
              code := yulContract
              codeOwner := FormalYul.contractOwner
              weiValue := ⟨0⟩
              perm := true },
            blocks := (Inhabited.default : EvmYul.SharedState .Yul).blocks,
            genesisBlockHeader := (Inhabited.default : EvmYul.SharedState .Yul).genesisBlockHeader,
            createdAccounts := (Inhabited.default : EvmYul.SharedState .Yul).createdAccounts,
            gasAvailable := EvmYul.UInt256.ofNat 1000000000,
            activeWords := (Inhabited.default : EvmYul.SharedState .Yul).activeWords,
            memory := (Inhabited.default : EvmYul.SharedState .Yul).memory,
            returnData := (Inhabited.default : EvmYul.SharedState .Yul).returnData,
            H_return := (Inhabited.default : EvmYul.SharedState .Yul).H_return }
          (Inhabited.default : EvmYul.Yul.VarStore)) =
        .error (EvmYul.Yul.Exception.YulHalt state value) := by
    simpa [FormalYul.accountMapFor, FormalYul.accountFor, FormalYul.envFor] using hdisp''
  rw [hdisp''']
  exact congrArg Except.ok hret

@[simp]
theorem runContract_sqrt512_wrapper_returnOf (xHi xLo : Nat) :
    FormalYul.runContract yulContract
      (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo]) 1000000 =
      Except.ok { returndata := (FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)).toByteArray } := by
  unfold FormalYul.runContract
  exact callDispatcher_sqrt512_returnOf xHi xLo

theorem run_sqrt512_wrapper_evm_eq_model_sqrt512_wrapper_evm (xHi xLo : Nat) :
    run_sqrt512_wrapper_evm xHi xLo = .ok (model_sqrt512_wrapper_evm xHi xLo) := by
  unfold run_sqrt512_wrapper_evm FormalYul.callWord FormalYul.call
  change (do
      let result ← FormalYul.runContract yulContract
        (selector_sqrt512 ++ FormalYul.encodeWords [xHi, xLo]) 1000000
      FormalYul.resultWord result) =
    Except.ok (model_sqrt512_wrapper_evm xHi xLo)
  rw [runContract_sqrt512_wrapper_returnOf xHi xLo]
  change FormalYul.resultWord
      { returndata := (FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)).toByteArray } =
    Except.ok (model_sqrt512_wrapper_evm xHi xLo)
  rw [show FormalYul.resultWord
        { returndata := (FormalYul.word (model_sqrt512_wrapper_evm xHi xLo)).toByteArray } =
      Except.ok (FormalYul.u256 (model_sqrt512_wrapper_evm xHi xLo)) by
        simp [FormalYul.resultWord, FormalYul.word,
          FormalYul.Preservation.decodeWord_toByteArray,
          EvmYul.UInt256.toByteArray_size,
          uint256_ofNat_toNat_eq_formal_u256]]
  rw [FormalYul.Preservation.u256_eq_self_of_lt (model_sqrt512_wrapper_evm_lt_word xHi xLo)]

end Sqrt512Yul
