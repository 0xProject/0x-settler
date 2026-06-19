import FormalYul.Runtime

namespace FormalYul

namespace Preservation

@[simp]
theorem wordNat_word (x : Nat) : wordNat (word x) = u256 x := by
  unfold wordNat word EvmYul.UInt256.toNat EvmYul.UInt256.ofNat u256 WORD_MOD EvmYul.UInt256.size
  change
    (Fin.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639936
        x).val =
      x % 115792089237316195423570985008687907853269984665640564039457584007913129639936
  rw [Fin.val_ofNat]

@[simp]
theorem wordNat_add (a b : EvmYul.UInt256) :
    wordNat (a + b) = evmAdd (wordNat a) (wordNat b) := by
  change wordNat (EvmYul.UInt256.add a b) = evmAdd (wordNat a) (wordNat b)
  unfold wordNat evmAdd u256 WORD_MOD EvmYul.UInt256.add EvmYul.UInt256.toNat
    EvmYul.UInt256.size
  simp [Fin.val_add]

@[simp]
theorem wordNat_mul (a b : EvmYul.UInt256) :
    wordNat (a * b) = evmMul (wordNat a) (wordNat b) := by
  change wordNat (EvmYul.UInt256.mul a b) = evmMul (wordNat a) (wordNat b)
  unfold wordNat evmMul u256 WORD_MOD EvmYul.UInt256.mul EvmYul.UInt256.toNat
    EvmYul.UInt256.size
  simp [Fin.val_mul]

@[simp]
theorem okWord_eq (x : Nat) : okWord x = .ok (u256 x) := rfl

@[simp]
theorem calldata_eq (selector : ByteArray) (args : List Nat) :
    calldata selector args = selector ++ encodeWords args := rfl

@[simp]
theorem callWord_eq_call_resultWord
    (contract : YulContract) (selector : ByteArray) (args : List Nat) (fuel : Nat) :
    callWord contract selector args fuel = (do
      let result ← call contract selector args fuel
      resultWord result) := rfl

@[simp]
theorem callPair_eq_call_resultWords
    (contract : YulContract) (selector : ByteArray) (args : List Nat) (fuel : Nat) :
    callPair contract selector args fuel = (do
      let words ← callWords contract selector args 2 fuel
      pairFromWords words) := rfl

@[simp]
theorem callTriple_eq_call_resultWords
    (contract : YulContract) (selector : ByteArray) (args : List Nat) (fuel : Nat) :
    callTriple contract selector args fuel = (do
      let words ← callWords contract selector args 3 fuel
      tripleFromWords words) := rfl

end Preservation

end FormalYul
