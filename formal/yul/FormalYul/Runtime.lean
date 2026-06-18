import EvmYul.Yul.Interpreter
import EvmYul.Yul.YulNotation

namespace FormalYul

abbrev YulContract := EvmYul.Yul.Ast.YulContract

def emptyContract : YulContract :=
  (Inhabited.default : YulContract)

def WORD_MOD : Nat :=
  2 ^ 256

def u256 (x : Nat) : Nat :=
  x % WORD_MOD

def word (x : Nat) : EvmYul.UInt256 :=
  EvmYul.UInt256.ofNat x

def wordNat (x : EvmYul.UInt256) : Nat :=
  x.toNat

private def byteAt (x i : Nat) : UInt8 :=
  UInt8.ofNat ((x / 2 ^ (8 * i)) % 256)

def encodeWord (x : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.empty
    for i in [:32] do
      out := out.push (byteAt (u256 x) (31 - i))
    out

def encodeWords (xs : List Nat) : ByteArray :=
  xs.foldl (fun acc x => acc ++ encodeWord x) ByteArray.empty

def bytes (xs : List Nat) : ByteArray :=
  xs.foldl (fun acc x => acc.push (UInt8.ofNat x)) ByteArray.empty

def calldata (selector : ByteArray) (args : List Nat) : ByteArray :=
  selector ++ encodeWords args

def decodeWord (data : ByteArray) (offset : Nat := 0) : Nat :=
  Id.run do
    let bytes := data.data
    let mut acc : Nat := 0
    for i in [0:32] do
      let j : Nat := offset + i
      acc := acc * 256 + (bytes.getD j 0).toNat
    acc

def decodeWords (data : ByteArray) (count : Nat) : List Nat :=
  (List.range count).map fun i => decodeWord data (32 * i)

structure CallResult where
  returndata : ByteArray
  deriving Inhabited, Repr

def resultWord (result : CallResult) : Except String Nat :=
  if result.returndata.size < 32 then
    .error "returndata shorter than one ABI word"
  else
    .ok (decodeWord result.returndata)

def resultWords (result : CallResult) (count : Nat) : Except String (List Nat) :=
  if result.returndata.size < 32 * count then
    .error "returndata shorter than requested ABI words"
  else
    .ok (decodeWords result.returndata count)

def pairFromWords : List Nat → Except String (Nat × Nat)
  | [a, b] => .ok (a, b)
  | _ => .error "expected two ABI words"

def tripleFromWords : List Nat → Except String (Nat × Nat × Nat)
  | [a, b, c] => .ok (a, b, c)
  | _ => .error "expected three ABI words"

def okWord (x : Nat) : Except String Nat :=
  .ok (u256 x)

def stateFor (contract : YulContract) (input : ByteArray) : EvmYul.Yul.State :=
  let env : EvmYul.ExecutionEnv .Yul :=
    { (Inhabited.default : EvmYul.ExecutionEnv .Yul) with
      calldata := input
      code := contract
      weiValue := ⟨0⟩
      perm := true }
  let shared : EvmYul.SharedState .Yul :=
    { (Inhabited.default : EvmYul.SharedState .Yul) with
      executionEnv := env
      gasAvailable := .ofNat 1000000000 }
  .Ok shared (Inhabited.default : EvmYul.Yul.VarStore)

def returnOf (state : EvmYul.Yul.State) : CallResult :=
  { returndata := EvmYul.Yul.State.toMachineState state |>.H_return }

def runContract (contract : YulContract) (input : ByteArray) (fuel : Nat := 1000000) :
    Except String CallResult :=
  match EvmYul.Yul.callDispatcher fuel (.some contract) (stateFor contract input) with
  | .ok (state, _) => .ok (returnOf state)
  | .error (.YulHalt state _) => .ok (returnOf state)
  | .error .Revert => .error "revert"
  | .error err => .error (reprStr err)

def call (contract : YulContract) (selector : ByteArray) (args : List Nat)
    (fuel : Nat := 1000000) : Except String CallResult :=
  runContract contract (calldata selector args) fuel

def callWord (contract : YulContract) (selector : ByteArray) (args : List Nat)
    (fuel : Nat := 1000000) : Except String Nat := do
  let result ← call contract selector args fuel
  resultWord result

def callWords (contract : YulContract) (selector : ByteArray) (args : List Nat) (count : Nat)
    (fuel : Nat := 1000000) : Except String (List Nat) := do
  let result ← call contract selector args fuel
  resultWords result count

def callPair (contract : YulContract) (selector : ByteArray) (args : List Nat)
    (fuel : Nat := 1000000) : Except String (Nat × Nat) := do
  let words ← callWords contract selector args 2 fuel
  pairFromWords words

def callTriple (contract : YulContract) (selector : ByteArray) (args : List Nat)
    (fuel : Nat := 1000000) : Except String (Nat × Nat × Nat) := do
  let words ← callWords contract selector args 3 fuel
  tripleFromWords words

end FormalYul
