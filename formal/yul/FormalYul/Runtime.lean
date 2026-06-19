import FormalYul.Word
import EvmYul.Yul.Interpreter
import EvmYul.Yul.YulNotation

namespace FormalYul

abbrev YulContract := EvmYul.Yul.Ast.YulContract

def emptyContract : YulContract :=
  (Inhabited.default : YulContract)

def word (x : Nat) : EvmYul.UInt256 :=
  EvmYul.UInt256.ofNat x

def wordNat (x : EvmYul.UInt256) : Nat :=
  x.toNat

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
