import Sqrt512Proof.GeneratedSqrt512Model

/-!
# Sqrt512 model evaluator

Compiled executable for evaluating the generated EVM-faithful 512-bit
Sqrt model on concrete inputs. Intended for fuzz testing via Foundry's
`vm.ffi`.

Usage:
  sqrt512-model sqrt512 <hex_x_hi> <hex_x_lo>

Output: 0x-prefixed hex uint256 on stdout.
-/

open Sqrt512GeneratedModel in
def evalFunction (name : String) (xHi xLo : Nat) : Option Nat :=
  match name with
  | "sqrt512" => some (model_sqrt512_evm xHi xLo)
  | _         => none

def natToHex64 (n : Nat) : String :=
  let hex := String.ofList (Nat.toDigits 16 n)
  "0x" ++ String.ofList (List.replicate (64 - hex.length) '0') ++ hex

def parseHex (s : String) : Option Nat :=
  let s := if s.startsWith "0x" || s.startsWith "0X" then s.drop 2 else s
  s.foldl (fun acc c =>
    acc.bind fun n =>
      if '0' ≤ c && c ≤ '9' then some (n * 16 + (c.toNat - '0'.toNat))
      else if 'a' ≤ c && c ≤ 'f' then some (n * 16 + (c.toNat - 'a'.toNat + 10))
      else if 'A' ≤ c && c ≤ 'F' then some (n * 16 + (c.toNat - 'A'.toNat + 10))
      else none
  ) (some 0)

def main (args : List String) : IO UInt32 := do
  match args with
  | [fnName, hexHi, hexLo] =>
    match parseHex hexHi, parseHex hexLo with
    | some hi, some lo =>
      match evalFunction fnName hi lo with
      | none => IO.eprintln s!"Unknown function: {fnName}"; return 1
      | some result =>
        IO.println (natToHex64 result)
        return 0
    | _, _ =>
      IO.eprintln s!"Invalid hex input"
      return 1
  | _ =>
    IO.eprintln "Usage: sqrt512-model sqrt512 <hex_x_hi> <hex_x_lo>"
    return 1
