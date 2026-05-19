import Cbrt512Proof.GeneratedCbrt512Model

/-!
# Cbrt512 model evaluator

Compiled executable for evaluating the generated EVM-faithful 512-bit
Cbrt model on concrete inputs. Intended for fuzz testing via Foundry's
`vm.ffi`.

Usage:
  cbrt512-model cbrt512          <hex_x_hi> <hex_x_lo>   → 1 hex word
  cbrt512-model cbrt512_wrapper  <hex_x_hi> <hex_x_lo>   → 1 hex word
  cbrt512-model cbrtUp512_wrapper <hex_x_hi> <hex_x_lo>  → 1 hex word
-/

open Cbrt512GeneratedModel in
def evalFunction (name : String) (xHi xLo : Nat) : Option Nat :=
  match name with
  | "cbrt512"           => some (model_cbrt512_evm xHi xLo)
  | "cbrt512_wrapper"   => some (model_cbrt512_wrapper_evm xHi xLo)
  | "cbrtUp512_wrapper" => some (model_cbrtUp512_wrapper_evm xHi xLo)
  | _                   => none

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
      | some result =>
        IO.println (natToHex64 result)
        return 0
      | none =>
        IO.eprintln s!"Unknown function: {fnName}"
        return 1
    | _, _ =>
      IO.eprintln s!"Invalid hex input"
      return 1
  | _ =>
    IO.eprintln "Usage: cbrt512-model <function> <hex_x_hi> <hex_x_lo>"
    return 1
