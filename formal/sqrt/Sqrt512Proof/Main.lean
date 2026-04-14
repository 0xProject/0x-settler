import Sqrt512Proof.GeneratedSqrt512Model

/-!
# Sqrt512 model evaluator

Compiled executable for evaluating the generated EVM-faithful 512-bit
Sqrt model on concrete inputs. Intended for fuzz testing via Foundry's
`vm.ffi`.

Usage:
  sqrt512-model sqrt512          <hex_x_hi> <hex_x_lo>   → 1 hex word
  sqrt512-model sqrt512_wrapper  <hex_x_hi> <hex_x_lo>   → 1 hex word
  sqrt512-model osqrtUp          <hex_x_hi> <hex_x_lo>   → 2 hex words (ABI-encoded)
-/

open Sqrt512GeneratedModel in
def evalFunction1 (name : String) (xHi xLo : Nat) : Option Nat :=
  match name with
  | "sqrt512"         => some (model_sqrt512_evm xHi xLo)
  | "sqrt512_wrapper" => some (model_sqrt512_wrapper_evm xHi xLo)
  | _                 => none

open Sqrt512GeneratedModel in
def evalFunction2 (name : String) (xHi xLo : Nat) : Option (Nat × Nat) :=
  match name with
  | "osqrtUp" => some (model_osqrtUp_evm xHi xLo)
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
      -- Try single-word functions first
      match evalFunction1 fnName hi lo with
      | some result =>
        -- ABI-encode as single uint256: 32 bytes zero-padded
        IO.println (natToHex64 result)
        return 0
      | none =>
        -- Try two-word functions
        match evalFunction2 fnName hi lo with
        | some (rHi, rLo) =>
          -- ABI-encode as (uint256, uint256): 64 bytes
          -- Foundry's vm.ffi decodes the stdout as raw ABI bytes
          IO.println (natToHex64 rHi ++ (natToHex64 rLo).drop 2)
          return 0
        | none =>
          IO.eprintln s!"Unknown function: {fnName}"
          return 1
    | _, _ =>
      IO.eprintln s!"Invalid hex input"
      return 1
  | _ =>
    IO.eprintln "Usage: sqrt512-model <function> <hex_x_hi> <hex_x_lo>"
    return 1
