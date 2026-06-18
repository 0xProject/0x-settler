import LnProof.LnYul

/-!
# Ln model evaluator

Compiled executable for evaluating the generated EVM-faithful Ln model
on concrete inputs. Intended for fuzz testing via Foundry's `vm.ffi`.

Usage:
  ln-model <function> <hex_x>

Functions: ln_wad, ln_wad_to_wad

Output: 0x-prefixed hex uint256 (two's complement int256) on stdout.
-/

open LnYul in
def evalFunction (name : String) (x : Nat) : Option Nat :=
  match name with
  | "ln_wad"        => some (model_ln_wad_evm x)
  | "ln_wad_to_wad" => some (model_ln_wad_to_wad_evm x)
  | _               => none

def natToHex64 (n : Nat) : String :=
  let hex := String.mk (Nat.toDigits 16 n)
  "0x" ++ String.mk (List.replicate (64 - hex.length) '0') ++ hex

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
  | [fnName, hexX] =>
    match parseHex hexX with
    | none => IO.eprintln s!"Invalid hex input: {hexX}"; return 1
    | some x =>
      match evalFunction fnName x with
      | none => IO.eprintln s!"Unknown function: {fnName}"; return 1
      | some result =>
        IO.println (natToHex64 result)
        return 0
  | _ =>
    IO.eprintln "Usage: ln-model <ln_wad|ln_wad_to_wad> <hex_x>"
    return 1
