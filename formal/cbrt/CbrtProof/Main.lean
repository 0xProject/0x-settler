import CbrtProof.GeneratedCbrtModel

/-!
# Cbrt model evaluator

Compiled executable for evaluating the generated EVM-faithful Cbrt model
on concrete inputs. Intended for fuzz testing via Foundry's `vm.ffi`.

Usage:
  cbrt-model <function> <hex_x>

Functions: cbrt, cbrt_floor, cbrt_up

Output: 0x-prefixed hex uint256 on stdout.
-/

open CbrtGeneratedModel in
def evalFunction (name : String) (x : Nat) : Option Nat :=
  match name with
  | "cbrt"       => some (model_cbrt_evm x)
  | "cbrt_floor" => some (model_cbrt_floor_evm x)
  | "cbrt_up"    => some (model_cbrt_up_evm x)
  | _            => none

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
    IO.eprintln "Usage: cbrt-model <cbrt|cbrt_floor|cbrt_up> <hex_x>"
    return 1
