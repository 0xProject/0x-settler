import LnProof.LnYulProof
import FormalYul.Preservation

namespace LnYul

def WORD_MOD : Nat :=
  2 ^ 256

def u256 (x : Nat) : Nat :=
  x % WORD_MOD

def evmAdd (a b : Nat) : Nat :=
  u256 (u256 a + u256 b)

def evmSub (a b : Nat) : Nat :=
  u256 (u256 a + WORD_MOD - u256 b)

def evmMul (a b : Nat) : Nat :=
  u256 (u256 a * u256 b)

def evmDiv (a b : Nat) : Nat :=
  let aa := u256 a
  let bb := u256 b
  if bb = 0 then 0 else aa / bb

def evmMod (a b : Nat) : Nat :=
  let aa := u256 a
  let bb := u256 b
  if bb = 0 then 0 else aa % bb

def evmNot (a : Nat) : Nat :=
  WORD_MOD - 1 - u256 a

def evmOr (a b : Nat) : Nat :=
  u256 a ||| u256 b

def evmAnd (a b : Nat) : Nat :=
  u256 a &&& u256 b

def evmByte (index value : Nat) : Nat :=
  let i := u256 index
  let v := u256 value
  if i < 32 then (v / 2 ^ (8 * (31 - i))) % 256 else 0

def evmEq (a b : Nat) : Nat :=
  if u256 a = u256 b then 1 else 0

def evmIszero (a : Nat) : Nat :=
  if u256 a = 0 then 1 else 0

def evmShl (shift value : Nat) : Nat :=
  let s := u256 shift
  let v := u256 value
  if s < 256 then u256 (v * 2 ^ s) else 0

def evmShr (shift value : Nat) : Nat :=
  let s := u256 shift
  let v := u256 value
  if s < 256 then v / 2 ^ s else 0

def evmClz (value : Nat) : Nat :=
  let v := u256 value
  if v = 0 then 256 else 255 - Nat.log2 v

def evmLt (a b : Nat) : Nat :=
  if u256 a < u256 b then 1 else 0

def evmGt (a b : Nat) : Nat :=
  if u256 a > u256 b then 1 else 0

def evmMulmod (a b n : Nat) : Nat :=
  let aa := u256 a
  let bb := u256 b
  let nn := u256 n
  if nn = 0 then 0 else (aa * bb) % nn

def evmSdiv (a b : Nat) : Nat :=
  let aa := u256 a
  let bb := u256 b
  let na := decide (2 ^ 255 ≤ aa)
  let nb := decide (2 ^ 255 ≤ bb)
  let ma := if na then WORD_MOD - aa else aa
  let mb := if nb then WORD_MOD - bb else bb
  if bb = 0 then 0
  else if na = nb then u256 (ma / mb)
  else u256 (WORD_MOD - ma / mb)

def evmSar (shift value : Nat) : Nat :=
  let s := u256 shift
  let v := u256 value
  if 2 ^ 255 ≤ v then
    if 256 ≤ s then WORD_MOD - 1
    else WORD_MOD - 1 - (WORD_MOD - 1 - v) / 2 ^ s
  else if 256 ≤ s then 0
  else v / 2 ^ s

def evmSlt (a b : Nat) : Nat :=
  if (u256 a + 2 ^ 255) % WORD_MOD < (u256 b + 2 ^ 255) % WORD_MOD then 1 else 0

def evmSgt (a b : Nat) : Nat :=
  if (u256 b + 2 ^ 255) % WORD_MOD < (u256 a + 2 ^ 255) % WORD_MOD then 1 else 0

def toInt (w : Nat) : Int :=
  if w < 2 ^ 255 then (w : Int) else (w : Int) - 2 ^ 256

def ofInt (x : Int) : Nat :=
  (x % (2 ^ 256 : Int)).toNat

theorem u256_eq_formal (x : Nat) : u256 x = FormalYul.u256 x := rfl

theorem toInt_eq_int256 (w : Nat) : toInt w = FormalYul.Preservation.int256 w := rfl

end LnYul
