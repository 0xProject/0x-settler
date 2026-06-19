import Init

namespace FormalYul

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

def normAdd (a b : Nat) : Nat := a + b

def normSub (a b : Nat) : Nat := a - b

def normMul (a b : Nat) : Nat := a * b

def normDiv (a b : Nat) : Nat := a / b

def normMod (a b : Nat) : Nat := a % b

def normNot (a : Nat) : Nat := WORD_MOD - 1 - a

def normOr (a b : Nat) : Nat := a ||| b

def normAnd (a b : Nat) : Nat := a &&& b

def normByte (index value : Nat) : Nat :=
  if index < 32 then (value / 2 ^ (8 * (31 - index))) % 256 else 0

def normEq (a b : Nat) : Nat :=
  if a = b then 1 else 0

def normIszero (a : Nat) : Nat :=
  if a = 0 then 1 else 0

def normShl (shift value : Nat) : Nat := value <<< shift

def normShr (shift value : Nat) : Nat := value / 2 ^ shift

def normClz (value : Nat) : Nat :=
  if value = 0 then 256 else 255 - Nat.log2 value

def normLt (a b : Nat) : Nat :=
  if a < b then 1 else 0

def normGt (a b : Nat) : Nat :=
  if a > b then 1 else 0

def normMulmod (a b n : Nat) : Nat :=
  if n = 0 then 0 else (a * b) % n

def normSdiv (a b : Nat) : Nat :=
  let na := decide (2 ^ 255 ≤ a % WORD_MOD)
  let nb := decide (2 ^ 255 ≤ b % WORD_MOD)
  let ma := if na then WORD_MOD - a % WORD_MOD else a % WORD_MOD
  let mb := if nb then WORD_MOD - b % WORD_MOD else b % WORD_MOD
  if b % WORD_MOD = 0 then 0
  else if na = nb then ma / mb % WORD_MOD
  else (WORD_MOD - ma / mb) % WORD_MOD

def normSar (shift value : Nat) : Nat :=
  let s := shift % WORD_MOD
  let v := value % WORD_MOD
  if 2 ^ 255 ≤ v then
    if 256 ≤ s then WORD_MOD - 1
    else WORD_MOD - 1 - (WORD_MOD - 1 - v) / 2 ^ s
  else if 256 ≤ s then 0
  else v / 2 ^ s

def normSlt (a b : Nat) : Nat :=
  if (a % WORD_MOD + 2 ^ 255) % WORD_MOD < (b % WORD_MOD + 2 ^ 255) % WORD_MOD then 1
  else 0

def normSgt (a b : Nat) : Nat :=
  if (b % WORD_MOD + 2 ^ 255) % WORD_MOD < (a % WORD_MOD + 2 ^ 255) % WORD_MOD then 1
  else 0

def byteAt (x i : Nat) : UInt8 :=
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
    let bytes := data.data.toList
    let mut acc : Nat := 0
    for i in [0:32] do
      let j : Nat := offset + i
      acc := acc * 256 + (bytes.getD j 0).toNat
    acc

def decodeWords (data : ByteArray) (count : Nat) : List Nat :=
  (List.range count).map fun i => decodeWord data (32 * i)

structure CallResult where
  returndata : ByteArray
  deriving Inhabited

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

end FormalYul
