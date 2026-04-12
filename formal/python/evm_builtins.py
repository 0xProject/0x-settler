"""
Shared EVM/Yul builtin facts and pure builtin semantics.

This module is the single source of truth for:
- the builtin names reserved by the resolver
- the modeled opcode subset emitted to Lean
- pure builtin constant evaluation used by selection and evaluators
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from .yul_ast import EvaluationError

WORD_BITS: int = 256
WORD_MOD: int = 2**WORD_BITS
_WORD_SIGN_BIT: int = 1 << (WORD_BITS - 1)


def u256(value: int) -> int:
    return value % WORD_MOD


@dataclass(frozen=True)
class ModeledBuiltin:
    name: str
    arity: int
    evm_def: str
    norm_def: str

    @property
    def opcode(self) -> str:
        return self.name.upper()

    @property
    def evm_helper(self) -> str:
        return f"evm{self.name.capitalize()}"

    @property
    def norm_helper(self) -> str:
        return f"norm{self.name.capitalize()}"


MODELED_BUILTINS: tuple[ModeledBuiltin, ...] = (
    ModeledBuiltin(
        "add",
        2,
        "def evmAdd (a b : Nat) : Nat :=\n  u256 (u256 a + u256 b)",
        "def normAdd (a b : Nat) : Nat := a + b",
    ),
    ModeledBuiltin(
        "sub",
        2,
        "def evmSub (a b : Nat) : Nat :=\n  u256 (u256 a + WORD_MOD - u256 b)",
        "def normSub (a b : Nat) : Nat := a - b",
    ),
    ModeledBuiltin(
        "mul",
        2,
        "def evmMul (a b : Nat) : Nat :=\n  u256 (u256 a * u256 b)",
        "def normMul (a b : Nat) : Nat := a * b",
    ),
    ModeledBuiltin(
        "div",
        2,
        "def evmDiv (a b : Nat) : Nat :=\n"
        "  let aa := u256 a\n"
        "  let bb := u256 b\n"
        "  if bb = 0 then 0 else aa / bb",
        "def normDiv (a b : Nat) : Nat := a / b",
    ),
    ModeledBuiltin(
        "mod",
        2,
        "def evmMod (a b : Nat) : Nat :=\n"
        "  let aa := u256 a\n"
        "  let bb := u256 b\n"
        "  if bb = 0 then 0 else aa % bb",
        "def normMod (a b : Nat) : Nat := a % b",
    ),
    ModeledBuiltin(
        "not",
        1,
        "def evmNot (a : Nat) : Nat :=\n  WORD_MOD - 1 - u256 a",
        "def normNot (a : Nat) : Nat := WORD_MOD - 1 - a",
    ),
    ModeledBuiltin(
        "or",
        2,
        "def evmOr (a b : Nat) : Nat :=\n  u256 a ||| u256 b",
        "def normOr (a b : Nat) : Nat := a ||| b",
    ),
    ModeledBuiltin(
        "and",
        2,
        "def evmAnd (a b : Nat) : Nat :=\n  u256 a &&& u256 b",
        "def normAnd (a b : Nat) : Nat := a &&& b",
    ),
    ModeledBuiltin(
        "eq",
        2,
        "def evmEq (a b : Nat) : Nat :=\n  if u256 a = u256 b then 1 else 0",
        "def normEq (a b : Nat) : Nat :=\n  if a = b then 1 else 0",
    ),
    ModeledBuiltin(
        "iszero",
        1,
        "def evmIszero (a : Nat) : Nat :=\n  if u256 a = 0 then 1 else 0",
        "def normIszero (a : Nat) : Nat :=\n  if a = 0 then 1 else 0",
    ),
    ModeledBuiltin(
        "shl",
        2,
        "def evmShl (shift value : Nat) : Nat :=\n"
        "  let s := u256 shift\n"
        "  let v := u256 value\n"
        "  if s < 256 then u256 (v * 2 ^ s) else 0",
        "def normShl (shift value : Nat) : Nat := value <<< shift",
    ),
    ModeledBuiltin(
        "shr",
        2,
        "def evmShr (shift value : Nat) : Nat :=\n"
        "  let s := u256 shift\n"
        "  let v := u256 value\n"
        "  if s < 256 then v / 2 ^ s else 0",
        "def normShr (shift value : Nat) : Nat := value / 2 ^ shift",
    ),
    ModeledBuiltin(
        "clz",
        1,
        "def evmClz (value : Nat) : Nat :=\n"
        "  let v := u256 value\n"
        "  if v = 0 then 256 else 255 - Nat.log2 v",
        "def normClz (value : Nat) : Nat :=\n"
        "  if value = 0 then 256 else 255 - Nat.log2 value",
    ),
    ModeledBuiltin(
        "lt",
        2,
        "def evmLt (a b : Nat) : Nat :=\n  if u256 a < u256 b then 1 else 0",
        "def normLt (a b : Nat) : Nat :=\n  if a < b then 1 else 0",
    ),
    ModeledBuiltin(
        "gt",
        2,
        "def evmGt (a b : Nat) : Nat :=\n  if u256 a > u256 b then 1 else 0",
        "def normGt (a b : Nat) : Nat :=\n  if a > b then 1 else 0",
    ),
    ModeledBuiltin(
        "mulmod",
        3,
        "def evmMulmod (a b n : Nat) : Nat :=\n"
        "  let aa := u256 a; let bb := u256 b; let nn := u256 n\n"
        "  if nn = 0 then 0 else (aa * bb) % nn",
        "def normMulmod (a b n : Nat) : Nat :=\n" "  if n = 0 then 0 else (a * b) % n",
    ),
)

# Complete set of Yul/EVM builtins that solc reserves (error 5568).
# The modeled builtins are the subset we model in Lean; this is the full set
# used by the resolver to reject function/variable declarations that would
# shadow a builtin name.
#
# Source: "EVM Dialect" table in the Yul section of the Solidity docs:
# https://docs.soliditylang.org/en/v0.8.34/yul.html#evm-dialect
EVM_BUILTINS: frozenset[str] = frozenset(
    spec.name for spec in MODELED_BUILTINS
) | frozenset(
    (
        "sdiv",
        "smod",
        "addmod",
        "exp",
        "signextend",
        "xor",
        "byte",
        "sar",
        "slt",
        "sgt",
        "mload",
        "mstore",
        "mstore8",
        "msize",
        "sload",
        "sstore",
        "tload",
        "tstore",
        "gas",
        "address",
        "balance",
        "selfbalance",
        "caller",
        "callvalue",
        "calldataload",
        "calldatasize",
        "calldatacopy",
        "codesize",
        "codecopy",
        "extcodesize",
        "extcodecopy",
        "returndatasize",
        "returndatacopy",
        "extcodehash",
        "blockhash",
        "coinbase",
        "timestamp",
        "number",
        "difficulty",
        "prevrandao",
        "gaslimit",
        "chainid",
        "basefee",
        "blobhash",
        "blobbasefee",
        "stop",
        "return",
        "revert",
        "invalid",
        "selfdestruct",
        "call",
        "callcode",
        "delegatecall",
        "staticcall",
        "create",
        "create2",
        "log0",
        "log1",
        "log2",
        "log3",
        "log4",
        "keccak256",
        "pop",
        "origin",
        "gasprice",
        "mcopy",
        "datasize",
        "dataoffset",
        "datacopy",
        "setimmutable",
        "loadimmutable",
        "linkersymbol",
        "memoryguard",
    )
)

MODELED_BUILTIN_ARITY: dict[str, int] = {
    spec.name: spec.arity for spec in MODELED_BUILTINS
}
OP_TO_LEAN_HELPER: dict[str, str] = {
    spec.name: spec.evm_helper for spec in MODELED_BUILTINS
}
OP_TO_OPCODE: dict[str, str] = {spec.name: spec.opcode for spec in MODELED_BUILTINS}
BASE_NORM_HELPERS: dict[str, str] = {
    spec.name: spec.norm_helper for spec in MODELED_BUILTINS
}


def _div(args: tuple[int, ...]) -> int:
    aa, bb = u256(args[0]), u256(args[1])
    return 0 if bb == 0 else aa // bb


def _mod(args: tuple[int, ...]) -> int:
    aa, bb = u256(args[0]), u256(args[1])
    return 0 if bb == 0 else aa % bb


def _shl(args: tuple[int, ...]) -> int:
    shift, value = u256(args[0]), u256(args[1])
    return u256(value << shift) if shift < WORD_BITS else 0


def _shr(args: tuple[int, ...]) -> int:
    shift, value = u256(args[0]), u256(args[1])
    return value >> shift if shift < WORD_BITS else 0


def _clz(args: tuple[int, ...]) -> int:
    value = u256(args[0])
    return WORD_BITS if value == 0 else WORD_BITS - 1 - (value.bit_length() - 1)


def _mulmod(args: tuple[int, ...]) -> int:
    aa, bb, nn = u256(args[0]), u256(args[1]), u256(args[2])
    return 0 if nn == 0 else (aa * bb) % nn


def _signed(value: int) -> int:
    value = u256(value)
    return value - WORD_MOD if value & _WORD_SIGN_BIT else value


def _sdiv(args: tuple[int, ...]) -> int:
    aa, bb = _signed(args[0]), _signed(args[1])
    if bb == 0:
        return 0
    sign = -1 if (aa < 0) ^ (bb < 0) else 1
    return u256(sign * (abs(aa) // abs(bb)))


def _smod(args: tuple[int, ...]) -> int:
    aa, bb = _signed(args[0]), _signed(args[1])
    if bb == 0:
        return 0
    sign = -1 if aa < 0 else 1
    return u256(sign * (abs(aa) % abs(bb)))


def _addmod(args: tuple[int, ...]) -> int:
    aa, bb, nn = u256(args[0]), u256(args[1]), u256(args[2])
    return 0 if nn == 0 else (aa + bb) % nn


def _exp(args: tuple[int, ...]) -> int:
    base, exponent = u256(args[0]), u256(args[1])
    return pow(base, exponent, WORD_MOD)


def _signextend(args: tuple[int, ...]) -> int:
    byte_index = u256(args[0])
    value = u256(args[1])
    if byte_index >= 32:
        return value
    width = 8 * (byte_index + 1)
    sign_bit = 1 << (width - 1)
    low_mask = (1 << width) - 1
    value &= low_mask
    if value & sign_bit:
        return u256(value | (WORD_MOD - (1 << width)))
    return value


def _byte(args: tuple[int, ...]) -> int:
    index, value = u256(args[0]), u256(args[1])
    if index >= 32:
        return 0
    shift = 8 * (31 - index)
    return (value >> shift) & 0xFF


def _sar(args: tuple[int, ...]) -> int:
    shift, value = u256(args[0]), _signed(args[1])
    if shift >= WORD_BITS:
        return WORD_MOD - 1 if value < 0 else 0
    return u256(value >> shift)


_PURE_BUILTIN_DISPATCH: dict[tuple[str, int], Callable[[tuple[int, ...]], int]] = {
    ("add", 2): lambda a: u256(u256(a[0]) + u256(a[1])),
    ("sub", 2): lambda a: u256(u256(a[0]) + WORD_MOD - u256(a[1])),
    ("mul", 2): lambda a: u256(u256(a[0]) * u256(a[1])),
    ("div", 2): _div,
    ("mod", 2): _mod,
    ("not", 1): lambda a: WORD_MOD - 1 - u256(a[0]),
    ("or", 2): lambda a: u256(a[0]) | u256(a[1]),
    ("and", 2): lambda a: u256(a[0]) & u256(a[1]),
    ("eq", 2): lambda a: 1 if u256(a[0]) == u256(a[1]) else 0,
    ("iszero", 1): lambda a: 1 if u256(a[0]) == 0 else 0,
    ("shl", 2): _shl,
    ("shr", 2): _shr,
    ("clz", 1): _clz,
    ("lt", 2): lambda a: 1 if u256(a[0]) < u256(a[1]) else 0,
    ("gt", 2): lambda a: 1 if u256(a[0]) > u256(a[1]) else 0,
    ("mulmod", 3): _mulmod,
    ("sdiv", 2): _sdiv,
    ("smod", 2): _smod,
    ("addmod", 3): _addmod,
    ("exp", 2): _exp,
    ("signextend", 2): _signextend,
    ("xor", 2): lambda a: u256(a[0]) ^ u256(a[1]),
    ("byte", 2): _byte,
    ("sar", 2): _sar,
    ("slt", 2): lambda a: 1 if _signed(a[0]) < _signed(a[1]) else 0,
    ("sgt", 2): lambda a: 1 if _signed(a[0]) > _signed(a[1]) else 0,
}


def eval_pure_builtin(name: str, args: tuple[int, ...]) -> int:
    fn = _PURE_BUILTIN_DISPATCH.get((name, len(args)))
    if fn is None:
        raise EvaluationError(
            f"Unsupported builtin call {name!r} with {len(args)} arg(s)"
        )
    return u256(fn(args))
