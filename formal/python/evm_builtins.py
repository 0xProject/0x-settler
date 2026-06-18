from __future__ import annotations

from collections.abc import Callable

WORD_BITS: int = 256
WORD_MOD: int = 2**WORD_BITS
_WORD_SIGN_BIT: int = 1 << (WORD_BITS - 1)


class EvaluationError(ValueError):
    pass


def u256(value: int) -> int:
    return value % WORD_MOD


def _signed(value: int) -> int:
    value = u256(value)
    return value - WORD_MOD if value & _WORD_SIGN_BIT else value


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
    return WORD_BITS if value == 0 else WORD_BITS - value.bit_length()


def _mulmod(args: tuple[int, ...]) -> int:
    aa, bb, nn = u256(args[0]), u256(args[1]), u256(args[2])
    return 0 if nn == 0 else (aa * bb) % nn


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
        raise EvaluationError(f"unsupported builtin call {name!r} with {len(args)} arg(s)")
    return u256(fn(args))


def is_pure_builtin(name: str, arity: int) -> bool:
    return (name, arity) in _PURE_BUILTIN_DISPATCH
