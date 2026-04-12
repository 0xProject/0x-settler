"""
Normalized imperative IR for resolved Yul programs.

Every variable reference carries a ``SymbolId`` from the binder
resolver, and every call is pre-classified as builtin, local helper,
top-level sibling, or unresolved.

The normalized IR faithfully preserves all Yul control flow (if,
switch, for, leave, bare blocks) without flattening, constant folding,
or helper inlining.  Later passes operate on this IR to inline, fold,
and restrict.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Union

from .evm_builtins import u256
from .yul_ast import SymbolId

# ---------------------------------------------------------------------------
# Expressions
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class NConst:
    """EVM word constant, canonicalized modulo 2^256."""

    value: int

    def __post_init__(self) -> None:
        object.__setattr__(self, "value", u256(self.value))


@dataclass(frozen=True)
class NRef:
    """Variable reference, resolved to its declaring SymbolId."""

    symbol_id: SymbolId
    name: str


@dataclass(frozen=True)
class NBuiltinCall:
    """Call to a known EVM opcode (e.g. ``add``, ``shr``)."""

    op: str
    args: tuple[NExpr, ...]


@dataclass(frozen=True)
class NLocalCall:
    """Call to a nested helper function visible in the current scope."""

    symbol_id: SymbolId
    name: str
    args: tuple[NExpr, ...]


@dataclass(frozen=True)
class NTopLevelCall:
    """Call to a sibling top-level function."""

    name: str
    args: tuple[NExpr, ...]


@dataclass(frozen=True)
class NUnresolvedCall:
    """Call to an unresolved target (not builtin, not in scope)."""

    name: str
    args: tuple[NExpr, ...]


@dataclass(frozen=True)
class NIte:
    """Conditional expression: if cond != 0 then if_true else if_false.

    Not present in the syntax AST (Yul has no ternary).  Produced by
    the inliner when merging branch-local values.
    """

    cond: NExpr
    if_true: NExpr
    if_false: NExpr


NExpr = Union[
    NConst, NRef, NBuiltinCall, NLocalCall, NTopLevelCall, NUnresolvedCall, NIte
]


# ---------------------------------------------------------------------------
# Statements
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class NBind:
    """``let x, y := expr`` or bare ``let x`` (expr is None)."""

    targets: tuple[SymbolId, ...]
    target_names: tuple[str, ...]
    expr: NExpr | None


@dataclass(frozen=True)
class NAssign:
    """``x, y := expr``."""

    targets: tuple[SymbolId, ...]
    target_names: tuple[str, ...]
    expr: NExpr


@dataclass(frozen=True)
class NExprEffect:
    """Bare expression-statement (may have side effects)."""

    expr: NExpr


@dataclass(frozen=True)
class NStore:
    """``mstore(addr, value)`` — first-class memory write statement."""

    addr: NExpr
    value: NExpr


@dataclass(frozen=True)
class NIf:
    """``if condition { then_body }``."""

    condition: NExpr
    then_body: NBlock


@dataclass(frozen=True)
class NSwitchCase:
    """``case value { body }``."""

    value: NConst
    body: NBlock


@dataclass(frozen=True)
class NSwitch:
    """``switch discriminant case ... default ...``."""

    discriminant: NExpr
    cases: tuple[NSwitchCase, ...]
    default: NBlock | None


@dataclass(frozen=True)
class NFor:
    """``for init condition post { body }``.

    ``condition_setup`` holds statements that must run before every
    condition evaluation (e.g. prelude from inlining a helper call
    in the condition position).  ``None`` when the condition is a
    plain expression with no setup needed.
    """

    init: NBlock
    condition: NExpr
    condition_setup: NBlock | None
    post: NBlock
    body: NBlock


@dataclass(frozen=True)
class NLeave:
    """``leave`` — early return from the enclosing function."""

    pass


@dataclass(frozen=True)
class NBlock:
    """Brace-delimited scope with hoisted local defs and runtime statements."""

    defs: tuple[NFunctionDef, ...] = ()
    stmts: tuple[NStmt, ...] = ()


@dataclass(frozen=True)
class NFunctionDef:
    """Nested function definition, hoisted within its enclosing block."""

    name: str
    symbol_id: SymbolId
    params: tuple[SymbolId, ...]
    param_names: tuple[str, ...]
    returns: tuple[SymbolId, ...]
    return_names: tuple[str, ...]
    body: NBlock


NStmt = Union[
    NBind,
    NAssign,
    NExprEffect,
    NStore,
    NIf,
    NSwitch,
    NFor,
    NLeave,
    NBlock,
]


# ---------------------------------------------------------------------------
# Top-level
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class NormalizedFunction:
    """A single function lowered to normalized IR."""

    name: str
    params: tuple[SymbolId, ...]
    param_names: tuple[str, ...]
    returns: tuple[SymbolId, ...]
    return_names: tuple[str, ...]
    body: NBlock
