"""
Pure syntax AST for Yul IR.

These types represent a faithful parse tree with no semantic lowering,
constant folding, block flattening, or alpha-renaming.  Every node
carries a ``Span`` for source-location error reporting.

This module is the first layer of the staged pipeline described in
``yul_to_lean_refactor_handoff.md``.
"""

from __future__ import annotations

import enum
from dataclasses import dataclass
from typing import Union

# ---------------------------------------------------------------------------
# Shared exceptions
# ---------------------------------------------------------------------------


class ParseError(RuntimeError):
    pass


class EvaluationError(RuntimeError):
    pass


# ---------------------------------------------------------------------------
# Source spans
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Span:
    """Token-index range [start, end) in the flat token list."""

    start: int
    end: int


# ---------------------------------------------------------------------------
# Expressions
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class IntExpr:
    value: int
    span: Span


@dataclass(frozen=True)
class NameExpr:
    """Variable reference or bare identifier."""

    name: str
    span: Span


@dataclass(frozen=True)
class StringExpr:
    """String literal — preserved so the resolver can reject it."""

    text: str
    span: Span


@dataclass(frozen=True)
class CallExpr:
    name: str
    name_span: Span
    args: tuple[SynExpr, ...]
    span: Span


SynExpr = Union[IntExpr, NameExpr, StringExpr, CallExpr]


# ---------------------------------------------------------------------------
# Statements
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class LetStmt:
    """``let x, y := expr`` or ``let x`` (bare declaration, init=None)."""

    targets: tuple[str, ...]
    target_spans: tuple[Span, ...]
    init: SynExpr | None
    span: Span


@dataclass(frozen=True)
class AssignStmt:
    """``x, y := expr``."""

    targets: tuple[str, ...]
    target_spans: tuple[Span, ...]
    expr: SynExpr
    span: Span


@dataclass(frozen=True)
class ExprStmt:
    """Bare expression-statement (including ``mstore`` calls)."""

    expr: SynExpr
    span: Span


@dataclass(frozen=True)
class Block:
    """Brace-delimited ``{ ... }`` sequence of statements."""

    stmts: tuple[SynStmt, ...]
    span: Span


@dataclass(frozen=True)
class BlockStmt:
    """Bare block used as a statement (introduces a lexical scope)."""

    block: Block
    span: Span


@dataclass(frozen=True)
class IfStmt:
    condition: SynExpr
    body: Block
    span: Span


@dataclass(frozen=True)
class SwitchCase:
    value: SynExpr
    body: Block
    span: Span


@dataclass(frozen=True)
class SwitchDefault:
    body: Block
    span: Span


@dataclass(frozen=True)
class SwitchStmt:
    discriminant: SynExpr
    cases: tuple[SwitchCase, ...]
    default: SwitchDefault | None
    span: Span


@dataclass(frozen=True)
class ForStmt:
    init: Block
    condition: SynExpr
    post: Block
    body: Block
    span: Span


@dataclass(frozen=True)
class LeaveStmt:
    span: Span


@dataclass(frozen=True)
class FunctionDef:
    """Top-level or nested function definition."""

    name: str
    name_span: Span
    params: tuple[str, ...]
    param_spans: tuple[Span, ...]
    returns: tuple[str, ...]
    return_spans: tuple[Span, ...]
    body: Block
    span: Span


@dataclass(frozen=True)
class FunctionDefStmt:
    """Function definition appearing as a statement inside a block."""

    func: FunctionDef
    span: Span


SynStmt = Union[
    LetStmt,
    AssignStmt,
    ExprStmt,
    IfStmt,
    SwitchStmt,
    ForStmt,
    LeaveStmt,
    BlockStmt,
    FunctionDefStmt,
]


# ---------------------------------------------------------------------------
# Symbol kinds (used by the resolver)
# ---------------------------------------------------------------------------


class SymbolKind(enum.Enum):
    PARAM = "param"
    RETURN = "return"
    LOCAL = "local"
    FUNCTION = "function"


# ---------------------------------------------------------------------------
# Symbol resolution types (populated by yul_resolve)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SymbolId:
    """Unique identifier for a declaration site."""

    _id: int


@dataclass(frozen=True)
class SymbolInfo:
    """Metadata for a single declaration."""

    id: SymbolId
    name: str
    kind: SymbolKind
    span: Span


@dataclass(frozen=True)
class BuiltinTarget:
    """Call target: a known EVM opcode (e.g. ``add``, ``shr``)."""

    name: str


@dataclass(frozen=True)
class LocalFunctionTarget:
    """Call target: a locally-declared function visible in scope."""

    id: SymbolId
    name: str


@dataclass(frozen=True)
class TopLevelFunctionTarget:
    """Call target: a sibling function in the enclosing module scope."""

    name: str


@dataclass(frozen=True)
class UnresolvedTarget:
    """Call target: callee not found in scope or builtins."""

    name: str


CallTarget = Union[
    BuiltinTarget, LocalFunctionTarget, TopLevelFunctionTarget, UnresolvedTarget
]
