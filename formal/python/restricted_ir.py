"""
Non-SSA restricted IR.

Uses ``SymbolId``-keyed variable references. SSA renaming happens
later.

The restricted IR is a flat sequence of ``RAssignment`` and
``RConditionalBlock`` statements with explicit branch outputs.
No nested blocks, no implicit control flow, and no memory operations.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Union

from .yul_ast import SymbolId

# ---------------------------------------------------------------------------
# Expressions
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class RConst:
    """Integer constant."""

    value: int


@dataclass(frozen=True)
class RRef:
    """Variable reference by SymbolId."""

    symbol_id: SymbolId
    name: str


@dataclass(frozen=True)
class RBuiltinCall:
    """Call to a known EVM opcode."""

    op: str
    args: tuple[RExpr, ...]


@dataclass(frozen=True)
class RModelCall:
    """Scalar call to another model-level function (top-level sibling)."""

    name: str
    args: tuple[RExpr, ...]


@dataclass(frozen=True)
class RIte:
    """Conditional expression: if cond != 0 then if_true else if_false."""

    cond: RExpr
    if_true: RExpr
    if_false: RExpr


RExpr = Union[RConst, RRef, RBuiltinCall, RModelCall, RIte]


# ---------------------------------------------------------------------------
# Statements
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class RAssignment:
    """Single variable assignment."""

    target: SymbolId
    target_name: str
    expr: RExpr


@dataclass(frozen=True)
class RCallAssign:
    """Model call assignment with explicit target arity.

    This is used for direct call sites, especially multi-return
    model calls, so the call is evaluated once and its outputs are
    assigned positionally to the targets.
    """

    targets: tuple[SymbolId, ...]
    target_names: tuple[str, ...]
    callee: str
    args: tuple[RExpr, ...]


@dataclass(frozen=True)
class RBranch:
    """One branch of a conditional with local statements and output expressions."""

    assignments: tuple[RStatement, ...]
    output_exprs: tuple[RExpr, ...]


@dataclass(frozen=True)
class RConditionalBlock:
    """Conditional with explicit outputs for both branches.

    ``output_targets`` are the outer-scope variables bound by this
    conditional. Each branch carries its local assignments plus one
    output expression per target, evaluated in the branch-local scope.
    """

    condition: RExpr
    output_targets: tuple[SymbolId, ...]
    output_names: tuple[str, ...]
    then_branch: RBranch
    else_branch: RBranch


RStatement = Union[RAssignment, RCallAssign, RConditionalBlock]


# ---------------------------------------------------------------------------
# Top-level
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class RestrictedFunction:
    """A function in the non-SSA restricted IR."""

    name: str
    params: tuple[SymbolId, ...]
    param_names: tuple[str, ...]
    returns: tuple[SymbolId, ...]
    return_names: tuple[str, ...]
    body: tuple[RStatement, ...]
