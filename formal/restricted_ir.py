"""
Non-SSA restricted IR for the new pipeline.

This is the output of Pass 8 (restricted IR construction) from the
handoff doc.  It uses ``SymbolId``-keyed variable references (not
string names — SSA renaming is a separate later pass).

The restricted IR is a flat sequence of ``RAssignment`` and
``RConditionalBlock`` statements with explicit branch outputs.
No nested blocks, no implicit control flow, no memory operations
(those are resolved during lowering).

Corresponds to the old pipeline's ``FunctionModel`` / ``Assignment``
/ ``ConditionalBlock`` types but with ``SymbolId`` instead of
string-based variable names.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Union

from yul_ast import SymbolId

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
    """Call to another model-level function (top-level sibling)."""

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
class RBranch:
    """One branch of a conditional with local statements and output mapping."""

    assignments: tuple[RStatement, ...]
    outputs: tuple[SymbolId, ...]


@dataclass(frozen=True)
class RConditionalBlock:
    """Conditional with explicit outputs for both branches.

    ``output_vars`` are the outer-scope variables bound by this
    conditional.  Each branch carries its local assignments and
    a mapping from local variables to the output slots.
    """

    condition: RExpr
    output_vars: tuple[SymbolId, ...]
    output_names: tuple[str, ...]
    then_branch: RBranch
    else_branch: RBranch


RStatement = Union[RAssignment, RConditionalBlock]


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
