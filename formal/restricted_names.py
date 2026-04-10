"""
Name legalization pass for restricted IR (pre-SSA).

Converts raw Yul variable names to valid, clean base names suitable
for Lean emission:

- ``var_x_1`` → ``x``   (Solidity compiler parameter/return pattern)
- ``usr$tmp`` → ``tmp``  (Solidity compiler user-local pattern)
- Invalid identifier characters sanitized
- Reserved Lean helper names avoided
- Model-call callee names rewritten to emitted names

This pass is the single source of truth for name demangling,
sanitization, and callee-name remapping.  It operates on
``RestrictedFunction`` and produces a new ``RestrictedFunction``
with legalized names.

Variable identity (``SymbolId``) is unchanged.  SSA versioning and
base-name collision avoidance are handled by the downstream SSA pass.
"""

from __future__ import annotations

import re

from restricted_ir import (
    RAssignment,
    RBranch,
    RBuiltinCall,
    RCallAssign,
    RConditionalBlock,
    RConst,
    RestrictedFunction,
    RExpr,
    RIte,
    RModelCall,
    RRef,
    RStatement,
)
from yul_ast import SymbolId
from yul_to_lean import _RESERVED_LEAN_NAMES

# ---------------------------------------------------------------------------
# Demangling + sanitization
# ---------------------------------------------------------------------------


def _demangle(name: str) -> str:
    """Demangle a Yul variable name to its Solidity-level name.

    - ``usr$foo`` → ``foo``
    - ``var_x_1`` → ``x``
    - Everything else → unchanged
    """
    if name.startswith("usr$"):
        return name[4:]
    m = re.fullmatch(r"var_(\w+?)_\d+", name)
    if m:
        return m.group(1)
    return name


def _sanitize(name: str) -> str:
    """Ensure *name* is a valid, non-reserved identifier."""
    name = name.replace("$", "_").replace(".", "_")
    name = re.sub(r"[^A-Za-z0-9_]", "", name)
    if not name or not name[0].isalpha() and name[0] != "_":
        name = "_" + name if name else "_v"
    # Avoid reserved Lean helper names.
    while name in _RESERVED_LEAN_NAMES:
        name = name + "_"
    return name


def _legalize_one(name: str) -> str:
    return _sanitize(_demangle(name))


# ---------------------------------------------------------------------------
# IR rewriting helpers
# ---------------------------------------------------------------------------


def _rewrite_expr(
    expr: RExpr,
    name_map: dict[SymbolId, str],
    callee_map: dict[str, str] | None,
) -> RExpr:
    if isinstance(expr, RConst):
        return expr
    if isinstance(expr, RRef):
        new_name = name_map.get(expr.symbol_id, expr.name)
        if new_name == expr.name:
            return expr
        return RRef(symbol_id=expr.symbol_id, name=new_name)
    if isinstance(expr, RBuiltinCall):
        new_args = tuple(_rewrite_expr(a, name_map, callee_map) for a in expr.args)
        return RBuiltinCall(op=expr.op, args=new_args)
    if isinstance(expr, RModelCall):
        new_args = tuple(_rewrite_expr(a, name_map, callee_map) for a in expr.args)
        new_name = callee_map.get(expr.name, expr.name) if callee_map else expr.name
        return RModelCall(name=new_name, args=new_args)
    if isinstance(expr, RIte):
        return RIte(
            cond=_rewrite_expr(expr.cond, name_map, callee_map),
            if_true=_rewrite_expr(expr.if_true, name_map, callee_map),
            if_false=_rewrite_expr(expr.if_false, name_map, callee_map),
        )
    raise ValueError(f"Unexpected RExpr: {type(expr).__name__}")


def _rewrite_stmt(
    stmt: RStatement,
    name_map: dict[SymbolId, str],
    callee_map: dict[str, str] | None,
) -> RStatement:
    if isinstance(stmt, RAssignment):
        return RAssignment(
            target=stmt.target,
            target_name=name_map.get(stmt.target, stmt.target_name),
            expr=_rewrite_expr(stmt.expr, name_map, callee_map),
        )
    if isinstance(stmt, RCallAssign):
        new_callee = (
            callee_map.get(stmt.callee, stmt.callee) if callee_map else stmt.callee
        )
        return RCallAssign(
            targets=stmt.targets,
            target_names=tuple(
                name_map.get(sid, n) for sid, n in zip(stmt.targets, stmt.target_names)
            ),
            callee=new_callee,
            args=tuple(_rewrite_expr(a, name_map, callee_map) for a in stmt.args),
        )
    if isinstance(stmt, RConditionalBlock):
        return RConditionalBlock(
            condition=_rewrite_expr(stmt.condition, name_map, callee_map),
            output_targets=stmt.output_targets,
            output_names=tuple(
                name_map.get(sid, n)
                for sid, n in zip(stmt.output_targets, stmt.output_names)
            ),
            then_branch=RBranch(
                assignments=tuple(
                    _rewrite_stmt(s, name_map, callee_map)
                    for s in stmt.then_branch.assignments
                ),
                output_exprs=tuple(
                    _rewrite_expr(e, name_map, callee_map)
                    for e in stmt.then_branch.output_exprs
                ),
            ),
            else_branch=RBranch(
                assignments=tuple(
                    _rewrite_stmt(s, name_map, callee_map)
                    for s in stmt.else_branch.assignments
                ),
                output_exprs=tuple(
                    _rewrite_expr(e, name_map, callee_map)
                    for e in stmt.else_branch.output_exprs
                ),
            ),
        )
    raise ValueError(f"Unexpected RStatement: {type(stmt).__name__}")


# ---------------------------------------------------------------------------
# Name collection
# ---------------------------------------------------------------------------


def _collect_all_sids(func: RestrictedFunction) -> dict[SymbolId, str]:
    """Collect every ``SymbolId → raw_name`` pair from the function."""
    result: dict[SymbolId, str] = {}
    for sid, name in zip(func.params, func.param_names):
        result[sid] = name
    for sid, name in zip(func.returns, func.return_names):
        result[sid] = name
    for stmt in func.body:
        _collect_sids_stmt(stmt, result)
    return result


def _collect_sids_stmt(stmt: RStatement, out: dict[SymbolId, str]) -> None:
    if isinstance(stmt, RAssignment):
        out[stmt.target] = stmt.target_name
    elif isinstance(stmt, RCallAssign):
        for sid, name in zip(stmt.targets, stmt.target_names):
            out[sid] = name
    elif isinstance(stmt, RConditionalBlock):
        for sid, name in zip(stmt.output_targets, stmt.output_names):
            out[sid] = name
        for s in stmt.then_branch.assignments:
            _collect_sids_stmt(s, out)
        for s in stmt.else_branch.assignments:
            _collect_sids_stmt(s, out)


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def legalize_names(
    func: RestrictedFunction,
    *,
    callee_names: dict[str, str] | None = None,
) -> RestrictedFunction:
    """Legalize all variable names in a ``RestrictedFunction``.

    Demangles compiler-generated names, sanitizes identifiers, and
    avoids reserved Lean helper names.

    If *callee_names* is provided, also rewrites ``RModelCall.name``
    and ``RCallAssign.callee`` to their emitted model names.
    """
    sid_to_raw = _collect_all_sids(func)

    name_map: dict[SymbolId, str] = {}
    for sid, raw in sid_to_raw.items():
        name_map[sid] = _legalize_one(raw)

    new_param_names = tuple(
        name_map.get(sid, n) for sid, n in zip(func.params, func.param_names)
    )
    new_return_names = tuple(
        name_map.get(sid, n) for sid, n in zip(func.returns, func.return_names)
    )
    new_body = tuple(_rewrite_stmt(s, name_map, callee_names) for s in func.body)

    return RestrictedFunction(
        name=func.name,
        params=func.params,
        param_names=new_param_names,
        returns=func.returns,
        return_names=new_return_names,
        body=new_body,
    )
