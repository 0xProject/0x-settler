"""
Shared walker utilities for the normalized imperative IR.

Provides generic expression and statement traversals so that
consumer passes (eval, classify, constprop, inline) don't each
duplicate the full isinstance dispatch over NExpr/NStmt variants.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import assert_never

from norm_ir import (
    NAssign,
    NBind,
    NBlock,
    NBuiltinCall,
    NConst,
    NExpr,
    NExprEffect,
    NFor,
    NFunctionDef,
    NIf,
    NIte,
    NLeave,
    NLocalCall,
    NormalizedFunction,
    NRef,
    NStmt,
    NStore,
    NSwitch,
    NSwitchCase,
    NTopLevelCall,
    NUnresolvedCall,
)
from yul_ast import SymbolId

# ---------------------------------------------------------------------------
# Expression mapper (bottom-up)
# ---------------------------------------------------------------------------


def map_expr(expr: NExpr, f: Callable[[NExpr], NExpr]) -> NExpr:
    """Apply *f* bottom-up to every node in the expression tree.

    Children are mapped first, then *f* is called on the
    reconstructed parent.  Callers provide a rewrite function
    that handles the node types they care about and returns the
    node unchanged otherwise.
    """
    if isinstance(expr, NConst):
        return f(expr)

    if isinstance(expr, NRef):
        return f(expr)

    if isinstance(expr, NBuiltinCall):
        mapped_args = tuple(map_expr(a, f) for a in expr.args)
        return f(NBuiltinCall(op=expr.op, args=mapped_args))

    if isinstance(expr, NLocalCall):
        mapped_args = tuple(map_expr(a, f) for a in expr.args)
        return f(NLocalCall(symbol_id=expr.symbol_id, name=expr.name, args=mapped_args))

    if isinstance(expr, NTopLevelCall):
        mapped_args = tuple(map_expr(a, f) for a in expr.args)
        return f(NTopLevelCall(name=expr.name, args=mapped_args))

    if isinstance(expr, NUnresolvedCall):
        mapped_args = tuple(map_expr(a, f) for a in expr.args)
        return f(NUnresolvedCall(name=expr.name, args=mapped_args))

    if isinstance(expr, NIte):
        return f(
            NIte(
                cond=map_expr(expr.cond, f),
                if_true=map_expr(expr.if_true, f),
                if_false=map_expr(expr.if_false, f),
            )
        )

    assert_never(expr)


# ---------------------------------------------------------------------------
# Expression visitor (pre-order)
# ---------------------------------------------------------------------------


def for_each_expr(expr: NExpr, f: Callable[[NExpr], None]) -> None:
    """Call *f* on every sub-expression in pre-order."""
    f(expr)
    if isinstance(expr, (NConst, NRef)):
        pass
    elif isinstance(expr, NBuiltinCall):
        for a in expr.args:
            for_each_expr(a, f)
    elif isinstance(expr, NLocalCall):
        for a in expr.args:
            for_each_expr(a, f)
    elif isinstance(expr, (NTopLevelCall, NUnresolvedCall)):
        for a in expr.args:
            for_each_expr(a, f)
    elif isinstance(expr, NIte):
        for_each_expr(expr.cond, f)
        for_each_expr(expr.if_true, f)
        for_each_expr(expr.if_false, f)
    else:
        assert_never(expr)


# ---------------------------------------------------------------------------
# Statement-level: sub-block mapper
# ---------------------------------------------------------------------------


def map_sub_blocks(stmt: NStmt, f: Callable[[NBlock], NBlock]) -> NStmt:
    """Apply *f* to every sub-block of *stmt*.

    Returns the statement with all sub-blocks replaced.  Statements
    without sub-blocks (NBind, NAssign, NExprEffect, NStore, NLeave)
    are returned unchanged.  NFunctionDef is returned unchanged
    (function bodies are separate scopes).
    """
    if isinstance(stmt, (NBind, NAssign, NExprEffect, NStore, NLeave)):
        return stmt

    if isinstance(stmt, NIf):
        return NIf(condition=stmt.condition, then_body=f(stmt.then_body))

    if isinstance(stmt, NSwitch):
        new_cases = tuple(
            NSwitchCase(value=c.value, body=f(c.body)) for c in stmt.cases
        )
        new_default = f(stmt.default) if stmt.default is not None else None
        return NSwitch(
            discriminant=stmt.discriminant, cases=new_cases, default=new_default
        )

    if isinstance(stmt, NFor):
        return NFor(
            init=f(stmt.init),
            condition=stmt.condition,
            post=f(stmt.post),
            body=f(stmt.body),
        )

    if isinstance(stmt, NBlock):
        return f(stmt)

    if isinstance(stmt, NFunctionDef):
        return stmt

    assert_never(stmt)


# ---------------------------------------------------------------------------
# Shared collectors
# ---------------------------------------------------------------------------


def collect_modified_in_block(block: NBlock) -> set[SymbolId]:
    """Collect all SymbolIds assigned (NBind/NAssign targets) in *block*."""
    out: set[SymbolId] = set()
    _collect_modified_walk(block, out)
    return out


def _collect_modified_walk(block: NBlock, out: set[SymbolId]) -> None:
    for stmt in block.stmts:
        if isinstance(stmt, (NBind, NAssign)):
            for sid in stmt.targets:
                out.add(sid)
        elif isinstance(stmt, NIf):
            _collect_modified_walk(stmt.then_body, out)
        elif isinstance(stmt, NSwitch):
            for case in stmt.cases:
                _collect_modified_walk(case.body, out)
            if stmt.default is not None:
                _collect_modified_walk(stmt.default, out)
        elif isinstance(stmt, NFor):
            _collect_modified_walk(stmt.init, out)
            _collect_modified_walk(stmt.post, out)
            _collect_modified_walk(stmt.body, out)
        elif isinstance(stmt, NBlock):
            _collect_modified_walk(stmt, out)


def collect_function_defs(block: NBlock) -> list[NFunctionDef]:
    """Recursively collect all ``NFunctionDef`` nodes from *block*.

    Descends into control-flow sub-blocks AND into NFunctionDef bodies.
    """
    out: list[NFunctionDef] = []

    def _walk(b: NBlock) -> None:
        for stmt in b.stmts:
            if isinstance(stmt, NFunctionDef):
                out.append(stmt)
                _walk(stmt.body)
            elif isinstance(stmt, NIf):
                _walk(stmt.then_body)
            elif isinstance(stmt, NSwitch):
                for case in stmt.cases:
                    _walk(case.body)
                if stmt.default is not None:
                    _walk(stmt.default)
            elif isinstance(stmt, NFor):
                _walk(stmt.init)
                _walk(stmt.post)
                _walk(stmt.body)
            elif isinstance(stmt, NBlock):
                _walk(stmt)

    _walk(block)
    return out


def max_symbol_id(func: NormalizedFunction) -> int:
    """Find the maximum ``SymbolId._id`` in *func*."""
    result: list[int] = [0]

    def _check(sid: SymbolId) -> None:
        if sid._id > result[0]:
            result[0] = sid._id

    for sid in func.params:
        _check(sid)
    for sid in func.returns:
        _check(sid)

    def visit_expr(e: NExpr) -> None:
        if isinstance(e, NRef):
            _check(e.symbol_id)
        elif isinstance(e, NLocalCall):
            _check(e.symbol_id)

    def _walk_block(b: NBlock) -> None:
        for stmt in b.stmts:
            _walk_stmt(stmt)

    def _walk_stmt(stmt: NStmt) -> None:
        if isinstance(stmt, NBind):
            for sid in stmt.targets:
                _check(sid)
            if stmt.expr is not None:
                for_each_expr(stmt.expr, visit_expr)
        elif isinstance(stmt, NAssign):
            for sid in stmt.targets:
                _check(sid)
            for_each_expr(stmt.expr, visit_expr)
        elif isinstance(stmt, NExprEffect):
            for_each_expr(stmt.expr, visit_expr)
        elif isinstance(stmt, NStore):
            for_each_expr(stmt.addr, visit_expr)
            for_each_expr(stmt.value, visit_expr)
        elif isinstance(stmt, NIf):
            for_each_expr(stmt.condition, visit_expr)
            _walk_block(stmt.then_body)
        elif isinstance(stmt, NSwitch):
            for_each_expr(stmt.discriminant, visit_expr)
            for case in stmt.cases:
                _walk_block(case.body)
            if stmt.default is not None:
                _walk_block(stmt.default)
        elif isinstance(stmt, NFor):
            _walk_block(stmt.init)
            for_each_expr(stmt.condition, visit_expr)
            _walk_block(stmt.post)
            _walk_block(stmt.body)
        elif isinstance(stmt, NLeave):
            pass
        elif isinstance(stmt, NBlock):
            _walk_block(stmt)
        elif isinstance(stmt, NFunctionDef):
            _check(stmt.symbol_id)
            for sid in stmt.params:
                _check(sid)
            for sid in stmt.returns:
                _check(sid)
            _walk_block(stmt.body)

    _walk_block(func.body)
    return result[0]
