"""
Shared walker utilities for the normalized imperative IR.

Provides generic expression and statement traversals so that
consumer passes (eval, classify, constprop, inline) don't each
duplicate the full isinstance dispatch over NExpr/NStmt variants.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import Protocol, assert_never

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


def max_symbol_id(func: NormalizedFunction | NFunctionDef) -> int:
    """Find the maximum ``SymbolId._id`` in *func*."""
    result: list[int] = [0]

    def _check(sid: SymbolId) -> None:
        if sid._id > result[0]:
            result[0] = sid._id

    if isinstance(func, NFunctionDef):
        _check(func.symbol_id)
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


# ---------------------------------------------------------------------------
# Subtree freshening (binder hygiene)
# ---------------------------------------------------------------------------


class SymbolIdAllocator(Protocol):
    """Protocol for SymbolId allocation."""

    def alloc(self) -> SymbolId: ...


def freshen_function_subtree(
    fdef: NFunctionDef,
    alloc: SymbolIdAllocator,
) -> NFunctionDef:
    """Return a copy of *fdef* with ALL internal SymbolIds freshened.

    Freshens params, returns, all NBind targets, all NFunctionDef
    symbol_ids/params/returns (recursively), and rewrites all NRef/
    NLocalCall references to use the new IDs.
    """
    # Phase 1: collect every SymbolId declared in the subtree.
    old_ids: set[SymbolId] = set()
    old_ids.update(fdef.params)
    old_ids.update(fdef.returns)
    _collect_declared_ids(fdef.body, old_ids)

    # Phase 2: allocate fresh ID for each.
    id_map: dict[SymbolId, SymbolId] = {}
    for old in old_ids:
        id_map[old] = alloc.alloc()

    # Phase 3: rewrite the subtree.
    new_params = tuple(id_map.get(s, s) for s in fdef.params)
    new_returns = tuple(id_map.get(s, s) for s in fdef.returns)
    new_body = _freshen_block(fdef.body, id_map)
    return NFunctionDef(
        name=fdef.name,
        symbol_id=id_map.get(fdef.symbol_id, fdef.symbol_id),
        params=new_params,
        param_names=fdef.param_names,
        returns=new_returns,
        return_names=fdef.return_names,
        body=new_body,
    )


def _collect_declared_ids(block: NBlock, out: set[SymbolId]) -> None:
    """Collect all SymbolIds declared in a block (recursive)."""
    for stmt in block.stmts:
        if isinstance(stmt, NBind):
            out.update(stmt.targets)
        elif isinstance(stmt, NFunctionDef):
            out.add(stmt.symbol_id)
            out.update(stmt.params)
            out.update(stmt.returns)
            _collect_declared_ids(stmt.body, out)
        elif isinstance(stmt, NIf):
            _collect_declared_ids(stmt.then_body, out)
        elif isinstance(stmt, NSwitch):
            for case in stmt.cases:
                _collect_declared_ids(case.body, out)
            if stmt.default is not None:
                _collect_declared_ids(stmt.default, out)
        elif isinstance(stmt, NFor):
            _collect_declared_ids(stmt.init, out)
            if stmt.condition_setup is not None:
                _collect_declared_ids(stmt.condition_setup, out)
            _collect_declared_ids(stmt.post, out)
            _collect_declared_ids(stmt.body, out)
        elif isinstance(stmt, NBlock):
            _collect_declared_ids(stmt, out)


def _freshen_block(block: NBlock, id_map: dict[SymbolId, SymbolId]) -> NBlock:
    return NBlock(tuple(_freshen_stmt(s, id_map) for s in block.stmts))


def _freshen_stmt(stmt: NStmt, m: dict[SymbolId, SymbolId]) -> NStmt:
    if isinstance(stmt, NBind):
        return NBind(
            targets=tuple(m.get(s, s) for s in stmt.targets),
            target_names=stmt.target_names,
            expr=_freshen_expr(stmt.expr, m) if stmt.expr is not None else None,
        )
    if isinstance(stmt, NAssign):
        return NAssign(
            targets=tuple(m.get(s, s) for s in stmt.targets),
            target_names=stmt.target_names,
            expr=_freshen_expr(stmt.expr, m),
        )
    if isinstance(stmt, NExprEffect):
        return NExprEffect(expr=_freshen_expr(stmt.expr, m))
    if isinstance(stmt, NStore):
        return NStore(
            addr=_freshen_expr(stmt.addr, m), value=_freshen_expr(stmt.value, m)
        )
    if isinstance(stmt, NIf):
        return NIf(
            condition=_freshen_expr(stmt.condition, m),
            then_body=_freshen_block(stmt.then_body, m),
        )
    if isinstance(stmt, NSwitch):
        return NSwitch(
            discriminant=_freshen_expr(stmt.discriminant, m),
            cases=tuple(
                NSwitchCase(value=c.value, body=_freshen_block(c.body, m))
                for c in stmt.cases
            ),
            default=(
                _freshen_block(stmt.default, m) if stmt.default is not None else None
            ),
        )
    if isinstance(stmt, NFor):
        return NFor(
            init=_freshen_block(stmt.init, m),
            condition=_freshen_expr(stmt.condition, m),
            condition_setup=(
                _freshen_block(stmt.condition_setup, m)
                if stmt.condition_setup is not None
                else None
            ),
            post=_freshen_block(stmt.post, m),
            body=_freshen_block(stmt.body, m),
        )
    if isinstance(stmt, NLeave):
        return stmt
    if isinstance(stmt, NBlock):
        return _freshen_block(stmt, m)
    if isinstance(stmt, NFunctionDef):
        return NFunctionDef(
            name=stmt.name,
            symbol_id=m.get(stmt.symbol_id, stmt.symbol_id),
            params=tuple(m.get(s, s) for s in stmt.params),
            param_names=stmt.param_names,
            returns=tuple(m.get(s, s) for s in stmt.returns),
            return_names=stmt.return_names,
            body=_freshen_block(stmt.body, m),
        )
    assert_never(stmt)


def _freshen_expr(expr: NExpr, m: dict[SymbolId, SymbolId]) -> NExpr:
    def rewrite(e: NExpr) -> NExpr:
        if isinstance(e, NRef) and e.symbol_id in m:
            return NRef(symbol_id=m[e.symbol_id], name=e.name)
        if isinstance(e, NLocalCall) and e.symbol_id in m:
            return NLocalCall(symbol_id=m[e.symbol_id], name=e.name, args=e.args)
        return e

    return map_expr(expr, rewrite)
