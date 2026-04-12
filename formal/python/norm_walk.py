"""
Shared walker utilities for the normalized imperative IR.

Provides generic expression and statement traversals so that
consumer passes (eval, classify, constprop, inline) don't each
duplicate the full isinstance dispatch over NExpr/NStmt variants.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import assert_never

from .norm_ir import (
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
    NSwitch,
    NSwitchCase,
    NTopLevelCall,
    NUnresolvedCall,
)
from .yul_ast import SymbolId

NBlockItem = NStmt | NFunctionDef

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


def expr_contains(expr: NExpr, predicate: Callable[[NExpr], bool]) -> bool:
    """Return whether any sub-expression satisfies *predicate*."""
    found = False

    def visit(node: NExpr) -> None:
        nonlocal found
        if predicate(node):
            found = True

    for_each_expr(expr, visit)
    return found


# ---------------------------------------------------------------------------
# Statement visitor (pre-order)
# ---------------------------------------------------------------------------


def for_each_stmt(
    block: NBlock,
    f: Callable[[NBlockItem], None],
    *,
    include_function_bodies: bool = False,
) -> None:
    """Call *f* on every statement in pre-order."""

    def walk(current: NBlock) -> None:
        for fdef in current.defs:
            f(fdef)
            if include_function_bodies:
                walk(fdef.body)
        for stmt in current.stmts:
            f(stmt)
            if isinstance(stmt, NIf):
                walk(stmt.then_body)
            elif isinstance(stmt, NSwitch):
                for case in stmt.cases:
                    walk(case.body)
                if stmt.default is not None:
                    walk(stmt.default)
            elif isinstance(stmt, NFor):
                walk(stmt.init)
                if stmt.condition_setup is not None:
                    walk(stmt.condition_setup)
                walk(stmt.post)
                walk(stmt.body)
            elif isinstance(stmt, NBlock):
                walk(stmt)
            elif isinstance(stmt, (NBind, NAssign, NExprEffect, NLeave)):
                pass
            else:
                assert_never(stmt)

    walk(block)


# ---------------------------------------------------------------------------
# Shared collectors
# ---------------------------------------------------------------------------


def collect_modified_in_block(block: NBlock) -> set[SymbolId]:
    """Collect all SymbolIds assigned (NBind/NAssign targets) in *block*."""
    out: set[SymbolId] = set()

    def collect_stmt(stmt: NBlockItem) -> None:
        _collect_modified_stmt(stmt, out)

    for_each_stmt(block, collect_stmt)
    return out


def _collect_modified_stmt(stmt: NBlockItem, out: set[SymbolId]) -> None:
    if isinstance(stmt, (NBind, NAssign)):
        out.update(stmt.targets)


def collect_reassigned_in_block(block: NBlock) -> set[SymbolId]:
    """Collect SymbolIds that appear as ``NAssign`` targets (mutable vars).

    Unlike ``collect_modified_in_block`` which includes ``NBind`` targets,
    this only finds variables that are re-assigned after initial binding.
    """
    out: set[SymbolId] = set()

    def collect_stmt(stmt: NBlockItem) -> None:
        _collect_reassigned_stmt(stmt, out)

    for_each_stmt(block, collect_stmt)
    return out


def _collect_reassigned_stmt(stmt: NBlockItem, out: set[SymbolId]) -> None:
    if isinstance(stmt, NAssign):
        out.update(stmt.targets)


def collect_function_defs(block: NBlock) -> list[NFunctionDef]:
    """Recursively collect all ``NFunctionDef`` nodes from *block*.

    Descends into control-flow sub-blocks AND into NFunctionDef bodies.
    """
    out: list[NFunctionDef] = []

    def collect_stmt(stmt: NBlockItem) -> None:
        if isinstance(stmt, NFunctionDef):
            out.append(stmt)

    for_each_stmt(block, collect_stmt, include_function_bodies=True)
    return out


def max_symbol_id(func: NormalizedFunction | NFunctionDef) -> int:
    """Find the maximum ``SymbolId._id`` in *func*."""
    result = 0

    def _check(sid: SymbolId) -> None:
        nonlocal result
        if sid._id > result:
            result = sid._id

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

    def visit_stmt(stmt: NBlockItem) -> None:
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
        elif isinstance(stmt, NIf):
            for_each_expr(stmt.condition, visit_expr)
        elif isinstance(stmt, NSwitch):
            for_each_expr(stmt.discriminant, visit_expr)
        elif isinstance(stmt, NFor):
            for_each_expr(stmt.condition, visit_expr)
        elif isinstance(stmt, NLeave):
            pass
        elif isinstance(stmt, NFunctionDef):
            _check(stmt.symbol_id)
            for sid in stmt.params:
                _check(sid)
            for sid in stmt.returns:
                _check(sid)
        elif isinstance(stmt, NBlock):
            pass
        else:
            assert_never(stmt)

    for_each_stmt(func.body, visit_stmt, include_function_bodies=True)
    return result


# ---------------------------------------------------------------------------
# Generic structural statement mapper
# ---------------------------------------------------------------------------


def map_stmt(
    stmt: NStmt,
    *,
    map_expr_fn: Callable[[NExpr], NExpr],
    map_block_fn: Callable[[NBlock], NBlock],
    map_bind_targets: Callable[[tuple[SymbolId, ...]], tuple[SymbolId, ...]] | None = (
        None
    ),
) -> NStmt:
    """Map expressions and recurse into sub-blocks structurally.

    This is the canonical "structural map over NStmt."  Each consumer
    pass supplies its own expression rewriter and block recursion
    callback; ``map_stmt`` handles the per-variant dispatch once.

    *map_bind_targets* (optional) remaps the ``targets`` tuple on
    ``NBind``/``NAssign``.  When *None*, targets pass through
    unchanged.

    """

    def _map_block_or_none(block: NBlock | None) -> NBlock | None:
        return map_block_fn(block) if block is not None else None

    if isinstance(stmt, NBind):
        targets = map_bind_targets(stmt.targets) if map_bind_targets else stmt.targets
        return NBind(
            targets=targets,
            target_names=stmt.target_names,
            expr=map_expr_fn(stmt.expr) if stmt.expr is not None else None,
        )
    if isinstance(stmt, NAssign):
        targets = map_bind_targets(stmt.targets) if map_bind_targets else stmt.targets
        return NAssign(
            targets=targets,
            target_names=stmt.target_names,
            expr=map_expr_fn(stmt.expr),
        )
    if isinstance(stmt, NExprEffect):
        return NExprEffect(expr=map_expr_fn(stmt.expr))
    if isinstance(stmt, NIf):
        return NIf(
            condition=map_expr_fn(stmt.condition),
            then_body=map_block_fn(stmt.then_body),
        )
    if isinstance(stmt, NSwitch):
        return NSwitch(
            discriminant=map_expr_fn(stmt.discriminant),
            cases=tuple(
                NSwitchCase(value=c.value, body=map_block_fn(c.body))
                for c in stmt.cases
            ),
            default=_map_block_or_none(stmt.default),
        )
    if isinstance(stmt, NFor):
        return NFor(
            init=map_block_fn(stmt.init),
            condition=map_expr_fn(stmt.condition),
            condition_setup=_map_block_or_none(stmt.condition_setup),
            post=map_block_fn(stmt.post),
            body=map_block_fn(stmt.body),
        )
    if isinstance(stmt, NLeave):
        return stmt
    if isinstance(stmt, NBlock):
        return map_block_fn(stmt)
    assert_never(stmt)


def map_function_def(
    fdef: NFunctionDef,
    *,
    map_block_fn: Callable[[NBlock], NBlock],
) -> NFunctionDef:
    """Map the body of a nested function definition structurally."""

    return NFunctionDef(
        name=fdef.name,
        symbol_id=fdef.symbol_id,
        params=fdef.params,
        param_names=fdef.param_names,
        returns=fdef.returns,
        return_names=fdef.return_names,
        body=map_block_fn(fdef.body),
    )


# ---------------------------------------------------------------------------
# Subtree freshening (binder hygiene)
# ---------------------------------------------------------------------------


class SymbolAllocator:
    """Generate fresh ``SymbolId`` values."""

    def __init__(self, start: int) -> None:
        self._next = start

    def alloc(self) -> SymbolId:
        sid = SymbolId(self._next)
        self._next += 1
        return sid


def freshen_function_subtree(
    fdef: NFunctionDef,
    alloc: SymbolAllocator,
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

    def collect_stmt(stmt: NBlockItem) -> None:
        if isinstance(stmt, NBind):
            out.update(stmt.targets)
        elif isinstance(stmt, NFunctionDef):
            out.add(stmt.symbol_id)
            out.update(stmt.params)
            out.update(stmt.returns)

    for_each_stmt(block, collect_stmt, include_function_bodies=True)


def _freshen_block(block: NBlock, id_map: dict[SymbolId, SymbolId]) -> NBlock:
    return NBlock(
        defs=tuple(_freshen_function_def(fdef, id_map) for fdef in block.defs),
        stmts=tuple(_freshen_stmt(stmt, id_map) for stmt in block.stmts),
    )


def _freshen_stmt(stmt: NStmt, m: dict[SymbolId, SymbolId]) -> NStmt:
    return map_stmt(
        stmt,
        map_expr_fn=lambda e: _freshen_expr(e, m),
        map_block_fn=lambda b: _freshen_block(b, m),
        map_bind_targets=lambda ts: tuple(m.get(s, s) for s in ts),
    )


def _freshen_function_def(
    fdef: NFunctionDef,
    m: dict[SymbolId, SymbolId],
) -> NFunctionDef:
    return NFunctionDef(
        name=fdef.name,
        symbol_id=m.get(fdef.symbol_id, fdef.symbol_id),
        params=tuple(m.get(s, s) for s in fdef.params),
        param_names=fdef.param_names,
        returns=tuple(m.get(s, s) for s in fdef.returns),
        return_names=fdef.return_names,
        body=_freshen_block(fdef.body, m),
    )


def _freshen_expr(expr: NExpr, m: dict[SymbolId, SymbolId]) -> NExpr:
    def rewrite(e: NExpr) -> NExpr:
        if isinstance(e, NRef) and e.symbol_id in m:
            return NRef(symbol_id=m[e.symbol_id], name=e.name)
        if isinstance(e, NLocalCall) and e.symbol_id in m:
            return NLocalCall(symbol_id=m[e.symbol_id], name=e.name, args=e.args)
        return e

    return map_expr(expr, rewrite)
