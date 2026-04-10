"""
Constant and copy propagation with dead branch elimination on normalized IR.

Folds constant expressions, propagates known constant and copy values
through variable assignments, and eliminates dead branches (``NIf`` with
constant-zero condition, ``NSwitch`` with constant discriminant).

Copy propagation is conservative: only copies whose source is an
immutable SymbolId (never appears as an ``NAssign`` target) are
propagated.  This covers compiler-generated temps and parameters that
are not reassigned.
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
    NTopLevelCall,
    NUnresolvedCall,
)
from norm_walk import collect_modified_in_block, map_expr
from yul_ast import SymbolId

# ---------------------------------------------------------------------------
# u256 arithmetic (must match norm_eval.py semantics)
# ---------------------------------------------------------------------------

WORD_MOD: int = 2**256


def _u256(value: int) -> int:
    return value % WORD_MOD


# ---------------------------------------------------------------------------
# Builtin dispatch for constant folding
# ---------------------------------------------------------------------------


def _div(a: tuple[int, ...]) -> int:
    aa, bb = _u256(a[0]), _u256(a[1])
    return 0 if bb == 0 else aa // bb


def _mod(a: tuple[int, ...]) -> int:
    aa, bb = _u256(a[0]), _u256(a[1])
    return 0 if bb == 0 else aa % bb


def _shl(a: tuple[int, ...]) -> int:
    shift, value = _u256(a[0]), _u256(a[1])
    return _u256(value << shift) if shift < 256 else 0


def _shr(a: tuple[int, ...]) -> int:
    shift, value = _u256(a[0]), _u256(a[1])
    return value >> shift if shift < 256 else 0


def _clz(a: tuple[int, ...]) -> int:
    value = _u256(a[0])
    return 256 if value == 0 else 255 - (value.bit_length() - 1)


def _mulmod(a: tuple[int, ...]) -> int:
    aa, bb, nn = _u256(a[0]), _u256(a[1]), _u256(a[2])
    return 0 if nn == 0 else (aa * bb) % nn


_BUILTIN_FOLD: dict[tuple[str, int], Callable[[tuple[int, ...]], int]] = {
    ("add", 2): lambda a: _u256(_u256(a[0]) + _u256(a[1])),
    ("sub", 2): lambda a: _u256(_u256(a[0]) + WORD_MOD - _u256(a[1])),
    ("mul", 2): lambda a: _u256(_u256(a[0]) * _u256(a[1])),
    ("div", 2): _div,
    ("mod", 2): _mod,
    ("not", 1): lambda a: WORD_MOD - 1 - _u256(a[0]),
    ("or", 2): lambda a: _u256(a[0]) | _u256(a[1]),
    ("and", 2): lambda a: _u256(a[0]) & _u256(a[1]),
    ("eq", 2): lambda a: 1 if _u256(a[0]) == _u256(a[1]) else 0,
    ("iszero", 1): lambda a: 1 if _u256(a[0]) == 0 else 0,
    ("shl", 2): _shl,
    ("shr", 2): _shr,
    ("clz", 1): _clz,
    ("lt", 2): lambda a: 1 if _u256(a[0]) < _u256(a[1]) else 0,
    ("gt", 2): lambda a: 1 if _u256(a[0]) > _u256(a[1]) else 0,
    ("mulmod", 3): _mulmod,
}


# ---------------------------------------------------------------------------
# Expression folding (via shared map_expr)
# ---------------------------------------------------------------------------


def _fold_node(expr: NExpr) -> NExpr:
    """Fold callback for map_expr: evaluate constant builtins and NIte."""
    if isinstance(expr, NConst):
        return NConst(_u256(expr.value))
    if isinstance(expr, NBuiltinCall):
        fn = _BUILTIN_FOLD.get((expr.op, len(expr.args)))
        if fn is not None and all(isinstance(a, NConst) for a in expr.args):
            vals = tuple(a.value for a in expr.args if isinstance(a, NConst))
            return NConst(_u256(fn(vals)))
    if isinstance(expr, NIte):
        if isinstance(expr.cond, NConst):
            return expr.if_true if expr.cond.value != 0 else expr.if_false
        if expr.if_true == expr.if_false:
            return expr.if_true
    return expr


def fold_expr(expr: NExpr) -> NExpr:
    """Fold constant sub-expressions bottom-up."""
    return map_expr(expr, _fold_node)


# ---------------------------------------------------------------------------
# Substitute known constants (via shared map_expr)
# ---------------------------------------------------------------------------


def _subst_and_fold(expr: NExpr, env: dict[SymbolId, NExpr]) -> NExpr:
    """Substitute known constants and copies from *env*, then fold."""

    def rewrite(e: NExpr) -> NExpr:
        if isinstance(e, NRef):
            val = env.get(e.symbol_id)
            if val is not None:
                return val
        return _fold_node(e)

    return map_expr(expr, rewrite)


def _collect_reassigned_sids(block: NBlock) -> set[SymbolId]:
    """Collect SymbolIds that appear as ``NAssign`` targets (mutable vars)."""
    out: set[SymbolId] = set()

    def walk(b: NBlock) -> None:
        for stmt in b.stmts:
            if isinstance(stmt, NAssign):
                out.update(stmt.targets)
            elif isinstance(stmt, NIf):
                walk(stmt.then_body)
            elif isinstance(stmt, NSwitch):
                for case in stmt.cases:
                    walk(case.body)
                if stmt.default is not None:
                    walk(stmt.default)
            elif isinstance(stmt, NFor):
                walk(stmt.init)
                walk(stmt.post)
                walk(stmt.body)
            elif isinstance(stmt, NBlock):
                walk(stmt)

    walk(block)
    return out


# ---------------------------------------------------------------------------
# Block-level constant propagation
# ---------------------------------------------------------------------------


def _prop_block(
    block: NBlock, env: dict[SymbolId, NExpr], mutable: set[SymbolId]
) -> NBlock:
    """Propagate constants and copies through a block."""
    stmts: list[NStmt] = []
    for stmt in block.stmts:
        _prop_stmt(stmt, env, stmts, mutable)
    return NBlock(tuple(stmts))


def _is_propagatable(folded: NExpr, mutable: set[SymbolId]) -> bool:
    """Check if *folded* is a value safe to add to the propagation env."""
    if isinstance(folded, NConst):
        return True
    if isinstance(folded, NRef) and folded.symbol_id not in mutable:
        return True
    return False


def _prop_stmt(
    stmt: NStmt,
    env: dict[SymbolId, NExpr],
    out: list[NStmt],
    mutable: set[SymbolId],
) -> None:
    """Process one statement, appending results to *out*."""
    if isinstance(stmt, NBind):
        if stmt.expr is not None:
            folded = _subst_and_fold(stmt.expr, env)
            if len(stmt.targets) == 1 and _is_propagatable(folded, mutable):
                env[stmt.targets[0]] = folded
            else:
                for sid in stmt.targets:
                    env.pop(sid, None)
            out.append(
                NBind(targets=stmt.targets, target_names=stmt.target_names, expr=folded)
            )
        else:
            for sid in stmt.targets:
                env[sid] = NConst(0)
            out.append(stmt)
        return

    if isinstance(stmt, NAssign):
        folded = _subst_and_fold(stmt.expr, env)
        if len(stmt.targets) == 1 and _is_propagatable(folded, mutable):
            env[stmt.targets[0]] = folded
        else:
            for sid in stmt.targets:
                env.pop(sid, None)
        out.append(
            NAssign(targets=stmt.targets, target_names=stmt.target_names, expr=folded)
        )
        return

    if isinstance(stmt, NExprEffect):
        folded = _subst_and_fold(stmt.expr, env)
        out.append(NExprEffect(expr=folded))
        return

    if isinstance(stmt, NStore):
        out.append(
            NStore(
                addr=_subst_and_fold(stmt.addr, env),
                value=_subst_and_fold(stmt.value, env),
            )
        )
        return

    if isinstance(stmt, NIf):
        cond = _subst_and_fold(stmt.condition, env)
        if isinstance(cond, NConst):
            if cond.value != 0:
                inner = _prop_block(stmt.then_body, env, mutable)
                out.extend(inner.stmts)
            return
        body_env = dict(env)
        new_body = _prop_block(stmt.then_body, body_env, mutable)
        for sid in collect_modified_in_block(stmt.then_body):
            env.pop(sid, None)
        out.append(NIf(condition=cond, then_body=new_body))
        return

    if isinstance(stmt, NSwitch):
        disc = _subst_and_fold(stmt.discriminant, env)
        if isinstance(disc, NConst):
            for case in stmt.cases:
                if case.value.value == disc.value:
                    inner = _prop_block(case.body, env, mutable)
                    out.extend(inner.stmts)
                    return
            if stmt.default is not None:
                inner = _prop_block(stmt.default, env, mutable)
                out.extend(inner.stmts)
            return
        new_cases = tuple(
            type(c)(value=c.value, body=_prop_block(c.body, dict(env), mutable))
            for c in stmt.cases
        )
        new_default = (
            _prop_block(stmt.default, dict(env), mutable)
            if stmt.default is not None
            else None
        )
        modified: set[SymbolId] = set()
        for c in stmt.cases:
            modified |= collect_modified_in_block(c.body)
        if stmt.default is not None:
            modified |= collect_modified_in_block(stmt.default)
        for sid in modified:
            env.pop(sid, None)
        out.append(NSwitch(discriminant=disc, cases=new_cases, default=new_default))
        return

    if isinstance(stmt, NFor):
        modified = collect_modified_in_block(stmt.init)
        modified |= collect_modified_in_block(stmt.post)
        modified |= collect_modified_in_block(stmt.body)
        for sid in modified:
            env.pop(sid, None)
        new_init = _prop_block(stmt.init, dict(env), mutable)
        new_cond_setup = (
            _prop_block(stmt.condition_setup, dict(env), mutable)
            if stmt.condition_setup is not None
            else None
        )
        new_cond = _subst_and_fold(stmt.condition, env)
        new_post = _prop_block(stmt.post, dict(env), mutable)
        new_body = _prop_block(stmt.body, dict(env), mutable)
        out.append(
            NFor(
                init=new_init,
                condition=new_cond,
                condition_setup=new_cond_setup,
                post=new_post,
                body=new_body,
            )
        )
        return

    if isinstance(stmt, NLeave):
        out.append(stmt)
        return

    if isinstance(stmt, NBlock):
        inner = _prop_block(stmt, env, mutable)
        out.append(inner)
        return

    if isinstance(stmt, NFunctionDef):
        out.append(stmt)
        return

    assert_never(stmt)


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def propagate_constants(func: NormalizedFunction) -> NormalizedFunction:
    """Fold constants, propagate copies of immutable vars, eliminate dead branches."""
    env: dict[SymbolId, NExpr] = {}
    mutable = _collect_reassigned_sids(func.body)
    new_body = _prop_block(func.body, env, mutable)
    return NormalizedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=new_body,
    )
