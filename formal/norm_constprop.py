"""
Constant propagation and dead branch elimination on normalized IR.

Folds constant expressions, propagates known constant values through
variable assignments, and eliminates dead branches (``NIf`` with
constant-zero condition, ``NSwitch`` with constant discriminant).

This is a single-pass IR-to-IR transform, replacing the old pipeline's
interleaved ``_try_const_eval``, ``const_subst``, and ``const_locals``.
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
    NSwitch,
    NTopLevelCall,
    NUnresolvedCall,
)
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
# Expression folding (bottom-up)
# ---------------------------------------------------------------------------


def fold_expr(expr: NExpr) -> NExpr:
    """Fold constant sub-expressions bottom-up."""
    if isinstance(expr, NConst):
        return NConst(_u256(expr.value))

    if isinstance(expr, NRef):
        return expr

    if isinstance(expr, NBuiltinCall):
        folded_args = tuple(fold_expr(a) for a in expr.args)
        # Try to evaluate if all args are constant.
        fn = _BUILTIN_FOLD.get((expr.op, len(folded_args)))
        if fn is not None and all(isinstance(a, NConst) for a in folded_args):
            vals = tuple(a.value for a in folded_args if isinstance(a, NConst))
            return NConst(_u256(fn(vals)))
        return NBuiltinCall(op=expr.op, args=folded_args)

    if isinstance(expr, NLocalCall):
        return NLocalCall(
            symbol_id=expr.symbol_id,
            name=expr.name,
            args=tuple(fold_expr(a) for a in expr.args),
        )

    if isinstance(expr, NTopLevelCall):
        return NTopLevelCall(
            name=expr.name,
            args=tuple(fold_expr(a) for a in expr.args),
        )

    if isinstance(expr, NUnresolvedCall):
        return NUnresolvedCall(
            name=expr.name,
            args=tuple(fold_expr(a) for a in expr.args),
        )

    if isinstance(expr, NIte):
        c = fold_expr(expr.cond)
        t = fold_expr(expr.if_true)
        f = fold_expr(expr.if_false)
        # Fold constant condition.
        if isinstance(c, NConst):
            return t if c.value != 0 else f
        # Identity: both branches same.
        if t == f:
            return t
        return NIte(cond=c, if_true=t, if_false=f)

    assert_never(expr)


# ---------------------------------------------------------------------------
# Substitute known constants in an expression
# ---------------------------------------------------------------------------


def _subst_expr(expr: NExpr, env: dict[SymbolId, NConst]) -> NExpr:
    """Replace NRef nodes with known constants from *env*, then fold."""
    if isinstance(expr, NConst):
        return expr
    if isinstance(expr, NRef):
        c = env.get(expr.symbol_id)
        if c is not None:
            return c
        return expr
    if isinstance(expr, NBuiltinCall):
        return NBuiltinCall(
            op=expr.op,
            args=tuple(_subst_expr(a, env) for a in expr.args),
        )
    if isinstance(expr, NLocalCall):
        return NLocalCall(
            symbol_id=expr.symbol_id,
            name=expr.name,
            args=tuple(_subst_expr(a, env) for a in expr.args),
        )
    if isinstance(expr, NTopLevelCall):
        return NTopLevelCall(
            name=expr.name,
            args=tuple(_subst_expr(a, env) for a in expr.args),
        )
    if isinstance(expr, NUnresolvedCall):
        return NUnresolvedCall(
            name=expr.name,
            args=tuple(_subst_expr(a, env) for a in expr.args),
        )
    if isinstance(expr, NIte):
        return NIte(
            cond=_subst_expr(expr.cond, env),
            if_true=_subst_expr(expr.if_true, env),
            if_false=_subst_expr(expr.if_false, env),
        )
    assert_never(expr)


# ---------------------------------------------------------------------------
# Collect modified SymbolIds in a block
# ---------------------------------------------------------------------------


def _collect_modified(block: NBlock, out: set[SymbolId]) -> None:
    """Collect all SymbolIds assigned (NBind/NAssign targets) in a block."""
    for stmt in block.stmts:
        if isinstance(stmt, (NBind, NAssign)):
            for sid in stmt.targets:
                out.add(sid)
        elif isinstance(stmt, NIf):
            _collect_modified(stmt.then_body, out)
        elif isinstance(stmt, NSwitch):
            for case in stmt.cases:
                _collect_modified(case.body, out)
            if stmt.default is not None:
                _collect_modified(stmt.default, out)
        elif isinstance(stmt, NFor):
            _collect_modified(stmt.init, out)
            _collect_modified(stmt.post, out)
            _collect_modified(stmt.body, out)
        elif isinstance(stmt, NBlock):
            _collect_modified(stmt, out)


# ---------------------------------------------------------------------------
# Block-level constant propagation
# ---------------------------------------------------------------------------


def _prop_block(block: NBlock, env: dict[SymbolId, NConst]) -> NBlock:
    """Propagate constants through a block, returning a new folded block."""
    stmts: list[NStmt] = []
    for stmt in block.stmts:
        _prop_stmt(stmt, env, stmts)
    return NBlock(tuple(stmts))


def _prop_stmt(
    stmt: NStmt,
    env: dict[SymbolId, NConst],
    out: list[NStmt],
) -> None:
    """Process one statement, appending results to *out*."""
    if isinstance(stmt, NBind):
        if stmt.expr is not None:
            folded = fold_expr(_subst_expr(stmt.expr, env))
            if len(stmt.targets) == 1 and isinstance(folded, NConst):
                env[stmt.targets[0]] = folded
            else:
                # Not constant — invalidate targets.
                for sid in stmt.targets:
                    env.pop(sid, None)
            out.append(
                NBind(targets=stmt.targets, target_names=stmt.target_names, expr=folded)
            )
        else:
            # Bare let — zero-initialized.
            for sid in stmt.targets:
                env[sid] = NConst(0)
            out.append(stmt)
        return

    if isinstance(stmt, NAssign):
        folded = fold_expr(_subst_expr(stmt.expr, env))
        if len(stmt.targets) == 1 and isinstance(folded, NConst):
            env[stmt.targets[0]] = folded
        else:
            for sid in stmt.targets:
                env.pop(sid, None)
        out.append(
            NAssign(targets=stmt.targets, target_names=stmt.target_names, expr=folded)
        )
        return

    if isinstance(stmt, NExprEffect):
        folded = fold_expr(_subst_expr(stmt.expr, env))
        out.append(NExprEffect(expr=folded))
        return

    if isinstance(stmt, NIf):
        cond = fold_expr(_subst_expr(stmt.condition, env))

        if isinstance(cond, NConst):
            if cond.value != 0:
                # Live branch — flatten into outer block.
                inner = _prop_block(stmt.then_body, env)
                out.extend(inner.stmts)
            # else: dead branch — eliminate entirely.
            return

        # Non-constant: process body with env copy, invalidate modified vars.
        body_env = dict(env)
        new_body = _prop_block(stmt.then_body, body_env)
        # Invalidate any variable modified in the body.
        modified: set[SymbolId] = set()
        _collect_modified(stmt.then_body, modified)
        for sid in modified:
            env.pop(sid, None)
        out.append(NIf(condition=cond, then_body=new_body))
        return

    if isinstance(stmt, NSwitch):
        disc = fold_expr(_subst_expr(stmt.discriminant, env))

        if isinstance(disc, NConst):
            # Find matching case.
            for case in stmt.cases:
                if case.value.value == disc.value:
                    inner = _prop_block(case.body, env)
                    out.extend(inner.stmts)
                    return
            # No case matched — use default.
            if stmt.default is not None:
                inner = _prop_block(stmt.default, env)
                out.extend(inner.stmts)
            return

        # Non-constant: process all branches, invalidate modified vars.
        new_cases = tuple(
            type(c)(value=c.value, body=_prop_block(c.body, dict(env)))
            for c in stmt.cases
        )
        new_default = (
            _prop_block(stmt.default, dict(env)) if stmt.default is not None else None
        )
        modified = set[SymbolId]()
        for c in stmt.cases:
            _collect_modified(c.body, modified)
        if stmt.default is not None:
            _collect_modified(stmt.default, modified)
        for sid in modified:
            env.pop(sid, None)
        out.append(NSwitch(discriminant=disc, cases=new_cases, default=new_default))
        return

    if isinstance(stmt, NFor):
        # Conservative: invalidate everything the loop touches.
        modified = set[SymbolId]()
        _collect_modified(stmt.init, modified)
        _collect_modified(stmt.post, modified)
        _collect_modified(stmt.body, modified)
        for sid in modified:
            env.pop(sid, None)
        # Still fold expressions inside the loop.
        new_init = _prop_block(stmt.init, dict(env))
        new_cond = fold_expr(_subst_expr(stmt.condition, env))
        new_post = _prop_block(stmt.post, dict(env))
        new_body = _prop_block(stmt.body, dict(env))
        out.append(
            NFor(init=new_init, condition=new_cond, post=new_post, body=new_body)
        )
        return

    if isinstance(stmt, NLeave):
        out.append(stmt)
        return

    if isinstance(stmt, NBlock):
        inner = _prop_block(stmt, env)
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
    """Fold constant expressions and eliminate dead branches."""
    env: dict[SymbolId, NConst] = {}
    new_body = _prop_block(func.body, env)
    return NormalizedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=new_body,
    )
