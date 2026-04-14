"""
Generic expression walkers for frozen-dataclass Union-typed IRs.

Works with any expression type whose variants are frozen dataclasses
where child expressions live in one of these field patterns:

- leaf:    no child-expression fields (e.g. NConst, RConst, IntLit)
- args:    an ``args`` field of type tuple[E, ...] (e.g. NBuiltinCall, Call)
- ite:     ``cond``, ``if_true``, ``if_false`` fields (e.g. NIte, Ite)
- project: an ``inner`` field (e.g. Project)

All four expression layers (Yul, norm, restricted, model) conform to this.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import replace
from typing import TypeVar

E = TypeVar("E")


def _child_exprs(expr: E) -> tuple[E, ...]:
    """Extract child expressions from a dataclass expression node."""
    if hasattr(expr, "args"):
        return expr.args  # type: ignore[misc,no-any-return]
    if hasattr(expr, "cond"):
        return (expr.cond, expr.if_true, expr.if_false)  # type: ignore[misc,attr-defined]
    if hasattr(expr, "inner"):
        return (expr.inner,)  # type: ignore[misc]
    return ()


def _with_children(expr: E, children: tuple[E, ...]) -> E:
    """Rebuild a dataclass expression node with new child expressions."""
    if hasattr(expr, "args"):
        return replace(expr, args=children)  # type: ignore[type-var]
    if hasattr(expr, "cond"):
        c, t, f = children
        return replace(expr, cond=c, if_true=t, if_false=f)  # type: ignore[type-var]
    if hasattr(expr, "inner"):
        (inner,) = children
        return replace(expr, inner=inner)  # type: ignore[type-var]
    return expr


def map_expr(expr: E, f: Callable[[E], E]) -> E:
    """Apply *f* bottom-up to every node in the expression tree.

    Children are mapped first, then *f* is called on the
    reconstructed parent.  Callers provide a rewrite function
    that handles the node types they care about and returns the
    node unchanged otherwise.
    """
    children = _child_exprs(expr)
    if not children:
        return f(expr)
    mapped = tuple(map_expr(child, f) for child in children)
    return f(_with_children(expr, mapped))


def for_each_expr(expr: E, f: Callable[[E], None]) -> None:
    """Call *f* on every sub-expression in pre-order."""
    f(expr)
    for child in _child_exprs(expr):
        for_each_expr(child, f)


def expr_contains(expr: E, predicate: Callable[[E], bool]) -> bool:
    """Return whether any sub-expression satisfies *predicate*."""
    if predicate(expr):
        return True
    return any(expr_contains(child, predicate) for child in _child_exprs(expr))
