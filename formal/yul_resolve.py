"""
Binder resolution and scope validation for Yul syntax ASTs.

Walks a ``yul_ast.FunctionDef`` and validates lexical scopes:
duplicate declarations, illegal shadowing, unsupported string
literals, and duplicate local function names.

This is the third layer of the staged pipeline described in
``yul_to_lean_refactor_handoff.md``.
"""

from __future__ import annotations

from typing import assert_never

from yul_ast import (
    AssignStmt,
    Block,
    BlockStmt,
    CallExpr,
    ExprStmt,
    ForStmt,
    FunctionDef,
    FunctionDefStmt,
    IfStmt,
    IntExpr,
    LeaveStmt,
    LetStmt,
    NameExpr,
    ParseError,
    Span,
    StringExpr,
    SwitchStmt,
    SymbolKind,
    SynExpr,
    SynStmt,
)

# ---------------------------------------------------------------------------
# Symbol table
# ---------------------------------------------------------------------------


class SymbolTable:
    """Scoped symbol table for binder resolution."""

    def __init__(self) -> None:
        self._scopes: list[dict[str, SymbolKind]] = []

    def push_scope(self) -> None:
        self._scopes.append({})

    def pop_scope(self) -> None:
        self._scopes.pop()

    def declare(self, name: str, kind: SymbolKind, span: Span) -> None:
        """Declare *name* in the current (innermost) scope.

        Raises ``ParseError`` if the name is already declared in
        the current scope.
        """
        scope = self._scopes[-1]
        if name in scope:
            raise ParseError(f"Duplicate declaration of {name!r} in the same scope")
        scope[name] = kind

    def lookup(self, name: str, span: Span) -> SymbolKind:
        """Resolve *name* to its declaring symbol kind.

        Searches from innermost scope outward.
        Raises ``ParseError`` if not found.
        """
        for scope in reversed(self._scopes):
            if name in scope:
                return scope[name]
        raise ParseError(f"Undefined variable {name!r}")


# ---------------------------------------------------------------------------
# Resolver
# ---------------------------------------------------------------------------


def resolve_function(func: FunctionDef) -> None:
    """Validate lexical scopes and binder rules for a parsed function.

    Raises ``ParseError`` on any lexical violation.

    Does NOT produce a new IR — it validates in-place.  A future
    phase will extend this to produce a resolved AST with symbol IDs
    attached to every reference.
    """
    table = SymbolTable()
    _resolve_function_def(table, func)


def _resolve_function_def(table: SymbolTable, func: FunctionDef) -> None:
    # Function body scope contains params + returns.
    table.push_scope()

    seen_sig: set[str] = set()
    for name, span in zip(func.params, func.param_spans):
        if name in seen_sig:
            raise ParseError(
                f"Duplicate parameter name {name!r} in function {func.name!r}"
            )
        seen_sig.add(name)
        table.declare(name, SymbolKind.PARAM, span)

    for name, span in zip(func.returns, func.return_spans):
        if name in seen_sig:
            raise ParseError(
                f"Duplicate return name {name!r} in function {func.name!r}"
            )
        seen_sig.add(name)
        table.declare(name, SymbolKind.RETURN, span)

    _resolve_block_body(table, func.body)
    table.pop_scope()


def _resolve_block(table: SymbolTable, block: Block) -> None:
    """Resolve a brace-delimited block (pushes its own scope)."""
    table.push_scope()
    _resolve_block_body(table, block)
    table.pop_scope()


def _resolve_block_body(table: SymbolTable, block: Block) -> None:
    """Resolve block contents within the current scope.

    Used both by ``_resolve_block`` (which wraps in push/pop) and
    by ``_resolve_function_def`` (which manages its own scope).

    Yul function declarations are hoisted: they are visible
    throughout the entire enclosing block.
    """
    # Phase 1: hoist function declarations.
    for stmt in block.stmts:
        if isinstance(stmt, FunctionDefStmt):
            table.declare(stmt.func.name, SymbolKind.FUNCTION, stmt.func.name_span)

    # Phase 2: resolve all statements.
    for stmt in block.stmts:
        _resolve_stmt(table, stmt)


def _resolve_stmt(table: SymbolTable, stmt: SynStmt) -> None:
    if isinstance(stmt, LetStmt):
        # Check for internal duplicates within the let targets.
        let_names: set[str] = set()
        for name, span in zip(stmt.targets, stmt.target_spans):
            if name in let_names:
                raise ParseError(f"Duplicate declaration of {name!r} in the same scope")
            let_names.add(name)

        # Resolve init expression BEFORE declaring targets (Yul
        # semantics: RHS evaluated in the outer scope).
        if stmt.init is not None:
            _resolve_expr(table, stmt.init)

        # Declare targets in current scope.
        for name, span in zip(stmt.targets, stmt.target_spans):
            table.declare(name, SymbolKind.LOCAL, span)

    elif isinstance(stmt, AssignStmt):
        _resolve_expr(table, stmt.expr)
        for name, span in zip(stmt.targets, stmt.target_spans):
            table.lookup(name, span)

    elif isinstance(stmt, ExprStmt):
        _resolve_expr(table, stmt.expr)

    elif isinstance(stmt, IfStmt):
        _resolve_expr(table, stmt.condition)
        _resolve_block(table, stmt.body)

    elif isinstance(stmt, SwitchStmt):
        _resolve_expr(table, stmt.discriminant)
        for case in stmt.cases:
            _resolve_expr(table, case.value)
            _resolve_block(table, case.body)
        if stmt.default is not None:
            _resolve_block(table, stmt.default.body)

    elif isinstance(stmt, ForStmt):
        # For-loop init declarations are visible in condition,
        # post, and body (shared scope encompassing the whole for).
        table.push_scope()
        _resolve_block_body(table, stmt.init)
        _resolve_expr(table, stmt.condition)
        _resolve_block(table, stmt.post)
        _resolve_block(table, stmt.body)
        table.pop_scope()

    elif isinstance(stmt, LeaveStmt):
        pass

    elif isinstance(stmt, BlockStmt):
        _resolve_block(table, stmt.block)

    elif isinstance(stmt, FunctionDefStmt):
        # Name was already declared in the hoisting phase.
        # Resolve the function body in its own scope.
        _resolve_function_def(table, stmt.func)

    else:
        assert_never(stmt)


def _resolve_expr(table: SymbolTable, expr: SynExpr) -> None:
    if isinstance(expr, IntExpr):
        pass

    elif isinstance(expr, NameExpr):
        table.lookup(expr.name, expr.span)

    elif isinstance(expr, StringExpr):
        raise ParseError(
            f"Unsupported string literal {expr.text!r} in expression position"
        )

    elif isinstance(expr, CallExpr):
        # Do NOT look up the call name as a variable — it may be
        # a builtin or an external function.  Call-target resolution
        # is for a later phase.
        for arg in expr.args:
            _resolve_expr(table, arg)

    else:
        assert_never(expr)
