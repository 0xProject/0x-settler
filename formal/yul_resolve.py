"""
Binder resolution and scope validation for Yul syntax ASTs.

Walks a ``yul_ast.FunctionDef`` and:
- assigns unique ``SymbolId``s to every declaration
- attaches each variable reference to its declaring ``SymbolId``
- classifies each call target as builtin, local function, or unresolved
- validates lexical scopes (duplicates, shadowing, undefined vars, strings)

Returns a ``ResolutionResult`` containing all symbol and call-target
maps keyed by ``Span``.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import assert_never

from yul_ast import (
    AssignStmt,
    Block,
    BlockStmt,
    BuiltinTarget,
    CallExpr,
    CallTarget,
    ExprStmt,
    ForStmt,
    FunctionDef,
    FunctionDefStmt,
    IfStmt,
    IntExpr,
    LeaveStmt,
    LetStmt,
    LocalFunctionTarget,
    NameExpr,
    ParseError,
    Span,
    StringExpr,
    SwitchStmt,
    SymbolId,
    SymbolInfo,
    SymbolKind,
    SynExpr,
    SynStmt,
    TopLevelFunctionTarget,
    UnresolvedTarget,
)

# ---------------------------------------------------------------------------
# Symbol table
# ---------------------------------------------------------------------------


class SymbolTable:
    """Scoped symbol table with unique ``SymbolId`` allocation."""

    def __init__(self, *, builtins: frozenset[str] = frozenset()) -> None:
        self._scopes: list[dict[str, SymbolInfo]] = []
        self._next_id: int = 0
        self._builtins = builtins

    def _alloc_id(self) -> SymbolId:
        sid = SymbolId(self._next_id)
        self._next_id += 1
        return sid

    @property
    def scope_depth(self) -> int:
        """Current number of active scopes."""
        return len(self._scopes)

    def push_scope(self) -> None:
        self._scopes.append({})

    def pop_scope(self) -> None:
        self._scopes.pop()

    def declare(self, name: str, kind: SymbolKind, span: Span) -> SymbolInfo:
        """Declare *name* in the current (innermost) scope.

        Returns the new ``SymbolInfo``.  Raises ``ParseError`` if the
        name collides with a builtin (solc error 5568) or is already
        visible in ANY enclosing scope.  Yul uses a single flat
        namespace — solc rejects cross-scope shadowing (error 1395 /
        6052).
        """
        if name in self._builtins:
            raise ParseError(
                f"Cannot use builtin function name {name!r} " f"as identifier name"
            )
        for scope in self._scopes:
            if name in scope:
                raise ParseError(f"Duplicate declaration of {name!r} in the same scope")
        sid = self._alloc_id()
        info = SymbolInfo(id=sid, name=name, kind=kind, span=span)
        scope[name] = info
        return info

    def lookup(self, name: str, span: Span, *, scope_floor: int = 0) -> SymbolInfo:
        """Resolve *name* to its ``SymbolInfo``.

        Searches from innermost scope outward, stopping at
        *scope_floor*.  The default (0) searches all scopes.
        Raises ``ParseError`` if not found.
        """
        for scope in reversed(self._scopes[scope_floor:]):
            if name in scope:
                return scope[name]
        raise ParseError(f"Undefined variable {name!r}")

    def lookup_function(self, name: str) -> SymbolInfo | None:
        """Look up *name* as a FUNCTION symbol (non-raising).

        Yul uses a single namespace for functions and variables.  If
        a non-function binding shadows the name, the function is not
        reachable and this returns ``None``.
        """
        for scope in reversed(self._scopes):
            if name in scope:
                info = scope[name]
                if info.kind == SymbolKind.FUNCTION:
                    return info
                return None  # variable shadows function
        return None


# ---------------------------------------------------------------------------
# Resolution context (mutable accumulator)
# ---------------------------------------------------------------------------


@dataclass
class _ResolveCtx:
    """Mutable accumulator threaded through the resolve walk."""

    table: SymbolTable
    builtins: frozenset[str]
    module_names: frozenset[str] = field(default_factory=frozenset)
    var_scope_floor: int = 0
    symbols: dict[SymbolId, SymbolInfo] = field(default_factory=dict)
    references: dict[Span, SymbolId] = field(default_factory=dict)
    declarations: dict[Span, SymbolId] = field(default_factory=dict)
    call_targets: dict[Span, CallTarget] = field(default_factory=dict)

    def record_declaration(self, info: SymbolInfo) -> None:
        self.symbols[info.id] = info
        self.declarations[info.span] = info.id

    def record_reference(self, span: Span, sid: SymbolId) -> None:
        self.references[span] = sid

    def record_call_target(self, name_span: Span, target: CallTarget) -> None:
        self.call_targets[name_span] = target


# ---------------------------------------------------------------------------
# Resolution result
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ResolutionResult:
    """Complete resolution output for a single ``FunctionDef``."""

    func: FunctionDef
    symbols: dict[SymbolId, SymbolInfo]
    references: dict[Span, SymbolId]
    declarations: dict[Span, SymbolId]
    call_targets: dict[Span, CallTarget]


# ---------------------------------------------------------------------------
# Resolver
# ---------------------------------------------------------------------------


def resolve_function(
    func: FunctionDef,
    *,
    builtins: frozenset[str] = frozenset(),
) -> ResolutionResult:
    """Resolve symbols and validate lexical scopes for a parsed function.

    Assigns unique ``SymbolId``s to every declaration, attaches each
    variable reference to its declaring ``SymbolId``, and classifies
    each call target.

    *builtins* is the set of known EVM opcode names (e.g. ``add``,
    ``shr``).  Calls to builtins are classified as ``BuiltinTarget``;
    calls to locally-declared functions as ``LocalFunctionTarget``;
    everything else as ``UnresolvedTarget``.

    Raises ``ParseError`` on any lexical violation.
    """
    if func.name in builtins:
        raise ParseError(
            f"Cannot use builtin function name {func.name!r} " f"as identifier name"
        )
    ctx = _ResolveCtx(table=SymbolTable(builtins=builtins), builtins=builtins)
    _resolve_function_def(ctx, func)
    return ResolutionResult(
        func=func,
        symbols=ctx.symbols,
        references=ctx.references,
        declarations=ctx.declarations,
        call_targets=ctx.call_targets,
    )


def _resolve_function_def(ctx: _ResolveCtx, func: FunctionDef) -> None:
    # Function body scope contains params + returns.
    # Yul functions are NOT closures — they cannot access variables
    # from enclosing function scopes (solc error 8198).  Set the
    # variable-lookup floor to this scope so that NameExpr / AssignStmt
    # targets can only resolve within the current function.
    old_floor = ctx.var_scope_floor
    ctx.table.push_scope()
    ctx.var_scope_floor = ctx.table.scope_depth - 1

    seen_sig: set[str] = set()
    for name, span in zip(func.params, func.param_spans):
        if name in seen_sig:
            raise ParseError(
                f"Duplicate parameter name {name!r} in function {func.name!r}"
            )
        seen_sig.add(name)
        info = ctx.table.declare(name, SymbolKind.PARAM, span)
        ctx.record_declaration(info)

    for name, span in zip(func.returns, func.return_spans):
        if name in seen_sig:
            raise ParseError(
                f"Duplicate return name {name!r} in function {func.name!r}"
            )
        seen_sig.add(name)
        info = ctx.table.declare(name, SymbolKind.RETURN, span)
        ctx.record_declaration(info)

    _resolve_block_body(ctx, func.body)
    ctx.table.pop_scope()
    ctx.var_scope_floor = old_floor


def _resolve_block(ctx: _ResolveCtx, block: Block) -> None:
    """Resolve a brace-delimited block (pushes its own scope)."""
    ctx.table.push_scope()
    _resolve_block_body(ctx, block)
    ctx.table.pop_scope()


def _resolve_block_body(ctx: _ResolveCtx, block: Block) -> None:
    """Resolve block contents within the current scope.

    Yul function declarations are hoisted: they are visible
    throughout the entire enclosing block.
    """
    # Phase 1: hoist function declarations.
    for stmt in block.stmts:
        if isinstance(stmt, FunctionDefStmt):
            info = ctx.table.declare(
                stmt.func.name, SymbolKind.FUNCTION, stmt.func.name_span
            )
            ctx.record_declaration(info)

    # Phase 2: resolve all statements.
    for stmt in block.stmts:
        _resolve_stmt(ctx, stmt)


def _resolve_stmt(ctx: _ResolveCtx, stmt: SynStmt) -> None:
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
            _resolve_expr(ctx, stmt.init)

        # Declare targets in current scope.
        for name, span in zip(stmt.targets, stmt.target_spans):
            info = ctx.table.declare(name, SymbolKind.LOCAL, span)
            ctx.record_declaration(info)

    elif isinstance(stmt, AssignStmt):
        _resolve_expr(ctx, stmt.expr)
        for name, span in zip(stmt.targets, stmt.target_spans):
            info = ctx.table.lookup(name, span, scope_floor=ctx.var_scope_floor)
            ctx.record_reference(span, info.id)

    elif isinstance(stmt, ExprStmt):
        _resolve_expr(ctx, stmt.expr)

    elif isinstance(stmt, IfStmt):
        _resolve_expr(ctx, stmt.condition)
        _resolve_block(ctx, stmt.body)

    elif isinstance(stmt, SwitchStmt):
        _resolve_expr(ctx, stmt.discriminant)
        for case in stmt.cases:
            _resolve_expr(ctx, case.value)
            _resolve_block(ctx, case.body)
        if stmt.default is not None:
            _resolve_block(ctx, stmt.default.body)

    elif isinstance(stmt, ForStmt):
        # For-loop init declarations are visible in condition,
        # post, and body (shared scope encompassing the whole for).
        ctx.table.push_scope()
        _resolve_block_body(ctx, stmt.init)
        _resolve_expr(ctx, stmt.condition)
        _resolve_block(ctx, stmt.post)
        _resolve_block(ctx, stmt.body)
        ctx.table.pop_scope()

    elif isinstance(stmt, LeaveStmt):
        pass

    elif isinstance(stmt, BlockStmt):
        _resolve_block(ctx, stmt.block)

    elif isinstance(stmt, FunctionDefStmt):
        # Name was already declared in the hoisting phase.
        # Resolve the function body in its own scope.
        _resolve_function_def(ctx, stmt.func)

    else:
        assert_never(stmt)


def _resolve_expr(ctx: _ResolveCtx, expr: SynExpr) -> None:
    if isinstance(expr, IntExpr):
        pass

    elif isinstance(expr, NameExpr):
        info = ctx.table.lookup(expr.name, expr.span, scope_floor=ctx.var_scope_floor)
        ctx.record_reference(expr.span, info.id)

    elif isinstance(expr, StringExpr):
        raise ParseError(
            f"Unsupported string literal {expr.text!r} in expression position"
        )

    elif isinstance(expr, CallExpr):
        # Classify the call target.
        if expr.name in ctx.builtins:
            ctx.record_call_target(expr.name_span, BuiltinTarget(name=expr.name))
        else:
            func_info = ctx.table.lookup_function(expr.name)
            if func_info is not None:
                if func_info.name in ctx.module_names:
                    ctx.record_call_target(
                        expr.name_span,
                        TopLevelFunctionTarget(name=func_info.name),
                    )
                else:
                    ctx.record_call_target(
                        expr.name_span,
                        LocalFunctionTarget(id=func_info.id, name=func_info.name),
                    )
            else:
                ctx.record_call_target(expr.name_span, UnresolvedTarget(name=expr.name))
        # Resolve arguments.
        for arg in expr.args:
            _resolve_expr(ctx, arg)

    else:
        assert_never(expr)


# ---------------------------------------------------------------------------
# Module-level resolution
# ---------------------------------------------------------------------------


def resolve_module(
    funcs: list[FunctionDef],
    *,
    builtins: frozenset[str] = frozenset(),
) -> dict[str, ResolutionResult]:
    """Resolve sibling functions in a shared top-level scope.

    All *funcs* are hoisted into a single module scope before any
    function body is resolved.  This enables:

    - cross-function call classification (``TopLevelFunctionTarget``)
    - cross-function duplicate/shadowing detection

    Returns one ``ResolutionResult`` per function, keyed by name.

    Raises ``ParseError`` on any lexical violation (including
    cross-function conflicts such as a ``let`` shadowing a sibling
    function name).
    """
    table = SymbolTable(builtins=builtins)
    table.push_scope()

    # Phase 1: hoist all function names into the module scope.
    module_symbols: dict[SymbolId, SymbolInfo] = {}
    module_declarations: dict[Span, SymbolId] = {}
    func_names: set[str] = set()
    for func in funcs:
        if func.name in builtins:
            raise ParseError(
                f"Cannot use builtin function name {func.name!r} " f"as identifier name"
            )
        info = table.declare(func.name, SymbolKind.FUNCTION, func.name_span)
        module_symbols[info.id] = info
        module_declarations[info.span] = info.id
        func_names.add(func.name)

    module_names = frozenset(func_names)

    # Phase 2: resolve each function body.
    results: dict[str, ResolutionResult] = {}
    for func in funcs:
        ctx = _ResolveCtx(
            table=table,
            builtins=builtins,
            module_names=module_names,
            symbols=dict(module_symbols),
            declarations=dict(module_declarations),
        )
        _resolve_function_def(ctx, func)
        results[func.name] = ResolutionResult(
            func=func,
            symbols=ctx.symbols,
            references=ctx.references,
            declarations=ctx.declarations,
            call_targets=ctx.call_targets,
        )

    table.pop_scope()
    return results
