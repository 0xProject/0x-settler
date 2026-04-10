"""
SSA renaming and FunctionModel conversion (Pass 9).

Converts a ``RestrictedFunction`` (SymbolId-keyed, non-SSA) into a
``FunctionModel`` (string-named, SSA-renamed) ready for Lean emission.

SSA naming rules match the old pipeline:
- First assignment to a clean name uses the bare name (e.g. ``z``)
- Subsequent assignments suffix ``_{n-1}`` (e.g. ``z_1``, ``z_2``)
- Collisions with existing names are skipped
- Branch-local SSA uses copied counters; merge uses outer counters
"""

from __future__ import annotations

from collections import Counter
from typing import assert_never

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

# Import the old pipeline's IR types for the output.
from yul_to_lean import (
    Assignment,
    Call,
    ConditionalBlock,
    ConditionalBranch,
    Expr,
    FunctionModel,
    IntLit,
    Ite,
    ModelStatement,
    Var,
)

# ---------------------------------------------------------------------------
# SSA state
# ---------------------------------------------------------------------------


class _SSACtx:
    """Mutable SSA naming state."""

    def __init__(self, all_clean_names: set[str]) -> None:
        self.ssa_count: Counter[str] = Counter()
        self.emitted: set[str] = set()
        self.all_clean_names = all_clean_names
        # SymbolId → current SSA name
        self.sid_map: dict[SymbolId, str] = {}

    def copy(self) -> _SSACtx:
        """Create a branch-local copy."""
        c = _SSACtx(self.all_clean_names)
        c.ssa_count = Counter(self.ssa_count)
        c.emitted = set(self.emitted)
        c.sid_map = dict(self.sid_map)
        return c

    def assign(self, sid: SymbolId, clean: str) -> str:
        """Generate an SSA name for an assignment to *clean* and bind *sid*."""
        self.ssa_count[clean] += 1
        count = self.ssa_count[clean]
        if count == 1:
            ssa_name = clean
        else:
            ssa_name = f"{clean}_{count - 1}"
            while ssa_name in self.emitted:
                self.ssa_count[clean] += 1
                count = self.ssa_count[clean]
                ssa_name = f"{clean}_{count - 1}"
        self.emitted.add(ssa_name)
        self.sid_map[sid] = ssa_name
        return ssa_name

    def lookup(self, sid: SymbolId) -> str:
        """Get the current SSA name for a SymbolId."""
        name = self.sid_map.get(sid)
        if name is None:
            raise ValueError(f"SymbolId {sid!r} has no SSA name")
        return name


# ---------------------------------------------------------------------------
# Expression conversion: RExpr → Expr
# ---------------------------------------------------------------------------


def _convert_expr(expr: RExpr, ctx: _SSACtx) -> Expr:
    if isinstance(expr, RConst):
        return IntLit(expr.value)
    if isinstance(expr, RRef):
        return Var(ctx.lookup(expr.symbol_id))
    if isinstance(expr, RBuiltinCall):
        args = tuple(_convert_expr(a, ctx) for a in expr.args)
        return Call(expr.op, args)
    if isinstance(expr, RModelCall):
        args = tuple(_convert_expr(a, ctx) for a in expr.args)
        return Call(expr.name, args)
    if isinstance(expr, RIte):
        return Ite(
            _convert_expr(expr.cond, ctx),
            _convert_expr(expr.if_true, ctx),
            _convert_expr(expr.if_false, ctx),
        )
    raise ValueError(f"Unexpected RExpr: {type(expr).__name__}")


# ---------------------------------------------------------------------------
# Statement conversion: RStatement → ModelStatement
# ---------------------------------------------------------------------------


def _convert_block(
    stmts: tuple[RStatement, ...],
    ctx: _SSACtx,
) -> list[ModelStatement]:
    out: list[ModelStatement] = []
    for stmt in stmts:
        _convert_stmt(stmt, ctx, out)
    return out


def _convert_stmt(
    stmt: RStatement,
    ctx: _SSACtx,
    out: list[ModelStatement],
) -> None:
    if isinstance(stmt, RAssignment):
        expr = _convert_expr(stmt.expr, ctx)
        ssa_name = ctx.assign(stmt.target, stmt.target_name)
        out.append(Assignment(target=ssa_name, expr=expr))
        return

    if isinstance(stmt, RCallAssign):
        args = tuple(_convert_expr(a, ctx) for a in stmt.args)
        call_expr: Expr = Call(stmt.callee, args)
        if len(stmt.targets) == 1:
            ssa_name = ctx.assign(stmt.targets[0], stmt.target_names[0])
            out.append(Assignment(target=ssa_name, expr=call_expr))
        else:
            # Multi-return: use Project to extract each return value.
            from yul_to_lean import Project

            total = len(stmt.targets)
            for i, (sid, name) in enumerate(zip(stmt.targets, stmt.target_names)):
                ssa_name = ctx.assign(sid, name)
                out.append(
                    Assignment(
                        target=ssa_name,
                        expr=Project(index=i, total=total, inner=call_expr),
                    )
                )
        return

    if isinstance(stmt, RConditionalBlock):
        _convert_conditional(stmt, ctx, out)
        return

    assert_never(stmt)


def _convert_conditional(
    stmt: RConditionalBlock,
    ctx: _SSACtx,
    out: list[ModelStatement],
) -> None:
    cond = _convert_expr(stmt.condition, ctx)

    # Process then-branch with branch-local SSA state.
    then_ctx = ctx.copy()
    then_assignments = _convert_branch_block(stmt.then_branch.assignments, then_ctx)
    then_outputs: list[str] = []
    for expr in stmt.then_branch.output_exprs:
        then_outputs.append(_ssa_name_for_output_expr(expr, then_ctx))

    # Process else-branch with branch-local SSA state.
    else_ctx = ctx.copy()
    else_assignments = _convert_branch_block(stmt.else_branch.assignments, else_ctx)
    else_outputs: list[str] = []
    for expr in stmt.else_branch.output_exprs:
        else_outputs.append(_ssa_name_for_output_expr(expr, else_ctx))

    # Generate merge-point SSA names using the OUTER context.
    output_vars: list[str] = []
    for sid, name in zip(stmt.output_targets, stmt.output_names):
        ssa_name = ctx.assign(sid, name)
        output_vars.append(ssa_name)

    out.append(
        ConditionalBlock(
            condition=cond,
            output_vars=tuple(output_vars),
            then_branch=ConditionalBranch(
                assignments=tuple(then_assignments),
                outputs=tuple(then_outputs),
            ),
            else_branch=ConditionalBranch(
                assignments=tuple(else_assignments),
                outputs=tuple(else_outputs),
            ),
        )
    )


def _convert_branch_block(
    stmts: tuple[RStatement, ...],
    ctx: _SSACtx,
) -> list[Assignment]:
    """Convert branch-local statements to Assignment only.

    The old pipeline's ConditionalBranch.assignments is
    tuple[Assignment, ...] — no nested ConditionalBlocks allowed
    inside branches.
    """
    out: list[Assignment] = []
    for stmt in stmts:
        if isinstance(stmt, RAssignment):
            expr = _convert_expr(stmt.expr, ctx)
            ssa_name = ctx.assign(stmt.target, stmt.target_name)
            out.append(Assignment(target=ssa_name, expr=expr))
        elif isinstance(stmt, RCallAssign):
            args = tuple(_convert_expr(a, ctx) for a in stmt.args)
            call_expr: Expr = Call(stmt.callee, args)
            if len(stmt.targets) == 1:
                ssa_name = ctx.assign(stmt.targets[0], stmt.target_names[0])
                out.append(Assignment(target=ssa_name, expr=call_expr))
            else:
                from yul_to_lean import Project

                total = len(stmt.targets)
                for i, (sid, name) in enumerate(zip(stmt.targets, stmt.target_names)):
                    ssa_name = ctx.assign(sid, name)
                    out.append(
                        Assignment(
                            target=ssa_name,
                            expr=Project(index=i, total=total, inner=call_expr),
                        )
                    )
        elif isinstance(stmt, RConditionalBlock):
            raise ValueError(
                "Nested ConditionalBlock inside branch not supported "
                "in the old pipeline's FunctionModel format"
            )
        else:
            assert_never(stmt)
    return out


def _ssa_name_for_output_expr(expr: RExpr, ctx: _SSACtx) -> str:
    """Get the SSA name for a branch output expression.

    Output expressions are typically RRef nodes pointing to the
    variable that feeds the outer output. For constant expressions
    or complex expressions, we need to emit a temp assignment.
    """
    if isinstance(expr, RRef):
        return ctx.lookup(expr.symbol_id)
    # For non-ref outputs (e.g. RConst), we'd need to emit a temp.
    # For now, only RRef is expected in branch outputs.
    raise ValueError(f"Branch output must be RRef, got {type(expr).__name__}: {expr!r}")


# ---------------------------------------------------------------------------
# Zero-initialization for return variables
# ---------------------------------------------------------------------------


def _needs_zero_init(
    sid: SymbolId,
    body: tuple[RStatement, ...],
) -> bool:
    """Check if a return variable needs explicit zero-initialization.

    Returns True if the variable might be read before being written
    on some execution path.
    """
    # Conservative: always zero-init. The old pipeline does a more
    # nuanced analysis, but zero-init is always safe.
    return True


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def to_function_model(
    func: RestrictedFunction,
    sol_fn_name: str,
) -> FunctionModel:
    """Convert a RestrictedFunction to a FunctionModel with SSA naming.

    This is Pass 9 from the handoff doc: SSA renaming as a dedicated
    transformation on the non-SSA restricted IR.
    """
    # Collect all clean names for collision detection.
    all_clean: set[str] = set()
    all_clean.update(func.param_names)
    all_clean.update(func.return_names)
    for stmt in func.body:
        _collect_clean_names(stmt, all_clean)

    ctx = _SSACtx(all_clean)

    # Register parameters (SSA count starts at 1).
    param_ssa: list[str] = []
    for sid, name in zip(func.params, func.param_names):
        ssa = ctx.assign(sid, name)
        param_ssa.append(ssa)

    # Zero-init return variables that need it.
    assignments: list[ModelStatement] = []
    return_sids_needing_init: list[tuple[SymbolId, str]] = []
    for sid, name in zip(func.returns, func.return_names):
        if _needs_zero_init(sid, func.body):
            ssa = ctx.assign(sid, name)
            assignments.append(Assignment(target=ssa, expr=IntLit(0)))
            return_sids_needing_init.append((sid, name))

    # Convert body statements.
    body_stmts = _convert_block(func.body, ctx)
    assignments.extend(body_stmts)

    # Extract final return names.
    return_ssa: list[str] = []
    for sid in func.returns:
        return_ssa.append(ctx.lookup(sid))

    return FunctionModel(
        fn_name=sol_fn_name,
        assignments=tuple(assignments),
        param_names=tuple(param_ssa),
        return_names=tuple(return_ssa),
    )


def _collect_clean_names(stmt: RStatement, out: set[str]) -> None:
    """Collect all target_name values from a statement tree."""
    if isinstance(stmt, RAssignment):
        out.add(stmt.target_name)
    elif isinstance(stmt, RCallAssign):
        out.update(stmt.target_names)
    elif isinstance(stmt, RConditionalBlock):
        out.update(stmt.output_names)
        for s in stmt.then_branch.assignments:
            _collect_clean_names(s, out)
        for s in stmt.else_branch.assignments:
            _collect_clean_names(s, out)
