"""
SSA renaming and FunctionModel conversion.

Converts a ``RestrictedFunction`` (SymbolId-keyed, non-SSA) into a
``FunctionModel`` (string-named, SSA-renamed) ready for validation,
evaluation, optimization, and emission.

The pipeline is:

1. **Module-wide naming** (``restricted_names.plan_module`` +
   ``restricted_names.apply_module_plan``): demangle compiler names,
   sanitize identifiers, and rewrite model-call callee names.
2. **SSA renaming** (this module): version base names and build
   ``FunctionModel`` with recursive branch support.

SSA naming rules for the emitted ``FunctionModel`` are:
- First assignment to a clean name uses the bare name (e.g. ``z``)
- Subsequent assignments suffix ``_{n-1}`` (e.g. ``z_1``, ``z_2``)
- Collisions with already-emitted names are skipped
- Branch-local SSA uses copied counters; merge uses outer counters
"""

from __future__ import annotations

from collections import Counter
from typing import assert_never

from .model_ir import (
    Assignment,
    Call,
    ConditionalBlock,
    ConditionalBranch,
    Expr,
    FunctionModel,
    IntLit,
    Ite,
    ModelStatement,
    Project,
    Var,
)
from .restricted_ir import (
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
from .restricted_names import apply_module_plan, plan_module
from .yul_ast import SymbolId

# ---------------------------------------------------------------------------
# SSA state
# ---------------------------------------------------------------------------


class _SSACtx:
    """Mutable SSA naming state."""

    def __init__(self) -> None:
        self.ssa_count: Counter[str] = Counter()
        self.emitted: set[str] = set()
        # SymbolId → current SSA name
        self.sid_map: dict[SymbolId, str] = {}

    def copy(self) -> _SSACtx:
        """Create a branch-local copy."""
        c = _SSACtx()
        c.ssa_count = Counter(self.ssa_count)
        c.emitted = set(self.emitted)
        c.sid_map = dict(self.sid_map)
        return c

    def assign(self, sid: SymbolId, clean: str) -> str:
        """Generate an SSA name for an assignment to *clean* and bind *sid*."""
        self.ssa_count[clean] += 1
        count = self.ssa_count[clean]
        ssa_name = clean if count == 1 else f"{clean}_{count - 1}"
        # Skip names already emitted (handles first-assignment collisions too).
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
    then_stmts = _convert_branch_block(stmt.then_branch.assignments, then_ctx)
    then_outputs: list[Expr] = [
        _convert_expr(e, then_ctx) for e in stmt.then_branch.output_exprs
    ]

    # Process else-branch with branch-local SSA state.
    else_ctx = ctx.copy()
    else_stmts = _convert_branch_block(stmt.else_branch.assignments, else_ctx)
    else_outputs: list[Expr] = [
        _convert_expr(e, else_ctx) for e in stmt.else_branch.output_exprs
    ]

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
                assignments=tuple(then_stmts),
                outputs=tuple(then_outputs),
            ),
            else_branch=ConditionalBranch(
                assignments=tuple(else_stmts),
                outputs=tuple(else_outputs),
            ),
        )
    )


def _convert_branch_block(
    stmts: tuple[RStatement, ...],
    ctx: _SSACtx,
) -> list[ModelStatement]:
    """Convert branch-local statements, handling nested conditionals recursively."""
    out: list[ModelStatement] = []
    for stmt in stmts:
        _convert_stmt(stmt, ctx, out)
    return out


# ---------------------------------------------------------------------------
# Zero-initialization for return variables
# ---------------------------------------------------------------------------


def _expr_uses_sid(expr: RExpr, sid: SymbolId) -> bool:
    if isinstance(expr, RConst):
        return False
    if isinstance(expr, RRef):
        return expr.symbol_id == sid
    if isinstance(expr, (RBuiltinCall, RModelCall)):
        return any(_expr_uses_sid(arg, sid) for arg in expr.args)
    if isinstance(expr, RIte):
        return (
            _expr_uses_sid(expr.cond, sid)
            or _expr_uses_sid(expr.if_true, sid)
            or _expr_uses_sid(expr.if_false, sid)
        )
    raise ValueError(f"Unexpected RExpr: {type(expr).__name__}")


def _analyze_branch_outputs(
    sid: SymbolId,
    branch: RBranch,
    assigned_in: bool,
) -> tuple[bool, bool]:
    needs_init, assigned = _analyze_init_need_in_block(
        sid,
        branch.assignments,
        assigned_in=assigned_in,
    )
    if needs_init:
        return True, assigned
    for expr in branch.output_exprs:
        if _expr_uses_sid(expr, sid) and not assigned:
            return True, assigned
    return False, assigned


def _analyze_init_need_in_stmt(
    sid: SymbolId,
    stmt: RStatement,
    *,
    assigned_in: bool,
) -> tuple[bool, bool]:
    if isinstance(stmt, RAssignment):
        if _expr_uses_sid(stmt.expr, sid) and not assigned_in:
            return True, assigned_in
        return False, assigned_in or stmt.target == sid

    if isinstance(stmt, RCallAssign):
        if any(_expr_uses_sid(arg, sid) for arg in stmt.args) and not assigned_in:
            return True, assigned_in
        return False, assigned_in or sid in stmt.targets

    if isinstance(stmt, RConditionalBlock):
        if _expr_uses_sid(stmt.condition, sid) and not assigned_in:
            return True, assigned_in
        then_needs, _then_assigned = _analyze_branch_outputs(
            sid,
            stmt.then_branch,
            assigned_in,
        )
        if then_needs:
            return True, assigned_in
        else_needs, _else_assigned = _analyze_branch_outputs(
            sid,
            stmt.else_branch,
            assigned_in,
        )
        if else_needs:
            return True, assigned_in
        if sid in stmt.output_targets:
            return False, True
        return False, assigned_in

    assert_never(stmt)


def _analyze_init_need_in_block(
    sid: SymbolId,
    stmts: tuple[RStatement, ...],
    *,
    assigned_in: bool,
) -> tuple[bool, bool]:
    assigned = assigned_in
    for stmt in stmts:
        needs_init, assigned = _analyze_init_need_in_stmt(
            sid,
            stmt,
            assigned_in=assigned,
        )
        if needs_init:
            return True, assigned
    return False, assigned


def _needs_zero_init(
    sid: SymbolId,
    body: tuple[RStatement, ...],
) -> bool:
    """Check if a return variable needs explicit zero-initialization."""
    needs_init, assigned_out = _analyze_init_need_in_block(
        sid,
        body,
        assigned_in=False,
    )
    return needs_init or not assigned_out


def to_function_models(
    funcs: dict[str, RestrictedFunction],
) -> dict[str, FunctionModel]:
    """Convert a module of ``RestrictedFunction``s to ``FunctionModel``s.

    Builds a ``ModuleNamePlan`` that owns all naming decisions
    (function names and binder names), applies it, then runs SSA per
    function. Returns a dict keyed by clean function names.
    """
    name_plan = plan_module(funcs)
    legalized = apply_module_plan(funcs, name_plan)
    models: dict[str, FunctionModel] = {}
    for raw_name, func in legalized.items():
        sol_name = name_plan.function_names[raw_name]
        # Name legalization already applied by apply_module_plan.
        models[sol_name] = _ssa_and_model(func, sol_name)
    from .model_validate import validate_model_set

    validate_model_set(list(models.values()))
    return models


def _ssa_and_model(func: RestrictedFunction, sol_fn_name: str) -> FunctionModel:
    """SSA renaming + FunctionModel construction (no legalization)."""
    ctx = _SSACtx()
    param_ssa: list[str] = []
    for sid, name in zip(func.params, func.param_names):
        ssa = ctx.assign(sid, name)
        param_ssa.append(ssa)
    assignments: list[ModelStatement] = []
    for sid, name in zip(func.returns, func.return_names):
        if _needs_zero_init(sid, func.body):
            ssa = ctx.assign(sid, name)
            assignments.append(Assignment(target=ssa, expr=IntLit(0)))
    body_stmts = _convert_block(func.body, ctx)
    assignments.extend(body_stmts)
    return_ssa: list[str] = []
    for sid in func.returns:
        return_ssa.append(ctx.lookup(sid))
    return FunctionModel(
        fn_name=sol_fn_name,
        assignments=tuple(assignments),
        param_names=tuple(param_ssa),
        return_names=tuple(return_ssa),
    )
