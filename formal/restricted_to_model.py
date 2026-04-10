"""
SSA renaming and FunctionModel conversion (Pass 9).

Converts a ``RestrictedFunction`` (SymbolId-keyed, non-SSA) into a
``FunctionModel`` (string-named, SSA-renamed) ready for Lean emission.

The pipeline is:

1. **Name legalization** (``restricted_names.legalize_names``):
   demangle compiler names, sanitize identifiers, rewrite callee names.
2. **SSA renaming** (this module): version base names and build
   ``FunctionModel`` with recursive branch support.

SSA naming rules match the old pipeline:
- First assignment to a clean name uses the bare name (e.g. ``z``)
- Subsequent assignments suffix ``_{n-1}`` (e.g. ``z_1``, ``z_2``)
- Collisions with already-emitted names are skipped
- Branch-local SSA uses copied counters; merge uses outer counters
"""

from __future__ import annotations

import re
from collections import Counter
from collections.abc import Callable
from typing import TYPE_CHECKING, assert_never

if TYPE_CHECKING:
    from yul_ast import FunctionDef

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
from norm_walk import for_each_expr, map_expr, max_symbol_id
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
from restricted_names import apply_module_plan, legalize_names, plan_module
from yul_ast import ParseError, SymbolId

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


def _needs_zero_init(
    sid: SymbolId,
    body: tuple[RStatement, ...],
) -> bool:
    """Check if a return variable needs explicit zero-initialization.

    Conservative: always zero-init.
    """
    return True


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def to_function_model(
    func: RestrictedFunction,
    sol_fn_name: str,
    *,
    callee_names: dict[str, str] | None = None,
) -> FunctionModel:
    """Convert a RestrictedFunction to a FunctionModel with SSA naming.

    Runs two passes in sequence:

    1. Name legalization (demangle, sanitize, callee rewriting)
    2. SSA renaming + ``FunctionModel`` construction

    If *callee_names* is provided, model-call callee names are
    rewritten from raw Yul names to their emitted model names.
    """
    # Pass 1: legalize names.
    func = legalize_names(func, callee_names=callee_names)

    # Pass 2: SSA renaming.
    ctx = _SSACtx()

    # Register parameters (SSA count starts at 1).
    param_ssa: list[str] = []
    for sid, name in zip(func.params, func.param_names):
        ssa = ctx.assign(sid, name)
        param_ssa.append(ssa)

    # Zero-init return variables that need it.
    assignments: list[ModelStatement] = []
    for sid, name in zip(func.returns, func.return_names):
        if _needs_zero_init(sid, func.body):
            ssa = ctx.assign(sid, name)
            assignments.append(Assignment(target=ssa, expr=IntLit(0)))

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


def to_function_models(
    funcs: dict[str, RestrictedFunction],
) -> dict[str, FunctionModel]:
    """Convert a module of ``RestrictedFunction``s to ``FunctionModel``s.

    Builds a ``ModuleNamePlan`` that owns all naming decisions
    (function names, binder names, reserved-name avoidance), applies
    it, then runs SSA per function.  Returns a dict keyed by clean
    (emitted) function names.
    """
    name_plan = plan_module(funcs)
    legalized = apply_module_plan(funcs, name_plan)
    models: dict[str, FunctionModel] = {}
    for raw_name, func in legalized.items():
        sol_name = name_plan.function_names[raw_name]
        # Name legalization already applied by apply_module_plan.
        models[sol_name] = _ssa_and_model(func, sol_name)
    from yul_to_lean import validate_selected_models

    validate_selected_models(list(models.values()))
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


def translate_module(
    yul_text: str,
    *,
    builtins: frozenset[str] | None = None,
) -> dict[str, FunctionModel]:
    """Full pipeline: Yul source → dict of ``FunctionModel``s.

    This is the public entry point for the new staged pipeline.
    Handles parsing, resolution, normalization, inlining, constant
    propagation, restricted IR lowering, name legalization, and SSA
    renaming.
    """
    from yul_to_lean import _EVM_BUILTINS

    if builtins is None:
        builtins = _EVM_BUILTINS
    groups = translate_groups(yul_text, builtins=builtins)
    if not groups:
        return {}
    if len(groups) != 1:
        raise ParseError(
            "translate_module found multiple function groups; use translate_groups() "
            "to translate object/code scopes independently"
        )
    return groups[0]


def translate_groups(
    yul_text: str,
    *,
    builtins: frozenset[str] | None = None,
) -> list[dict[str, FunctionModel]]:
    """Full pipeline: Yul source -> one model map per lexical function group."""
    from norm_constprop import propagate_constants
    from norm_inline import inline_pure_helpers
    from norm_to_restricted import lower_to_restricted
    from yul_normalize import normalize_function
    from yul_parser import SyntaxParser
    from yul_resolve import resolve_module
    from yul_to_lean import _EVM_BUILTINS, tokenize_yul

    if builtins is None:
        builtins = _EVM_BUILTINS
    tokens = tokenize_yul(yul_text)
    groups = SyntaxParser(tokens).parse_function_groups()
    out: list[dict[str, FunctionModel]] = []
    for funcs in groups:
        resolved = resolve_module(funcs, builtins=builtins)
        restricted: dict[str, RestrictedFunction] = {}
        for name, result in resolved.items():
            nf = normalize_function(result.func, result)
            nf = inline_pure_helpers(nf)
            nf = propagate_constants(nf)
            restricted[name] = lower_to_restricted(nf)
        out.append(to_function_models(restricted))
    return out


# ---------------------------------------------------------------------------
# Selection-aware pipeline
# ---------------------------------------------------------------------------


def _demangle_fn(name: str) -> str:
    """Demangle ``fun_f_1`` → ``f``; identity otherwise."""
    m = re.fullmatch(r"fun_(\w+?)_\d+", name)
    return m.group(1) if m else name


def _for_each_expr_in_block(
    block: NBlock,
    visitor: Callable[[NExpr], None],
) -> None:
    """Call *visitor* on every expression reachable from *block*."""
    for stmt in block.stmts:
        _for_each_expr_in_stmt(stmt, visitor)


def _for_each_expr_in_stmt(
    stmt: NStmt,
    visitor: Callable[[NExpr], None],
) -> None:
    if isinstance(stmt, NBind):
        if stmt.expr is not None:
            for_each_expr(stmt.expr, visitor)
    elif isinstance(stmt, NAssign):
        for_each_expr(stmt.expr, visitor)
    elif isinstance(stmt, NExprEffect):
        for_each_expr(stmt.expr, visitor)
    elif isinstance(stmt, NStore):
        for_each_expr(stmt.addr, visitor)
        for_each_expr(stmt.value, visitor)
    elif isinstance(stmt, NIf):
        for_each_expr(stmt.condition, visitor)
        _for_each_expr_in_block(stmt.then_body, visitor)
    elif isinstance(stmt, NSwitch):
        for_each_expr(stmt.discriminant, visitor)
        for case in stmt.cases:
            _for_each_expr_in_block(case.body, visitor)
        if stmt.default is not None:
            _for_each_expr_in_block(stmt.default, visitor)
    elif isinstance(stmt, NFor):
        _for_each_expr_in_block(stmt.init, visitor)
        for_each_expr(stmt.condition, visitor)
        if stmt.condition_setup is not None:
            _for_each_expr_in_block(stmt.condition_setup, visitor)
        _for_each_expr_in_block(stmt.post, visitor)
        _for_each_expr_in_block(stmt.body, visitor)
    elif isinstance(stmt, NFunctionDef):
        _for_each_expr_in_block(stmt.body, visitor)
    elif isinstance(stmt, NBlock):
        _for_each_expr_in_block(stmt, visitor)
    # NLeave: no expressions


def _map_all_exprs_in_block(
    block: NBlock,
    f: Callable[[NExpr], NExpr],
) -> NBlock:
    """Apply expression mapper *f* (via ``map_expr``) to every expression
    in *block*, recursing into sub-blocks and function defs."""
    return NBlock(tuple(_map_all_exprs_in_stmt(s, f) for s in block.stmts))


def _map_all_exprs_in_stmt(
    stmt: NStmt,
    f: Callable[[NExpr], NExpr],
) -> NStmt:
    if isinstance(stmt, NBind):
        return NBind(
            targets=stmt.targets,
            target_names=stmt.target_names,
            expr=map_expr(stmt.expr, f) if stmt.expr is not None else None,
        )
    if isinstance(stmt, NAssign):
        return NAssign(
            targets=stmt.targets,
            target_names=stmt.target_names,
            expr=map_expr(stmt.expr, f),
        )
    if isinstance(stmt, NExprEffect):
        return NExprEffect(expr=map_expr(stmt.expr, f))
    if isinstance(stmt, NStore):
        return NStore(addr=map_expr(stmt.addr, f), value=map_expr(stmt.value, f))
    if isinstance(stmt, NIf):
        return NIf(
            condition=map_expr(stmt.condition, f),
            then_body=_map_all_exprs_in_block(stmt.then_body, f),
        )
    if isinstance(stmt, NSwitch):
        return NSwitch(
            discriminant=map_expr(stmt.discriminant, f),
            cases=tuple(
                NSwitchCase(value=c.value, body=_map_all_exprs_in_block(c.body, f))
                for c in stmt.cases
            ),
            default=(
                _map_all_exprs_in_block(stmt.default, f)
                if stmt.default is not None
                else None
            ),
        )
    if isinstance(stmt, NFor):
        return NFor(
            init=_map_all_exprs_in_block(stmt.init, f),
            condition=map_expr(stmt.condition, f),
            condition_setup=(
                _map_all_exprs_in_block(stmt.condition_setup, f)
                if stmt.condition_setup is not None
                else None
            ),
            post=_map_all_exprs_in_block(stmt.post, f),
            body=_map_all_exprs_in_block(stmt.body, f),
        )
    if isinstance(stmt, NLeave):
        return stmt
    if isinstance(stmt, NBlock):
        return _map_all_exprs_in_block(stmt, f)
    if isinstance(stmt, NFunctionDef):
        return NFunctionDef(
            name=stmt.name,
            symbol_id=stmt.symbol_id,
            params=stmt.params,
            param_names=stmt.param_names,
            returns=stmt.returns,
            return_names=stmt.return_names,
            body=_map_all_exprs_in_block(stmt.body, f),
        )
    raise ValueError(f"Unexpected NStmt: {type(stmt).__name__}")


# ---------------------------------------------------------------------------
# Helper embedding
# ---------------------------------------------------------------------------


def _collect_top_level_call_names(body: NBlock) -> set[str]:
    """Collect all ``NTopLevelCall`` callee names from *body*."""
    names: set[str] = set()

    def _visit(e: NExpr) -> None:
        if isinstance(e, NTopLevelCall):
            names.add(e.name)

    _for_each_expr_in_block(body, _visit)
    return names


def _collect_helper_closure(
    target_name: str,
    all_normalized: dict[str, NormalizedFunction],
    selected_names: set[str],
) -> set[str]:
    """BFS: collect all non-selected helpers reachable from *target_name*."""
    closure: set[str] = set()
    worklist = [target_name]
    visited: set[str] = set()
    while worklist:
        name = worklist.pop()
        if name in visited:
            continue
        visited.add(name)
        if name not in all_normalized:
            continue
        for callee in _collect_top_level_call_names(all_normalized[name].body):
            if (
                callee in all_normalized
                and callee not in selected_names
                and callee not in closure
            ):
                closure.add(callee)
                worklist.append(callee)
    return closure


def _embed_helpers(
    target: NormalizedFunction,
    helpers: dict[str, NormalizedFunction],
) -> NormalizedFunction:
    """Embed *helpers* into *target* as ``NFunctionDef`` nodes.

    Rewrites ``NTopLevelCall`` → ``NLocalCall`` for all embedded names
    in both the target body and the helper bodies (transitive calls).
    """
    # Find max SymbolId across target and all helpers.
    max_id = max_symbol_id(target)
    for h in helpers.values():
        max_id = max(max_id, max_symbol_id(h))
    next_id = max_id + 1

    # Allocate a SymbolId for each embedded helper's NFunctionDef.
    name_to_sid: dict[str, SymbolId] = {}
    for name in helpers:
        name_to_sid[name] = SymbolId(next_id)
        next_id += 1

    # Expression rewriter: NTopLevelCall → NLocalCall for embedded names.
    def _rewrite(e: NExpr) -> NExpr:
        if isinstance(e, NTopLevelCall) and e.name in name_to_sid:
            return NLocalCall(symbol_id=name_to_sid[e.name], name=e.name, args=e.args)
        return e

    # Create NFunctionDef for each helper with rewritten bodies.
    fdefs: list[NStmt] = []
    for name, nf in helpers.items():
        fdefs.append(
            NFunctionDef(
                name=name,
                symbol_id=name_to_sid[name],
                params=nf.params,
                param_names=nf.param_names,
                returns=nf.returns,
                return_names=nf.return_names,
                body=_map_all_exprs_in_block(nf.body, _rewrite),
            )
        )

    # Rewrite target body and prepend helper definitions.
    new_body = _map_all_exprs_in_block(target.body, _rewrite)
    return NormalizedFunction(
        name=target.name,
        params=target.params,
        param_names=target.param_names,
        returns=target.returns,
        return_names=target.return_names,
        body=NBlock(tuple(fdefs) + new_body.stmts),
    )


# ---------------------------------------------------------------------------
# Target selection
# ---------------------------------------------------------------------------


def _select_targets(
    selected: tuple[str, ...],
    parsed_groups: list[list[FunctionDef]],
    exact_yul_names: dict[str, str] | None,
    n_params: dict[str, int] | None,
) -> dict[int, list[tuple[str, str]]]:
    """Map each sol_name in *selected* to ``(group_idx, raw_name)``.

    Returns a dict keyed by group index, values are lists of
    ``(sol_name, raw_name)`` for targets in that group.
    """
    # Build lookup indices: by demangled name and by raw name.
    by_demangled: dict[str, list[tuple[int, FunctionDef]]] = {}
    by_raw: dict[str, list[tuple[int, FunctionDef]]] = {}
    for gi, funcs in enumerate(parsed_groups):
        for fdef in funcs:
            by_raw.setdefault(fdef.name, []).append((gi, fdef))
            clean = _demangle_fn(fdef.name)
            by_demangled.setdefault(clean, []).append((gi, fdef))

    result: dict[int, list[tuple[str, str]]] = {}

    for sol_name in selected:
        exact_raw = exact_yul_names.get(sol_name) if exact_yul_names else None

        if exact_raw is not None:
            candidates = by_raw.get(exact_raw, [])
            if not candidates:
                raise ParseError(
                    f"exact_yul_names[{sol_name!r}] = {exact_raw!r} not found. "
                    f"Available: {sorted(by_raw.keys())}"
                )
        else:
            candidates = by_demangled.get(sol_name, [])
            if not candidates:
                raise ParseError(
                    f"Selected function {sol_name!r} not found. "
                    f"Available: {sorted(by_demangled.keys())}"
                )

        # Filter by n_params if set.
        if n_params and sol_name in n_params:
            expected = n_params[sol_name]
            candidates = [(gi, f) for gi, f in candidates if len(f.params) == expected]
            if not candidates:
                raise ParseError(f"No {sol_name!r} with {expected} parameter(s) found")

        if len(candidates) > 1:
            raise ParseError(
                f"Ambiguous selection for {sol_name!r}: "
                f"{[f.name for _, f in candidates]}"
            )

        gi, fdef = candidates[0]
        result.setdefault(gi, []).append((sol_name, fdef.name))

    return result


# ---------------------------------------------------------------------------
# Selection-aware pipeline entry point
# ---------------------------------------------------------------------------


def translate_selected(
    yul_text: str,
    selected: tuple[str, ...],
    *,
    exact_yul_names: dict[str, str] | None = None,
    n_params: dict[str, int] | None = None,
    builtins: frozenset[str] | None = None,
) -> list[FunctionModel]:
    """Selection-aware staged pipeline.

    Parses, resolves, and normalizes all functions, then for each
    selected target embeds its non-selected helper closure as local
    function definitions and runs the full optimization pipeline.

    Returns ``FunctionModel``s ordered by *selected*.
    """
    from norm_constprop import propagate_constants
    from norm_inline import inline_pure_helpers
    from norm_to_restricted import lower_to_restricted
    from yul_normalize import normalize_function
    from yul_parser import SyntaxParser
    from yul_resolve import resolve_module
    from yul_to_lean import _EVM_BUILTINS, tokenize_yul

    if builtins is None:
        builtins = _EVM_BUILTINS

    tokens = tokenize_yul(yul_text)
    parsed_groups = SyntaxParser(tokens).parse_function_groups()

    # Resolve each group.
    resolved_groups = [
        resolve_module(funcs, builtins=builtins) for funcs in parsed_groups
    ]

    # Select targets.
    selections = _select_targets(selected, parsed_groups, exact_yul_names, n_params)

    # Zero-return validation.
    for gi, targets in selections.items():
        resolved = resolved_groups[gi]
        for sol_name, raw_name in targets:
            fdef = resolved[raw_name].func
            if not fdef.returns:
                raise ParseError(
                    f"Selected function {sol_name!r} ({raw_name}) has "
                    f"zero return values"
                )

    # Process each group that has selected targets.
    all_restricted: dict[str, RestrictedFunction] = {}

    for gi, targets in selections.items():
        resolved = resolved_groups[gi]

        # Normalize all functions in the group.
        normalized: dict[str, NormalizedFunction] = {}
        for name, result in resolved.items():
            normalized[name] = normalize_function(result.func, result)

        selected_raws = {raw for _, raw in targets}

        for _sol_name, raw_name in targets:
            target_nf = normalized[raw_name]

            # Embed non-selected helper closure.
            closure = _collect_helper_closure(raw_name, normalized, selected_raws)
            if closure:
                helpers = {n: normalized[n] for n in closure}
                target_nf = _embed_helpers(target_nf, helpers)

            # Optimization passes.
            target_nf = inline_pure_helpers(target_nf)
            target_nf = propagate_constants(target_nf)
            all_restricted[raw_name] = lower_to_restricted(target_nf)

    # Build models with module-wide SSA naming.
    models_dict = to_function_models(all_restricted)

    # Order by selected: match sol_name → clean model name.
    ordered: list[FunctionModel] = []
    for sol_name in selected:
        if sol_name in models_dict:
            ordered.append(models_dict[sol_name])
        else:
            # Find by fn_name fallback (demangled names may differ from sol_name).
            found = False
            for model in models_dict.values():
                if model.fn_name == sol_name:
                    ordered.append(model)
                    found = True
                    break
            if not found:
                raise ParseError(
                    f"Model for selected function {sol_name!r} not found "
                    f"after pipeline. Available: {sorted(models_dict.keys())}"
                )

    return ordered
