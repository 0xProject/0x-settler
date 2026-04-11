"""
Lower memory-free normalized imperative IR to non-SSA restricted IR.

The resulting IR has:

- no memory operations
- explicit conditional outputs
- direct model-call assignments for top-level calls
- no SSA renaming
"""

from __future__ import annotations

from .evm_builtins import WORD_MOD
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
    NStore,
    NSwitch,
    NSwitchCase,
    NTopLevelCall,
    NUnresolvedCall,
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
from .yul_ast import ParseError, SymbolId


def _name_for_sid(sid: SymbolId, names: dict[SymbolId, str]) -> str:
    return names.get(sid, f"_v_{sid._id}")


def _lower_expr(expr: NExpr) -> RExpr:
    if isinstance(expr, NConst):
        return RConst(value=expr.value)

    if isinstance(expr, NRef):
        return RRef(symbol_id=expr.symbol_id, name=expr.name)

    if isinstance(expr, NBuiltinCall):
        if expr.op in ("mload", "mstore", "mstore8"):
            raise ParseError(
                f"Memory builtin {expr.op!r} reached restricted IR lowering. "
                "Memory must be lowered before this pass."
            )
        args = tuple(_lower_expr(a) for a in expr.args)
        return RBuiltinCall(op=expr.op, args=args)

    if isinstance(expr, NLocalCall):
        raise ParseError(
            f"Unresolved local call to {expr.name!r} in restricted IR lowering. "
            f"All helpers should be inlined before this pass."
        )

    if isinstance(expr, NTopLevelCall):
        args = tuple(_lower_expr(a) for a in expr.args)
        return RModelCall(name=expr.name, args=args)

    if isinstance(expr, NUnresolvedCall):
        raise ParseError(f"Unresolved call to {expr.name!r} in restricted IR lowering")

    if isinstance(expr, NIte):
        return RIte(
            cond=_lower_expr(expr.cond),
            if_true=_lower_expr(expr.if_true),
            if_false=_lower_expr(expr.if_false),
        )

    raise ParseError(f"Unexpected expression: {type(expr).__name__}")


def _modified_union(
    outer_order: tuple[SymbolId, ...],
    then_var: dict[SymbolId, bool],
    else_var: dict[SymbolId, bool],
) -> list[SymbolId]:
    return [sid for sid in outer_order if sid in then_var or sid in else_var]


def _build_conditional(
    *,
    condition: RExpr,
    then_assignments: list[RStatement],
    then_var: dict[SymbolId, bool],
    else_assignments: list[RStatement],
    else_var: dict[SymbolId, bool],
    outer_order: tuple[SymbolId, ...],
    names: dict[SymbolId, str],
) -> tuple[RConditionalBlock | None, list[SymbolId]]:
    output_targets = _modified_union(outer_order, then_var, else_var)
    if not output_targets:
        return None, []

    output_names = tuple(_name_for_sid(sid, names) for sid in output_targets)
    branch_outputs = tuple(
        RRef(symbol_id=sid, name=_name_for_sid(sid, names)) for sid in output_targets
    )
    return (
        RConditionalBlock(
            condition=condition,
            output_targets=tuple(output_targets),
            output_names=output_names,
            then_branch=RBranch(
                assignments=tuple(then_assignments),
                output_exprs=branch_outputs,
            ),
            else_branch=RBranch(
                assignments=tuple(else_assignments),
                output_exprs=branch_outputs,
            ),
        ),
        output_targets,
    )


def _lower_block(
    block: NBlock,
    names: dict[SymbolId, str],
    visible_state: dict[SymbolId, bool],
    modified_state: dict[SymbolId, bool],
) -> list[RStatement]:
    out: list[RStatement] = []
    for stmt in block.stmts:
        _lower_stmt(stmt, names, visible_state, modified_state, out)
    return out


def _lower_stmt(
    stmt: NStmt,
    names: dict[SymbolId, str],
    visible_state: dict[SymbolId, bool],
    modified_state: dict[SymbolId, bool],
    out: list[RStatement],
) -> None:
    if isinstance(stmt, NStore):
        raise ParseError(
            "NStore reached restricted IR lowering. Memory must be lowered "
            "before this pass."
        )

    if isinstance(stmt, NExprEffect):
        raise ParseError(
            "Expression statement reached restricted IR lowering. Effect "
            "statements must be eliminated before this pass."
        )

    if isinstance(stmt, (NBind, NAssign)):
        expr = stmt.expr
        if isinstance(stmt, NBind) and expr is None:
            for sid, name in zip(stmt.targets, stmt.target_names):
                names[sid] = name
                out.append(RAssignment(target=sid, target_name=name, expr=RConst(0)))
                visible_state[sid] = True
                modified_state[sid] = True
            return

        assert expr is not None
        if isinstance(expr, NTopLevelCall):
            args = tuple(_lower_expr(a) for a in expr.args)
            for sid, name in zip(stmt.targets, stmt.target_names):
                names[sid] = name
                visible_state[sid] = True
                modified_state[sid] = True
            out.append(
                RCallAssign(
                    targets=stmt.targets,
                    target_names=stmt.target_names,
                    callee=expr.name,
                    args=args,
                )
            )
            return

        if len(stmt.targets) > 1:
            raise ParseError(
                "Multi-target assignment in restricted IR lowering requires "
                "a top-level model call"
            )

        rexpr = _lower_expr(expr)
        sid = stmt.targets[0]
        name = stmt.target_names[0]
        names[sid] = name
        out.append(RAssignment(target=sid, target_name=name, expr=rexpr))
        visible_state[sid] = True
        modified_state[sid] = True
        return

    if isinstance(stmt, NIf):
        _lower_if(stmt, names, visible_state, modified_state, out)
        return

    if isinstance(stmt, NSwitch):
        _lower_switch(stmt, names, visible_state, modified_state, out)
        return

    if isinstance(stmt, NBlock):
        out.extend(_lower_block(stmt, names, visible_state, modified_state))
        return

    if isinstance(stmt, NFunctionDef):
        return

    if isinstance(stmt, NLeave):
        raise ParseError("NLeave in restricted IR lowering — should have been inlined")

    if isinstance(stmt, NFor):
        raise ParseError("NFor in restricted IR lowering — not supported")

    raise ParseError(f"Unexpected statement: {type(stmt).__name__}")


def _lower_if(
    stmt: NIf,
    names: dict[SymbolId, str],
    visible_state: dict[SymbolId, bool],
    modified_state: dict[SymbolId, bool],
    out: list[RStatement],
) -> None:
    cond = _lower_expr(stmt.condition)
    outer_order = tuple(visible_state.keys())

    then_visible = dict(visible_state)
    then_modified: dict[SymbolId, bool] = {}
    then_assignments = _lower_block(stmt.then_body, names, then_visible, then_modified)

    conditional, outputs = _build_conditional(
        condition=cond,
        then_assignments=then_assignments,
        then_var=then_modified,
        else_assignments=[],
        else_var={},
        outer_order=outer_order,
        names=names,
    )
    if conditional is not None:
        out.append(conditional)
        for sid in outputs:
            visible_state[sid] = True
            modified_state[sid] = True


def _lower_switch_chain(
    *,
    disc: RExpr,
    cases: tuple[NSwitchCase, ...],
    default: NBlock | None,
    names: dict[SymbolId, str],
    outer_order: tuple[SymbolId, ...],
    visible_state: dict[SymbolId, bool],
) -> tuple[list[RStatement], dict[SymbolId, bool]]:
    if not cases:
        if default is None:
            return [], {}
        default_visible = dict(visible_state)
        default_modified: dict[SymbolId, bool] = {}
        default_assignments = _lower_block(
            default, names, default_visible, default_modified
        )
        return default_assignments, default_modified

    case = cases[0]
    then_visible = dict(visible_state)
    then_modified: dict[SymbolId, bool] = {}
    then_assignments = _lower_block(case.body, names, then_visible, then_modified)

    else_assignments, else_var = _lower_switch_chain(
        disc=disc,
        cases=cases[1:],
        default=default,
        names=names,
        outer_order=outer_order,
        visible_state=visible_state,
    )

    condition = RBuiltinCall(
        op="eq",
        args=(disc, RConst(case.value.value % WORD_MOD)),
    )
    conditional, outputs = _build_conditional(
        condition=condition,
        then_assignments=then_assignments,
        then_var=then_modified,
        else_assignments=else_assignments,
        else_var=else_var,
        outer_order=outer_order,
        names=names,
    )
    if conditional is None:
        return else_assignments, else_var
    return [conditional], {sid: True for sid in outputs}


def _lower_switch(
    stmt: NSwitch,
    names: dict[SymbolId, str],
    visible_state: dict[SymbolId, bool],
    modified_state: dict[SymbolId, bool],
    out: list[RStatement],
) -> None:
    disc = _lower_expr(stmt.discriminant)
    outer_order = tuple(visible_state.keys())

    chain_assignments, chain_var = _lower_switch_chain(
        disc=disc,
        cases=stmt.cases,
        default=stmt.default,
        names=names,
        outer_order=outer_order,
        visible_state=visible_state,
    )
    out.extend(chain_assignments)
    for sid in chain_var:
        visible_state[sid] = True
        modified_state[sid] = True


def lower_to_restricted(func: NormalizedFunction) -> RestrictedFunction:
    """Lower memory-free normalized IR to non-SSA restricted IR."""
    names: dict[SymbolId, str] = {}
    var_state: dict[SymbolId, bool] = {}

    for sid, name in zip(func.params, func.param_names):
        names[sid] = name
        var_state[sid] = True
    for sid, name in zip(func.returns, func.return_names):
        names[sid] = name
        var_state[sid] = True

    body = _lower_block(func.body, names, var_state, {})

    return RestrictedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=tuple(body),
    )
