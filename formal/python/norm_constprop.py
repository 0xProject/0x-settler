"""
Structured simplification on raw normalized IR.

This pass operates before leave lowering and memory lowering. It:
- folds constant expressions
- propagates known constants and aliases through assignments
- eliminates dead branches when control-flow conditions become constant
- joins facts only at real control-flow joins
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import assert_never

from .evm_builtins import eval_pure_builtin, is_pure_builtin
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
from .norm_walk import const_truthy, const_value, map_expr, simplify_ite
from .yul_ast import EvaluationError, SymbolId

# ---------------------------------------------------------------------------
# Expression folding (via shared map_expr)
# ---------------------------------------------------------------------------


def _is_zero(expr: NExpr) -> bool:
    return isinstance(expr, NConst) and expr.value == 0


def _is_one(expr: NExpr) -> bool:
    return isinstance(expr, NConst) and expr.value == 1


def _is_all_ones(expr: NExpr) -> bool:
    return isinstance(expr, NConst) and expr.value == (2**256 - 1)


def _expr_is_obviously_pure(expr: NExpr) -> bool:
    if isinstance(expr, (NConst, NRef)):
        return True
    if isinstance(expr, NBuiltinCall):
        return is_pure_builtin(expr.op, len(expr.args)) and all(
            _expr_is_obviously_pure(arg) for arg in expr.args
        )
    if isinstance(expr, NIte):
        return (
            _expr_is_obviously_pure(expr.cond)
            and _expr_is_obviously_pure(expr.if_true)
            and _expr_is_obviously_pure(expr.if_false)
        )
    if isinstance(expr, (NLocalCall, NTopLevelCall, NUnresolvedCall)):
        return False
    assert_never(expr)


def _same_pure_expr(lhs: NExpr, rhs: NExpr) -> bool:
    return lhs == rhs and _expr_is_obviously_pure(lhs)


def _fold_builtin(expr: NBuiltinCall) -> NExpr:
    if all(isinstance(arg, NConst) for arg in expr.args):
        vals = tuple(arg.value for arg in expr.args if isinstance(arg, NConst))
        try:
            return NConst(eval_pure_builtin(expr.op, vals))
        except EvaluationError:
            return expr

    if len(expr.args) != 2:
        return expr

    lhs, rhs = expr.args
    if expr.op == "add":
        if _is_zero(lhs):
            return rhs
        if _is_zero(rhs):
            return lhs
        return expr

    if expr.op == "sub":
        if _is_zero(rhs):
            return lhs
        if _same_pure_expr(lhs, rhs):
            return NConst(0)
        return expr

    if expr.op == "mul":
        if _is_one(lhs):
            return rhs
        if _is_one(rhs):
            return lhs
        if _is_zero(lhs) and _expr_is_obviously_pure(rhs):
            return NConst(0)
        if _is_zero(rhs) and _expr_is_obviously_pure(lhs):
            return NConst(0)
        return expr

    if expr.op == "and":
        if _is_all_ones(lhs):
            return rhs
        if _is_all_ones(rhs):
            return lhs
        if _is_zero(lhs) and _expr_is_obviously_pure(rhs):
            return NConst(0)
        if _is_zero(rhs) and _expr_is_obviously_pure(lhs):
            return NConst(0)
        if _same_pure_expr(lhs, rhs):
            return lhs
        return expr

    if expr.op == "or":
        if _is_zero(lhs):
            return rhs
        if _is_zero(rhs):
            return lhs
        if _same_pure_expr(lhs, rhs):
            return lhs
        return expr

    if expr.op == "xor":
        if _is_zero(lhs):
            return rhs
        if _is_zero(rhs):
            return lhs
        if _same_pure_expr(lhs, rhs):
            return NConst(0)
        return expr

    if expr.op == "eq":
        if _same_pure_expr(lhs, rhs):
            return NConst(1)
        return expr

    if expr.op in ("lt", "gt"):
        if _same_pure_expr(lhs, rhs):
            return NConst(0)
        return expr

    if expr.op == "shl" and _is_zero(lhs):
        return rhs

    if expr.op == "shr" and _is_zero(lhs):
        return rhs

    return expr


def _fold_node(expr: NExpr) -> NExpr:
    """Fold callback for map_expr."""
    if isinstance(expr, NConst):
        return expr
    if isinstance(expr, NBuiltinCall):
        return _fold_builtin(expr)
    if isinstance(expr, NIte):
        return simplify_ite(expr.cond, expr.if_true, expr.if_false)
    return expr


def fold_expr(expr: NExpr) -> NExpr:
    """Fold constant sub-expressions bottom-up."""
    return map_expr(expr, _fold_node)


# ---------------------------------------------------------------------------
# Structured forward simplification
# ---------------------------------------------------------------------------


_FactExpr = NConst | NRef


@dataclass(frozen=True, slots=True)
class _StmtRewrite:
    stmts: tuple[NStmt, ...]
    env: _FactEnv
    falls_through: bool

    @classmethod
    def continue_with(
        cls,
        stmts: tuple[NStmt, ...],
        env: _FactEnv,
    ) -> _StmtRewrite:
        return cls(stmts=stmts, env=env, falls_through=True)

    @classmethod
    def stop_with(
        cls,
        stmts: tuple[NStmt, ...],
        env: _FactEnv,
    ) -> _StmtRewrite:
        return cls(stmts=stmts, env=env, falls_through=False)


@dataclass(frozen=True, slots=True)
class _BlockRewrite:
    block: NBlock
    env: _FactEnv
    falls_through: bool

    @classmethod
    def continue_with(
        cls,
        block: NBlock,
        env: _FactEnv,
    ) -> _BlockRewrite:
        return cls(block=block, env=env, falls_through=True)

    @classmethod
    def stop_with(
        cls,
        block: NBlock,
        env: _FactEnv,
    ) -> _BlockRewrite:
        return cls(block=block, env=env, falls_through=False)


class _FactEnv:
    """Forward facts for constant and copy propagation."""

    def __init__(self) -> None:
        self._facts: dict[SymbolId, _FactExpr] = {}
        self._sources_by_target: dict[SymbolId, set[SymbolId]] = {}
        self._dependents_by_source: dict[SymbolId, set[SymbolId]] = {}

    def copy(self) -> _FactEnv:
        other = _FactEnv()
        other._facts = dict(self._facts)
        other._sources_by_target = {
            sid: set(sources) for sid, sources in self._sources_by_target.items()
        }
        other._dependents_by_source = {
            sid: set(dependents)
            for sid, dependents in self._dependents_by_source.items()
        }
        return other

    def same_facts(self, other: _FactEnv) -> bool:
        return self._facts == other._facts

    def rewrite_expr(self, expr: NExpr) -> NExpr:
        def rewrite(node: NExpr) -> NExpr:
            if isinstance(node, NRef):
                return self._resolve_ref(node)
            return _fold_node(node)

        return map_expr(expr, rewrite)

    def assign_zero_targets(self, targets: tuple[SymbolId, ...]) -> None:
        self.kill_targets(targets)
        for sid in targets:
            self._install_fact(sid, NConst(0))

    def assign_expr(self, target: SymbolId, expr: NExpr) -> None:
        self.invalidate(target)
        fact = self._canonical_fact(expr)
        if fact is None:
            return
        if isinstance(fact, NRef) and fact.symbol_id == target:
            return
        self._install_fact(target, fact)

    def kill_targets(self, targets: tuple[SymbolId, ...]) -> None:
        pending = list(targets)
        seen: set[SymbolId] = set()
        while pending:
            sid = pending.pop()
            if sid in seen:
                continue
            seen.add(sid)
            pending.extend(self._dependents_by_source.get(sid, ()))
        for sid in seen:
            self._drop_fact(sid)

    def invalidate(self, target: SymbolId) -> None:
        self.kill_targets((target,))

    @classmethod
    def join(cls, envs: list[_FactEnv]) -> _FactEnv:
        if not envs:
            return cls()

        common = set(envs[0]._facts)
        for env in envs[1:]:
            common &= set(env._facts)

        joined = cls()
        for sid in common:
            fact = envs[0]._facts[sid]
            if all(env._facts[sid] == fact for env in envs[1:]):
                joined._install_fact(sid, fact)
        return joined

    def _resolve_ref(self, ref: NRef) -> _FactExpr:
        current: _FactExpr = ref
        seen: set[SymbolId] = set()
        while isinstance(current, NRef):
            if current.symbol_id in seen:
                return current
            seen.add(current.symbol_id)
            next_fact = self._facts.get(current.symbol_id)
            if next_fact is None:
                return current
            current = next_fact
        return current

    def _canonical_fact(self, expr: NExpr) -> _FactExpr | None:
        if isinstance(expr, NConst):
            return expr
        if isinstance(expr, NRef):
            return self._resolve_ref(expr)
        return None

    def _install_fact(self, target: SymbolId, fact: _FactExpr) -> None:
        self._facts[target] = fact
        sources: set[SymbolId] = set()
        if isinstance(fact, NRef):
            sources.add(fact.symbol_id)
            self._dependents_by_source.setdefault(fact.symbol_id, set()).add(target)
        self._sources_by_target[target] = sources

    def _drop_fact(self, target: SymbolId) -> None:
        old_sources = self._sources_by_target.pop(target, set())
        for source in old_sources:
            dependents = self._dependents_by_source.get(source)
            if dependents is None:
                continue
            dependents.discard(target)
            if not dependents:
                self._dependents_by_source.pop(source, None)
        self._facts.pop(target, None)


def _entry_env(returns: tuple[SymbolId, ...]) -> _FactEnv:
    env = _FactEnv()
    env.assign_zero_targets(returns)
    return env


def _rewrite_block(block: NBlock, env: _FactEnv) -> _BlockRewrite:
    defs = tuple(_rewrite_function_def(fdef) for fdef in block.defs)
    stmts: list[NStmt] = []
    current_env = env
    for stmt in block.stmts:
        result = _rewrite_stmt(stmt, current_env)
        stmts.extend(result.stmts)
        current_env = result.env
        if not result.falls_through:
            return _BlockRewrite.stop_with(
                NBlock(defs=defs, stmts=tuple(stmts)),
                current_env,
            )
    return _BlockRewrite.continue_with(
        NBlock(defs=defs, stmts=tuple(stmts)),
        current_env,
    )


def _rewrite_binding(stmt: NBind | NAssign, env: _FactEnv) -> _StmtRewrite:
    if isinstance(stmt, NBind) and stmt.expr is None:
        next_env = env.copy()
        next_env.assign_zero_targets(stmt.targets)
        return _StmtRewrite.continue_with((stmt,), next_env)

    expr = stmt.expr
    assert expr is not None

    rewritten_expr = env.rewrite_expr(expr)
    next_env = env.copy()
    if len(stmt.targets) == 1:
        next_env.assign_expr(stmt.targets[0], rewritten_expr)
    else:
        next_env.kill_targets(stmt.targets)

    if isinstance(stmt, NBind):
        rewritten_stmt: NStmt = NBind(
            targets=stmt.targets,
            target_names=stmt.target_names,
            expr=rewritten_expr,
        )
    else:
        rewritten_stmt = NAssign(
            targets=stmt.targets,
            target_names=stmt.target_names,
            expr=rewritten_expr,
        )
    return _StmtRewrite.continue_with((rewritten_stmt,), next_env)


def _nest_block(block_result: _BlockRewrite) -> _StmtRewrite:
    """Preserve a rewritten block as a nested runtime statement."""
    if block_result.falls_through:
        return _StmtRewrite.continue_with(
            (block_result.block,),
            block_result.env,
        )
    return _StmtRewrite.stop_with(
        (block_result.block,),
        block_result.env,
    )


def _splice_block(block_result: _BlockRewrite) -> _StmtRewrite:
    """Flatten a rewritten block when it does not introduce a new scope."""
    if block_result.block.defs:
        return _nest_block(block_result)
    if block_result.falls_through:
        return _StmtRewrite.continue_with(block_result.block.stmts, block_result.env)
    return _StmtRewrite.stop_with(block_result.block.stmts, block_result.env)


def _rewrite_stmt(stmt: NStmt, env: _FactEnv) -> _StmtRewrite:
    if isinstance(stmt, (NBind, NAssign)):
        return _rewrite_binding(stmt, env)

    if isinstance(stmt, NExprEffect):
        return _StmtRewrite.continue_with(
            (NExprEffect(expr=env.rewrite_expr(stmt.expr)),),
            env,
        )

    if isinstance(stmt, NIf):
        cond = env.rewrite_expr(stmt.condition)
        cond_truthy = const_truthy(cond)
        if cond_truthy is not None:
            if not cond_truthy:
                return _StmtRewrite.continue_with((), env)
            return _splice_block(_rewrite_block(stmt.then_body, env))

        then_result = _rewrite_block(stmt.then_body, env.copy())
        joined_env = _FactEnv.join(
            [env] + ([then_result.env] if then_result.falls_through else [])
        )
        return _StmtRewrite.continue_with(
            (
                NIf(
                    condition=cond,
                    then_body=then_result.block,
                ),
            ),
            joined_env,
        )

    if isinstance(stmt, NSwitch):
        disc = env.rewrite_expr(stmt.discriminant)
        disc_value = const_value(disc)
        if disc_value is not None:
            for case in stmt.cases:
                if case.value.value == disc_value:
                    return _splice_block(_rewrite_block(case.body, env))
            if stmt.default is None:
                return _StmtRewrite.continue_with((), env)
            return _splice_block(_rewrite_block(stmt.default, env))

        rewritten_cases: list[NSwitchCase] = []
        fallthrough_envs: list[_FactEnv] = []
        for case in stmt.cases:
            case_result = _rewrite_block(case.body, env.copy())
            rewritten_cases.append(
                NSwitchCase(value=case.value, body=case_result.block)
            )
            if case_result.falls_through:
                fallthrough_envs.append(case_result.env)

        rewritten_default = None
        if stmt.default is not None:
            default_result = _rewrite_block(stmt.default, env.copy())
            rewritten_default = default_result.block
            if default_result.falls_through:
                fallthrough_envs.append(default_result.env)
        else:
            fallthrough_envs.append(env)

        return _StmtRewrite(
            stmts=(
                NSwitch(
                    discriminant=disc,
                    cases=tuple(rewritten_cases),
                    default=rewritten_default,
                ),
            ),
            env=_FactEnv.join(fallthrough_envs),
            falls_through=bool(fallthrough_envs),
        )

    if isinstance(stmt, NFor):
        return _rewrite_for(stmt, env)

    if isinstance(stmt, NLeave):
        return _StmtRewrite.stop_with((stmt,), env)

    if isinstance(stmt, NBlock):
        return _nest_block(_rewrite_block(stmt, env))

    assert_never(stmt)


def _rewrite_for(stmt: NFor, env: _FactEnv) -> _StmtRewrite:
    """Rewrite one loop using a localized loop-head fact fixpoint."""
    init_result = _rewrite_block(stmt.init, env)
    if not init_result.falls_through:
        return _loop_preamble_result(
            env=init_result.env,
            falls_through=False,
            init=init_result.block,
        )

    pre_setup_env = init_result.env
    loop_result: (
        tuple[
            _BlockRewrite | None,
            _FactEnv,
            NExpr,
            _BlockRewrite,
            _BlockRewrite,
        ]
        | None
    ) = None

    while True:
        working_env = pre_setup_env.copy()
        if stmt.condition_setup is not None:
            setup_result = _rewrite_block(stmt.condition_setup, working_env)
            cond_env = setup_result.env
            if not setup_result.falls_through:
                return _loop_preamble_result(
                    env=setup_result.env,
                    falls_through=False,
                    init=init_result.block,
                    condition_setup=setup_result.block,
                )
        else:
            setup_result = None
            cond_env = working_env

        cond = cond_env.rewrite_expr(stmt.condition)
        cond_truthy = const_truthy(cond)
        if cond_truthy is False:
            return _loop_preamble_result(
                env=cond_env,
                falls_through=True,
                init=init_result.block,
                condition_setup=setup_result.block if setup_result else None,
            )

        body_result = _rewrite_block(stmt.body, cond_env.copy())
        if body_result.falls_through:
            post_result = _rewrite_block(stmt.post, body_result.env.copy())
        else:
            post_result = _BlockRewrite.continue_with(NBlock(), body_result.env)
        loop_result = (setup_result, cond_env, cond, body_result, post_result)

        backedge_envs: list[_FactEnv] = []
        if body_result.falls_through and post_result.falls_through:
            backedge_envs.append(post_result.env)

        next_pre_setup = _FactEnv.join([init_result.env] + backedge_envs)
        if next_pre_setup.same_facts(pre_setup_env):
            pre_setup_env = next_pre_setup
            break
        pre_setup_env = next_pre_setup

    assert loop_result is not None
    setup_result, cond_env, cond, body_result, post_result = loop_result

    cond_truthy = const_truthy(cond)
    loop_falls_through = cond_truthy is not True
    loop_exit_env = cond_env if loop_falls_through else _FactEnv()

    return _StmtRewrite(
        stmts=(
            NFor(
                init=init_result.block,
                condition=cond,
                condition_setup=setup_result.block if setup_result else None,
                post=post_result.block,
                body=body_result.block,
            ),
        ),
        env=loop_exit_env,
        falls_through=loop_falls_through,
    )


def _sequential_block(*blocks: NBlock | None) -> NBlock | None:
    """Build one executable block from sequential sub-blocks."""

    executed = tuple(
        block for block in blocks if block is not None and (block.defs or block.stmts)
    )
    if not executed:
        return None
    return NBlock(stmts=executed)


def _loop_preamble_result(
    *,
    env: _FactEnv,
    falls_through: bool,
    init: NBlock | None,
    condition_setup: NBlock | None = None,
) -> _StmtRewrite:
    preamble = _sequential_block(init, condition_setup)
    stmts: tuple[NStmt, ...] = (preamble,) if preamble is not None else ()
    if falls_through:
        return _StmtRewrite.continue_with(stmts, env)
    return _StmtRewrite.stop_with(stmts, env)


def _rewrite_function_def(fdef: NFunctionDef) -> NFunctionDef:
    rewritten = _rewrite_block(fdef.body, _entry_env(fdef.returns))
    return NFunctionDef(
        name=fdef.name,
        symbol_id=fdef.symbol_id,
        params=fdef.params,
        param_names=fdef.param_names,
        returns=fdef.returns,
        return_names=fdef.return_names,
        body=rewritten.block,
    )


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def simplify_normalized(func: NormalizedFunction) -> NormalizedFunction:
    """Simplify a raw normalized function before leave and memory lowering."""
    rewritten = _rewrite_block(func.body, _entry_env(func.returns))
    return NormalizedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=rewritten.block,
    )
