"""
Memory model lowering on normalized IR.

Resolves ``NStore`` (mstore) and ``NBuiltinCall("mload", ...)`` to
direct value references.  After this pass, the IR contains no memory
operations — all mload calls are replaced with the expressions
previously stored at those addresses.

The memory model enforces:
- Constant addresses (compile-time evaluable)
- 32-byte alignment
- Single write per address (no aliasing/overwriting)
- All reads reference a prior write
"""

from __future__ import annotations

from norm_constprop import fold_expr
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
from norm_walk import map_expr
from yul_ast import ParseError, SymbolId

# ---------------------------------------------------------------------------
# Address validation
# ---------------------------------------------------------------------------


def _resolve_const_addr(expr: NExpr, op: str) -> int:
    """Fold an address expression to a constant int. Validates alignment."""
    folded = fold_expr(expr)
    if not isinstance(folded, NConst):
        raise ParseError(
            f"Non-constant {op} address: {expr!r}. "
            f"The memory model requires constant 32-byte-aligned addresses."
        )
    addr = folded.value
    if addr % 32 != 0:
        raise ParseError(f"Unaligned {op} address {addr} (must be 32-byte aligned)")
    return addr


# ---------------------------------------------------------------------------
# Reject memory ops inside control flow
# ---------------------------------------------------------------------------


def _reject_memory_ops_in_block(block: NBlock, context: str) -> None:
    """Raise if a block contains any memory operations (straight-line only)."""
    for stmt in block.stmts:
        if isinstance(stmt, NStore):
            raise ParseError(
                f"NStore inside control flow ({context}). "
                f"The memory model requires straight-line memory operations."
            )
        if isinstance(stmt, NExprEffect):
            if isinstance(stmt.expr, NBuiltinCall) and stmt.expr.op == "mstore":
                raise ParseError(
                    f"mstore inside control flow ({context}). "
                    f"The memory model requires straight-line memory operations."
                )
        if isinstance(stmt, (NBind, NAssign)):
            if stmt.expr is not None and _expr_has_mload(stmt.expr):
                raise ParseError(
                    f"mload inside control flow ({context}). "
                    f"The memory model requires straight-line memory operations."
                )
        if isinstance(stmt, NIf):
            _reject_memory_ops_in_block(stmt.then_body, context)
        if isinstance(stmt, NBlock):
            _reject_memory_ops_in_block(stmt, context)
        if isinstance(stmt, NFor):
            _reject_memory_ops_in_block(stmt.init, context)
            _reject_memory_ops_in_block(stmt.post, context)
            _reject_memory_ops_in_block(stmt.body, context)


def _expr_has_mload(expr: NExpr) -> bool:
    """Check if an expression contains an mload call."""
    from norm_walk import for_each_expr

    found: list[bool] = [False]

    def check(e: NExpr) -> None:
        if isinstance(e, NBuiltinCall) and e.op == "mload":
            found[0] = True

    for_each_expr(expr, check)
    return found[0]


# ---------------------------------------------------------------------------
# Expression-level mload resolution
# ---------------------------------------------------------------------------


def _resolve_memory_in_expr(expr: NExpr, mem: dict[int, NExpr]) -> NExpr:
    """Replace ``mload(addr)`` calls with the stored value from *mem*."""

    def rewrite(e: NExpr) -> NExpr:
        if isinstance(e, NBuiltinCall) and e.op == "mload" and len(e.args) == 1:
            addr = _resolve_const_addr(e.args[0], "mload")
            if addr not in mem:
                available = sorted(mem.keys())
                raise ParseError(
                    f"mload from address {addr} which has no prior mstore. "
                    f"Available addresses: {available}"
                )
            return mem[addr]
        return e

    return map_expr(expr, rewrite)


# ---------------------------------------------------------------------------
# Block-level lowering
# ---------------------------------------------------------------------------


def _lower_block(block: NBlock, mem: dict[int, NExpr]) -> NBlock:
    """Lower memory operations in a block."""
    stmts: list[NStmt] = []
    for stmt in block.stmts:
        _lower_stmt(stmt, mem, stmts)
    return NBlock(tuple(stmts))


def _lower_stmt(
    stmt: NStmt,
    mem: dict[int, NExpr],
    out: list[NStmt],
) -> None:
    if isinstance(stmt, NStore):
        addr = _resolve_const_addr(stmt.addr, "mstore")
        if addr in mem:
            raise ParseError(
                f"Duplicate mstore to address {addr}. "
                f"The memory model forbids aliasing or overwriting."
            )
        # Resolve any mload references in the stored value.
        resolved_value = _resolve_memory_in_expr(stmt.value, mem)
        mem[addr] = resolved_value
        # NStore is consumed — not emitted to output.
        return

    if isinstance(stmt, NBind):
        if stmt.expr is not None:
            new_expr = _resolve_memory_in_expr(stmt.expr, mem)
            out.append(
                NBind(
                    targets=stmt.targets,
                    target_names=stmt.target_names,
                    expr=new_expr,
                )
            )
        else:
            out.append(stmt)
        return

    if isinstance(stmt, NAssign):
        new_expr = _resolve_memory_in_expr(stmt.expr, mem)
        out.append(
            NAssign(
                targets=stmt.targets,
                target_names=stmt.target_names,
                expr=new_expr,
            )
        )
        return

    if isinstance(stmt, NExprEffect):
        # NExprEffect(NBuiltinCall("mstore", (addr, value))) is a bare
        # mstore from Yul source — treat the same as NStore.
        if (
            isinstance(stmt.expr, NBuiltinCall)
            and stmt.expr.op == "mstore"
            and len(stmt.expr.args) == 2
        ):
            addr_expr, value_expr = stmt.expr.args
            addr = _resolve_const_addr(addr_expr, "mstore")
            if addr in mem:
                raise ParseError(
                    f"Duplicate mstore to address {addr}. "
                    f"The memory model forbids aliasing or overwriting."
                )
            resolved_value = _resolve_memory_in_expr(value_expr, mem)
            mem[addr] = resolved_value
            return  # Consumed — not emitted
        new_expr = _resolve_memory_in_expr(stmt.expr, mem)
        out.append(NExprEffect(expr=new_expr))
        return

    if isinstance(stmt, NIf):
        _reject_memory_ops_in_block(stmt.then_body, "if-body")
        new_cond = _resolve_memory_in_expr(stmt.condition, mem)
        out.append(NIf(condition=new_cond, then_body=stmt.then_body))
        return

    if isinstance(stmt, NSwitch):
        for case in stmt.cases:
            _reject_memory_ops_in_block(case.body, "switch-case")
        if stmt.default is not None:
            _reject_memory_ops_in_block(stmt.default, "switch-default")
        new_disc = _resolve_memory_in_expr(stmt.discriminant, mem)
        out.append(stmt)
        return

    if isinstance(stmt, NFor):
        _reject_memory_ops_in_block(stmt.init, "for-init")
        if stmt.condition_setup is not None:
            _reject_memory_ops_in_block(stmt.condition_setup, "for-condition-setup")
        _reject_memory_ops_in_block(stmt.post, "for-post")
        _reject_memory_ops_in_block(stmt.body, "for-body")
        out.append(stmt)
        return

    if isinstance(stmt, (NLeave, NFunctionDef)):
        out.append(stmt)
        return

    if isinstance(stmt, NBlock):
        out.append(_lower_block(stmt, mem))
        return

    raise ParseError(f"Unexpected statement in memory lowering: {type(stmt).__name__}")


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def lower_memory(func: NormalizedFunction) -> NormalizedFunction:
    """Resolve memory operations to direct value references.

    Removes ``NStore`` statements and replaces ``mload(addr)`` with
    the expression previously stored at that address.  Raises
    ``ParseError`` if any memory constraint is violated.
    """
    mem: dict[int, NExpr] = {}
    new_body = _lower_block(func.body, mem)
    return NormalizedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=new_body,
    )
