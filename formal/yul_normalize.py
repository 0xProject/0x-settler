"""
Lower a resolved Yul syntax AST into the normalized imperative IR.

This is a 1:1 structural transformation.  Each syntax AST node maps to
exactly one normalized IR node, with string-based names replaced by
``SymbolId`` references from the binder resolver.

No constant folding, block flattening, or helper inlining occurs here.
"""

from __future__ import annotations

import ast
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
from yul_ast import (
    AssignStmt,
    Block,
    BlockStmt,
    BuiltinTarget,
    CallExpr,
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
    StringExpr,
    SwitchStmt,
    SynExpr,
    SynStmt,
    TopLevelFunctionTarget,
    UnresolvedTarget,
)
from yul_resolve import ResolutionResult


def normalize_function(
    func: FunctionDef,
    result: ResolutionResult,
) -> NormalizedFunction:
    """Lower a resolved ``FunctionDef`` into a ``NormalizedFunction``."""
    params = tuple(result.declarations[s] for s in func.param_spans)
    returns = tuple(result.declarations[s] for s in func.return_spans)
    body = _lower_block(func.body, result)
    return NormalizedFunction(
        name=func.name,
        params=params,
        param_names=func.params,
        returns=returns,
        return_names=func.returns,
        body=body,
    )


def _lower_block(block: Block, r: ResolutionResult) -> NBlock:
    stmts: list[NStmt] = []
    for stmt in block.stmts:
        stmts.append(_lower_stmt(stmt, r))
    return NBlock(tuple(stmts))


def _lower_stmt(stmt: SynStmt, r: ResolutionResult) -> NStmt:
    if isinstance(stmt, LetStmt):
        targets = tuple(r.declarations[s] for s in stmt.target_spans)
        expr = _lower_expr(stmt.init, r) if stmt.init is not None else None
        return NBind(targets=targets, target_names=stmt.targets, expr=expr)

    if isinstance(stmt, AssignStmt):
        targets = tuple(r.references[s] for s in stmt.target_spans)
        expr = _lower_expr(stmt.expr, r)
        return NAssign(targets=targets, target_names=stmt.targets, expr=expr)

    if isinstance(stmt, ExprStmt):
        return NExprEffect(expr=_lower_expr(stmt.expr, r))

    if isinstance(stmt, IfStmt):
        return NIf(
            condition=_lower_expr(stmt.condition, r),
            then_body=_lower_block(stmt.body, r),
        )

    if isinstance(stmt, SwitchStmt):
        cases = tuple(
            NSwitchCase(
                value=NConst(value=_const_value(c.value)),
                body=_lower_block(c.body, r),
            )
            for c in stmt.cases
        )
        default = (
            _lower_block(stmt.default.body, r) if stmt.default is not None else None
        )
        return NSwitch(
            discriminant=_lower_expr(stmt.discriminant, r),
            cases=cases,
            default=default,
        )

    if isinstance(stmt, ForStmt):
        return NFor(
            init=_lower_block(stmt.init, r),
            condition=_lower_expr(stmt.condition, r),
            condition_setup=None,
            post=_lower_block(stmt.post, r),
            body=_lower_block(stmt.body, r),
        )

    if isinstance(stmt, LeaveStmt):
        return NLeave()

    if isinstance(stmt, BlockStmt):
        return _lower_block(stmt.block, r)

    if isinstance(stmt, FunctionDefStmt):
        f = stmt.func
        sym_id = r.declarations[f.name_span]
        params = tuple(r.declarations[s] for s in f.param_spans)
        returns = tuple(r.declarations[s] for s in f.return_spans)
        return NFunctionDef(
            name=f.name,
            symbol_id=sym_id,
            params=params,
            param_names=f.params,
            returns=returns,
            return_names=f.returns,
            body=_lower_block(f.body, r),
        )

    assert_never(stmt)


def _lower_expr(expr: SynExpr, r: ResolutionResult) -> NExpr:
    if isinstance(expr, IntExpr):
        return NConst(value=expr.value)

    if isinstance(expr, NameExpr):
        sid = r.references[expr.span]
        return NRef(symbol_id=sid, name=expr.name)

    if isinstance(expr, StringExpr):
        # Decode the literal contents first, then lower them to the
        # right-padded bytes32-style integer used by Yul.
        raw = _decode_string_literal(expr.text)
        if len(raw) > 32:
            raise ParseError(
                f"String literal {expr.text!r} exceeds 32 bytes " f"({len(raw)} bytes)"
            )
        padded = raw.ljust(32, b"\x00")
        return NConst(value=int.from_bytes(padded, "big"))

    if isinstance(expr, CallExpr):
        args = tuple(_lower_expr(a, r) for a in expr.args)
        target = r.call_targets[expr.name_span]

        if isinstance(target, BuiltinTarget):
            return NBuiltinCall(op=target.name, args=args)
        if isinstance(target, LocalFunctionTarget):
            return NLocalCall(symbol_id=target.id, name=target.name, args=args)
        if isinstance(target, TopLevelFunctionTarget):
            return NTopLevelCall(name=target.name, args=args)
        if isinstance(target, UnresolvedTarget):
            return NUnresolvedCall(name=target.name, args=args)

        assert_never(target)

    assert_never(expr)


def _const_value(expr: SynExpr) -> int:
    """Extract the integer value from a switch case literal."""
    if isinstance(expr, IntExpr):
        return expr.value
    raise ParseError(f"Switch case value must be an integer, got {type(expr).__name__}")


def _decode_string_literal(token_text: str) -> bytes:
    """Decode a tokenized Yul string literal into its UTF-8 bytes."""
    try:
        decoded = ast.literal_eval(token_text)
    except (SyntaxError, ValueError) as err:
        raise ParseError(f"Invalid Yul string literal {token_text!r}") from err
    if not isinstance(decoded, str):
        raise ParseError(f"Invalid Yul string literal {token_text!r}")
    return decoded.encode("utf-8")
