from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class IntLit:
    value: int


@dataclass(frozen=True)
class Var:
    name: str


@dataclass(frozen=True)
class Call:
    name: str
    args: tuple["Expr", ...]
    binding_token_idx: int | None = None


@dataclass(frozen=True)
class Ite:
    """Conditional value: ``if cond ≠ 0 then if_true else if_false``."""

    cond: "Expr"
    if_true: "Expr"
    if_false: "Expr"


@dataclass(frozen=True)
class Project:
    """Projection of the Nth return value from a multi-return call."""

    index: int
    total: int
    inner: "Expr"


Expr = IntLit | Var | Call | Ite | Project


@dataclass(frozen=True)
class Assignment:
    target: str
    expr: Expr


@dataclass(frozen=True)
class ConditionalBranch:
    """A single branch of a restricted-IR conditional."""

    assignments: tuple["ModelStatement", ...]
    outputs: tuple["Expr", ...]


@dataclass(frozen=True)
class ConditionalBlock:
    """A restricted-IR conditional with explicit outputs for both branches."""

    condition: Expr
    output_vars: tuple[str, ...]
    then_branch: ConditionalBranch
    else_branch: ConditionalBranch


ModelStatement = Assignment | ConditionalBlock


@dataclass(frozen=True)
class FunctionModel:
    fn_name: str
    assignments: tuple[ModelStatement, ...]
    param_names: tuple[str, ...] = ("x",)
    return_names: tuple[str, ...] = ("z",)


ModelValue = int | tuple[int, ...]
