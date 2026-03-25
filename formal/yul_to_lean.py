"""
Shared infrastructure for generating Lean models from Yul IR.

Provides:
- Yul tokenizer and recursive-descent parser
- AST types (IntLit, Var, Call, Ite, Project, Assignment, FunctionModel)
- Yul → FunctionModel conversion (copy propagation + demangling)
- Explicit translation pipelines: raw translation + optional transforms
- Lean expression emission
- Common Lean source scaffolding
"""

from __future__ import annotations

import argparse
import enum
import pathlib
import re
import sys
from collections import Counter
from dataclasses import dataclass
from typing import Callable, assert_never


class ParseError(RuntimeError):
    pass


class EvaluationError(RuntimeError):
    pass


# ---------------------------------------------------------------------------
# AST nodes (shared by Yul parser and Lean emitter)
# ---------------------------------------------------------------------------


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
    """A single branch of a restricted-IR conditional.

    ``assignments`` are the branch-local let-bindings.
    ``outputs`` lists the variables whose values become the outer
    ``ConditionalBlock.output_vars`` when this branch is taken.
    """

    assignments: tuple[Assignment, ...]
    outputs: tuple[str, ...]


@dataclass(frozen=True)
class ConditionalBlock:
    """A restricted-IR conditional with explicit outputs for both branches.

    ``output_vars`` are the outer variables bound by the conditional.
    ``then_branch`` and ``else_branch`` each carry both their local
    assignments and the exact variables that feed the outer outputs.
    """

    condition: Expr
    output_vars: tuple[str, ...]
    then_branch: ConditionalBranch
    else_branch: ConditionalBranch


# A model statement is either a plain assignment or a conditional block.
ModelStatement = Assignment | ConditionalBlock


@dataclass(frozen=True)
class FunctionModel:
    fn_name: str
    assignments: tuple[ModelStatement, ...]
    param_names: tuple[str, ...] = ("x",)
    return_names: tuple[str, ...] = ("z",)


ModelValue = int | tuple[int, ...]


@dataclass(frozen=True)
class TranslationPipeline:
    """Controls which non-literal passes run after raw model construction."""

    name: str
    hoist_repeated_calls: bool
    prune_dead_assignments: bool


RAW_TRANSLATION_PIPELINE = TranslationPipeline(
    name="raw",
    hoist_repeated_calls=False,
    prune_dead_assignments=False,
)

OPTIMIZED_TRANSLATION_PIPELINE = TranslationPipeline(
    name="optimized",
    # Zero-assignment elision is not semantics-preserving in general. Keep the
    # optimized default limited to passes with direct equivalence tests.
    hoist_repeated_calls=True,
    prune_dead_assignments=True,
)

TRANSLATION_PIPELINES = {
    RAW_TRANSLATION_PIPELINE.name: RAW_TRANSLATION_PIPELINE,
    OPTIMIZED_TRANSLATION_PIPELINE.name: OPTIMIZED_TRANSLATION_PIPELINE,
}


# ---------------------------------------------------------------------------
# Yul tokenizer
# ---------------------------------------------------------------------------

YUL_TOKEN_RE = re.compile(
    r"""
    (?P<doccomment>///[^\n]*)
  | (?P<linecomment>//[^\n]*)
  | (?P<ws>\s+)
  | (?P<string>"(?:[^"\\]|\\.)*")
  | (?P<hex>0x[0-9a-fA-F]+)
  | (?P<num>[0-9]+)
  | (?P<assign>:=)
  | (?P<arrow>->)
  | (?P<ident>[A-Za-z_.$][A-Za-z0-9_.$]*)
  | (?P<lbrace>\{)
  | (?P<rbrace>\})
  | (?P<lparen>\()
  | (?P<rparen>\))
  | (?P<comma>,)
""",
    re.VERBOSE,
)

_TOKEN_KIND_MAP = {
    "doccomment": None,
    "linecomment": None,
    "ws": None,
    "string": "string",
    "hex": "num",
    "num": "num",
    "assign": ":=",
    "arrow": "->",
    "ident": "ident",
    "lbrace": "{",
    "rbrace": "}",
    "lparen": "(",
    "rparen": ")",
    "comma": ",",
}


def tokenize_yul(source: str) -> list[tuple[str, str]]:
    """Tokenize Yul IR source into a list of (kind, text) pairs.

    Comments and whitespace are discarded.  String literals are kept as
    single tokens so that braces inside ``"contract Foo {..."`` never
    confuse downstream code.
    """
    tokens: list[tuple[str, str]] = []
    pos = 0
    length = len(source)
    while pos < length:
        m = YUL_TOKEN_RE.match(source, pos)
        if not m:
            snippet = source[pos : pos + 30]
            raise ParseError(f"Yul tokenizer stuck at position {pos}: {snippet!r}")
        pos = m.end()
        raw_kind = m.lastgroup
        if raw_kind is None:
            raise ParseError(
                f"Yul tokenizer produced a match with no token kind at position {pos}"
            )
        kind = _TOKEN_KIND_MAP[raw_kind]
        if kind is None:
            continue
        text = m.group()
        tokens.append((kind, text))
    return tokens


# ---------------------------------------------------------------------------
# Yul recursive-descent parser
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ParsedIfBlock:
    """Raw parsed ``if cond { body }`` or ``switch`` from Yul, before demangling.

    When ``else_body`` is present, this represents an if/else or a
    ``switch expr case 0 { else_body } default { body }`` construct.

    ``has_leave`` always refers to the ``body`` branch. For ``switch``
    statements we normalize the parsed shape so that, when exactly one branch
    contains ``leave``, that branch is placed in ``body`` and ``condition`` is
    inverted with ``iszero(...)`` when necessary.
    """

    condition: Expr
    body: tuple["PlainAssignment", ...]
    has_leave: bool = False
    else_body: tuple["PlainAssignment", ...] | None = None
    body_expr_stmts: tuple[Expr, ...] = ()
    else_body_expr_stmts: tuple[Expr, ...] = ()


@dataclass(frozen=True)
class MemoryWrite:
    """A supported straight-line ``mstore(addr, value)`` statement."""

    address: Expr
    value: Expr


@dataclass(frozen=True)
class FromWriteEffect:
    """Deferred lowering for the exact emitted ``uint512.from(x_hi, x_lo)`` helper."""

    ptr: Expr
    hi: Expr
    lo: Expr
    lo_addr: Expr

    def lower(self) -> tuple[MemoryWrite, MemoryWrite]:
        return (
            MemoryWrite(self.ptr, self.hi),
            MemoryWrite(self.lo_addr, self.lo),
        )


@dataclass(frozen=True)
class PlainAssignment:
    target: str
    expr: Expr
    is_declaration: bool = False


# A raw parsed statement is either an assignment, a supported memory write,
# or an if/switch block.
RawStatement = PlainAssignment | MemoryWrite | ParsedIfBlock


@dataclass
class YulFunction:
    """Parsed representation of a single Yul ``function`` definition."""

    yul_name: str
    params: list[str]
    rets: list[str]
    assignments: list[RawStatement]
    # Bare expression-statements that are not part of the supported memory
    # subset. The translator rejects any function that still contains them.
    expr_stmts: list[Expr] | None = None
    token_idx: int | None = None

    @property
    def param(self) -> str:
        """Backward-compat accessor for single-parameter functions."""
        if len(self.params) != 1:
            raise ValueError(
                f"YulFunction {self.yul_name!r} has {len(self.params)} params; "
                f"use .params instead of .param"
            )
        return self.params[0]

    @property
    def ret(self) -> str:
        """Backward-compat accessor for single-return functions."""
        if len(self.rets) != 1:
            raise ValueError(
                f"YulFunction {self.yul_name!r} has {len(self.rets)} return vars; "
                f"use .rets instead of .ret"
            )
        return self.rets[0]


@dataclass(frozen=True)
class CollectedFunctions:
    """All helper functions discovered during a collection pass.

    ``functions`` contains successfully parsed helpers.
    ``rejected`` records helper names whose bodies were rejected, along with
    the parse error that explains why.
    """

    functions: dict[str, YulFunction]
    rejected: dict[str, str]


@dataclass(frozen=True)
class ReferenceExprStatement:
    expr: Expr


@dataclass(frozen=True)
class ReferenceBlock:
    scope: "ReferenceScope"


@dataclass(frozen=True)
class ReferenceIf:
    condition: Expr
    body: "ReferenceScope"
    else_body: "ReferenceScope | None" = None


@dataclass(frozen=True)
class ReferenceSwitchCase:
    value: Expr
    body: "ReferenceScope"


@dataclass(frozen=True)
class ReferenceSwitch:
    discriminant: Expr
    cases: tuple[ReferenceSwitchCase, ...]
    default: "ReferenceScope | None" = None


@dataclass(frozen=True)
class ReferenceFor:
    init: "ReferenceScope"
    condition: Expr
    post: "ReferenceScope"
    body: "ReferenceScope"


@dataclass(frozen=True)
class ReferenceLeave:
    pass


ReferenceStatement = (
    ReferenceExprStatement
    | ReferenceBlock
    | ReferenceIf
    | ReferenceSwitch
    | ReferenceFor
    | ReferenceLeave
)


@dataclass(frozen=True)
class ReferenceLocalFunction:
    name: str
    body: "ReferenceScope"


@dataclass(frozen=True)
class ReferenceScope:
    statements: tuple[ReferenceStatement, ...]
    local_functions: tuple[ReferenceLocalFunction, ...] = ()


@dataclass(frozen=True)
class ReferenceAnalysisResult:
    live_references: bool
    dead_references: bool
    definitely_terminates: bool


class _TokenReader:
    """Shared token-stream primitives for Yul parsers.

    Holds a flat token list and a cursor, plus low-level consumption
    helpers and the common expression parser.  Subclasses add
    domain-specific parsing logic.
    """

    def __init__(self, tokens: list[tuple[str, str]]) -> None:
        self.tokens = tokens
        self.i = 0

    def _at_end(self) -> bool:
        return self.i >= len(self.tokens)

    def _peek(self) -> tuple[str, str] | None:
        if self._at_end():
            return None
        return self.tokens[self.i]

    def _peek_kind(self) -> str | None:
        tok = self._peek()
        return tok[0] if tok else None

    def _pop(self) -> tuple[str, str]:
        tok = self._peek()
        if tok is None:
            raise ParseError("Unexpected end of Yul token stream")
        self.i += 1
        return tok

    def _expect(self, kind: str) -> str:
        k, text = self._pop()
        if k != kind:
            raise ParseError(f"Expected {kind!r}, got {k!r} ({text!r})")
        return text

    def _expect_ident(self) -> str:
        return self._expect("ident")

    def _parse_expr(self) -> Expr:
        kind, text = self._pop()
        if kind == "num":
            return IntLit(int(text, 0))
        if kind == "ident":
            if self._peek_kind() == "(":
                self._pop()
                args: list[Expr] = []
                if self._peek_kind() != ")":
                    while True:
                        args.append(self._parse_expr())
                        if self._peek_kind() == ",":
                            self._pop()
                            continue
                        break
                self._expect(")")
                return Call(text, tuple(args))
            return Var(text)
        if kind == "string":
            return Var(text)
        raise ParseError(f"Expected expression, got {kind!r} ({text!r})")


class _ReferenceScopeParser(_TokenReader):
    """Parse a lexical Yul scope for helper-reference analysis.

    This parser is intentionally broader than the main model-generation parser:
    it keeps local function definitions and lexical blocks so dependency
    analysis can follow real scope rules, while still reusing the same basic
    expression grammar.
    """

    def _parse_block(self) -> ReferenceScope:
        self._expect("{")
        scope = self.parse_scope()
        self._expect("}")
        return scope

    def _looks_like_assignment(self) -> bool:
        if self._peek_kind() != "ident":
            return False
        j = self.i + 1
        while j < len(self.tokens) and self.tokens[j][0] == ",":
            j += 1
            if j >= len(self.tokens) or self.tokens[j][0] != "ident":
                return False
            j += 1
        return j < len(self.tokens) and self.tokens[j][0] == ":="

    def _parse_let_statement(self) -> Expr | None:
        self._expect_ident()  # let
        self._expect_ident()
        while self._peek_kind() == ",":
            self._pop()
            self._expect_ident()
        if self._peek_kind() != ":=":
            return None
        self._pop()
        return self._parse_expr()

    def _parse_assignment_statement(self) -> Expr:
        self._expect_ident()
        while self._peek_kind() == ",":
            self._pop()
            self._expect_ident()
        self._expect(":=")
        return self._parse_expr()

    def _parse_function(self) -> ReferenceLocalFunction:
        fn_kw = self._expect_ident()
        if fn_kw != "function":
            raise ParseError(f"Expected 'function', got {fn_kw!r}")
        name = self._expect_ident()
        self._expect("(")
        if self._peek_kind() != ")":
            self._expect_ident()
            while self._peek_kind() == ",":
                self._pop()
                self._expect_ident()
        self._expect(")")
        if self._peek_kind() == "->":
            self._pop()
            self._expect_ident()
            while self._peek_kind() == ",":
                self._pop()
                self._expect_ident()
        body = self._parse_block()
        return ReferenceLocalFunction(name=name, body=body)

    def _parse_if(self) -> ReferenceIf:
        self._expect_ident()  # if
        condition = self._parse_expr()
        body = self._parse_block()
        return ReferenceIf(condition=condition, body=body)

    def _parse_switch(self) -> ReferenceSwitch:
        self._expect_ident()  # switch
        discriminant = self._parse_expr()
        cases: list[ReferenceSwitchCase] = []
        default: ReferenceScope | None = None
        while (
            not self._at_end()
            and self._peek_kind() == "ident"
            and self.tokens[self.i][1] in ("case", "default")
        ):
            branch = self._expect_ident()
            if branch == "case":
                value = self._parse_expr()
                cases.append(ReferenceSwitchCase(value=value, body=self._parse_block()))
            else:
                if default is not None:
                    raise ParseError("Duplicate 'default' in switch statement")
                default = self._parse_block()
        return ReferenceSwitch(
            discriminant=discriminant,
            cases=tuple(cases),
            default=default,
        )

    def _parse_for(self) -> ReferenceFor:
        self._expect_ident()  # for
        init = self._parse_block()
        condition = self._parse_expr()
        post = self._parse_block()
        body = self._parse_block()
        return ReferenceFor(init=init, condition=condition, post=post, body=body)

    def parse_scope(self) -> ReferenceScope:
        statements: list[ReferenceStatement] = []
        local_functions: list[ReferenceLocalFunction] = []

        while not self._at_end() and self._peek_kind() != "}":
            kind = self._peek_kind()
            if kind == "{":
                statements.append(ReferenceBlock(self._parse_block()))
                continue

            if kind == "ident":
                text = self.tokens[self.i][1]
                if text == "function":
                    local_functions.append(self._parse_function())
                    continue
                if text == "let":
                    expr = self._parse_let_statement()
                    if expr is not None:
                        statements.append(ReferenceExprStatement(expr))
                    continue
                if text == "leave":
                    self._pop()
                    statements.append(ReferenceLeave())
                    continue
                if text == "if":
                    statements.append(self._parse_if())
                    continue
                if text == "switch":
                    statements.append(self._parse_switch())
                    continue
                if text == "for":
                    statements.append(self._parse_for())
                    continue
                if self._looks_like_assignment():
                    statements.append(
                        ReferenceExprStatement(self._parse_assignment_statement())
                    )
                    continue

            if kind in ("ident", "num", "string"):
                statements.append(ReferenceExprStatement(self._parse_expr()))
                continue

            tok = self._peek()
            raise ParseError(
                f"Unsupported statement start {tok!r} in helper reference analysis"
            )

        return ReferenceScope(
            statements=tuple(statements),
            local_functions=tuple(local_functions),
        )


def _expr_reference_summary(
    expr: Expr,
    live_names: set[str],
    dead_names: set[str],
) -> ReferenceAnalysisResult:
    if isinstance(expr, (IntLit, Var)):
        return ReferenceAnalysisResult(False, False, False)
    if isinstance(expr, Ite):
        live = False
        dead = False
        for sub in (expr.cond, expr.if_true, expr.if_false):
            child = _expr_reference_summary(sub, live_names, dead_names)
            live = live or child.live_references
            dead = dead or child.dead_references
        return ReferenceAnalysisResult(live, dead, False)
    if isinstance(expr, Project):
        return _expr_reference_summary(expr.inner, live_names, dead_names)
    if isinstance(expr, Call):
        live = expr.name in live_names
        dead = expr.name in dead_names
        for arg in expr.args:
            child = _expr_reference_summary(arg, live_names, dead_names)
            live = live or child.live_references
            dead = dead or child.dead_references
        return ReferenceAnalysisResult(live, dead, False)
    assert_never(expr)


def _scope_reference_summary(
    scope: ReferenceScope,
    live_names: set[str],
    dead_names: set[str] | None = None,
) -> ReferenceAnalysisResult:
    if dead_names is None:
        dead_names = set()
    local_names = {fn.name for fn in scope.local_functions}
    live_referencing: set[str] = set()
    dead_referencing: set[str] = set()

    changed = True
    while changed:
        changed = False
        visible_live = (live_names - local_names) | live_referencing
        visible_dead = (
            (dead_names - local_names) | dead_referencing
        ) - live_referencing
        for local_fn in scope.local_functions:
            summary = _scope_reference_summary(
                local_fn.body,
                visible_live,
                visible_dead,
            )
            if summary.live_references and local_fn.name not in live_referencing:
                live_referencing.add(local_fn.name)
                dead_referencing.discard(local_fn.name)
                changed = True
                continue
            if (
                not summary.live_references
                and summary.dead_references
                and local_fn.name not in dead_referencing
            ):
                dead_referencing.add(local_fn.name)
                changed = True

    visible_live = (live_names - local_names) | live_referencing
    visible_dead = ((dead_names - local_names) | dead_referencing) - live_referencing
    live = False
    dead = False
    terminated = False
    for stmt in scope.statements:
        stmt_summary = _statement_reference_summary(
            stmt,
            visible_live,
            visible_dead,
        )
        if terminated:
            dead = dead or stmt_summary.live_references or stmt_summary.dead_references
            continue
        live = live or stmt_summary.live_references
        dead = dead or stmt_summary.dead_references
        terminated = stmt_summary.definitely_terminates
    return ReferenceAnalysisResult(live, dead, terminated)


def _statement_reference_summary(
    stmt: ReferenceStatement,
    live_names: set[str],
    dead_names: set[str],
) -> ReferenceAnalysisResult:
    if isinstance(stmt, ReferenceExprStatement):
        expr_summary = _expr_reference_summary(stmt.expr, live_names, dead_names)
        return ReferenceAnalysisResult(
            expr_summary.live_references,
            expr_summary.dead_references,
            False,
        )

    if isinstance(stmt, ReferenceLeave):
        return ReferenceAnalysisResult(False, False, True)

    if isinstance(stmt, ReferenceBlock):
        return _scope_reference_summary(stmt.scope, live_names, dead_names)

    if isinstance(stmt, ReferenceIf):
        cond_summary = _expr_reference_summary(stmt.condition, live_names, dead_names)

        const_cond = _try_const_eval(stmt.condition)
        if const_cond is not None:
            live = cond_summary.live_references
            dead = cond_summary.dead_references
            if const_cond != 0:
                chosen_summary = _scope_reference_summary(
                    stmt.body,
                    live_names,
                    dead_names,
                )
                live = live or chosen_summary.live_references
                dead = dead or chosen_summary.dead_references
                if stmt.else_body is not None:
                    dead_branch = _scope_reference_summary(
                        stmt.else_body,
                        live_names,
                        dead_names,
                    )
                    dead = (
                        dead
                        or dead_branch.live_references
                        or dead_branch.dead_references
                    )
                return ReferenceAnalysisResult(
                    live,
                    dead,
                    chosen_summary.definitely_terminates,
                )
            if stmt.else_body is None:
                dead_branch = _scope_reference_summary(
                    stmt.body,
                    live_names,
                    dead_names,
                )
                dead = (
                    dead or dead_branch.live_references or dead_branch.dead_references
                )
                return ReferenceAnalysisResult(live, dead, False)
            chosen_summary = _scope_reference_summary(
                stmt.else_body,
                live_names,
                dead_names,
            )
            dead_branch = _scope_reference_summary(
                stmt.body,
                live_names,
                dead_names,
            )
            live = live or chosen_summary.live_references
            dead = (
                dead
                or chosen_summary.dead_references
                or dead_branch.live_references
                or dead_branch.dead_references
            )
            return ReferenceAnalysisResult(
                live,
                dead,
                chosen_summary.definitely_terminates,
            )

        then_summary = _scope_reference_summary(stmt.body, live_names, dead_names)

        if stmt.else_body is None:
            return ReferenceAnalysisResult(
                cond_summary.live_references or then_summary.live_references,
                cond_summary.dead_references or then_summary.dead_references,
                False,
            )

        else_summary = _scope_reference_summary(
            stmt.else_body,
            live_names,
            dead_names,
        )

        return ReferenceAnalysisResult(
            cond_summary.live_references
            or then_summary.live_references
            or else_summary.live_references,
            cond_summary.dead_references
            or then_summary.dead_references
            or else_summary.dead_references,
            then_summary.definitely_terminates and else_summary.definitely_terminates,
        )

    if isinstance(stmt, ReferenceSwitch):
        discrim_summary = _expr_reference_summary(
            stmt.discriminant,
            live_names,
            dead_names,
        )

        const_disc = _try_const_eval(stmt.discriminant)
        if const_disc is not None:
            chosen_scope = None
            dead = discrim_summary.dead_references
            for case in stmt.cases:
                case_val = _try_const_eval(case.value)
                if case_val is not None and case_val == const_disc:
                    chosen_scope = case.body
                else:
                    dead_branch = _scope_reference_summary(
                        case.body,
                        live_names,
                        dead_names,
                    )
                    dead = (
                        dead
                        or dead_branch.live_references
                        or dead_branch.dead_references
                    )
            default_summary = (
                _scope_reference_summary(stmt.default, live_names, dead_names)
                if stmt.default is not None
                else None
            )
            switch_chosen: ReferenceAnalysisResult | None
            if chosen_scope is None:
                switch_chosen = default_summary
            else:
                switch_chosen = _scope_reference_summary(
                    chosen_scope,
                    live_names,
                    dead_names,
                )
                if default_summary is not None:
                    dead = (
                        dead
                        or default_summary.live_references
                        or default_summary.dead_references
                    )
            if switch_chosen is None:
                return ReferenceAnalysisResult(
                    discrim_summary.live_references,
                    dead,
                    False,
                )
            return ReferenceAnalysisResult(
                discrim_summary.live_references or switch_chosen.live_references,
                dead or switch_chosen.dead_references,
                switch_chosen.definitely_terminates,
            )

        branch_summaries = [
            _scope_reference_summary(case.body, live_names, dead_names)
            for case in stmt.cases
        ]
        default_summary = (
            _scope_reference_summary(stmt.default, live_names, dead_names)
            if stmt.default is not None
            else None
        )
        return ReferenceAnalysisResult(
            discrim_summary.live_references
            or any(summary.live_references for summary in branch_summaries)
            or (
                default_summary.live_references
                if default_summary is not None
                else False
            ),
            discrim_summary.dead_references
            or any(summary.dead_references for summary in branch_summaries)
            or (
                default_summary.dead_references
                if default_summary is not None
                else False
            ),
            default_summary is not None
            and all(summary.definitely_terminates for summary in branch_summaries)
            and default_summary.definitely_terminates,
        )

    if isinstance(stmt, ReferenceFor):
        init_summary = _scope_reference_summary(stmt.init, live_names, dead_names)
        cond_summary = _expr_reference_summary(stmt.condition, live_names, dead_names)
        body_summary = _scope_reference_summary(stmt.body, live_names, dead_names)
        post_summary = _scope_reference_summary(stmt.post, live_names, dead_names)

        if init_summary.definitely_terminates:
            return ReferenceAnalysisResult(
                init_summary.live_references,
                init_summary.dead_references
                or cond_summary.live_references
                or cond_summary.dead_references
                or body_summary.live_references
                or body_summary.dead_references
                or post_summary.live_references
                or post_summary.dead_references,
                True,
            )

        const_cond = _try_const_eval(stmt.condition)
        if const_cond is not None and const_cond == 0:
            return ReferenceAnalysisResult(
                init_summary.live_references or cond_summary.live_references,
                init_summary.dead_references
                or cond_summary.dead_references
                or body_summary.live_references
                or body_summary.dead_references
                or post_summary.live_references
                or post_summary.dead_references,
                False,
            )

        return ReferenceAnalysisResult(
            init_summary.live_references
            or cond_summary.live_references
            or body_summary.live_references
            or post_summary.live_references,
            init_summary.dead_references
            or cond_summary.dead_references
            or body_summary.dead_references
            or post_summary.dead_references,
            const_cond is not None
            and const_cond != 0
            and body_summary.definitely_terminates,
        )

    raise TypeError(f"Unsupported ReferenceStatement: {type(stmt)}")


class YulParser(_TokenReader):
    """Recursive-descent parser over a pre-tokenized Yul token stream.

    Only the subset of Yul needed for our extraction is handled: function
    definitions, ``let``/bare assignments, supported straight-line
    ``mstore`` statements, blocks, and ``leave``.

    Control flow (``if``, ``switch``, ``for``) is **rejected** unless it is
    part of the explicitly supported subset. Bare expression-statements are
    tracked so later passes can either handle them explicitly or reject
    them as incomplete semantics.
    """

    def __init__(self, tokens: list[tuple[str, str]]) -> None:
        super().__init__(tokens)
        self._expr_stmts: list[Expr] = []
        self._reference_scope_cache: dict[int, ReferenceScope] = {}
        self._source_names: set[str] | None = None

    def _all_source_names(self) -> set[str]:
        """Lazily collect all identifier names from the token stream."""
        if self._source_names is None:
            self._source_names = {text for kind, text in self.tokens if kind == "ident"}
        return self._source_names

    def _skip_until_matching_brace(self) -> None:
        self._expect("{")
        depth = 1
        while depth > 0:
            k, _ = self._pop()
            if k == "{":
                depth += 1
            elif k == "}":
                depth -= 1

    def _skip_to_end_of_current_block(self) -> None:
        """Discard tokens until the ``}`` that closes the current block.

        Leaves the closing brace unconsumed so the caller can handle it.
        """
        depth = 0
        while not self._at_end():
            kind, _text = self._peek() or ("", "")
            if kind == "{":
                depth += 1
                self._pop()
                continue
            if kind == "}":
                if depth == 0:
                    return
                depth -= 1
                self._pop()
                continue
            self._pop()
        raise ParseError("Unterminated block while discarding unreachable code")

    def _expect_plain_assignments(
        self,
        statements: list[RawStatement],
        *,
        context: str,
    ) -> list[PlainAssignment]:
        plain: list[PlainAssignment] = []
        for stmt in statements:
            if isinstance(stmt, (ParsedIfBlock, MemoryWrite)):
                raise ParseError(f"Unexpected non-assignment statement in {context}")
            plain.append(stmt)
        return plain

    def _parse_let(
        self,
        results: list[RawStatement],
        let_vars: set[str] | None = None,
    ) -> None:
        """Parse a ``let`` statement and append to *results*.

        Handles three forms:
        - ``let x := expr``          — single-value assignment
        - ``let a, b, c := call()``  — multi-value; each target gets a
          synthetic ``Project(N, M, call)`` wrapper (index N of M total)
        - ``let x``                  — bare declaration (zero-init, skipped)

        When *let_vars* is provided, all declared variable names are added to
        the set so callers can distinguish ``let`` declarations from
        reassignments.
        """
        self._pop()  # consume 'let'
        target = self._expect_ident()
        if let_vars is not None:
            let_vars.add(target)
        if self._peek_kind() == ",":
            all_targets: list[str] = [target]
            while self._peek_kind() == ",":
                self._pop()
                t = self._expect_ident()
                if let_vars is not None:
                    let_vars.add(t)
                all_targets.append(t)
            if self._peek_kind() != ":=":
                # Multi-var declaration without initializer — zero-init all
                for t in all_targets:
                    results.append(PlainAssignment(t, IntLit(0), is_declaration=True))
                return
            self._expect(":=")
            expr = self._parse_expr()
            if not isinstance(expr, Call):
                raise ParseError(
                    f"Multi-variable let expects a function call as "
                    f"initializer, got {type(expr).__name__}"
                )
            if expr.name in _SUPPORTED_OPS:
                raise ParseError(
                    f"Multi-variable let has builtin {expr.name!r} as initializer, "
                    f"but builtins return a single value"
                )
            for idx, t in enumerate(all_targets):
                results.append(
                    PlainAssignment(
                        t,
                        Project(idx, len(all_targets), expr),
                        is_declaration=True,
                    )
                )
        elif self._peek_kind() == ":=":
            self._pop()
            expr = self._parse_expr()
            results.append(PlainAssignment(target, expr, is_declaration=True))
        else:
            # Bare declaration: ``let x``  (zero-initialized per Yul spec)
            results.append(PlainAssignment(target, IntLit(0), is_declaration=True))

    def _parse_scoped_body(
        self,
        *,
        allow_control_flow: bool,
        context: str,
    ) -> tuple[list[RawStatement], bool, tuple[Expr, ...]]:
        """Parse ``{ ... }`` isolating expression-statements from the caller.

        Returns ``(body, has_leave, expr_stmts)`` where *expr_stmts*
        contains the bare expression-statements found directly in this
        scope (not captured deeper on a ``ParsedIfBlock``).
        """
        self._expect("{")
        saved = self._expr_stmts
        self._expr_stmts = []
        body, has_leave = self._parse_assignment_loop(
            allow_control_flow=allow_control_flow,
            context=context,
        )
        captured = tuple(self._expr_stmts)
        self._expr_stmts = saved
        self._expect("}")
        return body, has_leave, captured

    def _parse_assignment_loop(
        self,
        *,
        allow_control_flow: bool,
        context: str,
        _let_vars: set[str] | None = None,
    ) -> tuple[list[RawStatement], bool]:
        """Parse statements until ``}`` or end of stream.

        Returns ``(statements, has_leave)``.

        When *allow_control_flow* is True, ``if`` and ``switch`` blocks
        are parsed and emitted as ``ParsedIfBlock`` entries.  When False,
        ``if``, ``switch``, and ``for`` keywords are rejected with a
        ``ParseError`` tied to *context*, preventing silent model
        incompleteness inside nested control-flow regions. Straight-line
        ``mstore`` statements are supported only when *allow_control_flow*
        is True; conditional memory writes are rejected. ``for`` is always
        rejected.
        """
        results: list[RawStatement] = []
        has_leave = False

        while not self._at_end() and self._peek_kind() != "}":
            kind = self._peek_kind()

            if kind == "{":
                # Bare scope block.  Parse inner statements, then
                # process sequentially with lexical scope tracking:
                # declarations create block-local bindings, only
                # reassignments to outer-scope names are emitted.
                self._pop()  # consume '{'
                saved_stmts = self._expr_stmts
                self._expr_stmts = []
                inner, inner_leave = self._parse_assignment_loop(
                    allow_control_flow=allow_control_flow,
                    context=context,
                )
                inner_es = self._expr_stmts
                self._expr_stmts = saved_stmts
                # Propagate: bare block is unconditional, so its
                # expr_stmts belong to the enclosing scope.
                self._expr_stmts.extend(inner_es)
                self._expect("}")
                block_subst: dict[str, Expr] = {}
                block_locals: set[str] = set()
                for stmt in inner:
                    if isinstance(stmt, MemoryWrite):
                        results.append(
                            MemoryWrite(
                                substitute_expr(stmt.address, block_subst),
                                substitute_expr(stmt.value, block_subst),
                            )
                        )
                    elif isinstance(stmt, ParsedIfBlock):
                        new_cond = substitute_expr(stmt.condition, block_subst)

                        # Split each branch with scope awareness.
                        outer_body, enc_body = _split_branch_scoped(
                            stmt.body,
                            block_subst,
                            block_locals,
                        )
                        if stmt.else_body is not None:
                            outer_else, enc_else = _split_branch_scoped(
                                stmt.else_body,
                                block_subst,
                                block_locals,
                            )
                        else:
                            outer_else = None
                            enc_else = {}

                        # Merge enclosing-local modifications via ITE.
                        if not stmt.has_leave:
                            all_enc = set(enc_body.keys()) | set(enc_else.keys())
                            for target in all_enc:
                                pre_val = block_subst.get(target, IntLit(0))
                                then_val = enc_body.get(target, pre_val)
                                else_val = enc_else.get(target, pre_val)
                                block_subst[target] = _simplify_ite(
                                    new_cond, then_val, else_val
                                )

                        # Emit ParsedIfBlock for outer-scope targets
                        # or branch-level expression-statements.
                        has_outer = bool(outer_body) or (
                            outer_else is not None and bool(outer_else)
                        )
                        has_branch_es = bool(stmt.body_expr_stmts) or bool(
                            stmt.else_body_expr_stmts
                        )
                        if has_outer or stmt.has_leave or has_branch_es:
                            results.append(
                                ParsedIfBlock(
                                    condition=new_cond,
                                    body=tuple(outer_body),
                                    has_leave=stmt.has_leave,
                                    else_body=(
                                        tuple(outer_else)
                                        if outer_else is not None
                                        else None
                                    ),
                                    body_expr_stmts=stmt.body_expr_stmts,
                                    else_body_expr_stmts=stmt.else_body_expr_stmts,
                                )
                            )
                    else:
                        expr = substitute_expr(stmt.expr, block_subst)
                        if stmt.is_declaration:
                            block_locals.add(stmt.target)
                            if stmt.target.startswith("usr$"):
                                # Real variable declaration: alpha-rename
                                # to a fresh internal name so the model
                                # lowerer treats it as a copy-propagated
                                # temporary.  This preserves point-in-time
                                # values even when outer variables with the
                                # same name are reassigned later.
                                fresh = _gensym("blk", avoid=self._all_source_names())
                                results.append(
                                    PlainAssignment(
                                        fresh,
                                        expr,
                                        is_declaration=True,
                                    )
                                )
                                block_subst[stmt.target] = Var(fresh)
                            else:
                                # Compiler temporary: substitute away.
                                block_subst[stmt.target] = expr
                        elif stmt.target in block_locals:
                            # Reassignment of a block-local name.
                            block_subst[stmt.target] = expr
                        else:
                            # Outer-scope write.
                            results.append(
                                PlainAssignment(
                                    stmt.target,
                                    expr,
                                    is_declaration=stmt.is_declaration,
                                )
                            )
                if inner_leave:
                    has_leave = True
                    self._skip_to_end_of_current_block()
                    break
                continue

            if kind == "ident" and self.tokens[self.i][1] == "let":
                self._parse_let(results, let_vars=_let_vars)
                continue

            if kind == "ident" and self.tokens[self.i][1] == "leave":
                self._pop()
                has_leave = True
                self._skip_to_end_of_current_block()
                break

            if kind == "ident" and self.tokens[self.i][1] == "function":
                self._skip_function_def()
                continue

            if kind == "ident" and self.tokens[self.i][1] in ("if", "switch", "for"):
                keyword = self.tokens[self.i][1]
                if keyword == "for" or not allow_control_flow:
                    raise ParseError(
                        f"Control flow statement '{keyword}' found in "
                        f"{context}. "
                        f"Only straight-line code"
                        f"{' and if/switch blocks' if keyword == 'for' else ''}"
                        f" is supported for Lean model generation."
                    )
                if keyword == "if":
                    self._pop()  # consume 'if'
                    condition = self._parse_expr()
                    # Same decision logic as _classify_if_fold, but at
                    # token level before ParsedIfBlock exists.
                    const_cond = _try_const_eval(condition)
                    if const_cond is not None and const_cond == 0:
                        # Constant-false: skip the entire body (parse
                        # but discard).  Use allow_control_flow=True to
                        # tolerate memory writes in dead code.
                        _dead_body, _dead_leave, _dead_es = self._parse_scoped_body(
                            allow_control_flow=True,
                            context="if-body (dead, constant-false)",
                        )
                        continue
                    if const_cond is not None and const_cond != 0:
                        # Constant-true: flatten the body into the outer
                        # scope with block scoping — declarations stay
                        # block-local, only reassignments are emitted.
                        live_body, live_leave, live_es = self._parse_scoped_body(
                            allow_control_flow=allow_control_flow,
                            context="if-body (live, constant-true)",
                        )
                        _flatten_scoped_block(live_body, results)
                        # Propagate live branch expr_stmts to outer scope.
                        self._expr_stmts.extend(live_es)
                        if live_leave:
                            has_leave = True
                            self._skip_to_end_of_current_block()
                            break
                        continue
                    body, body_leave, body_expr_stmts = self._parse_scoped_body(
                        allow_control_flow=False,
                        context="if-body",
                    )
                    plain_body = self._expect_plain_assignments(
                        body,
                        context="if-body",
                    )
                    results.append(
                        ParsedIfBlock(
                            condition=condition,
                            body=tuple(plain_body),
                            has_leave=body_leave,
                            body_expr_stmts=body_expr_stmts,
                        )
                    )
                else:  # switch
                    self._pop()  # consume 'switch'
                    condition = self._parse_expr()
                    const_disc = _try_const_eval(condition)
                    if const_disc is not None:
                        # Constant discriminant: parse all branches but
                        # only keep the matching one (flattened).
                        # No shape restriction (case-value or branch-count)
                        # is enforced here — the constant-fold path handles
                        # any valid Yul switch.  The only check is that
                        # ``default`` is the last branch (the parser loop
                        # breaks on ``default``, so trailing branches would
                        # be silently dropped).
                        live_branch_stmts: list[RawStatement] = []
                        live_leave = False
                        found_live = False
                        has_default = False
                        while (
                            not self._at_end()
                            and self._peek_kind() == "ident"
                            and self.tokens[self.i][1] in ("case", "default")
                        ):
                            br = self.tokens[self.i][1]
                            self._pop()
                            if br == "case":
                                case_val = self._parse_expr()
                                cv = _try_const_eval(case_val)
                                is_live = (cv == const_disc) and not found_live
                            else:
                                has_default = True
                                is_live = not found_live
                            br_body, br_leave, br_es = self._parse_scoped_body(
                                allow_control_flow=(
                                    allow_control_flow if is_live else True
                                ),
                                context=f"switch branch ({'live' if is_live else 'dead'})",
                            )
                            if is_live:
                                live_branch_stmts = br_body
                                live_leave = br_leave
                                # Propagate live branch expr_stmts.
                                self._expr_stmts.extend(br_es)
                                found_live = True
                            if br == "default":
                                break
                        # Reject trailing branches after default.
                        if (
                            has_default
                            and not self._at_end()
                            and self._peek_kind() == "ident"
                            and self.tokens[self.i][1] in ("case", "default")
                        ):
                            raise ParseError(
                                "'default' must be the last branch in a switch."
                            )
                        _flatten_scoped_block(live_branch_stmts, results)
                        if live_leave:
                            has_leave = True
                            self._skip_to_end_of_current_block()
                            break
                        continue
                    # We support exactly one form of switch:
                    #   switch e case 0 { else_body } default { if_body }
                    # (branches may appear in either order).  Anything else
                    # is rejected loudly.
                    case0_body: list[PlainAssignment] | None = None
                    case0_leave = False
                    case0_expr_stmts: tuple[Expr, ...] = ()
                    default_body: list[PlainAssignment] | None = None
                    default_leave = False
                    default_expr_stmts: tuple[Expr, ...] = ()
                    n_branches = 0
                    while (
                        not self._at_end()
                        and self._peek_kind() == "ident"
                        and self.tokens[self.i][1] in ("case", "default")
                    ):
                        branch = self.tokens[self.i][1]
                        self._pop()  # consume 'case' or 'default'
                        if branch == "case":
                            case_val = self._parse_expr()
                            cv = _try_const_eval(case_val)
                            if cv != 0:
                                raise ParseError(
                                    f"switch case value {case_val!r} is not 0. "
                                    f"Only 'switch e case 0 {{ ... }} default "
                                    f"{{ ... }}' is supported."
                                )
                            if case0_body is not None:
                                raise ParseError(
                                    "Duplicate 'case 0' in switch statement."
                                )
                            raw_case0_body, case0_leave, case0_expr_stmts = (
                                self._parse_scoped_body(
                                    allow_control_flow=False,
                                    context="switch branch",
                                )
                            )
                            case0_body = self._expect_plain_assignments(
                                raw_case0_body,
                                context="switch branch",
                            )
                        else:  # default
                            if default_body is not None:
                                raise ParseError(
                                    "Duplicate 'default' in switch statement."
                                )
                            raw_default_body, default_leave, default_expr_stmts = (
                                self._parse_scoped_body(
                                    allow_control_flow=False,
                                    context="switch branch",
                                )
                            )
                            default_body = self._expect_plain_assignments(
                                raw_default_body,
                                context="switch branch",
                            )
                            # default must be the last branch.
                            n_branches += 1
                            break
                        n_branches += 1
                    # Reject trailing case branches after default.
                    if (
                        default_body is not None
                        and not self._at_end()
                        and self._peek_kind() == "ident"
                        and self.tokens[self.i][1] in ("case", "default")
                    ):
                        raise ParseError(
                            "'default' must be the last branch in a switch."
                        )
                    if n_branches == 0:
                        raise ParseError("switch with no case/default branches")
                    if n_branches != 2 or case0_body is None or default_body is None:
                        raise ParseError(
                            f"switch must have exactly 'case 0' + 'default' "
                            f"(got {n_branches} branch(es), case0="
                            f"{'present' if case0_body is not None else 'missing'}"
                            f", default="
                            f"{'present' if default_body is not None else 'missing'}"
                            f")."
                        )
                    # Normalize to ParsedIfBlock. When exactly one switch branch
                    # contains `leave`, make that the `body` branch so downstream
                    # passes can keep interpreting `has_leave` as "then branch
                    # exits". If the leaving branch is `case 0`, invert the
                    # condition with `iszero(...)`.
                    if_body: tuple[PlainAssignment, ...]
                    else_body: tuple[PlainAssignment, ...] | None
                    parsed_condition: Expr
                    if case0_leave and not default_leave:
                        if_body = tuple(case0_body)
                        else_body = tuple(default_body)
                        parsed_condition = Call("iszero", (condition,))
                        parsed_has_leave = True
                        body_es = case0_expr_stmts
                        else_body_es = default_expr_stmts
                    else:
                        if_body = tuple(default_body)
                        else_body = tuple(case0_body) if case0_body else None
                        parsed_condition = condition
                        parsed_has_leave = default_leave
                        body_es = default_expr_stmts
                        else_body_es = case0_expr_stmts
                    results.append(
                        ParsedIfBlock(
                            condition=parsed_condition,
                            body=if_body,
                            has_leave=parsed_has_leave,
                            else_body=else_body,
                            body_expr_stmts=body_es,
                            else_body_expr_stmts=else_body_es,
                        )
                    )
                continue

            # Multi-target assignment: ``a, b := call()``
            if (
                kind == "ident"
                and self.i + 1 < len(self.tokens)
                and self.tokens[self.i + 1][0] == ","
            ):
                all_targets: list[str] = [self._expect_ident()]
                while self._peek_kind() == ",":
                    self._pop()
                    all_targets.append(self._expect_ident())
                self._expect(":=")
                rhs = self._parse_expr()
                if not isinstance(rhs, Call):
                    raise ParseError(
                        f"Multi-target assignment expects a function call "
                        f"as initializer, got {type(rhs).__name__}"
                    )
                if rhs.name in _SUPPORTED_OPS:
                    raise ParseError(
                        f"Multi-target assignment has builtin {rhs.name!r} as initializer, "
                        f"but builtins return a single value"
                    )
                for idx, t in enumerate(all_targets):
                    results.append(
                        PlainAssignment(
                            t,
                            Project(idx, len(all_targets), rhs),
                        )
                    )
                continue

            if (
                kind == "ident"
                and self.i + 1 < len(self.tokens)
                and self.tokens[self.i + 1][0] == ":="
            ):
                target = self._expect_ident()
                self._expect(":=")
                expr = self._parse_expr()
                results.append(PlainAssignment(target, expr))
                continue

            if kind in ("ident", "num"):
                expr = self._parse_expr()
                if (
                    isinstance(expr, Call)
                    and expr.name == "mstore"
                    and len(expr.args) == 2
                ):
                    if not allow_control_flow:
                        raise ParseError(
                            "Conditional memory write detected in an if/switch "
                            "branch. The supported memory model only allows "
                            "straight-line mstore statements outside control flow."
                        )
                    results.append(MemoryWrite(expr.args[0], expr.args[1]))
                    continue
                self._expr_stmts.append(expr)
                continue

            tok = self._peek()
            raise ParseError(
                f"Unsupported statement start {tok!r} in function body. "
                f"Refuse to skip unrecognized Yul syntax."
            )

        return results, has_leave

    def _skip_function_def(self) -> None:
        self._pop()  # consume 'function'
        self._expect_ident()
        self._expect("(")
        while self._peek_kind() != ")":
            self._pop()
        self._expect(")")
        if self._peek_kind() == "->":
            self._pop()
            self._expect_ident()
            while self._peek_kind() == ",":
                self._pop()
                self._expect_ident()
        self._skip_until_matching_brace()

    def parse_function(self) -> YulFunction:
        token_idx = self.i
        fn_kw = self._expect_ident()
        if fn_kw != "function":
            raise ParseError(f"Expected 'function', got {fn_kw!r}")
        yul_name = self._expect_ident()
        self._expect("(")
        params: list[str] = []
        if self._peek_kind() != ")":
            params.append(self._expect_ident())
            while self._peek_kind() == ",":
                self._pop()
                params.append(self._expect_ident())
        self._expect(")")
        rets: list[str] = []
        if self._peek_kind() == "->":
            self._pop()
            rets.append(self._expect_ident())
            while self._peek_kind() == ",":
                self._pop()
                rets.append(self._expect_ident())
        self._expect("{")
        self._expr_stmts = []
        assignments, has_top_level_leave = self._parse_assignment_loop(
            allow_control_flow=True,
            context="function body",
        )
        self._expect("}")
        # Top-level ``leave`` is a no-op: it just means "return now" after all
        # assignments have been captured.  Dead code after it is already
        # skipped by ``_skip_to_end_of_current_block``.
        return YulFunction(
            yul_name=yul_name,
            params=params,
            rets=rets,
            assignments=assignments,
            expr_stmts=self._expr_stmts if self._expr_stmts else None,
            token_idx=token_idx,
        )

    def _count_params_at(self, idx: int) -> int:
        """Count the number of parameters of the function at token index ``idx``.

        Scans the parenthesized parameter list without advancing the main
        cursor.  Returns the count of comma-separated identifiers.
        """
        # idx points to 'function', idx+1 is the name, idx+2 should be '('
        j = idx + 2
        if j >= len(self.tokens) or self.tokens[j][0] != "(":
            return 0
        j += 1  # skip '('
        if j < len(self.tokens) and self.tokens[j][0] == ")":
            return 0
        count = 1
        while j < len(self.tokens) and self.tokens[j][0] != ")":
            if self.tokens[j][0] == ",":
                count += 1
            j += 1
        return count

    def _disambiguate_by_references(
        self,
        matches: list[int],
        known_yul_names: set[str],
        exclude_known: bool,
    ) -> list[int]:
        """Narrow *matches* using helper-reference analysis.

        Each candidate's body is analyzed for references to
        *known_yul_names*.  References are classified as **live**
        (reachable at runtime) or **dead** (behind constant-false
        guards or after ``leave``).

        **exclude_known=True** — selecting a *leaf* function that does
        NOT call known helpers:

        1. Prefer candidates with no live references.
        2. Among those, prefer candidates that DO have dead references
           (a dead reference proves the compiler originally considered
           this variant related to the helper — it is the right leaf
           rather than an unrelated function that happens to match).
        3. If no candidate has dead references, accept all
           live-independent candidates.

        **exclude_known=False** — selecting a *wrapper* that calls
        known helpers:

        1. Prefer candidates with live references.
        2. If none have live references, prefer candidates with no
           dead references (a dead reference suggests the optimizer
           stripped a real call — probably not the right match).

        **Partial-parse fallback** — when some candidate bodies fail
        to parse (summary is None), use only the live-reference signal.

        Returns the narrowed list, or *matches* unchanged when no
        filtering applies.
        """
        summaries = {
            m: self._body_reference_summary(m, known_yul_names) for m in matches
        }

        def _has_live(m: int) -> bool:
            s = summaries[m]
            return s is not None and s.live_references

        def _has_dead(m: int) -> bool:
            s = summaries[m]
            return s is not None and s.dead_references

        if all(summary is not None for summary in summaries.values()):
            # All bodies parsed — use full disambiguation.
            if exclude_known:
                # Leaf selection: discard candidates that call known helpers.
                live_independent = [m for m in matches if not _has_live(m)]
                if live_independent:
                    # Tiebreak: prefer candidates whose dead code DOES
                    # reference known helpers (proves compiler affinity).
                    dead_tiebreak = [m for m in live_independent if _has_dead(m)]
                    return dead_tiebreak if dead_tiebreak else live_independent
            else:
                # Wrapper selection: prefer candidates that call known helpers.
                live_dependent = [m for m in matches if _has_live(m)]
                if live_dependent:
                    return live_dependent
                # No live references anywhere.  Prefer candidates with
                # no dead references — a dead ref suggests the optimizer
                # stripped a real call, making that candidate the wrong match.
                clean_candidates = [m for m in matches if not _has_dead(m)]
                if clean_candidates:
                    return clean_candidates
        else:
            # Some bodies failed to parse — simple fallback.
            live_dependent = [m for m in matches if _has_live(m)]
            if live_dependent:
                return live_dependent

        return matches

    def find_function(
        self,
        sol_fn_name: str,
        *,
        n_params: int | None = None,
        known_yul_names: set[str] | None = None,
        exclude_known: bool = False,
    ) -> YulFunction:
        """Find and parse ``function fun_{sol_fn_name}_<digits>(...)``.

        When *n_params* is set and multiple candidates match the name
        pattern, only those with exactly *n_params* parameters are kept.

        When *known_yul_names* is set and still ambiguous, prefer
        candidates whose body references at least one of the given Yul
        function names.  This disambiguates e.g. ``sqrt(uint512)`` (which
        calls ``_sqrt``) from ``Sqrt.sqrt(uint256)`` (which does not).

        When *exclude_known* is True, the filter is inverted: prefer
        candidates whose body does NOT reference any known Yul name.
        This selects leaf functions (e.g. 256-bit ``Sqrt.sqrt``) over
        higher-level wrappers that call into already-targeted functions.

        Raises on zero or ambiguous matches.
        """
        target_prefix = f"fun_{sol_fn_name}_"
        matches: list[int] = []
        # Track function-body nesting so that functions defined inside
        # other function bodies are ignored.  We use a stack of brace
        # depths: when we enter a function body, we push the current
        # brace depth, and when we return to that depth, the function
        # body is closed.
        fn_body_stack: list[int] = []  # brace depths at fn body open
        depth = 0
        expect_fn_body = False

        for idx in range(len(self.tokens) - 1):
            k, text = self.tokens[idx]
            if k == "{":
                depth += 1
                if expect_fn_body:
                    fn_body_stack.append(depth)
                    expect_fn_body = False
            elif k == "}":
                if fn_body_stack and fn_body_stack[-1] == depth:
                    fn_body_stack.pop()
                depth -= 1
            elif k == "ident" and text == "function":
                if (
                    not fn_body_stack
                    and self.tokens[idx + 1][0] == "ident"
                    and self.tokens[idx + 1][1].startswith(target_prefix)
                    and self.tokens[idx + 1][1][len(target_prefix) :].isdigit()
                ):
                    matches.append(idx)
                # The next `{` opens a function body.
                expect_fn_body = True

        if not matches:
            raise ParseError(
                f"Yul function for '{sol_fn_name}' not found "
                f"(expected pattern fun_{sol_fn_name}_<digits>)"
            )

        if n_params is not None:
            matches = [m for m in matches if self._count_params_at(m) == n_params]
            if not matches:
                raise ParseError(
                    f"No Yul function for {sol_fn_name!r} matches "
                    f"{n_params} parameter(s)"
                )

        if known_yul_names and len(matches) > 1:
            matches = self._disambiguate_by_references(
                matches, known_yul_names, exclude_known
            )

        if len(matches) > 1:
            names = [self.tokens[m + 1][1] for m in matches]
            raise ParseError(
                f"Multiple Yul functions match '{sol_fn_name}': {names}. "
                f"Rename wrapper functions to avoid collisions "
                f"(e.g. prefix with 'wrap_')."
            )

        self.i = matches[0]
        return self.parse_function()

    def find_exact_function(
        self,
        yul_name: str,
        *,
        n_params: int | None = None,
        search_nested: bool = False,
    ) -> YulFunction:
        """Find and parse the function whose Yul symbol exactly matches ``yul_name``.

        By default, functions nested inside other function bodies are
        skipped.  Pass *search_nested=True* to also search inside
        function bodies (for selecting nested helpers).
        """
        matches = self._find_exact_function_matches(
            yul_name,
            n_params=n_params,
            search_nested=search_nested,
        )

        if not matches:
            if n_params is None:
                raise ParseError(f"Exact Yul function {yul_name!r} not found")
            raise ParseError(
                f"Exact Yul function {yul_name!r} with {n_params} parameter(s) not found"
            )

        if len(matches) > 1:
            qualified = ["::".join(path) for _, path in matches]
            raise ParseError(
                f"Multiple exact Yul functions matched {yul_name!r}: {qualified}. "
                "Use a scope-qualified exact_yul_names entry such as '::name' "
                "for a top-level function or 'outer::inner' for a nested one."
            )

        self.i = matches[0][0]
        return self.parse_function()

    def find_exact_function_path(
        self,
        yul_path: tuple[str, ...],
        *,
        n_params: int | None = None,
    ) -> YulFunction:
        """Find a function by its exact lexical path.

        ``("top",)`` selects a top-level function, while
        ``("outer", "helper")`` selects ``helper`` nested inside ``outer``.
        """
        if not yul_path:
            raise ParseError("Exact Yul function path cannot be empty")
        yul_name = yul_path[-1]
        matches = [
            (idx, path)
            for idx, path in self._find_exact_function_matches(
                yul_name,
                n_params=n_params,
                search_nested=True,
            )
            if path == yul_path
        ]
        if not matches:
            rendered = "::".join(yul_path)
            if n_params is None:
                raise ParseError(f"Exact Yul function path {rendered!r} not found")
            raise ParseError(
                f"Exact Yul function path {rendered!r} with {n_params} "
                f"parameter(s) not found"
            )
        if len(matches) > 1:
            rendered = "::".join(yul_path)
            raise ParseError(
                f"Multiple exact Yul functions matched path {rendered!r}. "
                "Refuse to guess."
            )
        self.i = matches[0][0]
        return self.parse_function()

    def _find_exact_function_matches(
        self,
        yul_name: str,
        *,
        n_params: int | None = None,
        search_nested: bool,
    ) -> list[tuple[int, tuple[str, ...]]]:
        """Return ``(token_idx, lexical_path)`` matches for ``yul_name``."""
        matches: list[tuple[int, tuple[str, ...]]] = []
        fn_body_stack: list[tuple[int, str]] = []
        depth = 0
        expect_fn_body: str | None = None

        for idx in range(len(self.tokens) - 1):
            k, text = self.tokens[idx]
            if k == "{":
                depth += 1
                if expect_fn_body is not None:
                    fn_body_stack.append((depth, expect_fn_body))
                    expect_fn_body = None
            elif k == "}":
                if fn_body_stack and fn_body_stack[-1][0] == depth:
                    fn_body_stack.pop()
                depth -= 1
            elif k == "ident" and text == "function":
                fn_name = self._function_name_at(idx)
                if fn_name is None:
                    expect_fn_body = None
                    continue
                if (
                    fn_name == yul_name
                    and (search_nested or not fn_body_stack)
                    and (n_params is None or self._count_params_at(idx) == n_params)
                ):
                    path = tuple(name for _, name in fn_body_stack) + (fn_name,)
                    matches.append((idx, path))
                expect_fn_body = fn_name
        return matches

    def _body_reference_summary(
        self,
        fn_start: int,
        yul_names: set[str],
    ) -> ReferenceAnalysisResult | None:
        """Summarize live/dead dependencies on *yul_names* for a function body."""
        # Find the opening brace of the function body.
        body_start = fn_start
        while body_start < len(self.tokens) and self.tokens[body_start][0] != "{":
            body_start += 1
        if body_start >= len(self.tokens):
            return None
        body_end = self._find_matching_brace(body_start)
        if fn_start not in self._reference_scope_cache:
            try:
                body_tokens = self.tokens[body_start + 1 : body_end]
                scope = _ReferenceScopeParser(body_tokens).parse_scope()
            except ParseError:
                return None
            self._reference_scope_cache[fn_start] = scope
        return _scope_reference_summary(
            self._reference_scope_cache[fn_start],
            yul_names,
        )

    def _find_matching_brace(self, open_idx: int) -> int:
        """Return the index of the ``}`` matching the ``{`` at *open_idx*."""
        depth = 0
        for j in range(open_idx, len(self.tokens)):
            k, _ = self.tokens[j]
            if k == "{":
                depth += 1
            elif k == "}":
                depth -= 1
                if depth == 0:
                    return j
        return len(self.tokens) - 1

    def _function_name_at(self, idx: int) -> str | None:
        if idx + 1 >= len(self.tokens):
            return None
        kind, text = self.tokens[idx + 1]
        if kind != "ident":
            return None
        return text

    def collect_all_functions(self) -> CollectedFunctions:
        """Parse all function definitions in the token stream.

        Only collects functions at the top level of the token stream.
        Brace-delimited blocks that are not function bodies (e.g.
        ``object`` blocks) are skipped, so functions in different
        ``object`` blocks never collide.  Duplicate function names
        at the same scope level raise ``ParseError``.

        Successfully parsed helpers go into ``functions``. Helpers whose
        bodies fail to parse are recorded in ``rejected`` so later inlining
        can fail loudly if a selected target depends on them.
        """
        functions: dict[str, YulFunction] = {}
        rejected: dict[str, str] = {}
        while not self._at_end():
            if self._peek_kind() == "ident" and self.tokens[self.i][1] == "function":
                saved_i = self.i
                saved_stmts = self._expr_stmts
                try:
                    fn = self.parse_function()
                except ParseError as err:
                    fn_name = self._function_name_at(saved_i) or f"<unknown@{saved_i}>"
                    if fn_name in functions or fn_name in rejected:
                        raise ParseError(
                            f"Duplicate helper function {fn_name!r} in the "
                            f"same scope. Refuse to collect ambiguous helpers."
                        )
                    rejected[fn_name] = str(err)
                    self.i = saved_i
                    self._skip_function_def()
                    continue
                finally:
                    self._expr_stmts = saved_stmts
                if fn.yul_name in functions or fn.yul_name in rejected:
                    raise ParseError(
                        f"Duplicate helper function {fn.yul_name!r} in the "
                        f"same scope. Refuse to collect ambiguous helpers."
                    )
                functions[fn.yul_name] = fn
            elif self._peek_kind() == "{":
                # Non-function brace block (object/code wrapper).
                # Skip to matching } to avoid collecting functions
                # from a different scope.
                brace_idx = self.i
                end_idx = self._find_matching_brace(brace_idx)
                self.i = end_idx + 1
            else:
                self._pop()
        return CollectedFunctions(functions=functions, rejected=rejected)


# ---------------------------------------------------------------------------
# Yul → FunctionModel conversion
# ---------------------------------------------------------------------------


def demangle_var(
    name: str,
    param_vars: list[str],
    return_vars: list[str],
    *,
    keep_solidity_locals: bool = False,
) -> str | None:
    """Map a Yul variable name back to its Solidity-level name.

    Returns the cleaned name, or None if the variable is a compiler temporary
    that should be copy-propagated away.

    ``param_vars`` is a list of Yul parameter variable names (supports
    multi-parameter functions).

    ``return_vars`` is a list of Yul return variable names.

    When *keep_solidity_locals* is True, variables matching the
    ``var_<name>_<digits>`` pattern (compiler representation of
    Solidity-declared locals) are kept in the model even if they are
    not the function parameter or return variable.
    """
    if name in param_vars or name in return_vars:
        m = re.fullmatch(r"var_(\w+?)_\d+", name)
        return m.group(1) if m else name
    if name.startswith("usr$"):
        return name[4:]
    if keep_solidity_locals:
        m = re.fullmatch(r"var_(\w+?)_\d+", name)
        if m:
            return m.group(1)
    return None


def rename_expr(expr: Expr, var_map: dict[str, str], fn_map: dict[str, str]) -> Expr:
    if isinstance(expr, IntLit):
        return expr
    if isinstance(expr, Var):
        return Var(var_map.get(expr.name, expr.name))
    if isinstance(expr, Ite):
        return Ite(
            rename_expr(expr.cond, var_map, fn_map),
            rename_expr(expr.if_true, var_map, fn_map),
            rename_expr(expr.if_false, var_map, fn_map),
        )
    if isinstance(expr, Project):
        return Project(expr.index, expr.total, rename_expr(expr.inner, var_map, fn_map))
    if isinstance(expr, Call):
        new_name = fn_map.get(expr.name, expr.name)
        new_args = tuple(rename_expr(a, var_map, fn_map) for a in expr.args)
        return Call(new_name, new_args)
    assert_never(expr)


def substitute_expr(expr: Expr, subst: dict[str, Expr]) -> Expr:
    if isinstance(expr, IntLit):
        return expr
    if isinstance(expr, Var):
        return subst.get(expr.name, expr)
    if isinstance(expr, Ite):
        return Ite(
            substitute_expr(expr.cond, subst),
            substitute_expr(expr.if_true, subst),
            substitute_expr(expr.if_false, subst),
        )
    if isinstance(expr, Project):
        return Project(expr.index, expr.total, substitute_expr(expr.inner, subst))
    if isinstance(expr, Call):
        return Call(expr.name, tuple(substitute_expr(a, subst) for a in expr.args))
    assert_never(expr)


def _find_function_body_range(
    tokens: list[tuple[str, str]], fn_start_idx: int
) -> tuple[int, int] | None:
    """Return the (start, end) token range of a function's body contents.

    *fn_start_idx* points to the ``function`` keyword. Returns the range
    of tokens INSIDE the body braces (exclusive of ``{`` and ``}``), or
    None if no body brace is found.
    """
    # Skip past the function keyword and signature to find the opening {.
    j = fn_start_idx + 1
    while j < len(tokens) and tokens[j][0] != "{":
        j += 1
    if j >= len(tokens):
        return None
    open_brace = j
    depth = 0
    for m in range(open_brace, len(tokens)):
        if tokens[m][0] == "{":
            depth += 1
        elif tokens[m][0] == "}":
            depth -= 1
            if depth == 0:
                return (open_brace + 1, m)
    return None


def _find_enclosing_block_range(
    tokens: list[tuple[str, str]], inner_idx: int
) -> tuple[int, int]:
    """Return (start, end) of the innermost brace-block containing *inner_idx*."""
    depth = 0
    start = 0
    found_start = False
    for j in range(inner_idx - 1, -1, -1):
        if tokens[j][0] == "}":
            depth += 1
        elif tokens[j][0] == "{":
            if depth == 0:
                start = j + 1
                found_start = True
                break
            depth -= 1
    if not found_start:
        return 0, len(tokens)
    depth = 0
    end = len(tokens)
    for j in range(start - 1, len(tokens)):
        if tokens[j][0] == "{":
            depth += 1
        elif tokens[j][0] == "}":
            depth -= 1
            if depth == 0:
                end = j
                break
    return start, end


def _flatten_scoped_block(
    stmts: list[RawStatement],
    results: list[RawStatement],
) -> None:
    """Emit *stmts* into *results* with block scoping applied.

    Maintains a block-local environment of names introduced by ``let``
    in this block.  A declaration adds its target to the local set and
    parks the value in ``block_sub``.  A later reassignment to a name
    in the local set updates that local binding (never escapes to outer
    scope).  Only assignments to names *not* local to this block are
    emitted to *results*.
    """
    block_sub: dict[str, Expr] = {}
    block_locals: set[str] = set()
    for stmt in stmts:
        if isinstance(stmt, PlainAssignment):
            expr = substitute_expr(stmt.expr, block_sub)
            if stmt.is_declaration:
                block_locals.add(stmt.target)
                block_sub[stmt.target] = expr
            elif stmt.target in block_locals:
                # Reassignment of a block-local name — update local.
                block_sub[stmt.target] = expr
            else:
                results.append(PlainAssignment(stmt.target, expr))
        elif isinstance(stmt, MemoryWrite):
            results.append(
                MemoryWrite(
                    substitute_expr(stmt.address, block_sub),
                    substitute_expr(stmt.value, block_sub),
                )
            )
        elif isinstance(stmt, ParsedIfBlock):
            new_cond = substitute_expr(stmt.condition, block_sub)
            new_body = tuple(
                PlainAssignment(
                    s.target,
                    substitute_expr(s.expr, block_sub),
                    is_declaration=s.is_declaration,
                )
                for s in stmt.body
            )
            new_else = None
            if stmt.else_body is not None:
                new_else = tuple(
                    PlainAssignment(
                        s.target,
                        substitute_expr(s.expr, block_sub),
                        is_declaration=s.is_declaration,
                    )
                    for s in stmt.else_body
                )
            results.append(
                ParsedIfBlock(
                    condition=new_cond,
                    body=new_body,
                    has_leave=stmt.has_leave,
                    else_body=new_else,
                    body_expr_stmts=stmt.body_expr_stmts,
                    else_body_expr_stmts=stmt.else_body_expr_stmts,
                )
            )


def _split_branch_scoped(
    assignments: tuple[PlainAssignment, ...],
    parent_subst: dict[str, Expr],
    enclosing_locals: set[str],
) -> tuple[list[PlainAssignment], dict[str, Expr]]:
    """Split a branch body into outer writes and enclosing-local modifications.

    Uses ``is_declaration`` to track a per-branch lexical scope:

    - **Declaration** (``is_declaration=True``): creates a branch-local
      binding.  Later writes to the same name stay branch-local.
      Neither the declaration nor its reassignments are returned.
    - **Reassignment of a branch-local name**: absorbed into the branch
      scope (not returned).
    - **Reassignment of an enclosing-local name** (in *enclosing_locals*):
      returned in the *enclosing_mods* dict for ITE merging by the caller.
    - **Outer-scope write**: returned in the *outer* list.
    """
    outer: list[PlainAssignment] = []
    enclosing_mods: dict[str, Expr] = {}
    working_subst = dict(parent_subst)
    branch_locals: set[str] = set()

    for s in assignments:
        sub_expr = substitute_expr(s.expr, working_subst)
        if s.is_declaration:
            branch_locals.add(s.target)
            working_subst[s.target] = sub_expr
        elif s.target in branch_locals:
            working_subst[s.target] = sub_expr
        elif s.target in enclosing_locals:
            enclosing_mods[s.target] = sub_expr
            working_subst[s.target] = sub_expr
        else:
            outer.append(
                PlainAssignment(s.target, sub_expr, is_declaration=s.is_declaration)
            )
    return outer, enclosing_mods


def _merge_helper_collection(
    helper_table: dict[str, YulFunction],
    rejected_helpers: dict[str, str],
    collection: CollectedFunctions,
) -> None:
    """Merge one lexical scope's helpers, with inner names overriding outer."""
    for name, fn in collection.functions.items():
        rejected_helpers.pop(name, None)
        helper_table[name] = fn
    for name, err in collection.rejected.items():
        helper_table.pop(name, None)
        rejected_helpers[name] = err


def _parse_exact_yul_selector(selector: str) -> tuple[str, ...] | None:
    """Parse a scope-qualified exact Yul selector.

    ``None`` means the selector is an unqualified function name.
    ``::top`` selects a top-level function. ``outer::helper`` selects a
    function nested inside ``outer``.
    """
    if "::" not in selector:
        return None
    raw = selector[2:] if selector.startswith("::") else selector
    parts = tuple(part for part in raw.split("::") if part)
    if not parts:
        raise ParseError(f"Invalid exact Yul selector {selector!r}")
    return parts


def _reject_expr_stmts(expr_stmts: list[Expr] | None, *, context: str) -> None:
    """Raise ``ParseError`` if *expr_stmts* is non-empty."""
    if not expr_stmts:
        return
    descriptions: list[str] = []
    for e in expr_stmts[:3]:
        if isinstance(e, Call):
            descriptions.append(f"{e.name}(...)")
        else:
            descriptions.append(repr(e))
    summary = ", ".join(descriptions)
    if len(expr_stmts) > 3:
        summary += ", ..."
    raise ParseError(
        f"{context} {len(expr_stmts)} unhandled expression-statement(s): "
        f"[{summary}]. Refuse to proceed with incomplete semantics."
    )


def _reject_branch_expr_stmts(stmt: ParsedIfBlock, *, context: str) -> None:
    """Raise ``ParseError`` if either branch carries expression-statements."""
    _reject_expr_stmts(
        list(stmt.body_expr_stmts) if stmt.body_expr_stmts else None,
        context=f"{context} then-branch",
    )
    _reject_expr_stmts(
        list(stmt.else_body_expr_stmts) if stmt.else_body_expr_stmts else None,
        context=f"{context} else-branch",
    )


# ---------------------------------------------------------------------------
# Function inlining
# ---------------------------------------------------------------------------

_gensym_counters: dict[str, int] = {}


def _gensym(prefix: str, avoid: set[str] | None = None) -> str:
    """Generate a unique variable name for generated locals.

    When *avoid* is provided, the counter is advanced past any
    candidate that appears in the set, so generated names never
    collide with user-visible identifiers.
    """
    _gensym_counters[prefix] = _gensym_counters.get(prefix, 0) + 1
    if avoid is not None:
        while f"_{prefix}_{_gensym_counters[prefix]}" in avoid:
            _gensym_counters[prefix] += 1
    return f"_{prefix}_{_gensym_counters[prefix]}"


def _try_const_eval(expr: Expr) -> int | None:
    """Try to evaluate an expression to a constant integer.

    Returns ``None`` if the expression contains variables or unsupported
    operations.  Delegates to ``_eval_builtin`` for all supported EVM
    opcodes so that constant-folding semantics stay in sync with the
    model evaluator.
    """
    if isinstance(expr, IntLit):
        return expr.value % WORD_MOD
    if isinstance(expr, Var):
        return None
    if isinstance(expr, Ite):
        cond_val = _try_const_eval(expr.cond)
        if_val = _try_const_eval(expr.if_true)
        else_val = _try_const_eval(expr.if_false)
        if if_val is not None and else_val is not None and if_val == else_val:
            return if_val  # already wrapped by recursive call
        if cond_val is not None and cond_val != 0 and if_val is not None:
            return if_val
        if cond_val is not None and cond_val == 0 and else_val is not None:
            return else_val
        return None
    if isinstance(expr, Project):
        return None
    if isinstance(expr, Call):
        # Delegate all ops to _eval_builtin (which wraps via u256).
        resolved: list[int] = []
        for arg in expr.args:
            v = _try_const_eval(arg)
            if v is None:
                return None
            resolved.append(v)
        try:
            return _eval_builtin(expr.name, tuple(resolved))
        except EvaluationError:
            return None
    assert_never(expr)


class _IfFoldDecision(enum.Enum):
    """Result of evaluating a ParsedIfBlock condition for constant-folding."""

    NOT_CONSTANT = "not_constant"  # condition is not compile-time constant
    DEAD = "dead"  # constant-false, no else → entire block is dead
    THEN_LIVE = "then_live"  # constant-true → then-body is live
    ELSE_LIVE = "else_live"  # constant-false with else → else-body is live


def _classify_if_fold(
    condition_value: int | None,
    has_else: bool,
) -> _IfFoldDecision:
    """Classify a conditional block for constant-folding.

    Pure decision function — takes the evaluated condition (or None if
    non-constant) and whether an else-body exists.  Callers act on the
    result according to their pipeline stage.
    """
    if condition_value is None:
        return _IfFoldDecision.NOT_CONSTANT
    if condition_value != 0:
        return _IfFoldDecision.THEN_LIVE
    if has_else:
        return _IfFoldDecision.ELSE_LIVE
    return _IfFoldDecision.DEAD


def _simplify_ite(cond: Expr, if_val: Expr, else_val: Expr) -> Expr:
    """Build an ``Ite`` node, simplifying when the condition or branches are trivial."""
    if if_val == else_val:
        return if_val
    cond_val = _try_const_eval(cond)
    if cond_val is not None:
        return if_val if cond_val != 0 else else_val
    return Ite(cond, if_val, else_val)


def _is_zero_init_expr(expr: Expr) -> bool:
    return (isinstance(expr, IntLit) and expr.value == 0) or (
        isinstance(expr, Call)
        and not expr.args
        and expr.name.startswith("zero_value_for_split_")
    )


def _is_add_32_to_var(expr: Expr, var_name: str) -> bool:
    if not isinstance(expr, Call) or expr.name != "add" or len(expr.args) != 2:
        return False
    left, right = expr.args
    return (left == IntLit(32) and right == Var(var_name)) or (
        left == Var(var_name) and right == IntLit(32)
    )


def _is_uint512_from_helper(fn: YulFunction) -> Expr | None:
    """Recognize the exact emitted shape of ``uint512.from(x_hi, x_lo)``.

    Returns the lo-address expression on match (preserving the compiler's
    emitted operand order), or ``None`` if *fn* doesn't match.
    """
    if fn.expr_stmts:
        return None
    if len(fn.params) != 3 or len(fn.rets) != 1:
        return None
    if len(fn.assignments) == 5:
        zero_tmp_stmt, init_stmt, write_hi, write_lo, ret_stmt = fn.assignments
        if (
            not isinstance(zero_tmp_stmt, PlainAssignment)
            or not _is_zero_init_expr(zero_tmp_stmt.expr)
            or not isinstance(init_stmt, PlainAssignment)
            or init_stmt.target != fn.rets[0]
            or init_stmt.expr != Var(zero_tmp_stmt.target)
        ):
            return None
    elif len(fn.assignments) == 4:
        init_stmt, write_hi, write_lo, ret_stmt = fn.assignments
        if (
            not isinstance(init_stmt, PlainAssignment)
            or init_stmt.target != fn.rets[0]
            or not _is_zero_init_expr(init_stmt.expr)
        ):
            return None
    else:
        return None

    ptr_param, hi_param, lo_param = fn.params
    ret_name = fn.rets[0]

    if (
        not isinstance(write_hi, MemoryWrite)
        or write_hi.address != Var(ptr_param)
        or write_hi.value != Var(hi_param)
    ):
        return None
    if (
        not isinstance(write_lo, MemoryWrite)
        or not _is_add_32_to_var(write_lo.address, ptr_param)
        or write_lo.value != Var(lo_param)
    ):
        return None
    if not (
        isinstance(ret_stmt, PlainAssignment)
        and ret_stmt.target == ret_name
        and ret_stmt.expr == Var(ptr_param)
    ):
        return None
    return write_lo.address


def _collect_vars_in_expr(expr: Expr, out: set[str]) -> None:
    """Collect all variable names referenced in *expr*."""
    if isinstance(expr, Var):
        out.add(expr.name)
    elif isinstance(expr, Ite):
        _collect_vars_in_expr(expr.cond, out)
        _collect_vars_in_expr(expr.if_true, out)
        _collect_vars_in_expr(expr.if_false, out)
    elif isinstance(expr, Project):
        _collect_vars_in_expr(expr.inner, out)
    elif isinstance(expr, Call):
        for a in expr.args:
            _collect_vars_in_expr(a, out)


def _alpha_rename_yul_function(
    fn: YulFunction, rename_map: dict[str, str]
) -> YulFunction:
    """Return a copy of *fn* with selected local variables renamed."""
    rename_subst: dict[str, Expr] = {old: Var(new) for old, new in rename_map.items()}

    def _rename_stmt(s: PlainAssignment) -> PlainAssignment:
        target = rename_map.get(s.target, s.target)
        expr = substitute_expr(s.expr, rename_subst)
        return PlainAssignment(target, expr, is_declaration=s.is_declaration)

    new_assignments: list[RawStatement] = []
    for stmt in fn.assignments:
        if isinstance(stmt, PlainAssignment):
            new_assignments.append(_rename_stmt(stmt))
        elif isinstance(stmt, MemoryWrite):
            new_assignments.append(
                MemoryWrite(
                    substitute_expr(stmt.address, rename_subst),
                    substitute_expr(stmt.value, rename_subst),
                )
            )
        elif isinstance(stmt, ParsedIfBlock):
            new_cond = substitute_expr(stmt.condition, rename_subst)
            new_body = tuple(_rename_stmt(s) for s in stmt.body)
            new_else = (
                tuple(_rename_stmt(s) for s in stmt.else_body)
                if stmt.else_body is not None
                else None
            )
            new_assignments.append(
                ParsedIfBlock(
                    condition=new_cond,
                    body=new_body,
                    has_leave=stmt.has_leave,
                    else_body=new_else,
                    body_expr_stmts=stmt.body_expr_stmts,
                    else_body_expr_stmts=stmt.else_body_expr_stmts,
                )
            )
        else:
            assert_never(stmt)
    return YulFunction(
        yul_name=fn.yul_name,
        params=fn.params,
        rets=fn.rets,
        assignments=new_assignments,
        expr_stmts=fn.expr_stmts,
        token_idx=fn.token_idx,
    )


def _inline_single_call(
    fn: YulFunction,
    args: tuple[Expr, ...],
    fn_table: dict[str, YulFunction],
    depth: int,
    max_depth: int,
    mstore_sink: list[FromWriteEffect] | None = None,
    unsupported_function_errors: dict[str, str] | None = None,
) -> Expr | tuple[Expr, ...]:
    """Inline one function call, returning its return-value expression(s).

    Depth is incremented at the top of this function so that only actual
    user-function inlining (not AST recursion over builtins) consumes
    the depth budget.

    Builds a substitution from parameters → argument expressions, then
    processes the helper body sequentially. Helpers must remain pure at the
    statement level, except for the exact emitted ``uint512.from(x_hi, x_lo)``
    accessor shape, whose two fixed-slot writes are sunk into the selected
    function body.
    """
    depth += 1
    if depth > max_depth:
        raise ParseError(
            f"Inlining depth {depth} exceeded max_depth={max_depth} while "
            f"inlining {fn.yul_name!r}. Refuse to leave the expression "
            f"partially inlined."
        )
    expected_arity = len(fn.params)
    actual_arity = len(args)
    if actual_arity != expected_arity:
        raise ParseError(
            f"Cannot inline helper {fn.yul_name!r}: expected {expected_arity} "
            f"argument(s), got {actual_arity}"
        )

    lo_addr_template = _is_uint512_from_helper(fn)
    if lo_addr_template is not None:
        if mstore_sink is None:
            raise ParseError(
                f"Cannot inline helper {fn.yul_name!r}: exact uint512.from(x_hi, x_lo) "
                "requires a memory sink."
            )
        ptr_expr, hi_expr, lo_expr = args
        # Substitute the helper's ptr parameter in the lo-address template
        # with the call-site ptr expression, preserving the compiler's
        # emitted operand order.
        ptr_param = fn.params[0]
        lo_addr = substitute_expr(lo_addr_template, {ptr_param: ptr_expr})
        mstore_sink.append(FromWriteEffect(ptr_expr, hi_expr, lo_expr, lo_addr))
        return ptr_expr

    _reject_expr_stmts(
        fn.expr_stmts,
        context=f"Inlining function {fn.yul_name!r} encountered",
    )

    # Alpha-rename callee-local variables that collide with names
    # appearing in argument expressions.  Without this, a callee
    # ``let usr$tmp := 0`` would clobber a caller-side ``usr$tmp``
    # passed as an argument.
    arg_var_names: set[str] = set()
    for a in args:
        _collect_vars_in_expr(a, arg_var_names)
    param_and_ret = set(fn.params) | set(fn.rets)
    callee_locals: set[str] = set()
    for stmt in fn.assignments:
        if isinstance(stmt, PlainAssignment) and stmt.target not in param_and_ret:
            callee_locals.add(stmt.target)
        elif isinstance(stmt, ParsedIfBlock):
            for s in stmt.body:
                if s.target not in param_and_ret:
                    callee_locals.add(s.target)
            if stmt.else_body is not None:
                for s in stmt.else_body:
                    if s.target not in param_and_ret:
                        callee_locals.add(s.target)
    collisions = callee_locals & arg_var_names
    if collisions:
        used_names = arg_var_names | param_and_ret | callee_locals
        rename_map: dict[str, str] = {}
        for old_name in sorted(collisions):
            counter = 0
            while True:
                candidate = f"_inl_{old_name}_{counter}"
                if candidate not in used_names:
                    rename_map[old_name] = candidate
                    used_names.add(candidate)
                    break
                counter += 1
        # Apply rename to all callee assignments.
        fn = _alpha_rename_yul_function(fn, rename_map)

    subst: dict[str, Expr] = {}
    for param, arg_expr in zip(fn.params, args):
        subst[param] = arg_expr
    # Also seed return variables with zero (they're typically zero-initialized)
    for r in fn.rets:
        if r not in subst:
            subst[r] = IntLit(0)

    leave_cond: Expr | None = None  # set when an if-block with leave is encountered
    leave_subst: dict[str, Expr] | None = None

    def _resolve(e: Expr, s: dict[str, Expr]) -> Expr:
        resolved = substitute_expr(e, s)
        # Since subst is built sequentially (each value is already fully
        # substituted at assignment time), one pass must suffice.  A second
        # pass that changes anything indicates a broken invariant.
        check = substitute_expr(resolved, s)
        if check != resolved:
            raise ParseError(
                f"Sequential-build invariant violated: a single substitution "
                f"pass was not sufficient.\n  original : {e!r}\n  after 1st: "
                f"{resolved!r}\n  after 2nd: {check!r}"
            )
        return resolved

    for stmt in fn.assignments:
        if isinstance(stmt, ParsedIfBlock):
            # Constant-fold leave-bearing if/switch before rejecting.
            # If the leave branch is dead, rewrite to a non-leave block.
            if stmt.has_leave:
                pre_cond = substitute_expr(stmt.condition, subst)
                fold = _classify_if_fold(
                    _try_const_eval(pre_cond),
                    has_else=stmt.else_body is not None,
                )
                if fold == _IfFoldDecision.THEN_LIVE:
                    _reject_expr_stmts(
                        list(stmt.body_expr_stmts) if stmt.body_expr_stmts else None,
                        context=f"Inlining {fn.yul_name!r} then-branch has",
                    )
                    if stmt.else_body is not None:
                        # Strip dead else-body, keep as leave block.
                        stmt = ParsedIfBlock(
                            condition=stmt.condition,
                            body=stmt.body,
                            has_leave=True,
                            else_body=None,
                            body_expr_stmts=stmt.body_expr_stmts,
                        )
                    else:
                        # Unconditional leave: process body, return immediately.
                        for s in stmt.body:
                            expr = substitute_expr(s.expr, subst)
                            expr = inline_calls(
                                expr,
                                fn_table,
                                depth,
                                max_depth,
                                mstore_sink=mstore_sink,
                                unsupported_function_errors=unsupported_function_errors,
                            )
                            subst[s.target] = expr
                        if len(fn.rets) == 1:
                            return subst.get(fn.rets[0], IntLit(0))
                        return tuple(subst.get(r, IntLit(0)) for r in fn.rets)
                elif fold == _IfFoldDecision.ELSE_LIVE:
                    _reject_expr_stmts(
                        (
                            list(stmt.else_body_expr_stmts)
                            if stmt.else_body_expr_stmts
                            else None
                        ),
                        context=f"Inlining {fn.yul_name!r} else-branch has",
                    )
                    # Process else-body as straight-line, skip then-body.
                    assert stmt.else_body is not None  # ELSE_LIVE requires else
                    for s in stmt.else_body:
                        expr = substitute_expr(s.expr, subst)
                        expr = inline_calls(
                            expr,
                            fn_table,
                            depth,
                            max_depth,
                            mstore_sink=mstore_sink,
                            unsupported_function_errors=unsupported_function_errors,
                        )
                        subst[s.target] = expr
                    continue
                elif fold == _IfFoldDecision.DEAD:
                    continue
                else:  # NOT_CONSTANT
                    if stmt.else_body is not None:
                        raise ParseError(
                            f"Function {fn.yul_name!r} contains a leave-bearing switch/if-else. "
                            "Only a single top-level 'if cond { ... leave }' is supported "
                            "during helper inlining."
                        )
            if stmt.has_leave and leave_cond is not None:
                raise ParseError(
                    f"Function {fn.yul_name!r} contains multiple leave sites. "
                    "Only a single top-level 'if cond { ... leave }' is supported "
                    "during helper inlining."
                )
            # Evaluate condition
            cond = substitute_expr(stmt.condition, subst)
            cond = inline_calls(
                cond,
                fn_table,
                depth,
                max_depth,
                unsupported_function_errors=unsupported_function_errors,
            )

            # Constant-fold non-leave if/switch: eliminate dead branches
            # BEFORE processing bodies.  This prevents spurious
            # "conditional memory write" errors on dead code.
            if not stmt.has_leave:
                fold = _classify_if_fold(
                    _try_const_eval(cond),
                    has_else=stmt.else_body is not None,
                )
                if fold != _IfFoldDecision.NOT_CONSTANT:
                    if fold == _IfFoldDecision.THEN_LIVE:
                        _reject_expr_stmts(
                            (
                                list(stmt.body_expr_stmts)
                                if stmt.body_expr_stmts
                                else None
                            ),
                            context=f"Inlining {fn.yul_name!r} then-branch has",
                        )
                        live_body = stmt.body
                    elif fold == _IfFoldDecision.ELSE_LIVE:
                        _reject_expr_stmts(
                            (
                                list(stmt.else_body_expr_stmts)
                                if stmt.else_body_expr_stmts
                                else None
                            ),
                            context=f"Inlining {fn.yul_name!r} else-branch has",
                        )
                        assert stmt.else_body is not None  # ELSE_LIVE requires else
                        live_body = stmt.else_body
                    else:  # DEAD
                        continue
                    for s in live_body:
                        expr = substitute_expr(s.expr, subst)
                        expr = inline_calls(
                            expr,
                            fn_table,
                            depth,
                            max_depth,
                            mstore_sink=mstore_sink,
                            unsupported_function_errors=unsupported_function_errors,
                        )
                        subst[s.target] = expr
                    continue

            # Non-constant condition: both branches are live,
            # reject if either carries expression-statements.
            _reject_branch_expr_stmts(
                stmt,
                context=f"Inlining {fn.yul_name!r}",
            )

            # Process if-body assignments into a separate subst branch.
            if_subst = dict(subst)
            pre_if_sink_len = len(mstore_sink) if mstore_sink is not None else 0
            for s in stmt.body:
                expr = substitute_expr(s.expr, if_subst)
                expr = inline_calls(
                    expr,
                    fn_table,
                    depth,
                    max_depth,
                    mstore_sink=mstore_sink,
                    unsupported_function_errors=unsupported_function_errors,
                )
                if_subst[s.target] = expr

            if mstore_sink is not None and len(mstore_sink) > pre_if_sink_len:
                raise ParseError(
                    f"Conditional memory write detected in {fn.yul_name!r}: "
                    f"{len(mstore_sink) - pre_if_sink_len} uint512.from accessor "
                    "effect(s) emitted inside an if-block body. Keep uint512.from(...) outside "
                    "conditional helper control flow."
                )

            # Also process else_body if present (from switch).
            if stmt.else_body is not None:
                else_subst = dict(subst)
                pre_else_sink_len = len(mstore_sink) if mstore_sink is not None else 0
                for s in stmt.else_body:
                    expr = substitute_expr(s.expr, else_subst)
                    expr = inline_calls(
                        expr,
                        fn_table,
                        depth,
                        max_depth,
                        mstore_sink=mstore_sink,
                        unsupported_function_errors=unsupported_function_errors,
                    )
                    else_subst[s.target] = expr
                if mstore_sink is not None and len(mstore_sink) > pre_else_sink_len:
                    raise ParseError(
                        f"Conditional memory write detected in {fn.yul_name!r}: "
                        "uint512.from accessor effect(s) emitted inside an else-body. Keep "
                        "uint512.from(...) outside conditional helper control flow."
                    )

            if stmt.has_leave:
                # The if-block contains ``leave`` (early return).  Save
                # the if-branch return values; remaining assignments
                # after this if-block form the else branch.
                leave_cond = cond
                leave_subst = if_subst
                # Don't update subst — remaining assignments use the
                # pre-if state (the "else" path where the condition is false).
            elif stmt.else_body is not None:
                # If/else or switch: merge both branches with Ite.
                all_targets: list[str] = []
                seen: set[str] = set()
                for s in (*stmt.body, *stmt.else_body):
                    if s.target not in seen:
                        seen.add(s.target)
                        all_targets.append(s.target)
                for target in all_targets:
                    pre_val = subst.get(target, IntLit(0))
                    if_val = if_subst.get(target, pre_val)
                    else_val = else_subst.get(target, pre_val)
                    merged = _simplify_ite(cond, if_val, else_val)
                    if merged != pre_val:
                        subst[target] = merged
            else:
                # Normal if-block (no leave, no else): preserve the pre-if value
                # on the false path and merge with Ite.
                for s in stmt.body:
                    if_val = if_subst[s.target]
                    orig_val = subst.get(s.target, IntLit(0))
                    merged = _simplify_ite(cond, if_val, orig_val)
                    if merged != orig_val:
                        subst[s.target] = merged
        elif isinstance(stmt, MemoryWrite):
            raise ParseError(
                f"Cannot inline helper {fn.yul_name!r}: helper memory writes are "
                "unsupported unless the helper exactly matches "
                "uint512.from(x_hi, x_lo). Keep scratch mstore/mload in the "
                "selected function body."
            )
        else:
            pre_stmt_sink_len = len(mstore_sink) if mstore_sink is not None else 0
            expr = substitute_expr(stmt.expr, subst)
            expr = inline_calls(
                expr,
                fn_table,
                depth,
                max_depth,
                mstore_sink=mstore_sink,
                unsupported_function_errors=unsupported_function_errors,
            )
            if leave_cond is not None and mstore_sink is not None:
                if len(mstore_sink) > pre_stmt_sink_len:
                    raise ParseError(
                        f"Function {fn.yul_name!r} emits accessor memory writes "
                        "after a leave site. The helper inliner only supports "
                        "pure else-path code after 'if cond { ... leave }'."
                    )
            subst[stmt.target] = expr

    def _get_ret(r: str) -> Expr:
        else_val = _resolve(subst.get(r, IntLit(0)), subst)
        if leave_cond is not None and leave_subst is not None:
            if_val = _resolve(leave_subst.get(r, IntLit(0)), leave_subst)
            resolved_cond = _resolve(leave_cond, subst)
            return _simplify_ite(resolved_cond, if_val, else_val)
        return else_val

    if len(fn.rets) == 1:
        return _get_ret(fn.rets[0])
    return tuple(_get_ret(r) for r in fn.rets)


def inline_calls(
    expr: Expr,
    fn_table: dict[str, YulFunction],
    depth: int = 0,
    max_depth: int = 40,
    mstore_sink: list[FromWriteEffect] | None = None,
    unsupported_function_errors: dict[str, str] | None = None,
) -> Expr:
    """Recursively inline function calls in an expression.

    Walks the expression tree. When a ``Call`` targets a function in
    *fn_table*, its body is inlined via sequential substitution.
    ``Project`` wrappers (from multi-value ``let``) are resolved
    to the Nth return value of the inlined function.
    """
    if isinstance(expr, (IntLit, Var)):
        return expr
    if isinstance(expr, Ite):
        return Ite(
            inline_calls(
                expr.cond,
                fn_table,
                depth,
                max_depth=max_depth,
                mstore_sink=mstore_sink,
                unsupported_function_errors=unsupported_function_errors,
            ),
            inline_calls(
                expr.if_true,
                fn_table,
                depth,
                max_depth=max_depth,
                mstore_sink=mstore_sink,
                unsupported_function_errors=unsupported_function_errors,
            ),
            inline_calls(
                expr.if_false,
                fn_table,
                depth,
                max_depth=max_depth,
                mstore_sink=mstore_sink,
                unsupported_function_errors=unsupported_function_errors,
            ),
        )
    if isinstance(expr, Project):
        # Handle Project(N, M, Call(fn, ...)) for multi-return.
        # Must check BEFORE recursively inlining arguments, because
        # we need to inline the inner call as multi-return to extract
        # the Nth component.
        idx = expr.index
        total = expr.total
        inner = expr.inner
        if isinstance(inner, Call):
            # Recursively inline the inner call's arguments first
            inner_args = tuple(
                inline_calls(
                    a,
                    fn_table,
                    depth,
                    max_depth=max_depth,
                    mstore_sink=mstore_sink,
                    unsupported_function_errors=unsupported_function_errors,
                )
                for a in inner.args
            )
            if inner.name in fn_table:
                result = _inline_single_call(
                    fn_table[inner.name],
                    inner_args,
                    fn_table,
                    depth,
                    max_depth,
                    mstore_sink=mstore_sink,
                    unsupported_function_errors=unsupported_function_errors,
                )
                if isinstance(result, tuple):
                    if len(result) != total:
                        raise ParseError(
                            f"Project({idx}, {total}) expected {total} "
                            f"return values from {inner.name!r}, got {len(result)}"
                        )
                    if idx >= len(result):
                        raise ParseError(
                            f"Project({idx}, {total}) requested index {idx}, "
                            f"but {inner.name!r} only returned {len(result)} value(s)"
                        )
                    return result[idx]
                if total != 1 or idx != 0:
                    raise ParseError(
                        f"Project({idx}, {total}) expects {total} return "
                        f"values, but {inner.name!r} returned a single value"
                    )
                return result
            if (
                unsupported_function_errors is not None
                and inner.name in unsupported_function_errors
            ):
                raise ParseError(
                    f"Cannot inline helper {inner.name!r}: its Yul body was "
                    f"rejected during collection: "
                    f"{unsupported_function_errors[inner.name]}"
                )
            # Inner call not in table — rebuild with inlined args
            return Project(idx, total, Call(inner.name, inner_args))
        # Non-Call inner — just recurse
        return Project(
            idx,
            total,
            inline_calls(
                inner,
                fn_table,
                depth,
                max_depth=max_depth,
                mstore_sink=mstore_sink,
                unsupported_function_errors=unsupported_function_errors,
            ),
        )
    if isinstance(expr, Call):
        # Recurse into arguments
        args = tuple(
            inline_calls(
                a,
                fn_table,
                depth,
                max_depth=max_depth,
                mstore_sink=mstore_sink,
                unsupported_function_errors=unsupported_function_errors,
            )
            for a in expr.args
        )

        # Direct call to a collected function
        if expr.name in fn_table:
            fn = fn_table[expr.name]
            result = _inline_single_call(
                fn,
                args,
                fn_table,
                depth,
                max_depth,
                mstore_sink=mstore_sink,
                unsupported_function_errors=unsupported_function_errors,
            )
            if isinstance(result, tuple):
                raise ParseError(
                    f"Cannot inline multi-return function {expr.name!r} into a "
                    f"single-value context. Use tuple destructuring or an "
                    f"explicit Project wrapper."
                )
            return result
        if (
            unsupported_function_errors is not None
            and expr.name in unsupported_function_errors
        ):
            raise ParseError(
                f"Cannot inline helper {expr.name!r}: its Yul body was "
                f"rejected during collection: {unsupported_function_errors[expr.name]}"
            )

        return Call(expr.name, args)
    assert_never(expr)


def _inline_yul_function(
    yf: YulFunction,
    fn_table: dict[str, YulFunction],
    unsupported_function_errors: dict[str, str] | None = None,
) -> YulFunction:
    """Apply ``inline_calls`` to every expression in a YulFunction."""

    _reject_expr_stmts(
        yf.expr_stmts,
        context=f"Function {yf.yul_name!r} contains",
    )

    mstore_sink: list[FromWriteEffect] = []
    new_assignments: list[RawStatement] = []
    const_subst: dict[str, Expr] = {}
    for stmt in yf.assignments:
        if isinstance(stmt, ParsedIfBlock):
            _reject_branch_expr_stmts(
                stmt,
                context=f"Function {yf.yul_name!r}",
            )
            pre_len = len(mstore_sink)
            new_cond = inline_calls(
                substitute_expr(stmt.condition, const_subst),
                fn_table,
                mstore_sink=mstore_sink,
                unsupported_function_errors=unsupported_function_errors,
            )
            new_body: list[PlainAssignment] = []
            body_subst = dict(const_subst)
            body_locals: set[str] = set()
            for s in stmt.body:
                if s.is_declaration:
                    body_locals.add(s.target)
                inlined = inline_calls(
                    substitute_expr(s.expr, body_subst),
                    fn_table,
                    mstore_sink=mstore_sink,
                    unsupported_function_errors=unsupported_function_errors,
                )
                if s.target in body_locals:
                    cv = _try_const_eval(inlined)
                    if cv is not None:
                        body_subst[s.target] = inlined
                    else:
                        body_subst.pop(s.target, None)
                new_body.append(
                    PlainAssignment(s.target, inlined, is_declaration=s.is_declaration)
                )
            new_else_body: list[PlainAssignment] | None = None
            if stmt.else_body is not None:
                new_else_body = []
                else_subst = dict(const_subst)
                else_locals: set[str] = set()
                for s in stmt.else_body:
                    if s.is_declaration:
                        else_locals.add(s.target)
                    inlined = inline_calls(
                        substitute_expr(s.expr, else_subst),
                        fn_table,
                        mstore_sink=mstore_sink,
                        unsupported_function_errors=unsupported_function_errors,
                    )
                    if s.target in else_locals:
                        cv = _try_const_eval(inlined)
                        if cv is not None:
                            else_subst[s.target] = inlined
                        else:
                            else_subst.pop(s.target, None)
                    new_else_body.append(
                        PlainAssignment(s.target, inlined, is_declaration=s.is_declaration)
                    )
            if len(mstore_sink) > pre_len:
                raise ParseError(
                    f"Conditional memory write detected in {yf.yul_name!r} while "
                    "inlining a control-flow block. Exact uint512.from(...) "
                    "accessor writes must stay on the straight-line path."
                )
            new_if = ParsedIfBlock(
                condition=new_cond,
                body=tuple(new_body),
                has_leave=stmt.has_leave,
                else_body=(tuple(new_else_body) if new_else_body is not None else None),
                body_expr_stmts=stmt.body_expr_stmts,
                else_body_expr_stmts=stmt.else_body_expr_stmts,
            )
            # Invalidate any variables conditionally assigned
            for t in _stmt_targets(new_if):
                const_subst.pop(t, None)
            new_assignments.append(new_if)
        elif isinstance(stmt, MemoryWrite):
            pre_len = len(mstore_sink)
            new_addr = inline_calls(
                substitute_expr(stmt.address, const_subst),
                fn_table,
                mstore_sink=mstore_sink,
                unsupported_function_errors=unsupported_function_errors,
            )
            new_value = inline_calls(
                substitute_expr(stmt.value, const_subst),
                fn_table,
                mstore_sink=mstore_sink,
                unsupported_function_errors=unsupported_function_errors,
            )
            if len(mstore_sink) > pre_len:
                raise ParseError(
                    f"Nested memory write detected while evaluating an mstore in "
                    f"{yf.yul_name!r}. The supported memory model requires "
                    "direct straight-line writes."
                )
            new_assignments.append(MemoryWrite(new_addr, new_value))
        else:
            pre_len = len(mstore_sink)
            inlined = inline_calls(
                substitute_expr(stmt.expr, const_subst),
                fn_table,
                mstore_sink=mstore_sink,
                unsupported_function_errors=unsupported_function_errors,
            )
            if _try_const_eval(inlined) is not None:
                const_subst[stmt.target] = inlined
            else:
                const_subst.pop(stmt.target, None)
            for effect in mstore_sink[pre_len:]:
                new_assignments.extend(effect.lower())
            del mstore_sink[pre_len:]
            new_assignments.append(
                PlainAssignment(
                    stmt.target, inlined, is_declaration=stmt.is_declaration
                )
            )

    if mstore_sink:
        raise ParseError(
            f"Undrained mstore_sink after inlining {yf.yul_name!r}: "
            f"{len(mstore_sink)} FromWriteEffect(s) were never lowered. "
            "All uint512.from(...) effects must appear in plain-assignment context."
        )

    return YulFunction(
        yul_name=yf.yul_name,
        params=yf.params,
        rets=yf.rets,
        assignments=new_assignments,
    )


def _stmt_targets(stmt: RawStatement) -> list[str]:
    """Extract assignment targets from a raw statement.

    For ``ParsedIfBlock``, only returns targets that are outer-scope
    writes.  Branch-local declarations and their subsequent
    reassignments are excluded because they are separate bindings
    scoped to each branch.
    """
    if isinstance(stmt, ParsedIfBlock):
        targets: list[str] = []
        for branch in (stmt.body, stmt.else_body or ()):
            branch_locals: set[str] = set()
            for s in branch:
                if s.is_declaration:
                    branch_locals.add(s.target)
                elif s.target not in branch_locals:
                    targets.append(s.target)
        return targets
    if isinstance(stmt, MemoryWrite):
        return []
    return [stmt.target]


def _branch_reads_var_before_write(
    assignments: tuple[PlainAssignment, ...],
    *,
    var: str,
    initialized: bool,
) -> bool:
    """Whether a straight-line branch reads *var* before assigning it.

    Branch-local declarations (``let``) shadow the enclosing ``var`` only
    after their RHS is evaluated. Once shadowed, later reads in the same
    branch refer to the branch-local binding and do not count as reads of
    the enclosing variable.
    """
    branch_initialized = initialized
    branch_locals: set[str] = set()
    for stmt in assignments:
        if (
            not branch_initialized
            and var not in branch_locals
            and var in _expr_vars(stmt.expr)
        ):
            return True
        if stmt.is_declaration:
            branch_locals.add(stmt.target)
        elif stmt.target == var and var not in branch_locals:
            branch_initialized = True
    return False


def _branch_definitely_initializes_var(
    assignments: tuple[PlainAssignment, ...],
    *,
    var: str,
    initialized: bool,
) -> bool:
    """Whether *var* is definitely initialized after a straight-line branch.

    Branch-local declarations (``let``) and their subsequent reassignments
    are scoped to the branch and do not initialize *var* in the enclosing
    scope.  This mirrors the scoping logic in ``_stmt_targets``.
    """
    branch_initialized = initialized
    branch_locals: set[str] = set()
    for stmt in assignments:
        if stmt.is_declaration:
            branch_locals.add(stmt.target)
        elif stmt.target == var and var not in branch_locals:
            branch_initialized = True
    return branch_initialized


def _stmt_reads_var_before_write(
    stmt: RawStatement,
    *,
    var: str,
    initialized: bool,
) -> bool:
    """Whether *stmt* can read *var* before it is initialized on that path."""
    if isinstance(stmt, PlainAssignment):
        return not initialized and var in _expr_vars(stmt.expr)
    if isinstance(stmt, MemoryWrite):
        return not initialized and var in (
            _expr_vars(stmt.address) | _expr_vars(stmt.value)
        )

    if not initialized and var in _expr_vars(stmt.condition):
        return True

    if _branch_reads_var_before_write(stmt.body, var=var, initialized=initialized):
        return True
    if stmt.else_body is not None:
        return _branch_reads_var_before_write(
            stmt.else_body,
            var=var,
            initialized=initialized,
        )
    return False


def _stmt_definitely_initializes_var(
    stmt: RawStatement,
    *,
    var: str,
    initialized: bool,
) -> bool:
    """Whether *var* is definitely initialized after executing *stmt*."""
    if isinstance(stmt, PlainAssignment):
        return initialized or (stmt.target == var and not stmt.is_declaration)
    if isinstance(stmt, MemoryWrite):
        return initialized

    then_initialized = _branch_definitely_initializes_var(
        stmt.body,
        var=var,
        initialized=initialized,
    )
    else_initialized = _branch_definitely_initializes_var(
        stmt.else_body or (),
        var=var,
        initialized=initialized,
    )
    return then_initialized and else_initialized


def yul_function_to_model(
    yf: YulFunction,
    sol_fn_name: str,
    fn_map: dict[str, str],
    keep_solidity_locals: bool = False,
) -> FunctionModel:
    """Convert a parsed YulFunction into a FunctionModel.

    Performs copy propagation to eliminate compiler temporaries and renames
    variables/calls back to Solidity-level names.

    Validates:
    - Multi-assigned compiler temporaries are rejected.
    - The return variable is recognized and assigned in the model.
    - Distinct Yul signature binders must demangle to distinct IR names.
    - Memory use must stay within the explicit supported subset:
      straight-line constant-address, 32-byte-aligned ``mstore``/``mload``
      with no aliasing.
    """
    _reject_expr_stmts(
        yf.expr_stmts,
        context=f"Function {sol_fn_name!r} contains",
    )

    # ------------------------------------------------------------------
    # Pre-pass: count how many times each variable is assigned and
    # collect clean (demangled) names for collision detection.
    # A compiler temporary assigned more than once is unusual and could
    # indicate a naming-convention change that made a real variable look
    # like a temporary.
    # ------------------------------------------------------------------
    assign_counts: Counter[str] = Counter()
    all_clean_names: set[str] = set()
    for stmt in yf.assignments:
        targets = _stmt_targets(stmt)
        for target in targets:
            assign_counts[target] += 1
            clean = demangle_var(
                target,
                yf.params,
                yf.rets,
                keep_solidity_locals=keep_solidity_locals,
            )
            if clean is not None:
                all_clean_names.add(clean)

    var_map: dict[str, str] = {}
    subst: dict[str, Expr] = {}
    const_locals: dict[str, Expr] = {}
    memory_state: dict[int, Expr] = {}

    signature_name_sources: dict[str, str] = {}
    for name in [*yf.params, *yf.rets]:
        clean = demangle_var(
            name, yf.params, yf.rets, keep_solidity_locals=keep_solidity_locals
        )
        if clean:
            prior = signature_name_sources.get(clean)
            if prior is not None and prior != name:
                raise ParseError(
                    f"Distinct Yul signature binders {prior!r} and {name!r} in "
                    f"{sol_fn_name!r} both demangle to {clean!r}. Refuse to "
                    f"collapse separate parameter/return slots into one IR name."
                )
            signature_name_sources[clean] = name
            var_map[name] = clean
            all_clean_names.add(clean)

    # Save param names before SSA processing may rename them.
    param_names = tuple(var_map[p] for p in yf.params)

    # ------------------------------------------------------------------
    # SSA state: track assignment count per clean name so that
    # reassigned variables get distinct Lean names (_1, _2, ...).
    # Parameters start at count 1 (the function-parameter binding).
    # ------------------------------------------------------------------
    ssa_count: Counter[str] = Counter()
    emitted_ssa_names: set[str] = set()
    for name in yf.params:
        clean = var_map.get(name)
        if clean:
            ssa_count[clean] = 1
            emitted_ssa_names.add(clean)

    assignments: list[ModelStatement] = []

    # Emit explicit zero-initialization for return variables (Yul semantics).
    # We only need an explicit binder when a path can read the return slot
    # before any assignment on that path, or when the slot can remain
    # uninitialized until function exit.
    needs_zero_init: set[str] = set()
    for ret in yf.rets:
        initialized = False
        for s in yf.assignments:
            if _stmt_reads_var_before_write(s, var=ret, initialized=initialized):
                needs_zero_init.add(ret)
                break
            # A conditional write while not yet initialized means the
            # ConditionalBlock's else-output needs the zero-init value —
            # but only if the statement doesn't definitely initialize
            # the variable (e.g. switch with all branches writing it).
            if (
                not initialized
                and isinstance(s, ParsedIfBlock)
                and any(a.target == ret and not a.is_declaration for a in s.body)
                and not _stmt_definitely_initializes_var(
                    s,
                    var=ret,
                    initialized=False,
                )
            ):
                needs_zero_init.add(ret)
                break
            initialized = _stmt_definitely_initializes_var(
                s,
                var=ret,
                initialized=initialized,
            )
        if not initialized and ret not in needs_zero_init:
            needs_zero_init.add(ret)
    for ret in yf.rets:
        clean = var_map.get(ret)
        if (
            clean is not None
            and clean not in emitted_ssa_names
            and ret in needs_zero_init
        ):
            emitted_ssa_names.add(clean)
            ssa_count[clean] = 1
            assignments.append(Assignment(target=clean, expr=IntLit(0)))
            const_locals[clean] = IntLit(0)

    def _resolve_memory_address(
        expr: Expr,
        *,
        op_name: str,
        const_locals_state: dict[str, Expr],
    ) -> int:
        addr = _try_const_eval(substitute_expr(expr, const_locals_state))
        if addr is None:
            raise ParseError(
                f"{op_name} with non-constant address {expr!r} in "
                f"{sol_fn_name!r}. The supported memory model only allows "
                f"constant 32-byte-aligned scratch slots."
            )
        if addr % 32 != 0:
            raise ParseError(
                f"{op_name} with unaligned address {addr} in {sol_fn_name!r}. "
                f"The supported memory model only allows 32-byte-aligned "
                f"scratch slots."
            )
        return addr

    def _resolve_memory_expr(
        expr: Expr,
        *,
        const_locals_state: dict[str, Expr],
    ) -> Expr:
        if isinstance(expr, (IntLit, Var)):
            return expr
        if isinstance(expr, Ite):
            return Ite(
                _resolve_memory_expr(expr.cond, const_locals_state=const_locals_state),
                _resolve_memory_expr(
                    expr.if_true, const_locals_state=const_locals_state
                ),
                _resolve_memory_expr(
                    expr.if_false, const_locals_state=const_locals_state
                ),
            )
        if isinstance(expr, Project):
            return Project(
                expr.index,
                expr.total,
                _resolve_memory_expr(expr.inner, const_locals_state=const_locals_state),
            )
        if isinstance(expr, Call):
            if expr.name == "mload" and len(expr.args) == 1:
                addr = _resolve_memory_address(
                    expr.args[0],
                    op_name="mload",
                    const_locals_state=const_locals_state,
                )
                if addr not in memory_state:
                    raise ParseError(
                        f"mload at address {addr} in {sol_fn_name!r} has no "
                        f"matching prior mstore. Available addresses: "
                        f"{sorted(memory_state.keys())}"
                    )
                return memory_state[addr]
            return Call(
                expr.name,
                tuple(
                    _resolve_memory_expr(arg, const_locals_state=const_locals_state)
                    for arg in expr.args
                ),
            )
        assert_never(expr)

    def _wrap_u256_literals(expr: Expr) -> Expr:
        """Normalize IntLit values to [0, 2^256) per EVM u256 semantics."""
        if isinstance(expr, IntLit):
            wrapped = expr.value % WORD_MOD
            return IntLit(wrapped) if wrapped != expr.value else expr
        if isinstance(expr, Var):
            return expr
        if isinstance(expr, Ite):
            new_cond = _wrap_u256_literals(expr.cond)
            new_if = _wrap_u256_literals(expr.if_true)
            new_else = _wrap_u256_literals(expr.if_false)
            if (
                new_cond is expr.cond
                and new_if is expr.if_true
                and new_else is expr.if_false
            ):
                return expr
            return Ite(new_cond, new_if, new_else)
        if isinstance(expr, Project):
            new_inner = _wrap_u256_literals(expr.inner)
            if new_inner is expr.inner:
                return expr
            return Project(expr.index, expr.total, new_inner)
        if isinstance(expr, Call):
            new_args = tuple(_wrap_u256_literals(a) for a in expr.args)
            if new_args == expr.args:
                return expr
            return Call(expr.name, new_args)
        assert_never(expr)

    def _process_assignment_into(
        target: str,
        raw_expr: Expr,
        *,
        var_map_state: dict[str, str],
        subst_state: dict[str, Expr],
        const_locals_state: dict[str, Expr],
        inside_conditional: bool = False,
    ) -> Assignment | None:
        """Process a single raw assignment through copy-prop and demangling.

        Returns an Assignment if the target is a real variable, or None if
        it was copy-propagated into ``subst``.
        """
        expr = substitute_expr(raw_expr, subst_state)
        expr = rename_expr(expr, var_map_state, fn_map)
        expr = _resolve_memory_expr(expr, const_locals_state=const_locals_state)
        expr = _wrap_u256_literals(expr)

        # Detect out-of-scope variable references.  After substitution
        # and renaming, every Var should reference a previously emitted
        # SSA name or a name currently in var_map (which covers block-
        # local real variables added during _lower_live_branch).
        if not inside_conditional:
            known_names = emitted_ssa_names | set(var_map_state.values())
            for v in _expr_vars(expr):
                if v not in known_names:
                    raise ParseError(
                        f"out-of-scope variable use: {v!r} referenced by "
                        f"assignment to {target!r} in {sol_fn_name!r}"
                    )

        clean = demangle_var(
            target, yf.params, yf.rets, keep_solidity_locals=keep_solidity_locals
        )
        if clean is None:
            if assign_counts[target] > 1:
                raise ParseError(
                    f"Variable {target!r} in {sol_fn_name!r} is classified "
                    f"as a compiler temporary but is assigned "
                    f"{assign_counts[target]} times. Refuse to copy-propagate "
                    f"a multi-assigned temporary; demangle_var may be "
                    f"misclassifying a real variable."
                )
            if isinstance(expr, Call) and expr.name.startswith("zero_value_for_split_"):
                subst_state[target] = IntLit(0)
            else:
                subst_state[target] = expr
            return None

        # SSA: compute the Lean target name.  Inside conditional
        # blocks, Lean's scoped ``let`` handles shadowing, so we
        # use the base clean name directly.
        if not inside_conditional:
            ssa_count[clean] += 1
            if ssa_count[clean] == 1:
                ssa_name = clean
            else:
                ssa_name = f"{clean}_{ssa_count[clean] - 1}"
                while ssa_name in emitted_ssa_names:
                    ssa_count[clean] += 1
                    ssa_name = f"{clean}_{ssa_count[clean] - 1}"
                if ssa_name in all_clean_names:
                    raise ParseError(
                        f"SSA-generated name {ssa_name!r} in {sol_fn_name!r} "
                        f"collides with the demangled name of another variable. "
                        f"Refuse to generate ambiguous Lean binders."
                    )
            emitted_ssa_names.add(ssa_name)
        else:
            ssa_name = clean

        # Update var_map AFTER rename_expr.
        var_map_state[target] = ssa_name

        if not inside_conditional:
            const_value = _try_const_eval(substitute_expr(expr, const_locals_state))
            if const_value is not None:
                const_locals_state[ssa_name] = IntLit(const_value)
            else:
                const_locals_state.pop(ssa_name, None)

        return Assignment(target=ssa_name, expr=expr)

    def _lower_live_branch(
        body: tuple[PlainAssignment, ...],
    ) -> None:
        """Lower a constant-folded live branch as straight-line in a lexical scope.

        Maintains a block-local environment of names introduced by
        ``let`` in this block:

        - A **declaration** adds its target to the local set and parks
          the processed value in ``subst``.
        - A later **reassignment** to a name in the local set updates
          that local binding in ``subst`` (never hits outer SSA).
        - Only assignments to names *not* local to this block go
          through the normal outer SSA machinery.

        At block exit, all local ``subst`` entries are removed (or
        shadowed outer values are restored).
        """
        # Track block-local subst entries for cleanup at block exit.
        # Each entry saves the previous subst value (or None) so that
        # shadowed outer copy-propagation entries are restored.
        local_subst_saves: list[tuple[str, Expr | None]] = []
        block_locals: set[str] = set()

        def _park_local(target: str, raw_expr: Expr) -> None:
            """Process *raw_expr* and park the result in subst for *target*."""
            expr = substitute_expr(raw_expr, subst)
            expr = rename_expr(expr, var_map, fn_map)
            expr = _resolve_memory_expr(
                expr,
                const_locals_state=const_locals,
            )
            expr = _wrap_u256_literals(expr)
            subst[target] = expr

        for s in body:
            if s.is_declaration:
                # Block-local declaration: add to local set, park in subst.
                block_locals.add(s.target)
                saved = subst.get(s.target)
                _park_local(s.target, s.expr)
                local_subst_saves.append((s.target, saved))
            elif s.target in block_locals:
                # Reassignment of a block-local name — update local subst.
                _park_local(s.target, s.expr)
            else:
                # Outer reassignment: full SSA, emit to assignments,
                # const_locals updated.
                a = _process_assignment_into(
                    s.target,
                    s.expr,
                    var_map_state=var_map,
                    subst_state=subst,
                    const_locals_state=const_locals,
                )
                if a is not None:
                    assignments.append(a)

        # Clean up block-local subst entries.
        for k, saved in local_subst_saves:
            if saved is None:
                subst.pop(k, None)
            else:
                subst[k] = saved

    for stmt in yf.assignments:
        if isinstance(stmt, ParsedIfBlock):
            # Constant-fold the condition before rejecting leave.
            if stmt.has_leave:
                cond_sub = substitute_expr(stmt.condition, subst)
                fold = _classify_if_fold(
                    _try_const_eval(cond_sub),
                    has_else=stmt.else_body is not None,
                )
                if fold == _IfFoldDecision.ELSE_LIVE:
                    _reject_expr_stmts(
                        (
                            list(stmt.else_body_expr_stmts)
                            if stmt.else_body_expr_stmts
                            else None
                        ),
                        context=f"Function {sol_fn_name!r} else-branch has",
                    )
                    assert stmt.else_body is not None  # ELSE_LIVE requires else
                    _lower_live_branch(stmt.else_body)
                    continue
                if fold == _IfFoldDecision.DEAD:
                    continue
                # THEN_LIVE or NOT_CONSTANT with leave → error
                raise ParseError(
                    f"Function {sol_fn_name!r} contains 'leave' in direct model "
                    "generation. Early return is only supported when inlining a "
                    "helper with a single top-level 'if cond { ... leave }'."
                )
            # Non-leave: constant-fold all cases via _classify_if_fold.
            cond_sub = substitute_expr(stmt.condition, subst)
            fold = _classify_if_fold(
                _try_const_eval(cond_sub),
                has_else=stmt.else_body is not None,
            )
            if fold == _IfFoldDecision.THEN_LIVE:
                _reject_expr_stmts(
                    list(stmt.body_expr_stmts) if stmt.body_expr_stmts else None,
                    context=f"Function {sol_fn_name!r} then-branch has",
                )
                _lower_live_branch(stmt.body)
                continue
            if fold == _IfFoldDecision.ELSE_LIVE:
                _reject_expr_stmts(
                    (
                        list(stmt.else_body_expr_stmts)
                        if stmt.else_body_expr_stmts
                        else None
                    ),
                    context=f"Function {sol_fn_name!r} else-branch has",
                )
                assert stmt.else_body is not None  # ELSE_LIVE requires else
                _lower_live_branch(stmt.else_body)
                continue
            if fold == _IfFoldDecision.DEAD:
                continue
            # NOT_CONSTANT: fall through to ConditionalBlock emission.
            _reject_branch_expr_stmts(
                stmt,
                context=f"Function {sol_fn_name!r}",
            )
            # Process the if-block: apply copy-prop/demangling to
            # condition and body, then emit a ConditionalBlock.
            cond = substitute_expr(stmt.condition, subst)
            cond = rename_expr(cond, var_map, fn_map)
            cond = _resolve_memory_expr(cond, const_locals_state=const_locals)

            # Save pre-if Lean names so each branch can explicitly return
            # the values that were live before the conditional ran.
            pre_if_names: dict[str, str] = {}
            # Snapshot of all Lean names in scope before the if-body.
            pre_if_scope: set[str] = set(var_map.values())

            def _record_pre_if_name(target: str) -> str | None:
                clean = demangle_var(
                    target,
                    yf.params,
                    yf.rets,
                    keep_solidity_locals=keep_solidity_locals,
                )
                if clean is not None and clean not in pre_if_names:
                    pre_if_names[clean] = var_map.get(target, clean)
                return clean

            def _process_conditional_branch(
                raw_assignments: tuple[PlainAssignment, ...],
            ) -> list[Assignment]:
                branch_var_map = dict(var_map)
                branch_subst = dict(subst)
                branch_const_locals = dict(const_locals)
                branch_assignments: list[Assignment] = []
                branch_locals: set[str] = set()
                for s in raw_assignments:
                    if s.is_declaration:
                        # Branch-local declaration: park in branch_subst
                        # so later statements can resolve it.  Do not
                        # emit — this binding dies at branch exit.
                        branch_locals.add(s.target)
                        expr = substitute_expr(s.expr, branch_subst)
                        expr = rename_expr(expr, branch_var_map, fn_map)
                        expr = _resolve_memory_expr(
                            expr,
                            const_locals_state=branch_const_locals,
                        )
                        expr = _wrap_u256_literals(expr)
                        branch_subst[s.target] = expr
                        # Track const fact for mload address resolution.
                        clean = demangle_var(
                            s.target,
                            yf.params,
                            yf.rets,
                            keep_solidity_locals=keep_solidity_locals,
                        )
                        if clean is not None:
                            cv = _try_const_eval(
                                substitute_expr(expr, branch_const_locals),
                            )
                            if cv is not None:
                                branch_const_locals[clean] = IntLit(cv)
                    elif s.target in branch_locals:
                        # Reassignment of branch-local — update subst.
                        expr = substitute_expr(s.expr, branch_subst)
                        expr = rename_expr(expr, branch_var_map, fn_map)
                        expr = _resolve_memory_expr(
                            expr,
                            const_locals_state=branch_const_locals,
                        )
                        expr = _wrap_u256_literals(expr)
                        branch_subst[s.target] = expr
                    else:
                        # Outer-scope modification.
                        _record_pre_if_name(s.target)
                        assignment = _process_assignment_into(
                            s.target,
                            s.expr,
                            var_map_state=branch_var_map,
                            subst_state=branch_subst,
                            const_locals_state=branch_const_locals,
                            inside_conditional=True,
                        )
                        if assignment is not None:
                            branch_assignments.append(assignment)
                return branch_assignments

            body_assignments = _process_conditional_branch(stmt.body)
            else_assignments_list = (
                _process_conditional_branch(stmt.else_body)
                if stmt.else_body is not None
                else []
            )

            # Deduplicate while preserving order, excluding block-scoped
            # variables that did not exist before the conditional.
            seen_vars: set[str] = set()
            modified_list: list[str] = []
            for branch_assignment in (*body_assignments, *else_assignments_list):
                if branch_assignment.target in seen_vars:
                    continue
                seen_vars.add(branch_assignment.target)
                pre_name = pre_if_names.get(branch_assignment.target)
                if pre_name is not None and pre_name in pre_if_scope:
                    modified_list.append(branch_assignment.target)

            if modified_list:
                modified = tuple(modified_list)
                then_assigned = {a.target for a in body_assignments}
                else_assigned = {a.target for a in else_assignments_list}
                then_outputs = tuple(
                    target if target in then_assigned else pre_if_names[target]
                    for target in modified_list
                )
                if stmt.else_body is None:
                    else_outputs = tuple(
                        pre_if_names[target] for target in modified_list
                    )
                else:
                    else_outputs = tuple(
                        target if target in else_assigned else pre_if_names[target]
                        for target in modified_list
                    )

                assignments.append(
                    ConditionalBlock(
                        condition=cond,
                        output_vars=modified,
                        then_branch=ConditionalBranch(
                            assignments=tuple(body_assignments),
                            outputs=then_outputs,
                        ),
                        else_branch=ConditionalBranch(
                            assignments=tuple(else_assignments_list),
                            outputs=else_outputs,
                        ),
                    )
                )

                # After the conditional the Lean tuple-destructuring creates
                # fresh bindings with the base clean names. Reset var_map and
                # ssa_count accordingly so later references are correct.
                modified_set = set(modified_list)

                # Build lookup of last expression per target in each branch.
                then_last: dict[str, Expr] = {}
                for a in body_assignments:
                    then_last[a.target] = a.expr
                else_last: dict[str, Expr] = {}
                for a in else_assignments_list:
                    else_last[a.target] = a.expr

                all_body_targets = list(stmt.body)
                if stmt.else_body is not None:
                    all_body_targets.extend(stmt.else_body)
                for s in all_body_targets:
                    c = demangle_var(
                        s.target,
                        yf.params,
                        yf.rets,
                        keep_solidity_locals=keep_solidity_locals,
                    )
                    if c is not None and c in modified_set:
                        var_map[s.target] = c
                        ssa_count[c] = 1
                        # Preserve const fact if both branches agree.
                        pre_cv = const_locals.get(c)
                        t_expr = then_last.get(c)
                        e_expr = else_last.get(c)
                        t_cv = (
                            _try_const_eval(t_expr)
                            if t_expr is not None
                            else (pre_cv.value if isinstance(pre_cv, IntLit) else None)
                        )
                        e_cv = (
                            _try_const_eval(e_expr)
                            if e_expr is not None
                            else (pre_cv.value if isinstance(pre_cv, IntLit) else None)
                        )
                        if t_cv is not None and t_cv == e_cv:
                            const_locals[c] = IntLit(t_cv)
                        else:
                            const_locals.pop(c, None)
            continue

        if isinstance(stmt, MemoryWrite):
            addr_expr = substitute_expr(stmt.address, subst)
            addr_expr = rename_expr(addr_expr, var_map, fn_map)
            value_expr = substitute_expr(stmt.value, subst)
            value_expr = rename_expr(value_expr, var_map, fn_map)
            value_expr = _resolve_memory_expr(
                value_expr,
                const_locals_state=const_locals,
            )
            addr = _resolve_memory_address(
                addr_expr,
                op_name="mstore",
                const_locals_state=const_locals,
            )
            if addr in memory_state:
                raise ParseError(
                    f"Multiple mstore writes to address {addr} in {sol_fn_name!r}. "
                    f"The supported memory model forbids aliasing or overwrite "
                    f"of scratch slots."
                )
            memory_state[addr] = value_expr
            continue

        maybe_a = _process_assignment_into(
            stmt.target,
            stmt.expr,
            var_map_state=var_map,
            subst_state=subst,
            const_locals_state=const_locals,
        )
        if maybe_a is not None:
            assignments.append(maybe_a)

    if not assignments:
        raise ParseError(f"No assignments parsed for function {sol_fn_name!r}")

    # ------------------------------------------------------------------
    # Post-build validation: ensure the return variable(s) were recognized.
    # If demangle_var failed to match a return variable's naming
    # pattern, the model would silently lose the output.
    # ------------------------------------------------------------------
    return_names_list: list[str] = []
    for ret_var in yf.rets:
        return_clean = var_map.get(ret_var)
        if return_clean is None:
            raise ParseError(
                f"Return variable {ret_var!r} of {sol_fn_name!r} was not "
                f"recognized as a real variable by demangle_var. The compiler "
                f"naming convention may have changed. Current patterns: "
                f"var_<name>_<digits> for param/return, usr$<name> for locals."
            )
        # Use the final (possibly SSA-renamed) var_map entry.
        return_names_list.append(var_map[ret_var])

    model = FunctionModel(
        fn_name=sol_fn_name,
        assignments=tuple(assignments),
        param_names=param_names,
        return_names=tuple(return_names_list),
    )

    validate_function_model(model)
    return model


def _prune_dead_assignments(
    model: FunctionModel,
) -> FunctionModel:
    """Drop dead pure assignments from a model to avoid unused Lean lets."""

    def _prune_assignment_block(
        assignments: tuple[Assignment, ...],
        live_out: set[str],
    ) -> tuple[tuple[Assignment, ...], set[str]]:
        live = set(live_out)
        kept_rev: list[Assignment] = []
        for stmt in reversed(assignments):
            if stmt.target not in live:
                continue
            live.remove(stmt.target)
            live.update(_expr_vars(stmt.expr))
            kept_rev.append(stmt)
        kept_rev.reverse()
        return tuple(kept_rev), live

    live = set(model.return_names)
    kept_rev: list[ModelStatement] = []

    for stmt in reversed(model.assignments):
        if isinstance(stmt, Assignment):
            if stmt.target not in live:
                continue
            live.remove(stmt.target)
            live.update(_expr_vars(stmt.expr))
            kept_rev.append(stmt)
            continue

        if not isinstance(stmt, ConditionalBlock):
            assert_never(stmt)

        needed_indices = tuple(
            idx for idx, output in enumerate(stmt.output_vars) if output in live
        )
        needed_outputs = tuple(stmt.output_vars[idx] for idx in needed_indices)
        if not needed_outputs:
            continue

        then_assignments, then_live = _prune_assignment_block(
            stmt.then_branch.assignments,
            {stmt.then_branch.outputs[idx] for idx in needed_indices},
        )
        else_assignments, else_live = _prune_assignment_block(
            stmt.else_branch.assignments,
            {stmt.else_branch.outputs[idx] for idx in needed_indices},
        )

        live.difference_update(needed_outputs)
        live.update(_expr_vars(stmt.condition))
        live.update(then_live)
        live.update(else_live)

        kept_rev.append(
            ConditionalBlock(
                condition=stmt.condition,
                output_vars=needed_outputs,
                then_branch=ConditionalBranch(
                    assignments=then_assignments,
                    outputs=tuple(
                        stmt.then_branch.outputs[idx] for idx in needed_indices
                    ),
                ),
                else_branch=ConditionalBranch(
                    assignments=else_assignments,
                    outputs=tuple(
                        stmt.else_branch.outputs[idx] for idx in needed_indices
                    ),
                ),
            )
        )

    kept_rev.reverse()
    result = FunctionModel(
        fn_name=model.fn_name,
        assignments=tuple(kept_rev),
        param_names=model.param_names,
        return_names=model.return_names,
    )
    validate_function_model(result)
    return result


# ---------------------------------------------------------------------------
# Lean emission helpers
# ---------------------------------------------------------------------------

_SUPPORTED_OPS = (
    "add",
    "sub",
    "mul",
    "div",
    "mod",
    "not",
    "or",
    "and",
    "eq",
    "iszero",
    "shl",
    "shr",
    "clz",
    "lt",
    "gt",
    "mulmod",
)

OP_TO_LEAN_HELPER: dict[str, str] = {
    op: f"evm{op.capitalize()}" for op in _SUPPORTED_OPS
}
OP_TO_OPCODE: dict[str, str] = {op: op.upper() for op in _SUPPORTED_OPS}

# Base norm helpers shared by all generators.  Per-generator extras (like
# bitLengthPlus1 for cbrt) are merged in via ModelConfig.extra_norm_ops.
_BASE_NORM_HELPERS: dict[str, str] = {
    op: f"norm{op.capitalize()}" for op in _SUPPORTED_OPS
}


_LEAN_KEYWORDS: frozenset[str] = frozenset(
    {
        "if",
        "then",
        "else",
        "let",
        "in",
        "do",
        "where",
        "match",
        "with",
        "fun",
        "return",
        "import",
        "open",
        "namespace",
        "end",
        "def",
        "theorem",
        "lemma",
        "example",
        "structure",
        "class",
        "instance",
        "section",
        "variable",
        "universe",
        "axiom",
        "inductive",
        "coinductive",
        "mutual",
        "partial",
        "unsafe",
        "private",
        "protected",
        "noncomputable",
        "macro",
        "syntax",
        "notation",
        "prefix",
        "infix",
        "infixl",
        "infixr",
        "postfix",
        "attribute",
        "deriving",
        "extends",
        "abbrev",
        "opaque",
        "set_option",
        "for",
        "true",
        "false",
        "Type",
        "Prop",
        "Sort",
    }
)

_RESERVED_LEAN_NAMES: frozenset[str] = frozenset(
    {"u256", "WORD_MOD"}
    | set(OP_TO_LEAN_HELPER.values())
    | set(_BASE_NORM_HELPERS.values())
    | _LEAN_KEYWORDS
)


def validate_ident(name: str, *, what: str) -> None:
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
        raise ParseError(f"Invalid {what}: {name!r}")
    if name in _RESERVED_LEAN_NAMES:
        raise ParseError(f"Reserved Lean helper name used as {what}: {name!r}")


def collect_ops(expr: Expr) -> list[str]:
    out: list[str] = []
    if isinstance(expr, Ite):
        out.extend(collect_ops(expr.cond))
        out.extend(collect_ops(expr.if_true))
        out.extend(collect_ops(expr.if_false))
    elif isinstance(expr, Project):
        out.extend(collect_ops(expr.inner))
    elif isinstance(expr, Call):
        if expr.name in OP_TO_OPCODE:
            out.append(expr.name)
        for arg in expr.args:
            out.extend(collect_ops(arg))
    return out


def collect_ops_from_statement(stmt: ModelStatement) -> list[str]:
    """Collect opcodes from an Assignment or ConditionalBlock."""
    if isinstance(stmt, Assignment):
        return collect_ops(stmt.expr)
    if isinstance(stmt, ConditionalBlock):
        ops = collect_ops(stmt.condition)
        for a in stmt.then_branch.assignments:
            ops.extend(collect_ops(a.expr))
        for a in stmt.else_branch.assignments:
            ops.extend(collect_ops(a.expr))
        return ops
    assert_never(stmt)


def ordered_unique(items: list[str]) -> list[str]:
    d: dict[str, None] = dict.fromkeys(items)
    return list(d)


def collect_model_opcodes(models: list[FunctionModel]) -> list[str]:
    """Collect ordered unique opcodes used across all models."""
    raw_ops: list[str] = []
    for model in models:
        for stmt in model.assignments:
            raw_ops.extend(collect_ops_from_statement(stmt))
    return ordered_unique([OP_TO_OPCODE[name] for name in raw_ops])


def _expr_size(expr: Expr) -> int:
    if isinstance(expr, (IntLit, Var)):
        return 1
    if isinstance(expr, Ite):
        return (
            1
            + _expr_size(expr.cond)
            + _expr_size(expr.if_true)
            + _expr_size(expr.if_false)
        )
    if isinstance(expr, Project):
        return 1 + _expr_size(expr.inner)
    if isinstance(expr, Call):
        return 1 + sum(_expr_size(arg) for arg in expr.args)
    assert_never(expr)


def _replace_expr(expr: Expr, replacements: dict[Expr, str]) -> Expr:
    if expr in replacements:
        return Var(replacements[expr])
    if isinstance(expr, (IntLit, Var)):
        return expr
    if isinstance(expr, Ite):
        return Ite(
            _replace_expr(expr.cond, replacements),
            _replace_expr(expr.if_true, replacements),
            _replace_expr(expr.if_false, replacements),
        )
    if isinstance(expr, Project):
        return Project(expr.index, expr.total, _replace_expr(expr.inner, replacements))
    if isinstance(expr, Call):
        return Call(
            expr.name, tuple(_replace_expr(arg, replacements) for arg in expr.args)
        )
    assert_never(expr)


def _expr_vars(expr: Expr) -> set[str]:
    if isinstance(expr, IntLit):
        return set()
    if isinstance(expr, Var):
        return {expr.name}
    if isinstance(expr, Ite):
        return (
            _expr_vars(expr.cond) | _expr_vars(expr.if_true) | _expr_vars(expr.if_false)
        )
    if isinstance(expr, Project):
        return _expr_vars(expr.inner)
    if isinstance(expr, Call):
        out: set[str] = set()
        for arg in expr.args:
            out.update(_expr_vars(arg))
        return out
    assert_never(expr)


def validate_function_model(model: FunctionModel) -> None:
    """Reject malformed restricted-IR models before Lean emission."""

    # -- Structural invariants on names --
    if len(set(model.param_names)) != len(model.param_names):
        raise ParseError(
            f"Model {model.fn_name!r} has duplicate param names: {model.param_names!r}"
        )
    if len(set(model.return_names)) != len(model.return_names):
        raise ParseError(
            f"Model {model.fn_name!r} has duplicate return names: {model.return_names!r}"
        )
    if model.fn_name in OP_TO_LEAN_HELPER:
        raise ParseError(f"Model name {model.fn_name!r} collides with builtin opcode")
    if not model.return_names:
        raise ParseError(
            f"Model {model.fn_name!r} has no return variables; "
            f"restricted-IR functions must return at least one value"
        )
    # Validate all identifiers used as binders.
    for name in model.param_names:
        validate_ident(name, what=f"param name in {model.fn_name!r}")
    for name in model.return_names:
        validate_ident(name, what=f"return name in {model.fn_name!r}")

    for stmt in model.assignments:
        if isinstance(stmt, Assignment):
            validate_ident(stmt.target, what=f"assignment target in {model.fn_name!r}")
        elif isinstance(stmt, ConditionalBlock):
            for var in stmt.output_vars:
                validate_ident(var, what=f"conditional output var in {model.fn_name!r}")
            if len(set(stmt.output_vars)) != len(stmt.output_vars):
                raise ParseError(
                    f"Model {model.fn_name!r} has duplicate conditional output_vars: "
                    f"{stmt.output_vars!r}"
                )
            for a in stmt.then_branch.assignments:
                validate_ident(
                    a.target, what=f"then-branch target in {model.fn_name!r}"
                )
            for a in stmt.else_branch.assignments:
                validate_ident(
                    a.target, what=f"else-branch target in {model.fn_name!r}"
                )

    def _validate_assignment_block(
        assignments: tuple[Assignment, ...],
        *,
        available: set[str],
        block_name: str,
    ) -> set[str]:
        scope = set(available)
        for stmt in assignments:
            missing = _expr_vars(stmt.expr) - scope
            if missing:
                raise ParseError(
                    f"Model {model.fn_name!r} has an out-of-scope variable use in "
                    f"{block_name}: {stmt.target!r} depends on {sorted(missing)}"
                )
            scope.add(stmt.target)
        return scope

    def _validate_conditional_branch(
        branch: ConditionalBranch,
        *,
        available: set[str],
        block_name: str,
        output_vars: tuple[str, ...],
    ) -> None:
        branch_scope = _validate_assignment_block(
            branch.assignments,
            available=available,
            block_name=block_name,
        )
        if len(branch.outputs) != len(output_vars):
            raise ParseError(
                f"Model {model.fn_name!r} has mismatched {block_name} output arity: "
                f"{len(branch.outputs)} vs {len(output_vars)}"
            )
        missing_outputs = set(branch.outputs) - branch_scope
        if missing_outputs:
            raise ParseError(
                f"Model {model.fn_name!r} has undefined {block_name} outputs: "
                f"{sorted(missing_outputs)}"
            )

    def _validate_expr_shape(expr: Expr) -> None:
        """Reject structurally malformed expressions."""
        if isinstance(expr, Var):
            return
        if isinstance(expr, IntLit):
            if expr.value < 0:
                raise ParseError(
                    f"Model {model.fn_name!r}: IntLit({expr.value}) is negative "
                    f"(Yul integers are unsigned)"
                )
            return
        if isinstance(expr, Ite):
            _validate_expr_shape(expr.cond)
            _validate_expr_shape(expr.if_true)
            _validate_expr_shape(expr.if_false)
            return
        if isinstance(expr, Project):
            if not isinstance(expr.inner, Call):
                raise ParseError(
                    f"Model {model.fn_name!r}: Project({expr.index}, {expr.total}) inner "
                    f"must be a Call, got {type(expr.inner).__name__}"
                )
            if expr.index < 0 or expr.index >= expr.total:
                raise ParseError(
                    f"Model {model.fn_name!r}: Project({expr.index}, {expr.total}) index "
                    f"{expr.index} out of range [0, {expr.total})"
                )
            if expr.total < 2:
                raise ParseError(
                    f"Model {model.fn_name!r}: Project({expr.index}, {expr.total}) "
                    f"requires total >= 2 (scalar values cannot be projected)"
                )
            if expr.inner.name in OP_TO_LEAN_HELPER:
                raise ParseError(
                    f"Model {model.fn_name!r}: cannot project builtin "
                    f"{expr.inner.name!r} (returns scalar, not tuple)"
                )
            _validate_expr_shape(expr.inner)
            return
        if not isinstance(expr, Call):
            assert_never(expr)
        # Builtin arity check
        if expr.name in OP_TO_LEAN_HELPER:
            expected = (
                1
                if expr.name in ("not", "clz", "iszero")
                else (3 if expr.name == "mulmod" else 2)
            )
            if len(expr.args) != expected:
                raise ParseError(
                    f"Model {model.fn_name!r}: builtin {expr.name!r} expects "
                    f"{expected} arg(s), got {len(expr.args)}"
                )
        for arg in expr.args:
            _validate_expr_shape(arg)

    scope = set(model.param_names)
    for stmt in model.assignments:
        if isinstance(stmt, Assignment):
            _validate_expr_shape(stmt.expr)
            missing = _expr_vars(stmt.expr) - scope
            if missing:
                raise ParseError(
                    f"Model {model.fn_name!r} has an out-of-scope variable use: "
                    f"{stmt.target!r} depends on {sorted(missing)}"
                )
            scope.add(stmt.target)
            continue

        if not isinstance(stmt, ConditionalBlock):
            assert_never(stmt)

        _validate_expr_shape(stmt.condition)
        for a in stmt.then_branch.assignments:
            _validate_expr_shape(a.expr)
        for a in stmt.else_branch.assignments:
            _validate_expr_shape(a.expr)

        missing = _expr_vars(stmt.condition) - scope
        if missing:
            raise ParseError(
                f"Model {model.fn_name!r} has an out-of-scope conditional: "
                f"{sorted(missing)}"
            )

        _validate_conditional_branch(
            stmt.then_branch,
            available=scope,
            block_name="then-branch",
            output_vars=stmt.output_vars,
        )
        _validate_conditional_branch(
            stmt.else_branch,
            available=scope,
            block_name="else-branch",
            output_vars=stmt.output_vars,
        )

        scope.update(stmt.output_vars)

    missing_returns = set(model.return_names) - scope
    if missing_returns:
        raise ParseError(
            f"Model {model.fn_name!r} returns undefined vars: {sorted(missing_returns)}"
        )


WORD_MOD = 2**256


def u256(value: int) -> int:
    return value % WORD_MOD


def _expect_scalar(value: ModelValue, *, context: str) -> int:
    if isinstance(value, tuple):
        raise EvaluationError(f"{context} expected a scalar value, got tuple {value!r}")
    return value


def _expect_tuple(value: ModelValue, *, size: int, context: str) -> tuple[int, ...]:
    if not isinstance(value, tuple):
        raise EvaluationError(
            f"{context} expected a {size}-tuple, got scalar {value!r}"
        )
    if len(value) != size:
        raise EvaluationError(
            f"{context} expected a {size}-tuple, got {len(value)} values: {value!r}"
        )
    return value


def _div(a: tuple[int, ...]) -> int:
    aa, bb = u256(a[0]), u256(a[1])
    return 0 if bb == 0 else aa // bb


def _mod(a: tuple[int, ...]) -> int:
    aa, bb = u256(a[0]), u256(a[1])
    return 0 if bb == 0 else aa % bb


def _shl(a: tuple[int, ...]) -> int:
    shift, value = u256(a[0]), u256(a[1])
    return u256(value << shift) if shift < 256 else 0


def _shr(a: tuple[int, ...]) -> int:
    shift, value = u256(a[0]), u256(a[1])
    return value >> shift if shift < 256 else 0


def _clz(a: tuple[int, ...]) -> int:
    value = u256(a[0])
    return 256 if value == 0 else 255 - (value.bit_length() - 1)


def _mulmod(a: tuple[int, ...]) -> int:
    aa, bb, nn = u256(a[0]), u256(a[1]), u256(a[2])
    return 0 if nn == 0 else (aa * bb) % nn


_BUILTIN_DISPATCH: dict[tuple[str, int], Callable[[tuple[int, ...]], int]] = {
    ("add", 2): lambda a: u256(u256(a[0]) + u256(a[1])),
    ("sub", 2): lambda a: u256(u256(a[0]) + WORD_MOD - u256(a[1])),
    ("mul", 2): lambda a: u256(u256(a[0]) * u256(a[1])),
    ("div", 2): _div,
    ("mod", 2): _mod,
    ("not", 1): lambda a: WORD_MOD - 1 - u256(a[0]),
    ("or", 2): lambda a: u256(a[0]) | u256(a[1]),
    ("and", 2): lambda a: u256(a[0]) & u256(a[1]),
    ("eq", 2): lambda a: 1 if u256(a[0]) == u256(a[1]) else 0,
    ("iszero", 1): lambda a: 1 if u256(a[0]) == 0 else 0,
    ("shl", 2): _shl,
    ("shr", 2): _shr,
    ("clz", 1): _clz,
    ("lt", 2): lambda a: 1 if u256(a[0]) < u256(a[1]) else 0,
    ("gt", 2): lambda a: 1 if u256(a[0]) > u256(a[1]) else 0,
    ("mulmod", 3): _mulmod,
}


def _eval_builtin(name: str, args: tuple[int, ...]) -> int:
    fn = _BUILTIN_DISPATCH.get((name, len(args)))
    if fn is not None:
        return fn(args)
    raise EvaluationError(f"Unsupported builtin call {name!r} with {len(args)} arg(s)")


def build_model_table(
    models: list[FunctionModel] | tuple[FunctionModel, ...],
) -> dict[str, FunctionModel]:
    table: dict[str, FunctionModel] = {}
    for model in models:
        if model.fn_name in table:
            raise EvaluationError(f"Duplicate FunctionModel name {model.fn_name!r}")
        table[model.fn_name] = model
    return table


def evaluate_model_expr(
    expr: Expr,
    env: dict[str, int],
    *,
    model_table: dict[str, FunctionModel] | None = None,
    call_stack: tuple[str, ...] = (),
) -> ModelValue:
    if isinstance(expr, IntLit):
        return expr.value % WORD_MOD
    if isinstance(expr, Var):
        try:
            return env[expr.name]
        except KeyError as err:
            raise EvaluationError(f"Undefined model variable {expr.name!r}") from err
    if isinstance(expr, Project):
        values = _expect_tuple(
            evaluate_model_expr(
                expr.inner,
                env,
                model_table=model_table,
                call_stack=call_stack,
            ),
            size=expr.total,
            context=f"Project({expr.index}, {expr.total}) projection",
        )
        try:
            return values[expr.index]
        except IndexError as err:
            raise EvaluationError(
                f"Project({expr.index}, {expr.total}) requested index {expr.index}, "
                f"but only {len(values)} value(s) exist"
            ) from err
    if isinstance(expr, Ite):
        cond = _expect_scalar(
            evaluate_model_expr(
                expr.cond,
                env,
                model_table=model_table,
                call_stack=call_stack,
            ),
            context="Ite condition",
        )
        branch = expr.if_true if cond != 0 else expr.if_false
        return evaluate_model_expr(
            branch,
            env,
            model_table=model_table,
            call_stack=call_stack,
        )
    if not isinstance(expr, Call):
        assert_never(expr)

    arg_values = tuple(
        evaluate_model_expr(arg, env, model_table=model_table, call_stack=call_stack)
        for arg in expr.args
    )

    if expr.name in OP_TO_LEAN_HELPER:
        return _eval_builtin(
            expr.name,
            tuple(
                _expect_scalar(value, context=f"builtin {expr.name}")
                for value in arg_values
            ),
        )

    if model_table is None or expr.name not in model_table:
        raise EvaluationError(f"Unsupported model call {expr.name!r}")

    model = model_table[expr.name]
    if expr.name in call_stack:
        cycle = " -> ".join((*call_stack, expr.name))
        raise EvaluationError(f"Recursive model call cycle detected: {cycle}")
    result = evaluate_function_model(
        model,
        tuple(
            _expect_scalar(value, context=f"model call {expr.name}")
            for value in arg_values
        ),
        model_table=model_table,
        call_stack=(*call_stack, expr.name),
    )
    if len(result) == 1:
        return result[0]
    return result


def _evaluate_statement_block(
    statements: tuple[ModelStatement, ...],
    env: dict[str, int],
    *,
    model_table: dict[str, FunctionModel] | None = None,
    call_stack: tuple[str, ...] = (),
) -> dict[str, int]:
    scope = dict(env)

    for stmt in statements:
        if isinstance(stmt, Assignment):
            scope[stmt.target] = _expect_scalar(
                evaluate_model_expr(
                    stmt.expr,
                    scope,
                    model_table=model_table,
                    call_stack=call_stack,
                ),
                context=f"assignment to {stmt.target!r}",
            )
            continue

        if not isinstance(stmt, ConditionalBlock):
            assert_never(stmt)

        condition = _expect_scalar(
            evaluate_model_expr(
                stmt.condition,
                scope,
                model_table=model_table,
                call_stack=call_stack,
            ),
            context="conditional",
        )

        branch = stmt.then_branch if condition != 0 else stmt.else_branch
        branch_scope = _evaluate_statement_block(
            branch.assignments,
            scope,
            model_table=model_table,
            call_stack=call_stack,
        )
        for target, source in zip(stmt.output_vars, branch.outputs, strict=True):
            scope[target] = branch_scope[source]

    return scope


def evaluate_function_model(
    model: FunctionModel,
    args: tuple[int, ...],
    *,
    model_table: dict[str, FunctionModel] | None = None,
    call_stack: tuple[str, ...] = (),
) -> tuple[int, ...]:
    if len(args) != len(model.param_names):
        raise EvaluationError(
            f"Model {model.fn_name!r} expects {len(model.param_names)} argument(s), "
            f"got {len(args)}"
        )

    env = {
        param_name: u256(value)
        for param_name, value in zip(model.param_names, args, strict=True)
    }
    final_env = _evaluate_statement_block(
        model.assignments,
        env,
        model_table=model_table,
        call_stack=call_stack,
    )
    try:
        return tuple(final_env[name] for name in model.return_names)
    except KeyError as err:
        raise EvaluationError(
            f"Model {model.fn_name!r} did not produce one of the declared return variables "
            f"{model.return_names!r}"
        ) from err


def _collect_repeated_model_calls(
    expr: Expr, model_call_names: frozenset[str]
) -> list[Expr]:
    counts: Counter[Expr] = Counter()
    _walk_model_calls(expr, model_call_names, counts)
    repeated = [node for node, count in counts.items() if count > 1]
    repeated.sort(key=_expr_size)
    return [node for node in repeated if isinstance(node, (Call, Project))]


def _is_component_wrapped_model_call(
    node: Expr, model_call_names: frozenset[str]
) -> bool:
    return (
        isinstance(node, Project)
        and isinstance(node.inner, Call)
        and node.inner.name in model_call_names
    )


def _walk_model_calls(
    node: Expr, model_call_names: frozenset[str], counts: Counter[Expr]
) -> None:
    """Recursively count model-call occurrences in *node*."""
    if isinstance(node, Project):
        if _is_component_wrapped_model_call(node, model_call_names):
            # Count the component-wrapped call as a unit and skip recursing
            # into the inner model call to avoid hoisting bare tuple-returning
            # calls that only appear inside component projections.
            counts[node] += 1
            assert isinstance(node.inner, Call)
            for arg in node.inner.args:
                _walk_model_calls(arg, model_call_names, counts)
            return
        _walk_model_calls(node.inner, model_call_names, counts)
    elif isinstance(node, Ite):
        _walk_model_calls(node.cond, model_call_names, counts)
        _walk_model_calls(node.if_true, model_call_names, counts)
        _walk_model_calls(node.if_false, model_call_names, counts)
    elif isinstance(node, Call):
        if node.name in model_call_names:
            counts[node] += 1
        for arg in node.args:
            _walk_model_calls(arg, model_call_names, counts)


def _replace_statement(
    stmt: ModelStatement, replacements: dict[Expr, str]
) -> ModelStatement:
    """Apply *replacements* inside a single statement."""
    if isinstance(stmt, Assignment):
        return Assignment(
            target=stmt.target,
            expr=_replace_expr(stmt.expr, replacements),
        )
    if isinstance(stmt, ConditionalBlock):
        return ConditionalBlock(
            condition=_replace_expr(stmt.condition, replacements),
            output_vars=stmt.output_vars,
            then_branch=ConditionalBranch(
                assignments=tuple(
                    Assignment(
                        target=a.target,
                        expr=_replace_expr(a.expr, replacements),
                    )
                    for a in stmt.then_branch.assignments
                ),
                outputs=stmt.then_branch.outputs,
            ),
            else_branch=ConditionalBranch(
                assignments=tuple(
                    Assignment(
                        target=a.target,
                        expr=_replace_expr(a.expr, replacements),
                    )
                    for a in stmt.else_branch.assignments
                ),
                outputs=stmt.else_branch.outputs,
            ),
        )
    assert_never(stmt)


def _hoist_repeated_calls_in_expr(
    expr: Expr,
    *,
    model_call_names: frozenset[str],
) -> tuple[list[Assignment], Expr]:
    repeated_calls = _collect_repeated_model_calls(expr, model_call_names)
    if not repeated_calls:
        return [], expr

    replacements: dict[Expr, str] = {}
    hoisted: list[Assignment] = []
    for call in repeated_calls:
        if isinstance(call, Project):
            if not _is_component_wrapped_model_call(call, model_call_names):
                raise ParseError(
                    f"CSE: refusing to hoist non-model projection {call!r}"
                )
        elif isinstance(call, Call):
            if call.name not in model_call_names:
                raise ParseError(f"CSE: refusing to hoist non-model call {call!r}")
        else:
            raise ParseError(f"CSE: refusing to hoist unexpected node {call!r}")
        hoisted_name = _gensym("cse")
        hoisted_expr = _replace_expr(call, replacements)
        hoisted.append(Assignment(target=hoisted_name, expr=hoisted_expr))
        replacements[call] = hoisted_name
    return hoisted, _replace_expr(expr, replacements)


def _localize_statement_cse(
    stmt: ModelStatement,
    *,
    model_call_names: frozenset[str],
) -> list[ModelStatement]:
    if isinstance(stmt, Assignment):
        hoisted, expr = _hoist_repeated_calls_in_expr(
            stmt.expr,
            model_call_names=model_call_names,
        )
        return [*hoisted, Assignment(target=stmt.target, expr=expr)]

    if isinstance(stmt, ConditionalBlock):
        prefix, condition = _hoist_repeated_calls_in_expr(
            stmt.condition,
            model_call_names=model_call_names,
        )

        then_assignments: list[Assignment] = []
        for assignment in stmt.then_branch.assignments:
            hoisted, expr = _hoist_repeated_calls_in_expr(
                assignment.expr,
                model_call_names=model_call_names,
            )
            then_assignments.extend(hoisted)
            then_assignments.append(Assignment(target=assignment.target, expr=expr))

        localized_else: list[Assignment] = []
        for assignment in stmt.else_branch.assignments:
            hoisted, expr = _hoist_repeated_calls_in_expr(
                assignment.expr,
                model_call_names=model_call_names,
            )
            localized_else.extend(hoisted)
            localized_else.append(Assignment(target=assignment.target, expr=expr))

        return [
            *prefix,
            ConditionalBlock(
                condition=condition,
                output_vars=stmt.output_vars,
                then_branch=ConditionalBranch(
                    assignments=tuple(then_assignments),
                    outputs=stmt.then_branch.outputs,
                ),
                else_branch=ConditionalBranch(
                    assignments=tuple(localized_else),
                    outputs=stmt.else_branch.outputs,
                ),
            ),
        ]

    assert_never(stmt)


def hoist_repeated_model_calls(
    model: FunctionModel,
    *,
    model_call_names: frozenset[str],
) -> FunctionModel:
    """Hoist repeated pure model-call sub-expressions into let-bindings.

    Collects repeated calls across *all* statements (assignments and
    conditional blocks), but only hoists them globally when every argument
    depends solely on function parameters. Calls that mention local or
    branch-assigned variables are hoisted only immediately before the
    statement that uses them (or inside the relevant conditional branch).
    This keeps hoisting within scopes where the referenced bindings are
    definitely available. Model calls are assumed pure.
    """
    # Initialize CSE counter past any existing _cse_N names (params, returns,
    # and assignment targets) to avoid collisions.
    max_cse = 0
    for name in (*model.param_names, *model.return_names):
        m = re.fullmatch(r"_cse_(\d+)", name)
        if m:
            max_cse = max(max_cse, int(m.group(1)))
    for stmt in model.assignments:
        if isinstance(stmt, Assignment):
            m = re.fullmatch(r"_cse_(\d+)", stmt.target)
            if m:
                max_cse = max(max_cse, int(m.group(1)))
        elif isinstance(stmt, ConditionalBlock):
            for var in stmt.output_vars:
                m = re.fullmatch(r"_cse_(\d+)", var)
                if m:
                    max_cse = max(max_cse, int(m.group(1)))
            for a in stmt.then_branch.assignments:
                m = re.fullmatch(r"_cse_(\d+)", a.target)
                if m:
                    max_cse = max(max_cse, int(m.group(1)))
            for a in stmt.else_branch.assignments:
                m = re.fullmatch(r"_cse_(\d+)", a.target)
                if m:
                    max_cse = max(max_cse, int(m.group(1)))
    _gensym_counters["cse"] = max_cse

    # -- Pass 1: count occurrences across the entire model -----------------
    counts: Counter[Expr] = Counter()
    for stmt in model.assignments:
        if isinstance(stmt, Assignment):
            _walk_model_calls(stmt.expr, model_call_names, counts)
        elif isinstance(stmt, ConditionalBlock):
            _walk_model_calls(stmt.condition, model_call_names, counts)
            for a in stmt.then_branch.assignments:
                _walk_model_calls(a.expr, model_call_names, counts)
            for a in stmt.else_branch.assignments:
                _walk_model_calls(a.expr, model_call_names, counts)

    param_names = set(model.param_names)
    repeated_global = [
        node
        for node, count in counts.items()
        if count > 1
        and isinstance(node, Call)
        and _expr_vars(node).issubset(param_names)
    ]
    repeated_global.sort(key=_expr_size)

    # Sanity: every hoisted call must be a known-pure model call.
    for call in repeated_global:
        if call.name not in model_call_names and not _is_component_wrapped_model_call(
            call, model_call_names
        ):
            raise ParseError(f"CSE: refusing to hoist non-model call {call!r}")

    # -- Pass 2: build global replacements and hoisted let-bindings --------
    global_replacements: dict[Expr, str] = {}
    hoisted_global: list[Assignment] = []
    for call in repeated_global:
        hoisted_name = _gensym("cse")
        hoisted_expr = _replace_expr(call, global_replacements)
        hoisted_global.append(Assignment(target=hoisted_name, expr=hoisted_expr))
        global_replacements[call] = hoisted_name

    # -- Pass 3: rewrite all statements with global replacements -----------
    rewritten_statements = [
        _replace_statement(stmt, global_replacements) for stmt in model.assignments
    ]

    # -- Pass 4: locally hoist remaining repeated calls in safe scopes -----
    new_assignments: list[ModelStatement] = list(hoisted_global)
    for stmt in rewritten_statements:
        new_assignments.extend(
            _localize_statement_cse(
                stmt,
                model_call_names=model_call_names,
            )
        )

    result = FunctionModel(
        fn_name=model.fn_name,
        assignments=tuple(new_assignments),
        param_names=model.param_names,
        return_names=model.return_names,
    )
    validate_function_model(result)
    return result


def prepare_translation(
    yul_text: str,
    config: ModelConfig,
    *,
    selected_functions: tuple[str, ...] | None = None,
) -> PreparedTranslation:
    """Parse Yul, select targets, and inline non-target helpers."""

    tokens = tokenize_yul(yul_text)
    selected = (
        selected_functions if selected_functions is not None else config.function_order
    )

    fn_map: dict[str, str] = {}
    yul_functions: dict[str, YulFunction] = {}

    known_yul_names: set[str] = set()
    for sol_name in selected:
        parser = YulParser(tokens)
        n_params = config.n_params.get(sol_name) if config.n_params else None
        exact_yul_name = (
            config.exact_yul_names.get(sol_name)
            if config.exact_yul_names is not None
            else None
        )
        if exact_yul_name is not None:
            exact_selector = _parse_exact_yul_selector(exact_yul_name)
            if exact_selector is None:
                yf = parser.find_exact_function(
                    exact_yul_name,
                    n_params=n_params,
                    search_nested=True,
                )
            else:
                yf = parser.find_exact_function_path(
                    exact_selector,
                    n_params=n_params,
                )
        else:
            yf = parser.find_function(
                sol_name,
                n_params=n_params,
                known_yul_names=known_yul_names or None,
                exclude_known=sol_name in config.exclude_known,
            )
        fn_map[yf.yul_name] = sol_name
        yul_functions[sol_name] = yf
        known_yul_names.add(yf.yul_name)

    # Scope helper collection per-target so that each target is inlined with
    # helpers from its own enclosing Yul object.
    all_helpers: dict[str, YulFunction] = {}
    all_rejected: dict[str, str] = {}

    inlined_targets: dict[str, YulFunction] = {}
    for sol_name in selected:
        yf = yul_functions[sol_name]
        yul_name = yf.yul_name

        fn_token_idx = yf.token_idx

        # Collect helpers from the scope chain, from outermost to
        # innermost.  Inner scopes override outer ones (Yul lexical
        # scoping).
        helper_table: dict[str, YulFunction] = {}
        rejected_helpers: dict[str, str] = {}

        if fn_token_idx is not None:
            # Walk up through enclosing block scopes from outermost to
            # innermost.  Each deeper scope overrides outer names.
            scope_chain: list[tuple[int, int]] = []
            cur_idx = fn_token_idx
            while True:
                obj_start, obj_end = _find_enclosing_block_range(tokens, cur_idx)
                scope_chain.append((obj_start, obj_end))
                if obj_start == 0 and obj_end == len(tokens):
                    break
                # Move to the enclosing block's opening brace to find
                # the next outer scope.
                if obj_start > 0:
                    cur_idx = obj_start - 1
                else:
                    break
            # Process from outermost to innermost (inner overrides outer).
            # Process from outermost to innermost (inner overrides outer).
            for s_start, s_end in reversed(scope_chain):
                scoped_tokens = tokens[s_start:s_end]
                scope_coll = YulParser(scoped_tokens).collect_all_functions()
                _merge_helper_collection(
                    helper_table,
                    rejected_helpers,
                    scope_coll,
                )

            # Also collect nested helpers from inside the target's body.
            # Track their names so the pop loop below preserves them —
            # a nested helper that shadows a selected target's Yul name
            # is a distinct function and must remain in the helper table.
            nested_helper_names: set[str] = set()
            body_range = _find_function_body_range(tokens, fn_token_idx)
            if body_range is not None:
                body_start, body_end = body_range
                body_tokens = tokens[body_start:body_end]
                nested_coll = YulParser(body_tokens).collect_all_functions()
                nested_helper_names = set(nested_coll.functions)
                _merge_helper_collection(
                    helper_table,
                    rejected_helpers,
                    nested_coll,
                )
        else:
            nested_helper_names: set[str] = set()
            function_collection = YulParser(tokens).collect_all_functions()
            _merge_helper_collection(
                helper_table,
                rejected_helpers,
                function_collection,
            )

        for yn in fn_map:
            if yn not in nested_helper_names:
                helper_table.pop(yn, None)

        inlined_targets[sol_name] = _inline_yul_function(
            yul_functions[sol_name],
            helper_table,
            unsupported_function_errors=rejected_helpers,
        )

        all_helpers.update(helper_table)
        all_rejected.update(rejected_helpers)

    return PreparedTranslation(
        selected_functions=tuple(selected),
        fn_map=fn_map,
        yul_functions=inlined_targets,
        collected_helpers=all_helpers,
        rejected_helpers=all_rejected,
    )


def build_restricted_ir_models(
    preparation: PreparedTranslation,
    config: ModelConfig,
) -> list[FunctionModel]:
    """Convert selected Yul functions into validated restricted-IR models."""

    models = [
        yul_function_to_model(
            preparation.yul_functions[fn],
            fn,
            preparation.fn_map,
            keep_solidity_locals=config.keep_solidity_locals,
        )
        for fn in preparation.selected_functions
    ]
    return models


def apply_optional_model_transforms(
    models: list[FunctionModel],
    config: ModelConfig,
    *,
    pipeline: TranslationPipeline,
) -> list[FunctionModel]:
    """Apply non-literal model rewrites that are outside the raw path."""

    transformed = list(models)

    if pipeline.hoist_repeated_calls and config.hoist_repeated_calls:
        model_call_names = frozenset(config.function_order)
        transformed = [
            (
                hoist_repeated_model_calls(
                    model,
                    model_call_names=model_call_names,
                )
                if model.fn_name in config.hoist_repeated_calls
                else model
            )
            for model in transformed
        ]

    if pipeline.prune_dead_assignments:
        transformed = [
            (
                _prune_dead_assignments(model)
                if model.fn_name not in config.skip_prune
                else model
            )
            for model in transformed
        ]

    return transformed


def validate_selected_models(models: list[FunctionModel]) -> None:
    """Cross-validate selected models for call-graph consistency."""

    # Build signature table: fn_name → (n_params, n_rets)
    sig_table: dict[str, tuple[int, int]] = {}
    for model in models:
        sig_table[model.fn_name] = (len(model.param_names), len(model.return_names))

    # Duplicate check
    seen_names: set[str] = set()
    for model in models:
        if model.fn_name in seen_names:
            raise ParseError(f"Duplicate selected function {model.fn_name!r}")
        seen_names.add(model.fn_name)

    # Collect and validate all inter-model calls
    def _check_calls(expr: Expr, model_fn_name: str) -> set[str]:
        """Walk expr, validate calls to other selected models, return callees."""
        callees: set[str] = set()
        if isinstance(expr, (IntLit, Var)):
            return callees
        if isinstance(expr, Ite):
            callees.update(_check_calls(expr.cond, model_fn_name))
            callees.update(_check_calls(expr.if_true, model_fn_name))
            callees.update(_check_calls(expr.if_false, model_fn_name))
            return callees
        if isinstance(expr, Project):
            inner = expr.inner
            if isinstance(inner, Call) and inner.name in sig_table:
                callees.add(inner.name)
                _, callee_rets = sig_table[inner.name]
                if callee_rets != expr.total:
                    raise ParseError(
                        f"Model {model_fn_name!r}: Project({expr.index}, {expr.total}) "
                        f"expects {expr.total} return values from {inner.name!r}, "
                        f"but it returns {callee_rets}"
                    )
                if callee_rets < 2:
                    raise ParseError(
                        f"Model {model_fn_name!r}: cannot project "
                        f"{inner.name!r} which returns {callee_rets} value(s) "
                        f"(need >= 2 for projection)"
                    )
                callee_params, _ = sig_table[inner.name]
                if len(inner.args) != callee_params:
                    raise ParseError(
                        f"Model {model_fn_name!r}: call to {inner.name!r} "
                        f"passes {len(inner.args)} arg(s), expected {callee_params}"
                    )
                for a in inner.args:
                    callees.update(_check_calls(a, model_fn_name))
            else:
                callees.update(_check_calls(inner, model_fn_name))
            return callees
        if not isinstance(expr, Call):
            assert_never(expr)

        if expr.name in sig_table:
            callees.add(expr.name)
            callee_params, callee_rets = sig_table[expr.name]
            if len(expr.args) != callee_params:
                raise ParseError(
                    f"Model {model_fn_name!r}: call to {expr.name!r} passes "
                    f"{len(expr.args)} arg(s), expected {callee_params}"
                )
            if callee_rets > 1:
                raise ParseError(
                    f"Model {model_fn_name!r}: multi-return function "
                    f"{expr.name!r} ({callee_rets} returns) used in scalar "
                    f"context without Project projection"
                )
        elif expr.name not in OP_TO_LEAN_HELPER:
            raise ParseError(
                f"Model {model_fn_name!r}: unresolved call target " f"{expr.name!r}"
            )

        for a in expr.args:
            callees.update(_check_calls(a, model_fn_name))
        return callees

    # Build call graph and check all expressions
    call_graph: dict[str, set[str]] = {m.fn_name: set() for m in models}
    for model in models:
        for stmt in model.assignments:
            if isinstance(stmt, Assignment):
                call_graph[model.fn_name].update(_check_calls(stmt.expr, model.fn_name))
            elif isinstance(stmt, ConditionalBlock):
                call_graph[model.fn_name].update(
                    _check_calls(stmt.condition, model.fn_name)
                )
                for a in stmt.then_branch.assignments:
                    call_graph[model.fn_name].update(
                        _check_calls(a.expr, model.fn_name)
                    )
                for a in stmt.else_branch.assignments:
                    call_graph[model.fn_name].update(
                        _check_calls(a.expr, model.fn_name)
                    )

    # Cycle detection via DFS
    WHITE, GRAY, BLACK = 0, 1, 2
    color: dict[str, int] = {name: WHITE for name in call_graph}

    def _dfs(node: str, path: list[str]) -> None:
        color[node] = GRAY
        path.append(node)
        for callee in call_graph[node]:
            if callee not in color:
                continue
            if color[callee] == GRAY:
                cycle_start = path.index(callee)
                cycle = path[cycle_start:]
                raise ParseError(
                    f"Cycle detected among selected models: "
                    f"{' → '.join(cycle)} → {callee}"
                )
            if color[callee] == WHITE:
                _dfs(callee, path)
        path.pop()
        color[node] = BLACK

    for name in call_graph:
        if color[name] == WHITE:
            _dfs(name, [])


def translate_yul_to_models(
    yul_text: str,
    config: ModelConfig,
    *,
    selected_functions: tuple[str, ...] | None = None,
    pipeline: TranslationPipeline = OPTIMIZED_TRANSLATION_PIPELINE,
) -> TranslationResult:
    """Run the selected translation pipeline and return the final models."""

    # Duplicate selected function check (early, before parsing)
    if selected_functions is not None:
        if len(set(selected_functions)) != len(selected_functions):
            dupes = [f for f in selected_functions if selected_functions.count(f) > 1]
            raise ParseError(f"Duplicate selected functions: {sorted(set(dupes))}")

    preparation = prepare_translation(
        yul_text,
        config,
        selected_functions=selected_functions,
    )
    models = build_restricted_ir_models(
        preparation,
        config,
    )
    validate_selected_models(models)
    models = apply_optional_model_transforms(
        models,
        config,
        pipeline=pipeline,
    )
    return TranslationResult(
        preparation=preparation,
        models=models,
        pipeline=pipeline,
    )


def emit_expr(
    expr: Expr,
    *,
    helper_map: dict[str, str],
) -> str:
    if isinstance(expr, IntLit):
        return str(expr.value % WORD_MOD)
    if isinstance(expr, Var):
        return expr.name
    if isinstance(expr, Project):
        # Emit Lean nested-pair projection for element N of M total:
        #   N=0       → .1
        #   0<N<M-1   → .2.2...2.1  (N-1 extra .2 prefixes)
        #   N=M-1     → .2.2...2    (N-1 extra .2 suffixes)
        # This handles Lean's right-nested Prod: A × B × C = A × (B × C).
        idx = expr.index
        total = expr.total
        inner = emit_expr(expr.inner, helper_map=helper_map)
        if total <= 2 or idx == 0:
            return f"({inner}).{idx + 1}"
        elif idx == total - 1:
            return f"({inner})" + ".2" * idx
        else:
            return f"({inner})" + ".2" * idx + ".1"
    if isinstance(expr, Ite):
        # Emits: if (cond) ≠ 0 then if_val else else_val
        cond = emit_expr(expr.cond, helper_map=helper_map)
        if_val = emit_expr(expr.if_true, helper_map=helper_map)
        else_val = emit_expr(expr.if_false, helper_map=helper_map)
        return f"if ({cond}) ≠ 0 then {if_val} else {else_val}"
    if isinstance(expr, Call):
        helper = helper_map.get(expr.name)
        if helper is None:
            raise ParseError(f"Unsupported call in Lean emitter: {expr.name!r}")
        args = " ".join(f"({emit_expr(a, helper_map=helper_map)})" for a in expr.args)
        return f"{helper} {args}".rstrip()
    assert_never(expr)


# ---------------------------------------------------------------------------
# Per-generator configuration
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ModelConfig:
    """All the per-library knobs that differ between cbrt and sqrt generators."""

    # Ordered Solidity function names to model.
    function_order: tuple[str, ...]
    # sol_fn_name → Lean model base name  (e.g. "_cbrt" → "model_cbrt")
    model_names: dict[str, str]
    # Lean header line  (e.g. "Auto-generated from Solidity Cbrt assembly …")
    header_comment: str
    # Generator script path for the header  (e.g. "formal/cbrt/generate_cbrt_model.py")
    generator_label: str
    # Additional norm-helper entries beyond the base set.
    extra_norm_ops: dict[str, str]
    # Additional Lean definitions emitted right before normLt/normGt.
    extra_lean_defs: str
    # Optional AST rewrite applied to expressions in the Nat model.
    norm_rewrite: Callable[[Expr], Expr] | None
    # Inner function name that the public functions depend on.
    inner_fn: str
    # Optional per-function expected parameter counts for disambiguation.
    # When set, find_function uses param count to pick among homonymous
    # Yul functions (e.g. single-param _sqrt vs two-param _sqrt).
    n_params: dict[str, int] | None = None
    # Optional per-function exact Yul symbol overrides. When set, the
    # translator selects the named Yul function directly instead of using
    # heuristic fun_<name>_<digits> discovery. Entries may be unqualified
    # (`helper`) or scope-qualified (`::top_level`, `outer::helper`).
    exact_yul_names: dict[str, str] | None = None
    # When True, variables matching var_<name>_<digits> (Solidity-declared
    # locals) are kept in the model instead of being copy-propagated.
    # Needed for functions with mixed assembly + Solidity code.
    keep_solidity_locals: bool = False
    # Function names whose find_function should use exclude_known=True,
    # i.e. prefer candidates that do NOT reference already-targeted
    # functions. Used to select leaf functions (e.g. 256-bit Sqrt.sqrt)
    # over higher-level wrappers with the same name.
    exclude_known: frozenset[str] = frozenset()
    # Function names for which the normalized (unbounded Nat) model
    # variation should be suppressed.  The norm model uses normShl/normMul
    # etc. which do NOT match EVM uint256 semantics.  For wrapper functions
    # whose proofs bridge the EVM model directly, the norm model is unused.
    skip_norm: frozenset[str] = frozenset()
    # Function names whose repeated generated-model calls should be hoisted
    # into let-bound temporaries before emission. Useful for wrappers whose
    # IR duplicates the same pure helper call many times.
    hoist_repeated_calls: frozenset[str] = frozenset()
    # Function names for which dead-assignment pruning should be skipped.
    skip_prune: frozenset[str] = frozenset()

    # -- CLI defaults --
    default_source_label: str = ""
    default_namespace: str = ""
    default_output: str = ""
    cli_description: str = ""


@dataclass(frozen=True)
class PreparedTranslation:
    """Selected Yul functions after parsing, discovery, and helper inlining."""

    selected_functions: tuple[str, ...]
    fn_map: dict[str, str]
    yul_functions: dict[str, YulFunction]
    collected_helpers: dict[str, YulFunction]
    rejected_helpers: dict[str, str]


@dataclass(frozen=True)
class TranslationResult:
    """End-to-end translation result before Lean source emission."""

    preparation: PreparedTranslation
    models: list[FunctionModel]
    pipeline: TranslationPipeline


class RunArguments(argparse.Namespace):
    yul: str
    source_label: str
    functions: str
    function: list[str] | None
    namespace: str
    output: str
    pipeline: str


def get_translation_pipeline(name: str) -> TranslationPipeline:
    """Resolve a named translation pipeline."""

    try:
        return TRANSLATION_PIPELINES[name]
    except KeyError as err:
        choices = ", ".join(sorted(TRANSLATION_PIPELINES))
        raise ParseError(
            f"Unknown translation pipeline {name!r}. Expected one of: {choices}"
        ) from err


# ---------------------------------------------------------------------------
# High-level pipeline (shared by both generators)
# ---------------------------------------------------------------------------


def build_model_body(
    assignments: tuple[ModelStatement, ...],
    *,
    evm: bool,
    config: ModelConfig,
    param_names: tuple[str, ...] = ("x",),
    return_names: tuple[str, ...] = ("z",),
) -> str:
    lines: list[str] = []
    norm_helpers = {**_BASE_NORM_HELPERS, **config.extra_norm_ops}

    if evm:
        for p in param_names:
            lines.append(f"  let {p} := u256 {p}")
        call_map = {fn: f"{config.model_names[fn]}_evm" for fn in config.function_order}
        op_map = OP_TO_LEAN_HELPER
    else:
        call_map = dict(config.model_names)
        op_map = norm_helpers

    merged_map = {**op_map, **call_map}

    def _emit_rhs(expr: Expr) -> str:
        rhs_expr = expr
        if not evm and config.norm_rewrite is not None:
            rhs_expr = config.norm_rewrite(rhs_expr)
        return emit_expr(rhs_expr, helper_map=merged_map)

    def _emit_tuple(vars_: tuple[str, ...]) -> str:
        if len(vars_) == 1:
            return vars_[0]
        return f"({', '.join(vars_)})"

    for stmt in assignments:
        if isinstance(stmt, ConditionalBlock):
            # Emit Lean tuple-destructuring if-then-else:
            #   let (v1, v2) := if cond ≠ 0 then
            #       let v1 := ...
            #       ...
            #       (v1, v2)
            #     else (v1, v2)
            cond_str = _emit_rhs(stmt.condition)
            lhs = _emit_tuple(stmt.output_vars)
            lines.append(f"  let {lhs} := if ({cond_str}) ≠ 0 then")
            for a in stmt.then_branch.assignments:
                rhs = _emit_rhs(a.expr)
                lines.append(f"      let {a.target} := {rhs}")
            lines.append(f"      {_emit_tuple(stmt.then_branch.outputs)}")
            lines.append("    else")
            for a in stmt.else_branch.assignments:
                rhs = _emit_rhs(a.expr)
                lines.append(f"      let {a.target} := {rhs}")
            lines.append(f"      {_emit_tuple(stmt.else_branch.outputs)}")
        elif isinstance(stmt, Assignment):
            rhs = _emit_rhs(stmt.expr)
            lines.append(f"  let {stmt.target} := {rhs}")
        else:
            assert_never(stmt)

    if len(return_names) == 1:
        lines.append(f"  {return_names[0]}")
    else:
        lines.append(f"  ({', '.join(return_names)})")
    return "\n".join(lines)


@dataclass(frozen=True)
class EmittedModelDef:
    fn_name: str
    base_name: str
    evm_name: str
    emit_norm: bool


@dataclass(frozen=True)
class LeanEmissionPlan:
    emit_any_norm: bool
    model_defs: tuple[EmittedModelDef, ...]
    generated_def_names: frozenset[str]
    extra_norm_binder_names: frozenset[str]


def _collect_model_binders(model: FunctionModel) -> list[str]:
    binders = [*model.param_names, *model.return_names]
    for stmt in model.assignments:
        if isinstance(stmt, Assignment):
            binders.append(stmt.target)
        elif isinstance(stmt, ConditionalBlock):
            binders.extend(stmt.output_vars)
            binders.extend(a.target for a in stmt.then_branch.assignments)
            binders.extend(a.target for a in stmt.else_branch.assignments)
        else:
            assert_never(stmt)
    return binders


def _build_lean_emission_plan(
    models: list[FunctionModel],
    config: ModelConfig,
) -> LeanEmissionPlan:
    emit_any_norm = any_norm_models(models, config)
    base_reserved = frozenset(
        {"u256", "WORD_MOD"} | set(OP_TO_LEAN_HELPER.values()) | _LEAN_KEYWORDS
    )
    norm_reserved = frozenset(
        (set(_BASE_NORM_HELPERS.values()) | set(config.extra_norm_ops.values()))
        if emit_any_norm
        else set()
    )
    builtin_helper_names = frozenset(
        {"u256", "WORD_MOD"} | set(OP_TO_LEAN_HELPER.values()) | set(norm_reserved)
    )

    model_defs: list[EmittedModelDef] = []
    generated_def_names: set[str] = set()
    for model in models:
        if model.fn_name not in config.model_names:
            raise ParseError(
                f"Model {model.fn_name!r} has no entry in config.model_names"
            )
        base_name = config.model_names[model.fn_name]
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", base_name):
            raise ParseError(
                f"Invalid generated model name for {model.fn_name!r}: {base_name!r}"
            )

        emit_norm = model.fn_name not in config.skip_norm
        reserved_names = base_reserved | (norm_reserved if emit_norm else frozenset())
        if base_name in reserved_names:
            raise ParseError(
                f"Reserved name used as model name for {model.fn_name!r}: "
                f"{base_name!r}"
            )

        evm_name = f"{base_name}_evm"
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", evm_name):
            raise ParseError(f"Invalid generated EVM model name: {evm_name!r}")
        if emit_norm and base_name in generated_def_names:
            raise ParseError(f"Duplicate generated model name {base_name!r}")
        if evm_name in generated_def_names:
            raise ParseError(f"Duplicate generated EVM model name {evm_name!r}")

        if emit_norm:
            generated_def_names.add(base_name)
        generated_def_names.add(evm_name)
        model_defs.append(
            EmittedModelDef(
                fn_name=model.fn_name,
                base_name=base_name,
                evm_name=evm_name,
                emit_norm=emit_norm,
            )
        )

    for name in generated_def_names:
        if name in builtin_helper_names:
            raise ParseError(
                f"Generated model name {name!r} collides with a builtin "
                f"helper or reserved name"
            )

    return LeanEmissionPlan(
        emit_any_norm=emit_any_norm,
        model_defs=tuple(model_defs),
        generated_def_names=frozenset(generated_def_names),
        extra_norm_binder_names=frozenset(config.extra_norm_ops.values()),
    )


def render_function_defs(
    models: list[FunctionModel],
    config: ModelConfig,
    *,
    emission_plan: LeanEmissionPlan | None = None,
) -> str:
    if emission_plan is None:
        emission_plan = _build_lean_emission_plan(models, config)
    if len(emission_plan.model_defs) != len(models):
        raise ParseError(
            "Lean emission plan/model count mismatch. Refuse to render "
            "with inconsistent emitted names."
        )

    parts: list[str] = []
    for model, planned in zip(models, emission_plan.model_defs):
        if planned.fn_name != model.fn_name:
            raise ParseError(
                "Lean emission plan/model order mismatch. Refuse to render "
                "with inconsistent emitted names."
            )
        evm_body = build_model_body(
            model.assignments,
            evm=True,
            config=config,
            param_names=model.param_names,
            return_names=model.return_names,
        )

        if model.param_names:
            param_sig = f" ({' '.join(model.param_names)} : Nat)"
        else:
            param_sig = ""
        if len(model.return_names) == 1:
            ret_type = "Nat"
        else:
            ret_type = " × ".join("Nat" for _ in model.return_names)
        parts.append(
            f"/-- Opcode-faithful auto-generated model of `{model.fn_name}` with uint256 EVM semantics. -/\n"
            f"def {planned.evm_name}{param_sig} : {ret_type} :=\n"
            f"{evm_body}\n"
        )
        if planned.emit_norm:
            norm_body = build_model_body(
                model.assignments,
                evm=False,
                config=config,
                param_names=model.param_names,
                return_names=model.return_names,
            )
            parts.append(
                f"/-- Normalized auto-generated model of `{model.fn_name}` on Nat arithmetic. -/\n"
                f"def {planned.base_name}{param_sig} : {ret_type} :=\n"
                f"{norm_body}\n"
            )
    return "\n".join(parts)


def any_norm_models(models: list[FunctionModel], config: ModelConfig) -> bool:
    """Return True if at least one function will emit a norm model."""
    return any(m.fn_name not in config.skip_norm for m in models)


def build_lean_source(
    *,
    models: list[FunctionModel],
    source_path: str,
    namespace: str,
    config: ModelConfig,
) -> str:
    # -- Namespace validation --
    validate_ident(namespace, what="Lean namespace")

    # -- Injection prevention --
    if "\n" in source_path:
        raise ParseError(
            f"Source path contains newline (potential injection): {source_path!r}"
        )
    if "\n" in config.generator_label:
        raise ParseError(
            f"Generator label contains newline (potential injection): "
            f"{config.generator_label!r}"
        )
    if "-/" in config.header_comment:
        raise ParseError(
            f"Header comment contains Lean doc-comment terminator '-/': "
            f"{config.header_comment!r}"
        )

    emission_plan = _build_lean_emission_plan(models, config)

    # Binder collision: check all binder names in all models against
    # generated def names.
    def _check_binder_collision(binder: str, model_fn_name: str) -> None:
        if binder in emission_plan.generated_def_names:
            raise ParseError(
                f"Binder {binder!r} in model {model_fn_name!r} collides "
                f"with a generated model def name"
            )

    for model in models:
        for binder in _collect_model_binders(model):
            _check_binder_collision(binder, model.fn_name)

    # Check binder names against config-specific reserved names that
    # validate_ident cannot see (it has no access to config).
    if emission_plan.extra_norm_binder_names:
        for model, planned in zip(models, emission_plan.model_defs):
            if not planned.emit_norm:
                continue
            for binder in _collect_model_binders(model):
                if binder in emission_plan.extra_norm_binder_names:
                    raise ParseError(
                        f"Reserved Lean helper name used as binder in "
                        f"{model.fn_name!r}: {binder!r}"
                    )

    modeled_functions = ", ".join(model.fn_name for model in models)

    opcodes = collect_model_opcodes(models)
    opcodes_line = ", ".join(opcodes)

    function_defs = render_function_defs(
        models,
        config,
        emission_plan=emission_plan,
    )

    # Normalize extra_lean_defs: ensure it ends with \n\n if non-empty.
    _extra_lean_defs = ""
    if config.extra_lean_defs and config.extra_lean_defs.strip():
        _extra_lean_defs = config.extra_lean_defs.rstrip() + "\n\n"

    norm_defs = ""
    if emission_plan.emit_any_norm:
        norm_defs = (
            "def normAdd (a b : Nat) : Nat := a + b\n\n"
            "def normSub (a b : Nat) : Nat := a - b\n\n"
            "def normMul (a b : Nat) : Nat := a * b\n\n"
            "def normDiv (a b : Nat) : Nat := a / b\n\n"
            "def normMod (a b : Nat) : Nat := a % b\n\n"
            "def normNot (a : Nat) : Nat := WORD_MOD - 1 - a\n\n"
            "def normOr (a b : Nat) : Nat := a ||| b\n\n"
            "def normAnd (a b : Nat) : Nat := a &&& b\n\n"
            "def normEq (a b : Nat) : Nat :=\n"
            "  if a = b then 1 else 0\n\n"
            "def normIszero (a : Nat) : Nat :=\n"
            "  if a = 0 then 1 else 0\n\n"
            "def normShl (shift value : Nat) : Nat := value <<< shift\n\n"
            "def normShr (shift value : Nat) : Nat := value / 2 ^ shift\n\n"
            "def normClz (value : Nat) : Nat :=\n"
            "  if value = 0 then 256 else 255 - Nat.log2 value\n\n"
            f"{_extra_lean_defs}"
            "def normLt (a b : Nat) : Nat :=\n"
            "  if a < b then 1 else 0\n\n"
            "def normGt (a b : Nat) : Nat :=\n"
            "  if a > b then 1 else 0\n\n"
            "def normMulmod (a b n : Nat) : Nat :=\n"
            "  if n = 0 then 0 else (a * b) % n\n\n"
        )

    src = (
        "import Init\n\n"
        f"namespace {namespace}\n\n"
        f"/-- {config.header_comment} -/\n"
        f"-- Source: {source_path}\n"
        f"-- Modeled functions: {modeled_functions}\n"
        f"-- Generated by: {config.generator_label}\n"
        f"-- Modeled opcodes/Yul builtins: {opcodes_line}\n\n"
        "def WORD_MOD : Nat := 2 ^ 256\n\n"
        "def u256 (x : Nat) : Nat :=\n"
        "  x % WORD_MOD\n\n"
        "def evmAdd (a b : Nat) : Nat :=\n"
        "  u256 (u256 a + u256 b)\n\n"
        "def evmSub (a b : Nat) : Nat :=\n"
        "  u256 (u256 a + WORD_MOD - u256 b)\n\n"
        "def evmMul (a b : Nat) : Nat :=\n"
        "  u256 (u256 a * u256 b)\n\n"
        "def evmDiv (a b : Nat) : Nat :=\n"
        "  let aa := u256 a\n"
        "  let bb := u256 b\n"
        "  if bb = 0 then 0 else aa / bb\n\n"
        "def evmMod (a b : Nat) : Nat :=\n"
        "  let aa := u256 a\n"
        "  let bb := u256 b\n"
        "  if bb = 0 then 0 else aa % bb\n\n"
        "def evmNot (a : Nat) : Nat :=\n"
        "  WORD_MOD - 1 - u256 a\n\n"
        "def evmOr (a b : Nat) : Nat :=\n"
        "  u256 a ||| u256 b\n\n"
        "def evmAnd (a b : Nat) : Nat :=\n"
        "  u256 a &&& u256 b\n\n"
        "def evmEq (a b : Nat) : Nat :=\n"
        "  if u256 a = u256 b then 1 else 0\n\n"
        "def evmIszero (a : Nat) : Nat :=\n"
        "  if u256 a = 0 then 1 else 0\n\n"
        "def evmShl (shift value : Nat) : Nat :=\n"
        "  let s := u256 shift\n"
        "  let v := u256 value\n"
        "  if s < 256 then u256 (v * 2 ^ s) else 0\n\n"
        "def evmShr (shift value : Nat) : Nat :=\n"
        "  let s := u256 shift\n"
        "  let v := u256 value\n"
        "  if s < 256 then v / 2 ^ s else 0\n\n"
        "def evmClz (value : Nat) : Nat :=\n"
        "  let v := u256 value\n"
        "  if v = 0 then 256 else 255 - Nat.log2 v\n\n"
        "def evmLt (a b : Nat) : Nat :=\n"
        "  if u256 a < u256 b then 1 else 0\n\n"
        "def evmGt (a b : Nat) : Nat :=\n"
        "  if u256 a > u256 b then 1 else 0\n\n"
        "def evmMulmod (a b n : Nat) : Nat :=\n"
        "  let aa := u256 a; let bb := u256 b; let nn := u256 n\n"
        "  if nn = 0 then 0 else (aa * bb) % nn\n\n"
        f"{norm_defs}"
        f"{function_defs}\n"
        f"end {namespace}\n"
    )
    return src


def parse_function_selection(
    args: RunArguments,
    config: ModelConfig,
) -> tuple[str, ...]:
    selected: list[str] = []

    if args.function:
        selected.extend(args.function)
    if args.functions:
        for fn in args.functions.split(","):
            name = fn.strip()
            if name:
                selected.append(name)

    if not selected:
        selected = list(config.function_order)

    allowed = set(config.function_order)
    bad = [f for f in selected if f not in allowed]
    if bad:
        raise ParseError(f"Unsupported function(s): {', '.join(bad)}")

    # Public functions depend on the inner function.
    if (
        any(fn != config.inner_fn for fn in selected)
        and config.inner_fn not in selected
    ):
        if config.inner_fn not in allowed:
            raise ParseError(
                f"Inner function {config.inner_fn!r} is not in function_order. "
                f"Available: {', '.join(config.function_order)}"
            )
        selected.append(config.inner_fn)

    selected_set = set(selected)
    return tuple(fn for fn in config.function_order if fn in selected_set)


def run(config: ModelConfig) -> int:
    """Main entry point shared by both generators."""
    global _gensym_counters
    _gensym_counters = {}

    ap = argparse.ArgumentParser(description=config.cli_description)
    ap.add_argument(
        "--yul",
        required=True,
        help="Path to Yul IR file, or '-' for stdin (from `forge inspect ... ir`)",
    )
    ap.add_argument(
        "--source-label",
        default=config.default_source_label,
        help="Source label for the Lean header comment",
    )
    ap.add_argument(
        "--functions",
        default="",
        help=f"Comma-separated function names (default: {','.join(config.function_order)})",
    )
    ap.add_argument(
        "--function",
        action="append",
        help="Optional repeatable function selector",
    )
    ap.add_argument(
        "--namespace",
        default=config.default_namespace,
        help="Lean namespace for generated definitions",
    )
    ap.add_argument(
        "--output",
        default=config.default_output,
        help="Output Lean file path",
    )
    ap.add_argument(
        "--pipeline",
        default=OPTIMIZED_TRANSLATION_PIPELINE.name,
        choices=sorted(TRANSLATION_PIPELINES),
        help="Translation pipeline to run (default: optimized)",
    )
    args = ap.parse_args(namespace=RunArguments())

    validate_ident(args.namespace, what="Lean namespace")

    selected_functions = parse_function_selection(args, config)
    pipeline = get_translation_pipeline(args.pipeline)

    yul_text: str
    if args.yul == "-":
        stdin = sys.stdin
        if stdin is None:
            raise ParseError("stdin is unavailable while reading Yul input")
        yul_text = stdin.read()
    else:
        yul_text = pathlib.Path(args.yul).read_text()

    result = translate_yul_to_models(
        yul_text,
        config,
        selected_functions=selected_functions,
        pipeline=pipeline,
    )
    models = result.models

    lean_src = build_lean_source(
        models=models,
        source_path=args.source_label,
        namespace=args.namespace,
        config=config,
    )

    out_path = pathlib.Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(lean_src)

    if result.preparation.collected_helpers:
        print(
            "Collected "
            f"{len(result.preparation.collected_helpers)} function definition(s) "
            "for inlining"
        )

    print(f"Generated {out_path}")
    print(f"Pipeline: {pipeline.name}")
    for model in models:
        print(f"Parsed {len(model.assignments)} assignments for {model.fn_name}")

    opcodes = collect_model_opcodes(models)
    print(f"Modeled opcodes: {', '.join(opcodes)}")

    return 0
