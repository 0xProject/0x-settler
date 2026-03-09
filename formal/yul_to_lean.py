"""
Shared infrastructure for generating Lean models from Yul IR.

Provides:
- Yul tokenizer and recursive-descent parser
- AST types (IntLit, Var, Call, Assignment, FunctionModel)
- Yul → FunctionModel conversion (copy propagation + demangling)
- Explicit translation pipelines: raw translation + optional transforms
- Lean expression emission
- Common Lean source scaffolding
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys
from collections import Counter
from dataclasses import dataclass
from typing import Callable, NoReturn


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


Expr = IntLit | Var | Call


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


def _unreachable_expr(expr: Expr) -> NoReturn:
    raise TypeError(f"Unsupported Expr node: {type(expr)}")


def _unreachable_stmt(stmt: ModelStatement) -> NoReturn:
    raise TypeError(f"Unsupported ModelStatement: {type(stmt)}")


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
  | (?P<colon>:)
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
    "colon": ":",
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
    """

    condition: Expr
    body: tuple["PlainAssignment", ...]
    has_leave: bool = False
    else_body: tuple["PlainAssignment", ...] | None = None


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


class YulParser:
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
        self.tokens = tokens
        self.i = 0
        self._expr_stmts: list[Expr] = []

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
          synthetic ``__component_N_M(call)`` wrapper (index N of M total)
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
            self._expect(":=")
            expr = self._parse_expr()
            for idx, t in enumerate(all_targets):
                results.append(
                    PlainAssignment(
                        t, Call(f"__component_{idx}_{len(all_targets)}", (expr,))
                    )
                )
        elif self._peek_kind() == ":=":
            self._pop()
            expr = self._parse_expr()
            results.append(PlainAssignment(target, expr))
        else:
            # Bare declaration: ``let x``  (zero-initialized per Yul spec)
            results.append(PlainAssignment(target, IntLit(0)))

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
                # Bare scope block (e.g. inline assembly wrapper).  Parse
                # inner statements, inline block-local ``let`` bindings, and
                # emit only reassignments to outer-scope variables.
                self._pop()  # consume '{'
                block_let_vars: set[str] = set()
                inner, inner_leave = self._parse_assignment_loop(
                    allow_control_flow=allow_control_flow,
                    context=context,
                    _let_vars=block_let_vars,
                )
                self._expect("}")
                block_subst: dict[str, Expr] = {}
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
                        new_body = tuple(
                            PlainAssignment(
                                s.target, substitute_expr(s.expr, block_subst)
                            )
                            for s in stmt.body
                        )
                        new_else = (
                            tuple(
                                PlainAssignment(
                                    s.target, substitute_expr(s.expr, block_subst)
                                )
                                for s in stmt.else_body
                            )
                            if stmt.else_body is not None
                            else None
                        )
                        results.append(
                            ParsedIfBlock(
                                condition=new_cond,
                                body=new_body,
                                has_leave=stmt.has_leave,
                                else_body=new_else,
                            )
                        )
                    else:
                        expr = substitute_expr(stmt.expr, block_subst)
                        if stmt.target in block_let_vars:
                            block_subst[stmt.target] = expr
                        else:
                            results.append(PlainAssignment(stmt.target, expr))
                if inner_leave:
                    has_leave = True
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
                        f"{' and if/switch blocks' if keyword == 'for' else ''} "
                        f"is supported for Lean model generation."
                    )
                if keyword == "if":
                    self._pop()  # consume 'if'
                    condition = self._parse_expr()
                    self._expect("{")
                    body, body_leave = self._parse_assignment_loop(
                        allow_control_flow=False,
                        context="if-body",
                    )
                    self._expect("}")
                    plain_body = self._expect_plain_assignments(
                        body,
                        context="if-body",
                    )
                    results.append(
                        ParsedIfBlock(
                            condition=condition,
                            body=tuple(plain_body),
                            has_leave=body_leave,
                        )
                    )
                else:  # switch
                    self._pop()  # consume 'switch'
                    condition = self._parse_expr()
                    # We support exactly one form of switch:
                    #   switch e case 0 { else_body } default { if_body }
                    # (branches may appear in either order).  Anything else
                    # is rejected loudly.
                    case0_body: list[PlainAssignment] | None = None
                    case0_leave = False
                    default_body: list[PlainAssignment] | None = None
                    default_leave = False
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
                            self._expect("{")
                            raw_case0_body, case0_leave = self._parse_assignment_loop(
                                allow_control_flow=False,
                                context="switch branch",
                            )
                            self._expect("}")
                            case0_body = self._expect_plain_assignments(
                                raw_case0_body,
                                context="switch branch",
                            )
                        else:  # default
                            if default_body is not None:
                                raise ParseError(
                                    "Duplicate 'default' in switch statement."
                                )
                            self._expect("{")
                            raw_default_body, default_leave = (
                                self._parse_assignment_loop(
                                    allow_control_flow=False,
                                    context="switch branch",
                                )
                            )
                            self._expect("}")
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
                    # Map to ParsedIfBlock: condition != 0 → default (if-body),
                    # condition == 0 → case 0 (else-body).
                    if_body = tuple(default_body)
                    else_body = tuple(case0_body) if case0_body else None
                    results.append(
                        ParsedIfBlock(
                            condition=condition,
                            body=if_body,
                            has_leave=default_leave or case0_leave,
                            else_body=else_body,
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

    def _parse_body_assignments(self) -> tuple[list[RawStatement], bool]:
        return self._parse_assignment_loop(
            allow_control_flow=True,
            context="function body",
        )

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
        assignments, has_top_level_leave = self._parse_body_assignments()
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

        for idx in range(len(self.tokens) - 1):
            if (
                self.tokens[idx] == ("ident", "function")
                and self.tokens[idx + 1][0] == "ident"
                and self.tokens[idx + 1][1].startswith(target_prefix)
                and self.tokens[idx + 1][1][len(target_prefix) :].isdigit()
            ):
                matches.append(idx)

        if not matches:
            raise ParseError(
                f"Yul function for '{sol_fn_name}' not found "
                f"(expected pattern fun_{sol_fn_name}_<digits>)"
            )

        if n_params is not None and len(matches) > 1:
            filtered = [m for m in matches if self._count_params_at(m) == n_params]
            if filtered:
                matches = filtered

        if known_yul_names and len(matches) > 1:
            if exclude_known:
                filtered = [
                    m
                    for m in matches
                    if not self._body_references_any(m, known_yul_names)
                ]
            else:
                filtered = [
                    m for m in matches if self._body_references_any(m, known_yul_names)
                ]
            if filtered:
                matches = filtered

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
    ) -> YulFunction:
        """Find and parse the function whose Yul symbol exactly matches ``yul_name``."""
        matches: list[int] = []

        for idx in range(len(self.tokens) - 1):
            if self.tokens[idx] == ("ident", "function") and self.tokens[idx + 1] == (
                "ident",
                yul_name,
            ):
                if n_params is not None and self._count_params_at(idx) != n_params:
                    continue
                matches.append(idx)

        if not matches:
            if n_params is None:
                raise ParseError(f"Exact Yul function {yul_name!r} not found")
            raise ParseError(
                f"Exact Yul function {yul_name!r} with {n_params} parameter(s) not found"
            )

        if len(matches) > 1:
            raise ParseError(
                f"Multiple exact Yul functions matched {yul_name!r}. Refuse to guess."
            )

        self.i = matches[0]
        return self.parse_function()

    def _body_references_any(self, fn_start: int, yul_names: set[str]) -> bool:
        """Check if the function at *fn_start* references any identifier in *yul_names*."""
        depth = 0
        started = False
        for j in range(fn_start, len(self.tokens)):
            k, text = self.tokens[j]
            if k == "{":
                depth += 1
                started = True
            elif k == "}":
                depth -= 1
                if started and depth == 0:
                    return False
            elif k == "ident" and text in yul_names:
                return True
        return False

    def _function_name_at(self, idx: int) -> str | None:
        if idx + 1 >= len(self.tokens):
            return None
        kind, text = self.tokens[idx + 1]
        if kind != "ident":
            return None
        return text

    def collect_all_functions(self) -> CollectedFunctions:
        """Parse all function definitions in the token stream.

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
                    functions[fn.yul_name] = fn
                except ParseError as err:
                    fn_name = self._function_name_at(saved_i) or f"<unknown@{saved_i}>"
                    rejected[fn_name] = str(err)
                    self.i = saved_i
                    self._skip_function_def()
                finally:
                    self._expr_stmts = saved_stmts
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
    if isinstance(expr, Call):
        new_name = fn_map.get(expr.name, expr.name)
        new_args = tuple(rename_expr(a, var_map, fn_map) for a in expr.args)
        return Call(new_name, new_args)
    _unreachable_expr(expr)


def substitute_expr(expr: Expr, subst: dict[str, Expr]) -> Expr:
    if isinstance(expr, IntLit):
        return expr
    if isinstance(expr, Var):
        return subst.get(expr.name, expr)
    if isinstance(expr, Call):
        return Call(expr.name, tuple(substitute_expr(a, subst) for a in expr.args))
    _unreachable_expr(expr)


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


# ---------------------------------------------------------------------------
# Function inlining
# ---------------------------------------------------------------------------

_gensym_counters: dict[str, int] = {}


def _gensym(prefix: str) -> str:
    """Generate a unique variable name for generated locals."""
    _gensym_counters[prefix] = _gensym_counters.get(prefix, 0) + 1
    return f"_{prefix}_{_gensym_counters[prefix]}"


def _try_const_eval(expr: Expr) -> int | None:
    """Try to evaluate an expression to a constant integer.

    Returns ``None`` if the expression contains variables or unsupported
    operations.  Delegates to ``_eval_builtin`` for all supported EVM
    opcodes so that constant-folding semantics stay in sync with the
    model evaluator.
    """
    if isinstance(expr, IntLit):
        return expr.value
    if isinstance(expr, Call):
        # Handle __ite(cond, if_val, else_val): if both branches
        # evaluate to the same constant, the result is that constant
        # regardless of the condition.
        if expr.name == "__ite" and len(expr.args) == 3:
            cond_val = _try_const_eval(expr.args[0])
            if_val = _try_const_eval(expr.args[1])
            else_val = _try_const_eval(expr.args[2])
            if if_val is not None and else_val is not None and if_val == else_val:
                return if_val
            if cond_val is not None and cond_val != 0 and if_val is not None:
                return if_val
            if cond_val is not None and cond_val == 0 and else_val is not None:
                return else_val
            return None
        # Delegate all other ops to _eval_builtin.
        arg_vals = tuple(_try_const_eval(arg) for arg in expr.args)
        if any(v is None for v in arg_vals):
            return None
        try:
            return _eval_builtin(expr.name, arg_vals)  # type: ignore[arg-type]
        except EvaluationError:
            return None
    return None


def _simplify_ite(cond: Expr, if_val: Expr, else_val: Expr) -> Expr:
    """Build an ``__ite`` node, simplifying when the condition or branches are trivial."""
    if if_val == else_val:
        return if_val
    cond_val = _try_const_eval(cond)
    if cond_val is not None:
        return if_val if cond_val != 0 else else_val
    return Call("__ite", (cond, if_val, else_val))


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

    Builds a substitution from parameters → argument expressions, then
    processes the helper body sequentially. Helpers must remain pure at the
    statement level, except for the exact emitted ``uint512.from(x_hi, x_lo)``
    accessor shape, whose two fixed-slot writes are sunk into the selected
    function body.
    """
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
            if stmt.has_leave and stmt.else_body is not None:
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
                depth + 1,
                max_depth,
                unsupported_function_errors=unsupported_function_errors,
            )
            # Process if-body assignments into a separate subst branch.
            if_subst = dict(subst)
            pre_if_sink_len = len(mstore_sink) if mstore_sink is not None else 0
            for s in stmt.body:
                expr = substitute_expr(s.expr, if_subst)
                expr = inline_calls(
                    expr,
                    fn_table,
                    depth + 1,
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
                        depth + 1,
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
                # If/else or switch: merge both branches with __ite.
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
                # on the false path and merge with __ite.
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
                depth + 1,
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
            resolved_cond = _resolve(leave_cond, leave_subst)
            return _simplify_ite(resolved_cond, if_val, else_val)
        return else_val

    if len(fn.rets) == 1:
        return _get_ret(fn.rets[0])
    return tuple(_get_ret(r) for r in fn.rets)


def inline_calls(
    expr: Expr,
    fn_table: dict[str, YulFunction],
    depth: int = 0,
    max_depth: int = 20,
    mstore_sink: list[FromWriteEffect] | None = None,
    unsupported_function_errors: dict[str, str] | None = None,
) -> Expr:
    """Recursively inline function calls in an expression.

    Walks the expression tree. When a ``Call`` targets a function in
    *fn_table*, its body is inlined via sequential substitution.
    ``__component_N`` wrappers (from multi-value ``let``) are resolved
    to the Nth return value of the inlined function.
    """
    if depth > max_depth:
        raise ParseError(
            f"Inlining depth {depth} exceeded max_depth={max_depth} while "
            f"processing {expr!r}. Refuse to leave the expression partially inlined."
        )
    if isinstance(expr, (IntLit, Var)):
        return expr
    if isinstance(expr, Call):
        # Handle __component_N_M(Call(fn, ...)) for multi-return.
        # Must check BEFORE recursively inlining arguments, because
        # we need to inline the inner call as multi-return to extract
        # the Nth component.
        m = re.fullmatch(r"__component_(\d+)_(\d+)", expr.name)
        if m and len(expr.args) == 1 and isinstance(expr.args[0], Call):
            idx = int(m.group(1))
            total = int(m.group(2))
            inner = expr.args[0]
            # Recursively inline the inner call's arguments first
            inner_args = tuple(
                inline_calls(
                    a,
                    fn_table,
                    depth + 1,
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
                    depth + 1,
                    max_depth,
                    mstore_sink=mstore_sink,
                    unsupported_function_errors=unsupported_function_errors,
                )
                if isinstance(result, tuple):
                    if len(result) != total:
                        raise ParseError(
                            f"Component wrapper {expr.name!r} expected {total} "
                            f"return values from {inner.name!r}, got {len(result)}"
                        )
                    if idx >= len(result):
                        raise ParseError(
                            f"Component wrapper {expr.name!r} requested index {idx}, "
                            f"but {inner.name!r} only returned {len(result)} value(s)"
                        )
                    return result[idx]
                if total != 1 or idx != 0:
                    raise ParseError(
                        f"Component wrapper {expr.name!r} expects {total} return "
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
            return Call(expr.name, (Call(inner.name, inner_args),))

        # Recurse into arguments
        args = tuple(
            inline_calls(
                a,
                fn_table,
                depth + 1,
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
                depth + 1,
                max_depth,
                mstore_sink=mstore_sink,
                unsupported_function_errors=unsupported_function_errors,
            )
            if isinstance(result, tuple):
                raise ParseError(
                    f"Cannot inline multi-return function {expr.name!r} into a "
                    f"single-value context. Use tuple destructuring or an "
                    f"explicit __component_N_M wrapper."
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
    _unreachable_expr(expr)


def _inline_yul_function(
    yf: YulFunction,
    fn_table: dict[str, YulFunction],
    unsupported_function_errors: dict[str, str] | None = None,
) -> YulFunction:
    """Apply ``inline_calls`` to every expression in a YulFunction."""

    mstore_sink: list[FromWriteEffect] = []
    new_assignments: list[RawStatement] = []
    for stmt in yf.assignments:
        if isinstance(stmt, ParsedIfBlock):
            pre_len = len(mstore_sink)
            new_cond = inline_calls(
                stmt.condition,
                fn_table,
                mstore_sink=mstore_sink,
                unsupported_function_errors=unsupported_function_errors,
            )
            new_body: list[PlainAssignment] = []
            for s in stmt.body:
                new_body.append(
                    PlainAssignment(
                        s.target,
                        inline_calls(
                            s.expr,
                            fn_table,
                            mstore_sink=mstore_sink,
                            unsupported_function_errors=unsupported_function_errors,
                        ),
                    )
                )
            new_else_body: list[PlainAssignment] | None = None
            if stmt.else_body is not None:
                new_else_body = []
                for s in stmt.else_body:
                    new_else_body.append(
                        PlainAssignment(
                            s.target,
                            inline_calls(
                                s.expr,
                                fn_table,
                                mstore_sink=mstore_sink,
                                unsupported_function_errors=unsupported_function_errors,
                            ),
                        )
                    )
            if len(mstore_sink) > pre_len:
                raise ParseError(
                    f"Conditional memory write detected in {yf.yul_name!r} while "
                    "inlining a control-flow block. Exact uint512.from(...) "
                    "accessor writes must stay on the straight-line path."
                )
            new_assignments.append(
                ParsedIfBlock(
                    condition=new_cond,
                    body=tuple(new_body),
                    has_leave=stmt.has_leave,
                    else_body=(
                        tuple(new_else_body) if new_else_body is not None else None
                    ),
                )
            )
        elif isinstance(stmt, MemoryWrite):
            pre_len = len(mstore_sink)
            new_addr = inline_calls(
                stmt.address,
                fn_table,
                mstore_sink=mstore_sink,
                unsupported_function_errors=unsupported_function_errors,
            )
            new_value = inline_calls(
                stmt.value,
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
                stmt.expr,
                fn_table,
                mstore_sink=mstore_sink,
                unsupported_function_errors=unsupported_function_errors,
            )
            for effect in mstore_sink[pre_len:]:
                new_assignments.extend(effect.lower())
            del mstore_sink[pre_len:]
            new_assignments.append(PlainAssignment(stmt.target, inlined))

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
    # Pre-pass: count how many times each variable is assigned.
    # A compiler temporary assigned more than once is unusual and could
    # indicate a naming-convention change that made a real variable look
    # like a temporary.
    # ------------------------------------------------------------------
    assign_counts: Counter[str] = Counter()
    for stmt in yf.assignments:
        if isinstance(stmt, ParsedIfBlock):
            for s in stmt.body:
                assign_counts[s.target] += 1
            if stmt.else_body is not None:
                for s in stmt.else_body:
                    assign_counts[s.target] += 1
        elif isinstance(stmt, MemoryWrite):
            continue
        else:
            assign_counts[stmt.target] += 1

    var_map: dict[str, str] = {}
    subst: dict[str, Expr] = {}
    const_locals: dict[str, int] = {}
    memory_state: dict[int, Expr] = {}
    all_clean_names: set[str] = set()

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

    for stmt in yf.assignments:
        if isinstance(stmt, ParsedIfBlock):
            targets = [s.target for s in stmt.body]
            if stmt.else_body is not None:
                targets.extend(s.target for s in stmt.else_body)
        elif isinstance(stmt, MemoryWrite):
            targets = []
        else:
            targets = [stmt.target]
        for target in targets:
            clean = demangle_var(
                target,
                yf.params,
                yf.rets,
                keep_solidity_locals=keep_solidity_locals,
            )
            if clean is not None:
                all_clean_names.add(clean)

    # Save param names before SSA processing may rename them.
    param_names = tuple(var_map[p] for p in yf.params)

    # ------------------------------------------------------------------
    # SSA state: track assignment count per clean name so that
    # reassigned variables get distinct Lean names (_1, _2, ...).
    # Parameters start at count 1 (the function-parameter binding).
    # ------------------------------------------------------------------
    ssa_count: Counter[str] = Counter()
    for name in yf.params:
        clean = var_map.get(name)
        if clean:
            ssa_count[clean] = 1

    assignments: list[ModelStatement] = []

    def _resolve_const_locals(
        expr: Expr,
        *,
        const_locals_state: dict[str, int],
    ) -> Expr:
        """Resolve constant local Lean bindings inside an address expression."""
        if isinstance(expr, IntLit):
            return expr
        if isinstance(expr, Var):
            if expr.name in const_locals_state:
                return IntLit(const_locals_state[expr.name])
            return expr
        if isinstance(expr, Call):
            return Call(
                expr.name,
                tuple(
                    _resolve_const_locals(arg, const_locals_state=const_locals_state)
                    for arg in expr.args
                ),
            )
        _unreachable_expr(expr)

    def _resolve_memory_address(
        expr: Expr,
        *,
        op_name: str,
        const_locals_state: dict[str, int],
    ) -> int:
        addr = _try_const_eval(
            _resolve_const_locals(expr, const_locals_state=const_locals_state)
        )
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
        const_locals_state: dict[str, int],
    ) -> Expr:
        if isinstance(expr, (IntLit, Var)):
            return expr
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
        _unreachable_expr(expr)

    def _process_assignment_into(
        target: str,
        raw_expr: Expr,
        *,
        var_map_state: dict[str, str],
        subst_state: dict[str, Expr],
        const_locals_state: dict[str, int],
        inside_conditional: bool = False,
    ) -> Assignment | None:
        """Process a single raw assignment through copy-prop and demangling.

        Returns an Assignment if the target is a real variable, or None if
        it was copy-propagated into ``subst``.
        """
        expr = substitute_expr(raw_expr, subst_state)
        expr = rename_expr(expr, var_map_state, fn_map)
        expr = _resolve_memory_expr(expr, const_locals_state=const_locals_state)

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
                if ssa_name in all_clean_names:
                    raise ParseError(
                        f"SSA-generated name {ssa_name!r} in {sol_fn_name!r} "
                        f"collides with the demangled name of another variable. "
                        f"Refuse to generate ambiguous Lean binders."
                    )
        else:
            ssa_name = clean

        # Update var_map AFTER rename_expr.
        var_map_state[target] = ssa_name

        if not inside_conditional:
            const_value = _try_const_eval(
                _resolve_const_locals(
                    expr,
                    const_locals_state=const_locals_state,
                )
            )
            if const_value is not None:
                const_locals_state[ssa_name] = const_value
            else:
                const_locals_state.pop(ssa_name, None)

        return Assignment(target=ssa_name, expr=expr)

    for stmt in yf.assignments:
        if isinstance(stmt, ParsedIfBlock):
            if stmt.has_leave:
                raise ParseError(
                    f"Function {sol_fn_name!r} contains 'leave' in direct model "
                    "generation. Early return is only supported when inlining a "
                    "helper with a single top-level 'if cond { ... leave }'."
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
                for s in raw_assignments:
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

        a = _process_assignment_into(
            stmt.target,
            stmt.expr,
            var_map_state=var_map,
            subst_state=subst,
            const_locals_state=const_locals,
        )
        if a is not None:
            assignments.append(a)

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
            _unreachable_stmt(stmt)

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

OP_TO_LEAN_HELPER: dict[str, str] = {
    "add": "evmAdd",
    "sub": "evmSub",
    "mul": "evmMul",
    "div": "evmDiv",
    "mod": "evmMod",
    "not": "evmNot",
    "or": "evmOr",
    "and": "evmAnd",
    "eq": "evmEq",
    "shl": "evmShl",
    "shr": "evmShr",
    "clz": "evmClz",
    "lt": "evmLt",
    "gt": "evmGt",
    "mulmod": "evmMulmod",
}

OP_TO_OPCODE: dict[str, str] = {
    "add": "ADD",
    "sub": "SUB",
    "mul": "MUL",
    "div": "DIV",
    "mod": "MOD",
    "not": "NOT",
    "or": "OR",
    "and": "AND",
    "eq": "EQ",
    "shl": "SHL",
    "shr": "SHR",
    "clz": "CLZ",
    "lt": "LT",
    "gt": "GT",
    "mulmod": "MULMOD",
}

# Catch key-set drift between Lean helper names and opcode names at import time.
if set(OP_TO_LEAN_HELPER) != set(OP_TO_OPCODE):
    raise RuntimeError(
        f"OP_TO_LEAN_HELPER keys {set(OP_TO_LEAN_HELPER)} != "
        f"OP_TO_OPCODE keys {set(OP_TO_OPCODE)}"
    )

# Base norm helpers shared by all generators.  Per-generator extras (like
# bitLengthPlus1 for cbrt) are merged in via ModelConfig.extra_norm_ops.
_BASE_NORM_HELPERS = {
    "add": "normAdd",
    "sub": "normSub",
    "mul": "normMul",
    "div": "normDiv",
    "mod": "normMod",
    "not": "normNot",
    "or": "normOr",
    "and": "normAnd",
    "eq": "normEq",
    "shl": "normShl",
    "shr": "normShr",
    "clz": "normClz",
    "lt": "normLt",
    "gt": "normGt",
    "mulmod": "normMulmod",
}

# Also catch drift between OP_TO_LEAN_HELPER and _BASE_NORM_HELPERS.
if set(OP_TO_LEAN_HELPER) != set(_BASE_NORM_HELPERS):
    raise RuntimeError(
        f"OP_TO_LEAN_HELPER keys {set(OP_TO_LEAN_HELPER)} != "
        f"_BASE_NORM_HELPERS keys {set(_BASE_NORM_HELPERS)}"
    )


def validate_ident(name: str, *, what: str) -> None:
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
        raise ParseError(f"Invalid {what}: {name!r}")


def collect_ops(expr: Expr) -> list[str]:
    out: list[str] = []
    if isinstance(expr, Call):
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
    _unreachable_stmt(stmt)


def ordered_unique(items: list[str]) -> list[str]:
    d: dict[str, None] = dict.fromkeys(items)
    return list(d)


def _expr_size(expr: Expr) -> int:
    if isinstance(expr, (IntLit, Var)):
        return 1
    if isinstance(expr, Call):
        return 1 + sum(_expr_size(arg) for arg in expr.args)
    _unreachable_expr(expr)


def _replace_expr(expr: Expr, replacements: dict[Expr, str]) -> Expr:
    if expr in replacements:
        return Var(replacements[expr])
    if isinstance(expr, (IntLit, Var)):
        return expr
    if isinstance(expr, Call):
        return Call(
            expr.name, tuple(_replace_expr(arg, replacements) for arg in expr.args)
        )
    _unreachable_expr(expr)


def _expr_vars(expr: Expr) -> set[str]:
    if isinstance(expr, IntLit):
        return set()
    if isinstance(expr, Var):
        return {expr.name}
    if isinstance(expr, Call):
        out: set[str] = set()
        for arg in expr.args:
            out.update(_expr_vars(arg))
        return out
    _unreachable_expr(expr)


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

    scope = set(model.param_names)
    for stmt in model.assignments:
        if isinstance(stmt, Assignment):
            missing = _expr_vars(stmt.expr) - scope
            if missing:
                raise ParseError(
                    f"Model {model.fn_name!r} has an out-of-scope variable use: "
                    f"{stmt.target!r} depends on {sorted(missing)}"
                )
            scope.add(stmt.target)
            continue

        if not isinstance(stmt, ConditionalBlock):
            _unreachable_stmt(stmt)

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
        return expr.value
    if isinstance(expr, Var):
        try:
            return env[expr.name]
        except KeyError as err:
            raise EvaluationError(f"Undefined model variable {expr.name!r}") from err
    if not isinstance(expr, Call):
        _unreachable_expr(expr)

    component_match = re.fullmatch(r"__component_(\d+)_(\d+)", expr.name)
    if component_match and len(expr.args) == 1:
        idx = int(component_match.group(1))
        total = int(component_match.group(2))
        values = _expect_tuple(
            evaluate_model_expr(
                expr.args[0],
                env,
                model_table=model_table,
                call_stack=call_stack,
            ),
            size=total,
            context=f"{expr.name} projection",
        )
        try:
            return values[idx]
        except IndexError as err:
            raise EvaluationError(
                f"{expr.name} requested index {idx}, but only {len(values)} value(s) exist"
            ) from err

    if expr.name == "__ite" and len(expr.args) == 3:
        cond = _expect_scalar(
            evaluate_model_expr(
                expr.args[0],
                env,
                model_table=model_table,
                call_stack=call_stack,
            ),
            context="__ite condition",
        )
        branch = expr.args[1] if cond != 0 else expr.args[2]
        return evaluate_model_expr(
            branch,
            env,
            model_table=model_table,
            call_stack=call_stack,
        )

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
            _unreachable_stmt(stmt)

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
) -> list[Call]:
    counts: Counter[Expr] = Counter()
    _walk_model_calls(expr, model_call_names, counts)
    repeated = [node for node, count in counts.items() if count > 1]
    repeated.sort(key=_expr_size)
    return [node for node in repeated if isinstance(node, Call)]


def _walk_model_calls(
    node: Expr, model_call_names: frozenset[str], counts: Counter[Expr]
) -> None:
    """Recursively count model-call occurrences in *node*."""
    if isinstance(node, Call):
        if node.name in model_call_names:
            counts[node] += 1
        for arg in node.args:
            _walk_model_calls(arg, model_call_names, counts)


def _walk_statement(
    stmt: ModelStatement, model_call_names: frozenset[str], counts: Counter[Expr]
) -> None:
    """Count model-call occurrences across all expressions in *stmt*."""
    if isinstance(stmt, Assignment):
        _walk_model_calls(stmt.expr, model_call_names, counts)
    elif isinstance(stmt, ConditionalBlock):
        _walk_model_calls(stmt.condition, model_call_names, counts)
        for a in stmt.then_branch.assignments:
            _walk_model_calls(a.expr, model_call_names, counts)
        for a in stmt.else_branch.assignments:
            _walk_model_calls(a.expr, model_call_names, counts)


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
    _unreachable_stmt(stmt)


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
        if call.name not in model_call_names:
            raise ParseError(f"CSE: refusing to hoist non-model call {call!r}")
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
        return [
            *_localize_assignment_cse(
                stmt,
                model_call_names=model_call_names,
            )
        ]

    if isinstance(stmt, ConditionalBlock):
        prefix, condition = _hoist_repeated_calls_in_expr(
            stmt.condition,
            model_call_names=model_call_names,
        )

        then_assignments: list[Assignment] = []
        for assignment in stmt.then_branch.assignments:
            then_assignments.extend(
                _localize_assignment_cse(
                    assignment,
                    model_call_names=model_call_names,
                )
            )

        localized_else: list[Assignment] = []
        for assignment in stmt.else_branch.assignments:
            localized_else.extend(
                _localize_assignment_cse(
                    assignment,
                    model_call_names=model_call_names,
                )
            )

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

    _unreachable_stmt(stmt)


def _localize_assignment_cse(
    stmt: Assignment,
    *,
    model_call_names: frozenset[str],
) -> list[Assignment]:
    hoisted, expr = _hoist_repeated_calls_in_expr(
        stmt.expr,
        model_call_names=model_call_names,
    )
    return [*hoisted, Assignment(target=stmt.target, expr=expr)]


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
    # Reset CSE counter so each function's hoisted names start at _cse_1.
    _gensym_counters.pop("cse", None)

    # -- Pass 1: count occurrences across the entire model -----------------
    counts: Counter[Expr] = Counter()
    for stmt in model.assignments:
        _walk_statement(stmt, model_call_names, counts)

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
        if call.name not in model_call_names:
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

    function_collection = YulParser(tokens).collect_all_functions()
    helper_table = dict(function_collection.functions)
    rejected_helpers = dict(function_collection.rejected)

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
            yf = parser.find_exact_function(
                exact_yul_name,
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

    for yul_name in fn_map:
        helper_table.pop(yul_name, None)

    inlined_targets: dict[str, YulFunction] = {}
    for sol_name in selected:
        inlined_targets[sol_name] = _inline_yul_function(
            yul_functions[sol_name],
            helper_table,
            unsupported_function_errors=rejected_helpers,
        )

    return PreparedTranslation(
        selected_functions=tuple(selected),
        fn_map=fn_map,
        yul_functions=inlined_targets,
        collected_helpers=helper_table,
        rejected_helpers=rejected_helpers,
    )


def build_restricted_ir_models(
    preparation: PreparedTranslation,
    config: ModelConfig,
    *,
    pipeline: TranslationPipeline,
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
        for model in transformed:
            validate_function_model(model)

    if pipeline.prune_dead_assignments:
        transformed = [
            (
                _prune_dead_assignments(model)
                if model.fn_name not in config.skip_prune
                else model
            )
            for model in transformed
        ]
        for model in transformed:
            validate_function_model(model)

    return transformed


def translate_yul_to_models(
    yul_text: str,
    config: ModelConfig,
    *,
    selected_functions: tuple[str, ...] | None = None,
    pipeline: TranslationPipeline = OPTIMIZED_TRANSLATION_PIPELINE,
) -> TranslationResult:
    """Run the selected translation pipeline and return the final models."""

    preparation = prepare_translation(
        yul_text,
        config,
        selected_functions=selected_functions,
    )
    models = build_restricted_ir_models(
        preparation,
        config,
        pipeline=pipeline,
    )
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
    op_helper_map: dict[str, str],
    call_helper_map: dict[str, str],
) -> str:
    if isinstance(expr, IntLit):
        return str(expr.value)
    if isinstance(expr, Var):
        return expr.name
    if isinstance(expr, Call):
        # Handle __component_N_M(call) for multi-return function calls.
        # Emits Lean nested-pair projection for element N of M total:
        #   N=0       → .1
        #   0<N<M-1   → .2.2...2.1  (N-1 extra .2 prefixes)
        #   N=M-1     → .2.2...2    (N-1 extra .2 suffixes)
        # This handles Lean's right-nested Prod: A × B × C = A × (B × C).
        m = re.fullmatch(r"__component_(\d+)_(\d+)", expr.name)
        if m and len(expr.args) == 1:
            idx = int(m.group(1))
            total = int(m.group(2))
            inner = emit_expr(
                expr.args[0],
                op_helper_map=op_helper_map,
                call_helper_map=call_helper_map,
            )
            if total <= 2 or idx == 0:
                return f"({inner}).{idx + 1}"
            elif idx == total - 1:
                return f"({inner})" + ".2" * idx
            else:
                return f"({inner})" + ".2" * idx + ".1"

        # Handle __ite(cond, if_val, else_val) from leave-handling.
        # Emits: if (cond) ≠ 0 then if_val else else_val
        if expr.name == "__ite" and len(expr.args) == 3:
            cond = emit_expr(
                expr.args[0],
                op_helper_map=op_helper_map,
                call_helper_map=call_helper_map,
            )
            if_val = emit_expr(
                expr.args[1],
                op_helper_map=op_helper_map,
                call_helper_map=call_helper_map,
            )
            else_val = emit_expr(
                expr.args[2],
                op_helper_map=op_helper_map,
                call_helper_map=call_helper_map,
            )
            return f"if ({cond}) ≠ 0 then {if_val} else {else_val}"

        helper = op_helper_map.get(expr.name)
        if helper is None:
            helper = call_helper_map.get(expr.name)
        if helper is None:
            raise ParseError(f"Unsupported call in Lean emitter: {expr.name!r}")
        args = " ".join(
            f"({emit_expr(a, op_helper_map=op_helper_map, call_helper_map=call_helper_map)})"
            for a in expr.args
        )
        return f"{helper} {args}".rstrip()
    _unreachable_expr(expr)


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
    # heuristic fun_<name>_<digits> discovery.
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

    def _emit_rhs(expr: Expr) -> str:
        rhs_expr = expr
        if not evm and config.norm_rewrite is not None:
            rhs_expr = config.norm_rewrite(rhs_expr)
        return emit_expr(
            rhs_expr,
            op_helper_map=op_map,
            call_helper_map=call_map,
        )

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
            _unreachable_stmt(stmt)

    if len(return_names) == 1:
        lines.append(f"  {return_names[0]}")
    else:
        lines.append(f"  ({', '.join(return_names)})")
    return "\n".join(lines)


def render_function_defs(models: list[FunctionModel], config: ModelConfig) -> str:
    parts: list[str] = []
    for model in models:
        model_base = config.model_names[model.fn_name]
        evm_name = f"{model_base}_evm"
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
            f"def {evm_name}{param_sig} : {ret_type} :=\n"
            f"{evm_body}\n"
        )
        if model.fn_name not in config.skip_norm:
            norm_name = model_base
            norm_body = build_model_body(
                model.assignments,
                evm=False,
                config=config,
                param_names=model.param_names,
                return_names=model.return_names,
            )
            parts.append(
                f"/-- Normalized auto-generated model of `{model.fn_name}` on Nat arithmetic. -/\n"
                f"def {norm_name}{param_sig} : {ret_type} :=\n"
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
    modeled_functions = ", ".join(model.fn_name for model in models)

    raw_ops: list[str] = []
    for model in models:
        for stmt in model.assignments:
            raw_ops.extend(collect_ops_from_statement(stmt))
    opcodes = ordered_unique([OP_TO_OPCODE[name] for name in raw_ops])
    opcodes_line = ", ".join(opcodes)

    function_defs = render_function_defs(models, config)
    emit_norm = any_norm_models(models, config)

    norm_defs = ""
    if emit_norm:
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
            "def normShl (shift value : Nat) : Nat := value <<< shift\n\n"
            "def normShr (shift value : Nat) : Nat := value / 2 ^ shift\n\n"
            "def normClz (value : Nat) : Nat :=\n"
            "  if value = 0 then 256 else 255 - Nat.log2 value\n\n"
            f"{config.extra_lean_defs}"
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

    raw_ops: list[str] = []
    for model in models:
        for stmt in model.assignments:
            raw_ops.extend(collect_ops_from_statement(stmt))
    opcodes = ordered_unique([OP_TO_OPCODE[name] for name in raw_ops])
    print(f"Modeled opcodes: {', '.join(opcodes)}")

    return 0
