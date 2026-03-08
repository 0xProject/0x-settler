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
from typing import Callable


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
    elide_zero_assignments: bool
    hoist_repeated_calls: bool
    prune_dead_assignments: bool


RAW_TRANSLATION_PIPELINE = TranslationPipeline(
    name="raw",
    elide_zero_assignments=False,
    hoist_repeated_calls=False,
    prune_dead_assignments=False,
)

OPTIMIZED_TRANSLATION_PIPELINE = TranslationPipeline(
    name="optimized",
    # Zero-assignment elision is not semantics-preserving in general. Keep the
    # optimized default limited to passes with direct equivalence tests.
    elide_zero_assignments=False,
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
    body: tuple[tuple[str, Expr], ...]
    has_leave: bool = False
    else_body: tuple[tuple[str, Expr], ...] | None = None


@dataclass(frozen=True)
class MemoryWrite:
    """A supported straight-line ``mstore(addr, value)`` statement."""

    address: Expr
    value: Expr


# A raw parsed statement is either an assignment, a supported memory write,
# or an if/switch block.
RawStatement = tuple[str, Expr] | MemoryWrite | ParsedIfBlock


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

    def _parse_let(self, results: list) -> None:
        """Parse a ``let`` statement and append to *results*.

        Handles three forms:
        - ``let x := expr``          — single-value assignment
        - ``let a, b, c := call()``  — multi-value; each target gets a
          synthetic ``__component_N_M(call)`` wrapper (index N of M total)
        - ``let x``                  — bare declaration (zero-init, skipped)
        """
        self._pop()  # consume 'let'
        target = self._expect_ident()
        if self._peek_kind() == ",":
            all_targets: list[str] = [target]
            while self._peek_kind() == ",":
                self._pop()
                all_targets.append(self._expect_ident())
            self._expect(":=")
            expr = self._parse_expr()
            for idx, t in enumerate(all_targets):
                results.append((t, Call(f"__component_{idx}_{len(all_targets)}", (expr,))))
        elif self._peek_kind() == ":=":
            self._pop()
            expr = self._parse_expr()
            results.append((target, expr))
        else:
            # Bare declaration: ``let x``  (zero-initialized per Yul spec)
            results.append((target, IntLit(0)))

    def _parse_assignment_loop(
        self,
        *,
        allow_control_flow: bool,
        context: str,
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
                self._pop()
                inner, inner_leave = self._parse_assignment_loop(
                    allow_control_flow=allow_control_flow,
                    context=context,
                )
                results.extend(inner)
                has_leave = has_leave or inner_leave
                self._expect("}")
                continue

            if kind == "ident" and self.tokens[self.i][1] == "let":
                self._parse_let(results)
                continue

            if kind == "ident" and self.tokens[self.i][1] == "leave":
                self._pop()
                has_leave = True
                continue

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
                    results.append(ParsedIfBlock(
                        condition=condition,
                        body=tuple(body),
                        has_leave=body_leave,
                    ))
                else:  # switch
                    self._pop()  # consume 'switch'
                    condition = self._parse_expr()
                    # We support exactly one form of switch:
                    #   switch e case 0 { else_body } default { if_body }
                    # (branches may appear in either order).  Anything else
                    # is rejected loudly.
                    case0_body: list[RawStatement] | None = None
                    case0_leave = False
                    default_body: list[RawStatement] | None = None
                    default_leave = False
                    n_branches = 0
                    while (not self._at_end()
                           and self._peek_kind() == "ident"
                           and self.tokens[self.i][1] in ("case", "default")):
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
                            case0_body, case0_leave = self._parse_assignment_loop(
                                allow_control_flow=False,
                                context="switch branch",
                            )
                            self._expect("}")
                        else:  # default
                            if default_body is not None:
                                raise ParseError(
                                    "Duplicate 'default' in switch statement."
                                )
                            self._expect("{")
                            default_body, default_leave = self._parse_assignment_loop(
                                allow_control_flow=False,
                                context="switch branch",
                            )
                            self._expect("}")
                            # default must be the last branch.
                            n_branches += 1
                            break
                        n_branches += 1
                    # Reject trailing case branches after default.
                    if (default_body is not None
                            and not self._at_end()
                            and self._peek_kind() == "ident"
                            and self.tokens[self.i][1] in ("case", "default")):
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
                    if_body = tuple(default_body) if default_body else ()
                    else_body = tuple(case0_body) if case0_body else None
                    results.append(ParsedIfBlock(
                        condition=condition,
                        body=if_body,
                        has_leave=default_leave or case0_leave,
                        else_body=else_body,
                    ))
                continue

            if kind == "ident" and self.i + 1 < len(self.tokens) and self.tokens[self.i + 1][0] == ":=":
                target = self._expect_ident()
                self._expect(":=")
                expr = self._parse_expr()
                results.append((target, expr))
                continue

            if kind == "ident" or kind == "num":
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

    def _parse_body_assignments(self) -> list[RawStatement]:
        results, _has_leave = self._parse_assignment_loop(
            allow_control_flow=True,
            context="function body",
        )
        return results

    def _parse_if_body_assignments(
        self,
    ) -> tuple[list[tuple[str, Expr]], bool]:
        """Parse the body of an ``if`` block.

        Returns ``(assignments, has_leave)`` where *has_leave* indicates
        that a ``leave`` statement (early return) was encountered.
        """
        raw, has_leave = self._parse_assignment_loop(
            allow_control_flow=False,
            context="if-body",
        )
        # When allow_control_flow=False, all statements are plain assignments.
        plain: list[tuple[str, Expr]] = []
        for stmt in raw:
            if isinstance(stmt, (ParsedIfBlock, MemoryWrite)):
                raise ParseError(
                    "Unexpected control-flow block inside if-body results"
                )
            plain.append(stmt)
        return plain, has_leave

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
        assignments = self._parse_body_assignments()
        self._expect("}")
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
        self, sol_fn_name: str, *, n_params: int | None = None,
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
                and self.tokens[idx + 1][1][len(target_prefix):].isdigit()
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
                filtered = [m for m in matches
                            if not self._body_references_any(m, known_yul_names)]
            else:
                filtered = [m for m in matches
                            if self._body_references_any(m, known_yul_names)]
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
            if (
                self.tokens[idx] == ("ident", "function")
                and self.tokens[idx + 1] == ("ident", yul_name)
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
            if (
                self._peek_kind() == "ident"
                and self.tokens[self.i][1] == "function"
            ):
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
    return_vars: list[str] | str,
    *,
    keep_solidity_locals: bool = False,
) -> str | None:
    """Map a Yul variable name back to its Solidity-level name.

    Returns the cleaned name, or None if the variable is a compiler temporary
    that should be copy-propagated away.

    ``param_vars`` is a list of Yul parameter variable names (supports
    multi-parameter functions).

    ``return_vars`` is a list of Yul return variable names (or a single
    string for backward compatibility with single-return functions).

    When *keep_solidity_locals* is True, variables matching the
    ``var_<name>_<digits>`` pattern (compiler representation of
    Solidity-declared locals) are kept in the model even if they are
    not the function parameter or return variable.
    """
    if isinstance(return_vars, str):
        return_vars = [return_vars]
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
    raise TypeError(f"Unsupported Expr node: {type(expr)}")


def substitute_expr(expr: Expr, subst: dict[str, Expr]) -> Expr:
    if isinstance(expr, IntLit):
        return expr
    if isinstance(expr, Var):
        return subst.get(expr.name, expr)
    if isinstance(expr, Call):
        return Call(expr.name, tuple(substitute_expr(a, subst) for a in expr.args))
    raise TypeError(f"Unsupported Expr node: {type(expr)}")


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
    operations.  Used for resolving constant memory addresses in
    mstore/mload folding.
    """
    if isinstance(expr, IntLit):
        return expr.value
    if isinstance(expr, Call):
        if expr.name == "add" and len(expr.args) == 2:
            a = _try_const_eval(expr.args[0])
            b = _try_const_eval(expr.args[1])
            if a is not None and b is not None:
                return (a + b) % (2 ** 256)
        if expr.name == "sub" and len(expr.args) == 2:
            a = _try_const_eval(expr.args[0])
            b = _try_const_eval(expr.args[1])
            if a is not None and b is not None:
                return (a + 2 ** 256 - b) % (2 ** 256)
        # Handle __ite(cond, if_val, else_val): if both branches
        # evaluate to the same constant, the result is that constant
        # regardless of the condition.
        if expr.name == "__ite" and len(expr.args) == 3:
            if_val = _try_const_eval(expr.args[1])
            else_val = _try_const_eval(expr.args[2])
            if if_val is not None and else_val is not None and if_val == else_val:
                return if_val
    return None


def _inline_single_call(
    fn: YulFunction,
    args: tuple[Expr, ...],
    fn_table: dict[str, YulFunction],
    depth: int,
    max_depth: int,
    mstore_sink: list[MemoryWrite] | None = None,
    unsupported_function_errors: dict[str, str] | None = None,
) -> Expr | tuple[Expr, ...]:
    """Inline one function call, returning its return-value expression(s).

    Builds a substitution from parameters → argument expressions, then
    processes the function body sequentially (same semantics as copy-prop).
    Each local variable gets a unique gensym name to avoid clashes with
    the caller's scope.

    When *mstore_sink* is not None, supported straight-line ``mstore``
    statements from inlined functions are collected as explicit
    ``MemoryWrite`` entries. The caller is responsible for injecting these
    into the outer function's statement list at the call site so the later
    model-construction pass can interpret memory sequentially.
    """
    if fn.expr_stmts:
        descriptions = []
        for e in fn.expr_stmts[:3]:
            if isinstance(e, Call):
                descriptions.append(f"{e.name}(...)")
            else:
                descriptions.append(repr(e))
        summary = ", ".join(descriptions)
        if len(fn.expr_stmts) > 3:
            summary += ", ..."
        raise ParseError(
            f"Inlining function {fn.yul_name!r} encountered "
            f"{len(fn.expr_stmts)} unhandled expression-statement(s): "
            f"[{summary}]. Refuse to inline incomplete semantics."
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
        for _ in range(50):
            prev = e
            e = substitute_expr(e, s)
            if e == prev:
                break
        else:
            raise ParseError(
                f"Substitution resolution did not converge after 50 "
                f"iterations for expression: {e!r}"
            )
        return e

    for stmt in fn.assignments:
        if isinstance(stmt, ParsedIfBlock):
            # Evaluate condition
            cond = substitute_expr(stmt.condition, subst)
            cond = inline_calls(cond, fn_table, depth + 1, max_depth,
                                mstore_sink=mstore_sink,
                                unsupported_function_errors=unsupported_function_errors)
            # Process if-body assignments into a separate subst branch.
            if_subst = dict(subst)
            # Track mstore count to detect conditional memory writes.
            pre_if_sink_len = len(mstore_sink) if mstore_sink is not None else 0
            for target, raw_expr in stmt.body:
                expr = substitute_expr(raw_expr, if_subst)
                expr = inline_calls(expr, fn_table, depth + 1, max_depth,
                                    mstore_sink=mstore_sink,
                                    unsupported_function_errors=unsupported_function_errors)
                if_subst[target] = expr

            # Reject conditional memory writes — they can't be modeled
            # faithfully without tracking memory state per branch.
            if mstore_sink is not None and len(mstore_sink) > pre_if_sink_len:
                raise ParseError(
                    f"Conditional memory write detected in {fn.yul_name!r}: "
                    f"{len(mstore_sink) - pre_if_sink_len} mstore(s) emitted "
                    f"inside an if-block body. Restructure the wrapper so "
                    f"memory writes occur outside conditionals."
                )

            # Also process else_body if present (from switch).
            if stmt.else_body is not None:
                else_subst = dict(subst)
                pre_else_sink_len = len(mstore_sink) if mstore_sink is not None else 0
                for target, raw_expr in stmt.else_body:
                    expr = substitute_expr(raw_expr, else_subst)
                    expr = inline_calls(expr, fn_table, depth + 1, max_depth,
                                        mstore_sink=mstore_sink,
                                        unsupported_function_errors=unsupported_function_errors)
                    else_subst[target] = expr
                if mstore_sink is not None and len(mstore_sink) > pre_else_sink_len:
                    raise ParseError(
                        f"Conditional memory write detected in "
                        f"{fn.yul_name!r}: mstore(s) emitted inside "
                        f"an else-body. Restructure the wrapper so "
                        f"memory writes occur outside conditionals."
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
                for target, _ in (*stmt.body, *stmt.else_body):
                    if target not in seen:
                        seen.add(target)
                        all_targets.append(target)
                for target in all_targets:
                    pre_val = subst.get(target, IntLit(0))
                    if_val = if_subst.get(target, pre_val)
                    else_val = else_subst.get(target, pre_val)
                    if if_val != else_val:
                        subst[target] = Call("__ite", (cond, if_val, else_val))
                    elif if_val != pre_val:
                        subst[target] = if_val
            else:
                # Normal if-block (no leave, no else): take the if-branch value.
                for target, _raw_expr in stmt.body:
                    if_val = if_subst[target]
                    orig_val = subst.get(target, IntLit(0))
                    if if_val != orig_val:
                        subst[target] = if_val
        elif isinstance(stmt, MemoryWrite):
            if mstore_sink is None:
                raise ParseError(
                    f"Function {fn.yul_name!r} contains supported memory writes, "
                    f"but no memory sink was provided during inlining."
                )
            addr_expr = substitute_expr(stmt.address, subst)
            addr_expr = inline_calls(
                addr_expr,
                fn_table,
                depth + 1,
                max_depth,
                mstore_sink=mstore_sink,
                unsupported_function_errors=unsupported_function_errors,
            )
            val_expr = substitute_expr(stmt.value, subst)
            val_expr = inline_calls(
                val_expr,
                fn_table,
                depth + 1,
                max_depth,
                mstore_sink=mstore_sink,
                unsupported_function_errors=unsupported_function_errors,
            )
            mstore_sink.append(
                MemoryWrite(
                    address=_resolve(addr_expr, subst),
                    value=_resolve(val_expr, subst),
                )
            )
        else:
            target, raw_expr = stmt
            expr = substitute_expr(raw_expr, subst)
            expr = inline_calls(expr, fn_table, depth + 1, max_depth,
                                mstore_sink=mstore_sink,
                                unsupported_function_errors=unsupported_function_errors)
            # Keep helper locals as pure substitutions. Introducing fresh
            # `_inline_*` aliases here can leak undefined names into sunk
            # MemoryWrite addresses/values after nested inlining.
            subst[target] = expr

    def _get_ret(r: str) -> Expr:
        else_val = _resolve(subst.get(r, IntLit(0)), subst)
        if leave_cond is not None and leave_subst is not None:
            if_val = _resolve(leave_subst.get(r, IntLit(0)), leave_subst)
            resolved_cond = _resolve(leave_cond, leave_subst)
            return Call("__ite", (resolved_cond, if_val, else_val))
        return else_val

    if len(fn.rets) == 1:
        return _get_ret(fn.rets[0])
    return tuple(_get_ret(r) for r in fn.rets)


def inline_calls(
    expr: Expr,
    fn_table: dict[str, YulFunction],
    depth: int = 0,
    max_depth: int = 20,
    mstore_sink: list[MemoryWrite] | None = None,
    unsupported_function_errors: dict[str, str] | None = None,
) -> Expr:
    """Recursively inline function calls in an expression.

    Walks the expression tree. When a ``Call`` targets a function in
    *fn_table*, its body is inlined via sequential substitution.
    ``__component_N`` wrappers (from multi-value ``let``) are resolved
    to the Nth return value of the inlined function.

    When *mstore_sink* is not None, explicit ``MemoryWrite`` side effects
    from inlined functions are collected (see ``_inline_single_call``).
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
            inner_args = tuple(inline_calls(a, fn_table, depth,
                                            max_depth=max_depth,
                                            mstore_sink=mstore_sink,
                                            unsupported_function_errors=unsupported_function_errors)
                               for a in inner.args)
            if inner.name in fn_table:
                result = _inline_single_call(
                    fn_table[inner.name], inner_args, fn_table, depth + 1,
                    max_depth, mstore_sink=mstore_sink,
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
        args = tuple(inline_calls(a, fn_table, depth,
                                  max_depth=max_depth,
                                  mstore_sink=mstore_sink,
                                  unsupported_function_errors=unsupported_function_errors)
                     for a in expr.args)

        # Direct call to a collected function
        if expr.name in fn_table:
            fn = fn_table[expr.name]
            result = _inline_single_call(fn, args, fn_table, depth + 1,
                                         max_depth, mstore_sink=mstore_sink,
                                         unsupported_function_errors=unsupported_function_errors)
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
    raise TypeError(f"Unsupported Expr node: {type(expr)}")


def _inline_yul_function(
    yf: YulFunction,
    fn_table: dict[str, YulFunction],
    unsupported_function_errors: dict[str, str] | None = None,
) -> YulFunction:
    """Apply ``inline_calls`` to every expression in a YulFunction.

    When inlined functions contain supported straight-line ``mstore``
    statements, they are collected and injected as explicit ``MemoryWrite``
    statements at the call site. Conditional memory writes are rejected.
    """
    # Shared sink for memory writes from inlined helpers. Effects are
    # injected into the statement list at the point they are collected so
    # later translation can interpret memory sequentially.
    mstore_sink: list[MemoryWrite] = []

    new_assignments: list[RawStatement] = []
    for stmt in yf.assignments:
        if isinstance(stmt, ParsedIfBlock):
            pre_len = len(mstore_sink)
            new_cond = inline_calls(stmt.condition, fn_table,
                                    mstore_sink=mstore_sink,
                                    unsupported_function_errors=unsupported_function_errors)
            new_body: list[tuple[str, Expr]] = []
            for target, raw_expr in stmt.body:
                new_body.append((target, inline_calls(raw_expr, fn_table,
                                                      mstore_sink=mstore_sink,
                                                      unsupported_function_errors=unsupported_function_errors)))
            new_else_body: list[tuple[str, Expr]] | None = None
            if stmt.else_body is not None:
                new_else_body = []
                for target, raw_expr in stmt.else_body:
                    new_else_body.append((target, inline_calls(
                        raw_expr,
                        fn_table,
                        mstore_sink=mstore_sink,
                        unsupported_function_errors=unsupported_function_errors,
                    )))
            if len(mstore_sink) > pre_len:
                raise ParseError(
                    f"Conditional memory write detected in {yf.yul_name!r} while "
                    f"inlining a control-flow block. The supported memory model "
                    f"only allows straight-line writes outside conditionals."
                )
            new_assignments.append(ParsedIfBlock(
                condition=new_cond,
                body=tuple(new_body),
                has_leave=stmt.has_leave,
                else_body=(
                    tuple(new_else_body)
                    if new_else_body is not None
                    else None
                ),
            ))
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
                    f"direct straight-line writes."
                )
            new_assignments.append(MemoryWrite(new_addr, new_value))
        else:
            target, raw_expr = stmt
            pre_len = len(mstore_sink)
            inlined = inline_calls(raw_expr, fn_table,
                                   mstore_sink=mstore_sink,
                                   unsupported_function_errors=unsupported_function_errors)
            # Inject any mstore effects collected during this inlining.
            new_assignments.extend(mstore_sink[pre_len:])
            new_assignments.append((target, inlined))

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
    *,
    elide_zero_assignments: bool = True,
) -> FunctionModel:
    """Convert a parsed YulFunction into a FunctionModel.

    Performs copy propagation to eliminate compiler temporaries and renames
    variables/calls back to Solidity-level names.

    Validates:
    - Multi-assigned compiler temporaries are rejected.
    - The return variable is recognized and assigned in the model.
    - ``elide_zero_assignments`` controls whether literal zero-initializations
      are dropped during model construction.
    - Memory use must stay within the explicit supported subset:
      straight-line constant-address, 32-byte-aligned ``mstore``/``mload``
      with no aliasing.
    """
    if yf.expr_stmts:
        descriptions = []
        for e in yf.expr_stmts[:3]:
            if isinstance(e, Call):
                descriptions.append(f"{e.name}(...)")
            else:
                descriptions.append(repr(e))
        summary = ", ".join(descriptions)
        if len(yf.expr_stmts) > 3:
            summary += ", ..."
        raise ParseError(
            f"Function {sol_fn_name!r} contains "
            f"{len(yf.expr_stmts)} expression-statement(s) not captured "
            f"in the direct model: [{summary}]. Refuse to generate an "
            f"incomplete model."
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
            for target, _ in stmt.body:
                assign_counts[target] += 1
            if stmt.else_body is not None:
                for target, _ in stmt.else_body:
                    assign_counts[target] += 1
        elif isinstance(stmt, MemoryWrite):
            continue
        else:
            target, _ = stmt
            assign_counts[target] += 1

    var_map: dict[str, str] = {}
    subst: dict[str, Expr] = {}
    const_locals: dict[str, int] = {}
    memory_state: dict[int, Expr] = {}
    all_clean_names: set[str] = set()

    for name in [*yf.params, *yf.rets]:
        clean = demangle_var(name, yf.params, yf.rets, keep_solidity_locals=keep_solidity_locals)
        if clean:
            var_map[name] = clean
            all_clean_names.add(clean)

    for stmt in yf.assignments:
        if isinstance(stmt, ParsedIfBlock):
            targets = [target for target, _ in stmt.body]
            if stmt.else_body is not None:
                targets.extend(target for target, _ in stmt.else_body)
        elif isinstance(stmt, MemoryWrite):
            targets = []
        else:
            target, _ = stmt
            targets = [target]
        for target in targets:
            clean = demangle_var(
                target, yf.params, yf.rets,
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

    def _resolve_const_locals(expr: Expr) -> Expr:
        """Resolve constant local Lean bindings inside an address expression."""
        if isinstance(expr, IntLit):
            return expr
        if isinstance(expr, Var):
            if expr.name in const_locals:
                return IntLit(const_locals[expr.name])
            return expr
        if isinstance(expr, Call):
            return Call(
                expr.name,
                tuple(_resolve_const_locals(arg) for arg in expr.args),
            )
        raise TypeError(f"Unsupported Expr node: {type(expr)}")

    def _resolve_memory_address(expr: Expr, *, op_name: str) -> int:
        addr = _try_const_eval(_resolve_const_locals(expr))
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

    def _resolve_memory_expr(expr: Expr) -> Expr:
        if isinstance(expr, (IntLit, Var)):
            return expr
        if isinstance(expr, Call):
            if expr.name == "mload" and len(expr.args) == 1:
                addr = _resolve_memory_address(expr.args[0], op_name="mload")
                if addr not in memory_state:
                    raise ParseError(
                        f"mload at address {addr} in {sol_fn_name!r} has no "
                        f"matching prior mstore. Available addresses: "
                        f"{sorted(memory_state.keys())}"
                    )
                return memory_state[addr]
            return Call(
                expr.name,
                tuple(_resolve_memory_expr(arg) for arg in expr.args),
            )
        raise TypeError(f"Unsupported Expr node: {type(expr)}")

    def _process_assignment(
        target: str, raw_expr: Expr, *, inside_conditional: bool = False,
    ) -> Assignment | None:
        """Process a single raw assignment through copy-prop and demangling.

        Returns an Assignment if the target is a real variable, or None if
        it was copy-propagated into ``subst``.
        """
        expr = substitute_expr(raw_expr, subst)
        expr = rename_expr(expr, var_map, fn_map)
        expr = _resolve_memory_expr(expr)

        clean = demangle_var(target, yf.params, yf.rets, keep_solidity_locals=keep_solidity_locals)
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
                subst[target] = IntLit(0)
            else:
                subst[target] = expr
            return None

        # Rename the RHS expression BEFORE updating var_map so that
        # self-references (e.g. ``x := f(x)``) resolve to the
        # *previous* binding, not the one being created.
        skip_zero = (
            elide_zero_assignments
            and isinstance(expr, IntLit)
            and expr.value == 0
        )

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
        var_map[target] = ssa_name

        if not inside_conditional:
            const_value = _try_const_eval(_resolve_const_locals(expr))
            if const_value is not None:
                const_locals[ssa_name] = const_value
            else:
                const_locals.pop(ssa_name, None)

        if skip_zero:
            return None

        return Assignment(target=ssa_name, expr=expr)

    for stmt in yf.assignments:
        if isinstance(stmt, ParsedIfBlock):
            # Process the if-block: apply copy-prop/demangling to
            # condition and body, then emit a ConditionalBlock.
            cond = substitute_expr(stmt.condition, subst)
            cond = rename_expr(cond, var_map, fn_map)
            cond = _resolve_memory_expr(cond)

            # Save pre-if Lean names so each branch can explicitly return
            # the values that were live before the conditional ran.
            pre_if_names: dict[str, str] = {}
            # Snapshot of all Lean names in scope before the if-body.
            pre_if_scope: set[str] = set(var_map.values())

            def _record_pre_if_name(target: str) -> str | None:
                clean = demangle_var(
                    target, yf.params, yf.rets,
                    keep_solidity_locals=keep_solidity_locals,
                )
                if clean is not None and clean not in pre_if_names:
                    pre_if_names[clean] = var_map.get(target, clean)
                return clean

            body_assignments: list[Assignment] = []
            for target, raw_expr in stmt.body:
                _record_pre_if_name(target)
                a = _process_assignment(
                    target, raw_expr, inside_conditional=True,
                )
                if a is not None:
                    body_assignments.append(a)

            else_assignments_list: list[Assignment] = []
            if stmt.else_body is not None:
                for target, raw_expr in stmt.else_body:
                    _record_pre_if_name(target)
                    a = _process_assignment(
                        target, raw_expr, inside_conditional=True,
                    )
                    if a is not None:
                        else_assignments_list.append(a)

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
                    else_outputs = tuple(pre_if_names[target] for target in modified_list)
                else:
                    else_outputs = tuple(
                        target if target in else_assigned else pre_if_names[target]
                        for target in modified_list
                    )

                assignments.append(ConditionalBlock(
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
                ))

                # After the conditional the Lean tuple-destructuring creates
                # fresh bindings with the base clean names. Reset var_map and
                # ssa_count accordingly so later references are correct.
                modified_set = set(modified_list)
                all_body_targets = list(stmt.body)
                if stmt.else_body is not None:
                    all_body_targets.extend(stmt.else_body)
                for target_name, _ in all_body_targets:
                    c = demangle_var(
                        target_name, yf.params, yf.rets,
                        keep_solidity_locals=keep_solidity_locals,
                    )
                    if c is not None and c in modified_set:
                        var_map[target_name] = c
                        ssa_count[c] = 1
                        const_locals.pop(c, None)
            continue

        if isinstance(stmt, MemoryWrite):
            addr_expr = substitute_expr(stmt.address, subst)
            addr_expr = rename_expr(addr_expr, var_map, fn_map)
            value_expr = substitute_expr(stmt.value, subst)
            value_expr = rename_expr(value_expr, var_map, fn_map)
            value_expr = _resolve_memory_expr(value_expr)
            addr = _resolve_memory_address(addr_expr, op_name="mstore")
            if addr in memory_state:
                raise ParseError(
                    f"Multiple mstore writes to address {addr} in {sol_fn_name!r}. "
                    f"The supported memory model forbids aliasing or overwrite "
                    f"of scratch slots."
                )
            memory_state[addr] = value_expr
            continue

        target, raw_expr = stmt
        a = _process_assignment(target, raw_expr)
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

    return model


def _prune_dead_assignments(
    model: "FunctionModel",
) -> "FunctionModel":
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
            raise TypeError(f"Unsupported ModelStatement: {type(stmt)}")

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
                    outputs=tuple(stmt.then_branch.outputs[idx] for idx in needed_indices),
                ),
                else_branch=ConditionalBranch(
                    assignments=else_assignments,
                    outputs=tuple(stmt.else_branch.outputs[idx] for idx in needed_indices),
                ),
            )
        )

    kept_rev.reverse()
    return FunctionModel(
        fn_name=model.fn_name,
        assignments=tuple(kept_rev),
        param_names=model.param_names,
        return_names=model.return_names,
    )


# ---------------------------------------------------------------------------
# Lean emission helpers
# ---------------------------------------------------------------------------

OP_TO_LEAN_HELPER = {
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

OP_TO_OPCODE = {
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
    raise TypeError(f"Unsupported ModelStatement: {type(stmt)}")


def ordered_unique(items: list[str]) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for item in items:
        if item in seen:
            continue
        seen.add(item)
        out.append(item)
    return out


def _expr_size(expr: Expr) -> int:
    if isinstance(expr, (IntLit, Var)):
        return 1
    if isinstance(expr, Call):
        return 1 + sum(_expr_size(arg) for arg in expr.args)
    raise TypeError(f"Unsupported Expr node: {type(expr)}")


def _replace_expr(expr: Expr, replacements: dict[Expr, str]) -> Expr:
    if expr in replacements:
        return Var(replacements[expr])
    if isinstance(expr, (IntLit, Var)):
        return expr
    if isinstance(expr, Call):
        return Call(expr.name, tuple(_replace_expr(arg, replacements) for arg in expr.args))
    raise TypeError(f"Unsupported Expr node: {type(expr)}")


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
    raise TypeError(f"Unsupported Expr node: {type(expr)}")


def validate_function_model(model: FunctionModel) -> None:
    """Reject malformed restricted-IR models before Lean emission."""

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
            raise TypeError(f"Unsupported ModelStatement: {type(stmt)}")

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


WORD_MOD = 2 ** 256


def u256(value: int) -> int:
    return value % WORD_MOD


def _expect_scalar(value: ModelValue, *, context: str) -> int:
    if isinstance(value, tuple):
        raise EvaluationError(f"{context} expected a scalar value, got tuple {value!r}")
    return value


def _expect_tuple(value: ModelValue, *, size: int, context: str) -> tuple[int, ...]:
    if not isinstance(value, tuple):
        raise EvaluationError(f"{context} expected a {size}-tuple, got scalar {value!r}")
    if len(value) != size:
        raise EvaluationError(
            f"{context} expected a {size}-tuple, got {len(value)} values: {value!r}"
        )
    return value


def _eval_builtin(name: str, args: tuple[int, ...]) -> int:
    if name == "add" and len(args) == 2:
        return u256(u256(args[0]) + u256(args[1]))
    if name == "sub" and len(args) == 2:
        return u256(u256(args[0]) + WORD_MOD - u256(args[1]))
    if name == "mul" and len(args) == 2:
        return u256(u256(args[0]) * u256(args[1]))
    if name == "div" and len(args) == 2:
        aa = u256(args[0])
        bb = u256(args[1])
        return 0 if bb == 0 else aa // bb
    if name == "mod" and len(args) == 2:
        aa = u256(args[0])
        bb = u256(args[1])
        return 0 if bb == 0 else aa % bb
    if name == "not" and len(args) == 1:
        return WORD_MOD - 1 - u256(args[0])
    if name == "or" and len(args) == 2:
        return u256(args[0]) | u256(args[1])
    if name == "and" and len(args) == 2:
        return u256(args[0]) & u256(args[1])
    if name == "eq" and len(args) == 2:
        return 1 if u256(args[0]) == u256(args[1]) else 0
    if name == "shl" and len(args) == 2:
        shift = u256(args[0])
        value = u256(args[1])
        return u256(value * (2 ** shift)) if shift < 256 else 0
    if name == "shr" and len(args) == 2:
        shift = u256(args[0])
        value = u256(args[1])
        return value // (2 ** shift) if shift < 256 else 0
    if name == "clz" and len(args) == 1:
        value = u256(args[0])
        return 256 if value == 0 else 255 - (value.bit_length() - 1)
    if name == "lt" and len(args) == 2:
        return 1 if u256(args[0]) < u256(args[1]) else 0
    if name == "gt" and len(args) == 2:
        return 1 if u256(args[0]) > u256(args[1]) else 0
    if name == "mulmod" and len(args) == 3:
        aa = u256(args[0])
        bb = u256(args[1])
        nn = u256(args[2])
        return 0 if nn == 0 else (aa * bb) % nn
    raise EvaluationError(f"Unsupported builtin call {name!r} with {len(args)} arg(s)")


def build_model_table(models: list[FunctionModel] | tuple[FunctionModel, ...]) -> dict[str, FunctionModel]:
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
        raise TypeError(f"Unsupported Expr node: {type(expr)}")

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
            raise TypeError(f"Unsupported ModelStatement: {type(stmt)}")

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
            f"Model {model.fn_name!r} did not produce return variable {err.args[0]!r}"
        ) from err


def _collect_repeated_model_calls(expr: Expr, model_call_names: frozenset[str]) -> list[Call]:
    counts: Counter[Expr] = Counter()
    _walk_model_calls(expr, model_call_names, counts)
    repeated = [node for node, count in counts.items() if count > 1]
    repeated.sort(key=_expr_size)
    return [node for node in repeated if isinstance(node, Call)]


def _walk_model_calls(node: Expr, model_call_names: frozenset[str],
                       counts: Counter[Expr]) -> None:
    """Recursively count model-call occurrences in *node*."""
    if isinstance(node, Call):
        if node.name in model_call_names:
            counts[node] += 1
        for arg in node.args:
            _walk_model_calls(arg, model_call_names, counts)


def _walk_statement(stmt: ModelStatement, model_call_names: frozenset[str],
                    counts: Counter[Expr]) -> None:
    """Count model-call occurrences across all expressions in *stmt*."""
    if isinstance(stmt, Assignment):
        _walk_model_calls(stmt.expr, model_call_names, counts)
    elif isinstance(stmt, ConditionalBlock):
        _walk_model_calls(stmt.condition, model_call_names, counts)
        for a in stmt.then_branch.assignments:
            _walk_model_calls(a.expr, model_call_names, counts)
        for a in stmt.else_branch.assignments:
            _walk_model_calls(a.expr, model_call_names, counts)


def _replace_statement(stmt: ModelStatement,
                       replacements: dict[Expr, str]) -> ModelStatement:
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
    raise TypeError(f"Unsupported ModelStatement: {type(stmt)}")


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
            raise ParseError(
                f"CSE: refusing to hoist non-model call {call!r}"
            )
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
            stmt.expr, model_call_names=model_call_names,
        )
        return [*hoisted, Assignment(target=stmt.target, expr=expr)]

    if isinstance(stmt, ConditionalBlock):
        prefix, condition = _hoist_repeated_calls_in_expr(
            stmt.condition, model_call_names=model_call_names,
        )

        then_assignments: list[Assignment] = []
        for assignment in stmt.then_branch.assignments:
            then_assignments.extend(_localize_statement_cse(
                assignment, model_call_names=model_call_names,
            ))

        localized_else: list[Assignment] = []
        for assignment in stmt.else_branch.assignments:
            localized_else.extend(_localize_statement_cse(
                assignment, model_call_names=model_call_names,
            ))

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

    raise TypeError(f"Unsupported ModelStatement: {type(stmt)}")


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
            raise ParseError(
                f"CSE: refusing to hoist non-model call {call!r}"
            )

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
        _replace_statement(stmt, global_replacements)
        for stmt in model.assignments
    ]

    # -- Pass 4: locally hoist remaining repeated calls in safe scopes -----
    new_assignments: list[ModelStatement] = list(hoisted_global)
    for stmt in rewritten_statements:
        new_assignments.extend(_localize_statement_cse(
            stmt, model_call_names=model_call_names,
        ))

    return FunctionModel(
        fn_name=model.fn_name,
        assignments=tuple(new_assignments),
        param_names=model.param_names,
        return_names=model.return_names,
    )


def prepare_translation(
    yul_text: str,
    config: ModelConfig,
    *,
    selected_functions: tuple[str, ...] | None = None,
) -> PreparedTranslation:
    """Parse Yul, select targets, and inline non-target helpers."""

    tokens = tokenize_yul(yul_text)
    selected = selected_functions if selected_functions is not None else config.function_order

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
            elide_zero_assignments=pipeline.elide_zero_assignments,
        )
        for fn in preparation.selected_functions
    ]
    for model in models:
        validate_function_model(model)
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
            hoist_repeated_model_calls(
                model,
                model_call_names=model_call_names,
            )
            if model.fn_name in config.hoist_repeated_calls
            else model
            for model in transformed
        ]
        for model in transformed:
            validate_function_model(model)

    if pipeline.prune_dead_assignments:
        transformed = [
            _prune_dead_assignments(model)
            if model.fn_name not in config.skip_prune
            else model
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
        args = " ".join(f"({emit_expr(a, op_helper_map=op_helper_map, call_helper_map=call_helper_map)})" for a in expr.args)
        return f"{helper} {args}".rstrip()
    raise TypeError(f"Unsupported Expr node: {type(expr)}")


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
            raise TypeError(f"Unsupported ModelStatement: {type(stmt)}")

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
            model.assignments, evm=True, config=config,
            param_names=model.param_names, return_names=model.return_names,
        )

        param_sig = " ".join(f"{p}" for p in model.param_names)
        if len(model.return_names) == 1:
            ret_type = "Nat"
        else:
            ret_type = " × ".join("Nat" for _ in model.return_names)
        parts.append(
            f"/-- Opcode-faithful auto-generated model of `{model.fn_name}` with uint256 EVM semantics. -/\n"
            f"def {evm_name} ({param_sig} : Nat) : {ret_type} :=\n"
            f"{evm_body}\n"
        )
        if model.fn_name not in config.skip_norm:
            norm_name = model_base
            norm_body = build_model_body(
                model.assignments, evm=False, config=config,
                param_names=model.param_names, return_names=model.return_names,
            )
            parts.append(
                f"/-- Normalized auto-generated model of `{model.fn_name}` on Nat arithmetic. -/\n"
                f"def {norm_name} ({param_sig} : Nat) : {ret_type} :=\n"
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
    args: argparse.Namespace,
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
    if any(fn != config.inner_fn for fn in selected) and config.inner_fn not in selected:
        selected.append(config.inner_fn)

    selected_set = set(selected)
    return tuple(fn for fn in config.function_order if fn in selected_set)


def run(config: ModelConfig) -> int:
    """Main entry point shared by both generators."""
    global _gensym_counters
    _gensym_counters = {}

    ap = argparse.ArgumentParser(description=config.cli_description)
    ap.add_argument(
        "--yul", required=True,
        help="Path to Yul IR file, or '-' for stdin (from `forge inspect ... ir`)",
    )
    ap.add_argument(
        "--source-label", default=config.default_source_label,
        help="Source label for the Lean header comment",
    )
    ap.add_argument(
        "--functions", default="",
        help=f"Comma-separated function names (default: {','.join(config.function_order)})",
    )
    ap.add_argument(
        "--function", action="append",
        help="Optional repeatable function selector",
    )
    ap.add_argument(
        "--namespace", default=config.default_namespace,
        help="Lean namespace for generated definitions",
    )
    ap.add_argument(
        "--output", default=config.default_output,
        help="Output Lean file path",
    )
    ap.add_argument(
        "--pipeline",
        default=OPTIMIZED_TRANSLATION_PIPELINE.name,
        choices=sorted(TRANSLATION_PIPELINES),
        help="Translation pipeline to run (default: optimized)",
    )
    args = ap.parse_args()

    validate_ident(args.namespace, what="Lean namespace")

    selected_functions = parse_function_selection(args, config)
    pipeline = get_translation_pipeline(args.pipeline)

    if args.yul == "-":
        yul_text = sys.stdin.read()
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
