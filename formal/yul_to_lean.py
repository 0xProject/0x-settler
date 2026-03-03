"""
Shared infrastructure for generating Lean models from Yul IR.

Provides:
- Yul tokenizer and recursive-descent parser
- AST types (IntLit, Var, Call, Assignment, FunctionModel)
- Yul → FunctionModel conversion (copy propagation + demangling)
- Lean expression emission
- Common Lean source scaffolding
"""

from __future__ import annotations

import argparse
import datetime as dt
import pathlib
import re
import sys
import warnings
from collections import Counter
from dataclasses import dataclass
from typing import Callable


class ParseError(RuntimeError):
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
class ConditionalBlock:
    """An ``if cond { ... }`` or ``if/else`` block assigning to declared vars.

    ``condition`` is the Yul condition expression.
    ``assignments`` are the assignments inside the if-body.
    ``modified_vars`` lists the Solidity-level variable names that the block
    may modify (used for Lean tuple-destructuring emission).
    ``else_vars`` are the variable names for pass-through values when
    there is no else-body (the pre-if values).
    ``else_assignments`` are assignments for the else-body when present
    (from ``switch`` or if/else constructs).
    """
    condition: Expr
    assignments: tuple[Assignment, ...]
    modified_vars: tuple[str, ...]
    else_vars: tuple[str, ...] | None = None
    else_assignments: tuple[Assignment, ...] | None = None


# A model statement is either a plain assignment or a conditional block.
ModelStatement = Assignment | ConditionalBlock


@dataclass(frozen=True)
class FunctionModel:
    fn_name: str
    assignments: tuple[ModelStatement, ...]
    param_names: tuple[str, ...] = ("x",)
    return_names: tuple[str, ...] = ("z",)


# ---------------------------------------------------------------------------
# Yul tokenizer
# ---------------------------------------------------------------------------

YUL_TOKEN_RE = re.compile(
    r"""
    (?P<linecomment>///[^\n]*)
  | (?P<blockcomment>//[^\n]*)
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
    "linecomment": None,
    "blockcomment": None,
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
        assert raw_kind is not None
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


# A raw parsed statement is either an assignment or an if-block.
RawStatement = tuple[str, Expr] | ParsedIfBlock


@dataclass
class YulFunction:
    """Parsed representation of a single Yul ``function`` definition."""
    yul_name: str
    params: list[str]
    rets: list[str]
    assignments: list[RawStatement]
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


class YulParser:
    """Recursive-descent parser over a pre-tokenized Yul token stream.

    Only the subset of Yul needed for our extraction is handled: function
    definitions, ``let``/bare assignments, blocks, and ``leave``.

    Control flow (``if``, ``switch``, ``for``) is **rejected** — its
    presence would make the straight-line Lean model incomplete and
    silently wrong.  Bare expression-statements are tracked and warned
    about since they may indicate side-effectful operations the model
    does not capture.
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
          synthetic ``__component_N(call)`` wrapper to distinguish them
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
                results.append((t, Call(f"__component_{idx}", (expr,))))
        elif self._peek_kind() == ":=":
            self._pop()
            expr = self._parse_expr()
            results.append((target, expr))
        else:
            # Bare declaration: ``let x``  (zero-initialized, skip)
            pass

    def _parse_body_assignments(self) -> list[RawStatement]:
        results: list[RawStatement] = []

        while not self._at_end() and self._peek_kind() != "}":
            kind = self._peek_kind()

            if kind == "{":
                self._pop()
                results.extend(self._parse_body_assignments())
                self._expect("}")
                continue

            if kind == "ident" and self.tokens[self.i][1] == "let":
                self._parse_let(results)
                continue

            if kind == "ident" and self.tokens[self.i][1] == "leave":
                self._pop()
                continue

            if kind == "ident" and self.tokens[self.i][1] == "function":
                self._skip_function_def()
                continue

            if kind == "ident" and self.tokens[self.i][1] == "if":
                self._pop()  # consume 'if'
                condition = self._parse_expr()
                self._expect("{")
                body, has_leave = self._parse_if_body_assignments()
                self._expect("}")
                results.append(ParsedIfBlock(
                    condition=condition,
                    body=tuple(body),
                    has_leave=has_leave,
                ))
                continue

            if kind == "ident" and self.tokens[self.i][1] == "switch":
                self._pop()  # consume 'switch'
                condition = self._parse_expr()
                # We support exactly one form of switch:
                #   switch e case 0 { else_body } default { if_body }
                # (branches may appear in either order).  Anything else
                # is rejected loudly.
                case0_body: list[tuple[str, Expr]] | None = None
                case0_leave = False
                default_body: list[tuple[str, Expr]] | None = None
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
                        case0_body, case0_leave = self._parse_if_body_assignments()
                        self._expect("}")
                    else:  # default
                        if default_body is not None:
                            raise ParseError(
                                "Duplicate 'default' in switch statement."
                            )
                        self._expect("{")
                        default_body, default_leave = self._parse_if_body_assignments()
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

            if kind == "ident" and self.tokens[self.i][1] == "for":
                raise ParseError(
                    f"Control flow statement 'for' found in function body. "
                    f"Only straight-line code and if/switch blocks are "
                    f"supported for Lean model generation."
                )

            if kind == "ident" and self.i + 1 < len(self.tokens) and self.tokens[self.i + 1][0] == ":=":
                target = self._expect_ident()
                self._expect(":=")
                expr = self._parse_expr()
                results.append((target, expr))
                continue

            if kind == "ident" or kind == "num":
                expr = self._parse_expr()
                self._expr_stmts.append(expr)
                continue

            tok = self._pop()
            warnings.warn(
                f"Unrecognized token {tok!r} in function body was skipped. "
                f"This may indicate a Yul IR construct the parser does not "
                f"handle.",
                stacklevel=2,
            )

        return results

    def _parse_if_body_assignments(
        self,
    ) -> tuple[list[tuple[str, Expr]], bool]:
        """Parse the body of an ``if`` block.

        Only bare assignments (``target := expr``) are expected inside
        if-bodies in the Yul IR patterns we handle.  ``let`` declarations
        are also accepted (they are locals scoped to the if-body that the
        compiler may introduce).

        Returns ``(assignments, has_leave)`` where *has_leave* indicates
        that a ``leave`` statement (early return) was encountered.
        """
        results: list[tuple[str, Expr]] = []
        has_leave = False
        while not self._at_end() and self._peek_kind() != "}":
            kind = self._peek_kind()

            if kind == "{":
                self._pop()
                inner_results, inner_leave = self._parse_if_body_assignments()
                results.extend(inner_results)
                has_leave = has_leave or inner_leave
                self._expect("}")
                continue

            if kind == "ident" and self.tokens[self.i][1] == "let":
                self._parse_let(results)
                continue

            if kind == "ident" and self.i + 1 < len(self.tokens) and self.tokens[self.i + 1][0] == ":=":
                target = self._expect_ident()
                self._expect(":=")
                expr = self._parse_expr()
                results.append((target, expr))
                continue

            if kind == "ident" and self.tokens[self.i][1] == "leave":
                self._pop()
                has_leave = True
                continue

            if kind == "ident" or kind == "num":
                expr = self._parse_expr()
                self._expr_stmts.append(expr)
                continue

            tok = self._pop()
            warnings.warn(
                f"Unrecognized token {tok!r} in if-body was skipped.",
                stacklevel=2,
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
        fn_kw = self._expect_ident()
        assert fn_kw == "function", f"Expected 'function', got {fn_kw!r}"
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
        if self._expr_stmts:
            descriptions = []
            for e in self._expr_stmts[:3]:
                if isinstance(e, Call):
                    descriptions.append(f"{e.name}(...)")
                else:
                    descriptions.append(repr(e))
            summary = ", ".join(descriptions)
            if len(self._expr_stmts) > 3:
                summary += ", ..."
            warnings.warn(
                f"Function {yul_name!r} contains "
                f"{len(self._expr_stmts)} expression-statement(s) "
                f"not captured in the model: [{summary}]. "
                f"If any have side effects (sstore, log, revert, ...) "
                f"the model may be incomplete.",
                stacklevel=2,
            )
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

    def collect_all_functions(self) -> dict[str, YulFunction]:
        """Parse all function definitions in the token stream.

        Functions whose bodies contain unsupported constructs (``switch``,
        ``for``, etc.) are silently skipped — they cannot be inlined but
        that is fine for model generation.

        Warnings about expression-statements (``revert``, ``mstore``, etc.)
        are suppressed because these auxiliary functions are parsed only for
        inlining, not for direct modelling.
        """
        functions: dict[str, YulFunction] = {}
        while not self._at_end():
            if (
                self._peek_kind() == "ident"
                and self.tokens[self.i][1] == "function"
            ):
                saved_i = self.i
                saved_stmts = self._expr_stmts
                try:
                    with warnings.catch_warnings():
                        warnings.simplefilter("ignore")
                        fn = self.parse_function()
                    functions[fn.yul_name] = fn
                except ParseError:
                    # Unsupported body — skip this function.
                    self.i = saved_i
                    self._pop()  # consume 'function'
                    self._expect_ident()  # consume name
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
                finally:
                    self._expr_stmts = saved_stmts
            else:
                self._pop()
        return functions


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

_inline_counter = 0


def _gensym(prefix: str) -> str:
    """Generate a unique variable name for inlined function locals."""
    global _inline_counter
    _inline_counter += 1
    return f"_inline_{prefix}_{_inline_counter}"


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
    mstore_sink: list[tuple[str, Expr]] | None = None,
) -> Expr | tuple[Expr, ...]:
    """Inline one function call, returning its return-value expression(s).

    Builds a substitution from parameters → argument expressions, then
    processes the function body sequentially (same semantics as copy-prop).
    Each local variable gets a unique gensym name to avoid clashes with
    the caller's scope.

    When *mstore_sink* is not None, ``mstore(addr, val)`` expression-
    statements from inlined functions are collected as synthetic
    assignments ``(gensym_name, Call("__mstore", [addr, val]))``.  The
    caller is responsible for injecting these into the outer function's
    assignment list so that ``yul_function_to_model`` can resolve
    ``mload`` calls lazily during copy propagation.
    """
    if fn.expr_stmts:
        # Filter out mstore calls when we have a sink to capture them.
        unhandled = [
            e for e in fn.expr_stmts
            if not (mstore_sink is not None
                    and isinstance(e, Call)
                    and e.name == "mstore"
                    and len(e.args) == 2)
        ]
        if unhandled:
            descriptions = []
            for e in unhandled[:3]:
                if isinstance(e, Call):
                    descriptions.append(f"{e.name}(...)")
                else:
                    descriptions.append(repr(e))
            summary = ", ".join(descriptions)
            if len(unhandled) > 3:
                summary += ", ..."
            warnings.warn(
                f"Inlining function {fn.yul_name!r} which contains "
                f"{len(unhandled)} unhandled expression-statement(s): "
                f"[{summary}]. If any have side effects (sstore, log, "
                f"revert, ...) the inlined model may be incomplete.",
                stacklevel=3,
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

    for stmt in fn.assignments:
        if isinstance(stmt, ParsedIfBlock):
            # Evaluate condition
            cond = substitute_expr(stmt.condition, subst)
            cond = inline_calls(cond, fn_table, depth + 1, max_depth,
                                mstore_sink=mstore_sink)
            # Process if-body assignments into a separate subst branch.
            if_subst = dict(subst)
            # Track mstore count to detect conditional memory writes.
            pre_if_sink_len = len(mstore_sink) if mstore_sink is not None else 0
            for target, raw_expr in stmt.body:
                expr = substitute_expr(raw_expr, if_subst)
                expr = inline_calls(expr, fn_table, depth + 1, max_depth,
                                    mstore_sink=mstore_sink)
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
                                        mstore_sink=mstore_sink)
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
                    if if_val is not else_val:
                        subst[target] = Call("__ite", (cond, if_val, else_val))
                    elif if_val is not pre_val:
                        subst[target] = if_val
            else:
                # Normal if-block (no leave, no else): take the if-branch value.
                for target, _raw_expr in stmt.body:
                    if_val = if_subst[target]
                    orig_val = subst.get(target, IntLit(0))
                    if if_val is not orig_val:
                        subst[target] = if_val
        else:
            target, raw_expr = stmt
            expr = substitute_expr(raw_expr, subst)
            expr = inline_calls(expr, fn_table, depth + 1, max_depth,
                                mstore_sink=mstore_sink)
            # Gensym: rename non-param, non-return locals to avoid clashes
            if target not in fn.params and target not in fn.rets:
                new_name = _gensym(target)
                subst[target] = Var(new_name)
                # Re-substitute the expression under the new name
                # (it was already substituted, so just store it)
                subst[new_name] = expr
            else:
                subst[target] = expr

    # Resolve any gensym'd variables remaining in return expressions.
    # Iterate because gensym'd vars may reference other gensym'd vars.
    def _resolve(e: Expr, s: dict[str, Expr]) -> Expr:
        for _ in range(20):
            prev = e
            e = substitute_expr(e, s)
            if e is prev:
                break
        return e

    # Emit mstore effects AFTER the full subst chain is built.
    # 1. Collect effects from this function's own expr_stmts.
    # 2. Resolve all sink entries through subst to eliminate gensyms.
    if mstore_sink is not None:
        # Step 1: emit this function's own mstore effects.
        for e in (fn.expr_stmts or []):
            if isinstance(e, Call) and e.name == "mstore" and len(e.args) == 2:
                addr_expr = _resolve(substitute_expr(e.args[0], subst), subst)
                val_expr = _resolve(substitute_expr(e.args[1], subst), subst)
                syn_name = _gensym("__mstore")
                mstore_sink.append(
                    (syn_name, Call("__mstore", (addr_expr, val_expr)))
                )

        # Step 2: resolve all sink entries through this level's subst.
        for i in range(len(mstore_sink)):
            name, val = mstore_sink[i]
            if isinstance(val, Call) and val.name == "__mstore":
                new_args = tuple(_resolve(a, subst) for a in val.args)
                if any(na is not oa for na, oa in zip(new_args, val.args)):
                    mstore_sink[i] = (name, Call("__mstore", new_args))

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
    mstore_sink: list[tuple[str, Expr]] | None = None,
) -> Expr:
    """Recursively inline function calls in an expression.

    Walks the expression tree. When a ``Call`` targets a function in
    *fn_table*, its body is inlined via sequential substitution.
    ``__component_N`` wrappers (from multi-value ``let``) are resolved
    to the Nth return value of the inlined function.

    When *mstore_sink* is not None, ``mstore`` side effects from inlined
    functions are collected (see ``_inline_single_call``).
    """
    if depth > max_depth:
        return expr
    if isinstance(expr, (IntLit, Var)):
        return expr
    if isinstance(expr, Call):
        # Handle __component_N(Call(fn, ...)) for multi-return.
        # Must check BEFORE recursively inlining arguments, because
        # we need to inline the inner call as multi-return to extract
        # the Nth component.
        m = re.fullmatch(r"__component_(\d+)", expr.name)
        if m and len(expr.args) == 1 and isinstance(expr.args[0], Call):
            idx = int(m.group(1))
            inner = expr.args[0]
            # Recursively inline the inner call's arguments first
            inner_args = tuple(inline_calls(a, fn_table, depth,
                                            mstore_sink=mstore_sink)
                               for a in inner.args)
            if inner.name in fn_table:
                result = _inline_single_call(
                    fn_table[inner.name], inner_args, fn_table, depth + 1,
                    max_depth, mstore_sink=mstore_sink,
                )
                if isinstance(result, tuple):
                    return result[idx] if idx < len(result) else expr
                return result  # single-return; component_0 = the value
            # Inner call not in table — rebuild with inlined args
            return Call(expr.name, (Call(inner.name, inner_args),))

        # Recurse into arguments
        args = tuple(inline_calls(a, fn_table, depth,
                                  mstore_sink=mstore_sink) for a in expr.args)

        # Direct call to a collected function
        if expr.name in fn_table:
            fn = fn_table[expr.name]
            result = _inline_single_call(fn, args, fn_table, depth + 1,
                                         max_depth, mstore_sink=mstore_sink)
            if isinstance(result, tuple):
                return result[0]  # single-call context; take first return
            return result

        return Call(expr.name, args)
    raise TypeError(f"Unsupported Expr node: {type(expr)}")


def _inline_yul_function(
    yf: YulFunction,
    fn_table: dict[str, YulFunction],
) -> YulFunction:
    """Apply ``inline_calls`` to every expression in a YulFunction.

    When inlined functions contain ``mstore`` expression-statements, they
    are collected and injected as synthetic ``__mstore`` assignments into
    the outer function's assignment list.  This enables lazy ``mload``
    resolution during ``yul_function_to_model``'s copy propagation.
    """
    # Shared sink for mstore effects from all inlined functions.
    # Effects are injected into the assignment list at the point they
    # are collected (not prepended) so that variables they reference
    # are already defined during copy propagation.
    mstore_sink: list[tuple[str, Expr]] = []

    new_assignments: list[RawStatement] = []
    for stmt in yf.assignments:
        if isinstance(stmt, ParsedIfBlock):
            pre_len = len(mstore_sink)
            new_cond = inline_calls(stmt.condition, fn_table,
                                    mstore_sink=mstore_sink)
            new_body: list[tuple[str, Expr]] = []
            for target, raw_expr in stmt.body:
                new_body.append((target, inline_calls(raw_expr, fn_table,
                                                      mstore_sink=mstore_sink)))
            # Inject any mstore effects collected during this statement.
            new_assignments.extend(mstore_sink[pre_len:])
            new_assignments.append(ParsedIfBlock(
                condition=new_cond,
                body=tuple(new_body),
                has_leave=stmt.has_leave,
            ))
        else:
            target, raw_expr = stmt
            pre_len = len(mstore_sink)
            inlined = inline_calls(raw_expr, fn_table,
                                   mstore_sink=mstore_sink)
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
) -> FunctionModel:
    """Convert a parsed YulFunction into a FunctionModel.

    Performs copy propagation to eliminate compiler temporaries and renames
    variables/calls back to Solidity-level names.

    Validates:
    - Multi-assigned compiler temporaries are flagged (copy propagation is
      still correct for sequential code, but the situation is unusual).
    - The return variable is recognized and assigned in the model.
    """
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
        else:
            target, _ = stmt
            assign_counts[target] += 1

    var_map: dict[str, str] = {}
    subst: dict[str, Expr] = {}

    for name in [*yf.params, *yf.rets]:
        clean = demangle_var(name, yf.params, yf.rets, keep_solidity_locals=keep_solidity_locals)
        if clean:
            var_map[name] = clean

    # Save param names before SSA processing may rename them.
    param_names = tuple(var_map[p] for p in yf.params)

    # ------------------------------------------------------------------
    # SSA state: track assignment count per clean name so that
    # reassigned variables get distinct Lean names (_1, _2, ...).
    # Parameters start at count 1 (the function-parameter binding).
    # ------------------------------------------------------------------
    ssa_count: dict[str, int] = {}
    for name in yf.params:
        clean = var_map.get(name)
        if clean:
            ssa_count[clean] = 1

    assignments: list[ModelStatement] = []
    warned_multi: set[str] = set()

    def _freeze_refs(expr: Expr) -> Expr:
        """Replace Var refs to Solidity-level vars with current Lean names,
        and rename function calls through ``fn_map``.

        Called when a compiler temporary is copy-propagated.  By
        resolving Solidity-level ``Var`` nodes to their *current* Lean
        name at copy-propagation time we "freeze" the reference,
        preventing a later SSA rename of the same variable from
        changing what the expression points to.

        Also renames function calls (e.g. ``fun__sqrt_4544`` → ``model_sqrt512``)
        so they are correct if the expression is later substituted into a
        real variable's assignment without going through ``rename_expr``.
        """
        if isinstance(expr, IntLit):
            return expr
        if isinstance(expr, Var):
            lean_name = var_map.get(expr.name)
            if lean_name is not None:
                return Var(lean_name)
            return expr
        if isinstance(expr, Call):
            new_args = tuple(_freeze_refs(a) for a in expr.args)
            new_name = fn_map.get(expr.name, expr.name)
            return Call(new_name, new_args)
        return expr

    def _process_assignment(
        target: str, raw_expr: Expr, *, inside_conditional: bool = False,
    ) -> Assignment | None:
        """Process a single raw assignment through copy-prop and demangling.

        Returns an Assignment if the target is a real variable, or None if
        it was copy-propagated into ``subst``.
        """
        expr = substitute_expr(raw_expr, subst)

        clean = demangle_var(target, yf.params, yf.rets, keep_solidity_locals=keep_solidity_locals)
        if clean is None:
            if assign_counts[target] > 1 and target not in warned_multi:
                warned_multi.add(target)
                warnings.warn(
                    f"Variable {target!r} in {sol_fn_name!r} is classified "
                    f"as a compiler temporary (copy-propagated) but is "
                    f"assigned {assign_counts[target]} times. Sequential "
                    f"propagation preserves semantics for straight-line "
                    f"code, but this is unusual — verify the Yul IR to "
                    f"confirm this is not a misclassified user variable.",
                    stacklevel=2,
                )
            if isinstance(expr, Call) and expr.name.startswith("zero_value_for_split_"):
                subst[target] = IntLit(0)
            else:
                subst[target] = _freeze_refs(expr)
            return None

        # Rename the RHS expression BEFORE updating var_map so that
        # self-references (e.g. ``x := f(x)``) resolve to the
        # *previous* binding, not the one being created.
        skip_zero = isinstance(expr, IntLit) and expr.value == 0
        if not skip_zero:
            expr = rename_expr(expr, var_map, fn_map)

        # SSA: compute the Lean target name.  Inside conditional
        # blocks, Lean's scoped ``let`` handles shadowing, so we
        # use the base clean name directly.
        if not inside_conditional:
            ssa_count[clean] = ssa_count.get(clean, 0) + 1
            if ssa_count[clean] == 1:
                ssa_name = clean
            else:
                ssa_name = f"{clean}_{ssa_count[clean] - 1}"
        else:
            ssa_name = clean

        # Update var_map AFTER rename_expr.
        var_map[target] = ssa_name

        if skip_zero:
            return None

        return Assignment(target=ssa_name, expr=expr)

    for stmt in yf.assignments:
        if isinstance(stmt, ParsedIfBlock):
            # Process the if-block: apply copy-prop/demangling to
            # condition and body, then emit a ConditionalBlock.
            cond = substitute_expr(stmt.condition, subst)
            cond = rename_expr(cond, var_map, fn_map)

            # Save pre-if Lean names so the else-tuple can reference
            # the values that were live *before* the if-body ran.
            pre_if_names: dict[str, str] = {}
            # Snapshot of all Lean names in scope before the if-body.
            pre_if_scope: set[str] = set(var_map.values())

            body_assignments: list[Assignment] = []
            for target, raw_expr in stmt.body:
                clean = demangle_var(
                    target, yf.params, yf.rets,
                    keep_solidity_locals=keep_solidity_locals,
                )
                if clean is not None and clean not in pre_if_names:
                    pre_if_names[clean] = var_map.get(target, clean)
                a = _process_assignment(
                    target, raw_expr, inside_conditional=True,
                )
                if a is not None:
                    body_assignments.append(a)
            if body_assignments:
                # Deduplicate while preserving order, excluding
                # block-scoped variables (declared with `let` inside
                # the if-body, never existed in the outer scope).
                # A variable is block-scoped if its pre-if Lean name
                # is not in the set of names that were live before
                # the if-block.
                seen_vars: set[str] = set()
                modified_list: list[str] = []
                for a in body_assignments:
                    if a.target not in seen_vars:
                        seen_vars.add(a.target)
                        # Only include variables that existed before
                        # the if-block.  Block-local `let` declarations
                        # (like Yul's `let usr$rem := ...`) are scoped
                        # to the if-body and must not escape.
                        pre_name = pre_if_names.get(a.target)
                        if pre_name is not None and pre_name in pre_if_scope:
                            modified_list.append(a.target)
                modified = tuple(modified_list)

                # Build else_vars from pre-if state (may differ from
                # modified_vars when SSA is active).
                else_vars_t = tuple(
                    pre_if_names[v] for v in modified_list
                )
                else_vars = (
                    else_vars_t if else_vars_t != modified else None
                )

                # Process else_body if present (from switch).
                else_assgn: tuple[Assignment, ...] | None = None
                if stmt.else_body is not None:
                    else_assignments_list: list[Assignment] = []
                    for target, raw_expr in stmt.else_body:
                        a = _process_assignment(
                            target, raw_expr, inside_conditional=True,
                        )
                        if a is not None:
                            else_assignments_list.append(a)
                    if else_assignments_list:
                        else_assgn = tuple(else_assignments_list)
                        # Ensure modified_vars covers vars from both
                        # branches.
                        for a in else_assignments_list:
                            if a.target not in seen_vars:
                                seen_vars.add(a.target)
                                modified_list.append(a.target)
                        modified = tuple(modified_list)
                        # When else_assignments are present, else_vars
                        # are not used (the else branch has its own
                        # computed values).
                        else_vars = None

                assignments.append(ConditionalBlock(
                    condition=cond,
                    assignments=tuple(body_assignments),
                    modified_vars=modified,
                    else_vars=else_vars,
                    else_assignments=else_assgn,
                ))

                # After the if-block the Lean tuple-destructuring
                # creates fresh bindings with the base clean names.
                # Reset var_map and ssa_count accordingly so that
                # subsequent references and assignments are correct.
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

    # ------------------------------------------------------------------
    # Lazy memory folding: resolve mload(addr) against __mstore(addr, val)
    # synthetic assignments that were injected during inlining.
    # ------------------------------------------------------------------
    # Build a lookup of Lean variable names → constant IntLit values
    # from the model's assignments.  This lets us resolve addresses
    # like Var('x_1') that refer to Solidity locals (which live in
    # `assignments`, not `subst`).
    _const_locals: dict[str, int] = {}
    for a in assignments:
        if isinstance(a, Assignment) and isinstance(a.expr, IntLit):
            _const_locals[a.target] = a.expr.value

    def _resolve_addr(expr: Expr) -> Expr:
        """Resolve Var references through _const_locals before const-eval."""
        if isinstance(expr, Var) and expr.name in _const_locals:
            return IntLit(_const_locals[expr.name])
        if isinstance(expr, Call):
            new_args = tuple(_resolve_addr(a) for a in expr.args)
            return Call(expr.name, new_args)
        return expr

    # Collect __mstore entries from the copy-propagation subst dict.
    # These have the form: subst[_inline___mstore_N] = Call("__mstore", [addr, val])
    # After copy propagation, addr and val are fully resolved.
    # Collect __mstore entries, resolving addresses to integer constants.
    mem_map: dict[int, Expr] = {}
    for key, val in subst.items():
        if (
            isinstance(val, Call)
            and val.name == "__mstore"
            and len(val.args) == 2
        ):
            addr = _try_const_eval(_resolve_addr(val.args[0]))
            if addr is None:
                raise ParseError(
                    f"__mstore synthetic assignment {key!r} has non-constant "
                    f"address {val.args[0]!r} after copy propagation. "
                    f"All mstore addresses must evaluate to constants "
                    f"(use tmp() in wrappers)."
                )
            mem_map[addr] = val.args[1]

    if mem_map:
        # Resolve mload calls within mem_map values against the same
        # mem_map.  This handles cases where e.g. the value at addr 0
        # contains mload(0x1080) which maps to x_hi from mem_map[4224].
        # Iterate until stable (acyclic references converge in one pass).
        def _fold_mem_val(expr: Expr) -> Expr:
            if isinstance(expr, (IntLit, Var)):
                return expr
            if isinstance(expr, Call):
                if expr.name == "mload" and len(expr.args) == 1:
                    addr = _try_const_eval(_resolve_addr(expr.args[0]))
                    if addr is not None and addr in mem_map:
                        return mem_map[addr]
                new_args = tuple(_fold_mem_val(a) for a in expr.args)
                return Call(expr.name, new_args)
            return expr

        changed = True
        for _pass in range(5):
            if not changed:
                break
            changed = False
            for addr in list(mem_map.keys()):
                new_val = _fold_mem_val(mem_map[addr])
                if new_val is not mem_map[addr]:
                    mem_map[addr] = new_val
                    changed = True

        model = _resolve_mloads(model, mem_map, _const_locals, sol_fn_name)

    return model


def _resolve_mloads(
    model: "FunctionModel",
    mem_map: dict[int, Expr],
    const_locals: dict[str, int],
    fn_name: str,
) -> "FunctionModel":
    """Replace ``mload(const_addr)`` calls in a FunctionModel with values
    from the memory map.

    Raises ``ParseError`` if any ``mload`` has a non-constant address or
    an address not found in the memory map.
    """
    def _resolve_addr(expr: Expr) -> Expr:
        """Resolve Var references through const_locals before const-eval."""
        if isinstance(expr, Var) and expr.name in const_locals:
            return IntLit(const_locals[expr.name])
        if isinstance(expr, Call):
            new_args = tuple(_resolve_addr(a) for a in expr.args)
            return Call(expr.name, new_args)
        return expr

    def _fold(expr: Expr) -> Expr:
        if isinstance(expr, (IntLit, Var)):
            return expr
        if isinstance(expr, Call):
            if expr.name == "mload" and len(expr.args) == 1:
                addr = _try_const_eval(_resolve_addr(expr.args[0]))
                if addr is None:
                    raise ParseError(
                        f"mload with non-constant address {expr.args[0]!r} "
                        f"in {fn_name!r} after copy propagation. "
                        f"All mload addresses must evaluate to constants."
                    )
                if addr not in mem_map:
                    raise ParseError(
                        f"mload at address {addr} in {fn_name!r} has no "
                        f"matching mstore. Available addresses: "
                        f"{sorted(mem_map.keys())}"
                    )
                return mem_map[addr]
            new_args = tuple(_fold(a) for a in expr.args)
            return Call(expr.name, new_args)
        return expr

    def _fold_stmt(stmt: ModelStatement) -> ModelStatement:
        if isinstance(stmt, Assignment):
            return Assignment(target=stmt.target, expr=_fold(stmt.expr))
        if isinstance(stmt, ConditionalBlock):
            ea = None
            if stmt.else_assignments is not None:
                ea = tuple(
                    Assignment(target=a.target, expr=_fold(a.expr))
                    for a in stmt.else_assignments
                )
            return ConditionalBlock(
                condition=_fold(stmt.condition),
                assignments=tuple(
                    Assignment(target=a.target, expr=_fold(a.expr))
                    for a in stmt.assignments
                ),
                modified_vars=stmt.modified_vars,
                else_vars=stmt.else_vars,
                else_assignments=ea,
            )
        raise TypeError(f"Unsupported ModelStatement: {type(stmt)}")

    return FunctionModel(
        fn_name=model.fn_name,
        assignments=tuple(_fold_stmt(s) for s in model.assignments),
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
        for a in stmt.assignments:
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
        # Handle __component_N(call) for multi-return function calls.
        # Emits Lean tuple projection: (f args).1 for component 0, etc.
        m = re.fullmatch(r"__component_(\d+)", expr.name)
        if m and len(expr.args) == 1:
            idx = int(m.group(1))
            inner = emit_expr(expr.args[0], op_helper_map=op_helper_map, call_helper_map=call_helper_map)
            return f"({inner}).{idx + 1}"

        # Handle __ite(cond, if_val, else_val) from leave-handling.
        # Emits: if (cond) ≠ 0 then if_val else else_val
        if expr.name == "__ite" and len(expr.args) == 3:
            cond = emit_expr(expr.args[0], op_helper_map=op_helper_map, call_helper_map=call_helper_map)
            if_val = emit_expr(expr.args[1], op_helper_map=op_helper_map, call_helper_map=call_helper_map)
            else_val = emit_expr(expr.args[2], op_helper_map=op_helper_map, call_helper_map=call_helper_map)
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

    # -- CLI defaults --
    default_source_label: str = ""
    default_namespace: str = ""
    default_output: str = ""
    cli_description: str = ""


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
        return emit_expr(rhs_expr, op_helper_map=op_map, call_helper_map=call_map)

    for stmt in assignments:
        if isinstance(stmt, ConditionalBlock):
            # Emit Lean tuple-destructuring if-then-else:
            #   let (v1, v2) := if cond ≠ 0 then
            #       let v1 := ...
            #       ...
            #       (v1, v2)
            #     else (v1, v2)
            cond_str = _emit_rhs(stmt.condition)
            mvars = stmt.modified_vars
            evars = stmt.else_vars if stmt.else_vars is not None else mvars
            if len(mvars) == 1:
                lhs = mvars[0]
                tup = mvars[0]
            else:
                lhs = f"({', '.join(mvars)})"
                tup = f"({', '.join(mvars)})"
            if len(evars) == 1:
                else_tup = evars[0]
            else:
                else_tup = f"({', '.join(evars)})"
            lines.append(f"  let {lhs} := if ({cond_str}) ≠ 0 then")
            for a in stmt.assignments:
                rhs = _emit_rhs(a.expr)
                lines.append(f"      let {a.target} := {rhs}")
            lines.append(f"      {tup}")
            if stmt.else_assignments is not None:
                lines.append(f"    else")
                for a in stmt.else_assignments:
                    rhs = _emit_rhs(a.expr)
                    lines.append(f"      let {a.target} := {rhs}")
                # Build the else tuple from the else-body's modified vars.
                # Variables in modified_vars but not assigned in else_body
                # keep their pre-if name.
                else_assigned = {a.target for a in stmt.else_assignments}
                else_tuple_parts = []
                for v in mvars:
                    if v in else_assigned:
                        else_tuple_parts.append(v)
                    elif evars is not None:
                        idx = list(mvars).index(v)
                        else_tuple_parts.append(evars[idx] if idx < len(evars) else v)
                    else:
                        else_tuple_parts.append(v)
                if len(else_tuple_parts) == 1:
                    lines.append(f"      {else_tuple_parts[0]}")
                else:
                    lines.append(f"      ({', '.join(else_tuple_parts)})")
            else:
                lines.append(f"    else {else_tup}")
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


def build_lean_source(
    *,
    models: list[FunctionModel],
    source_path: str,
    namespace: str,
    config: ModelConfig,
) -> str:
    generated_at = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    modeled_functions = ", ".join(model.fn_name for model in models)

    raw_ops: list[str] = []
    for model in models:
        for stmt in model.assignments:
            raw_ops.extend(collect_ops_from_statement(stmt))
    opcodes = ordered_unique([OP_TO_OPCODE[name] for name in raw_ops])
    opcodes_line = ", ".join(opcodes)

    function_defs = render_function_defs(models, config)

    src = (
        "import Init\n\n"
        f"namespace {namespace}\n\n"
        f"/-- {config.header_comment} -/\n"
        f"-- Source: {source_path}\n"
        f"-- Modeled functions: {modeled_functions}\n"
        f"-- Generated by: {config.generator_label}\n"
        f"-- Generated at (UTC): {generated_at}\n"
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
    args = ap.parse_args()

    validate_ident(args.namespace, what="Lean namespace")

    selected_functions = parse_function_selection(args, config)

    if args.yul == "-":
        yul_text = sys.stdin.read()
    else:
        yul_text = pathlib.Path(args.yul).read_text()

    tokens = tokenize_yul(yul_text)

    # Collect all parseable function definitions for inlining.
    fn_table = YulParser(tokens).collect_all_functions()

    fn_map: dict[str, str] = {}
    yul_functions: dict[str, YulFunction] = {}

    # First pass: find target functions and record their Yul names.
    known_yul_names: set[str] = set()
    for sol_name in selected_functions:
        p = YulParser(tokens)
        np = config.n_params.get(sol_name) if config.n_params else None
        yf = p.find_function(sol_name, n_params=np,
                             known_yul_names=known_yul_names or None,
                             exclude_known=sol_name in config.exclude_known)
        fn_map[yf.yul_name] = sol_name
        yul_functions[sol_name] = yf
        known_yul_names.add(yf.yul_name)

    # Remove target functions from the inlining table so they remain
    # as named calls in the model (e.g. sqrt calling _sqrt → model_sqrt).
    for yul_name in fn_map:
        fn_table.pop(yul_name, None)

    if fn_table:
        print(f"Collected {len(fn_table)} function definition(s) for inlining")

    # Second pass: inline non-target function calls.
    for sol_name in selected_functions:
        yf = yul_functions[sol_name]
        yf = _inline_yul_function(yf, fn_table)
        yul_functions[sol_name] = yf

    models = [
        yul_function_to_model(
            yul_functions[fn], fn, fn_map,
            keep_solidity_locals=config.keep_solidity_locals,
        )
        for fn in selected_functions
    ]

    lean_src = build_lean_source(
        models=models,
        source_path=args.source_label,
        namespace=args.namespace,
        config=config,
    )

    out_path = pathlib.Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(lean_src)

    print(f"Generated {out_path}")
    for model in models:
        print(f"Parsed {len(model.assignments)} assignments for {model.fn_name}")

    raw_ops: list[str] = []
    for model in models:
        for stmt in model.assignments:
            raw_ops.extend(collect_ops_from_statement(stmt))
    opcodes = ordered_unique([OP_TO_OPCODE[name] for name in raw_ops])
    print(f"Modeled opcodes: {', '.join(opcodes)}")

    return 0
