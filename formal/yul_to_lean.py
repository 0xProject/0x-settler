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
    """An ``if cond { ... }`` block that assigns to already-declared variables.

    ``condition`` is the Yul condition expression.
    ``assignments`` are the assignments inside the if-body.
    ``modified_vars`` lists the Solidity-level variable names that the block
    may modify (used for Lean tuple-destructuring emission).
    """
    condition: Expr
    assignments: tuple[Assignment, ...]
    modified_vars: tuple[str, ...]
    else_vars: tuple[str, ...] | None = None


# A model statement is either a plain assignment or a conditional block.
ModelStatement = Assignment | ConditionalBlock


@dataclass(frozen=True)
class FunctionModel:
    fn_name: str
    assignments: tuple[ModelStatement, ...]
    param_names: tuple[str, ...] = ("x",)
    return_name: str = "z"


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
    """Raw parsed ``if cond { body }`` from Yul, before demangling."""
    condition: Expr
    body: tuple[tuple[str, Expr], ...]


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
                body = self._parse_if_body_assignments()
                self._expect("}")
                results.append(ParsedIfBlock(
                    condition=condition,
                    body=tuple(body),
                ))
                continue

            if kind == "ident" and self.tokens[self.i][1] in ("switch", "for"):
                stmt = self.tokens[self.i][1]
                raise ParseError(
                    f"Control flow statement '{stmt}' found in function body. "
                    f"Only straight-line code (let/bare assignments, leave, "
                    f"nested blocks, inner function definitions, if blocks) "
                    f"is supported for Lean model generation. If the Solidity "
                    f"compiler introduced a branch, the generated model would "
                    f"silently omit it. Review the Yul IR and, if the control "
                    f"flow is semantically irrelevant, extend the parser to "
                    f"handle it."
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

    def _parse_if_body_assignments(self) -> list[tuple[str, Expr]]:
        """Parse the body of an ``if`` block.

        Only bare assignments (``target := expr``) are expected inside
        if-bodies in the Yul IR patterns we handle.  ``let`` declarations
        are also accepted (they are locals scoped to the if-body that the
        compiler may introduce).
        """
        results: list[tuple[str, Expr]] = []
        while not self._at_end() and self._peek_kind() != "}":
            kind = self._peek_kind()

            if kind == "{":
                self._pop()
                results.extend(self._parse_if_body_assignments())
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
        return results

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
        self, sol_fn_name: str, *, n_params: int | None = None
    ) -> YulFunction:
        """Find and parse ``function fun_{sol_fn_name}_<digits>(...)``.

        When *n_params* is set and multiple candidates match the name
        pattern, only those with exactly *n_params* parameters are kept.
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

        if len(matches) > 1:
            names = [self.tokens[m + 1][1] for m in matches]
            raise ParseError(
                f"Multiple Yul functions match '{sol_fn_name}': {names}. "
                f"Rename wrapper functions to avoid collisions "
                f"(e.g. prefix with 'wrap_')."
            )

        self.i = matches[0]
        return self.parse_function()

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
    return_var: str,
    *,
    keep_solidity_locals: bool = False,
) -> str | None:
    """Map a Yul variable name back to its Solidity-level name.

    Returns the cleaned name, or None if the variable is a compiler temporary
    that should be copy-propagated away.

    ``param_vars`` is a list of Yul parameter variable names (supports
    multi-parameter functions).

    When *keep_solidity_locals* is True, variables matching the
    ``var_<name>_<digits>`` pattern (compiler representation of
    Solidity-declared locals) are kept in the model even if they are
    not the function parameter or return variable.
    """
    if name in param_vars or name == return_var:
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


def _inline_single_call(
    fn: YulFunction,
    args: tuple[Expr, ...],
    fn_table: dict[str, YulFunction],
    depth: int,
    max_depth: int,
) -> Expr | tuple[Expr, ...]:
    """Inline one function call, returning its return-value expression(s).

    Builds a substitution from parameters → argument expressions, then
    processes the function body sequentially (same semantics as copy-prop).
    Each local variable gets a unique gensym name to avoid clashes with
    the caller's scope.
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
        warnings.warn(
            f"Inlining function {fn.yul_name!r} which contains "
            f"{len(fn.expr_stmts)} expression-statement(s) not captured "
            f"in the model: [{summary}]. If any have side effects "
            f"(sstore, log, revert, ...) the inlined model may be "
            f"incomplete.",
            stacklevel=3,
        )

    subst: dict[str, Expr] = {}
    for param, arg_expr in zip(fn.params, args):
        subst[param] = arg_expr
    # Also seed return variables with zero (they're typically zero-initialized)
    for r in fn.rets:
        if r not in subst:
            subst[r] = IntLit(0)

    for stmt in fn.assignments:
        if isinstance(stmt, ParsedIfBlock):
            # Evaluate condition
            cond = substitute_expr(stmt.condition, subst)
            cond = inline_calls(cond, fn_table, depth + 1, max_depth)
            # Process if-body assignments into a separate subst branch
            if_subst = dict(subst)
            for target, raw_expr in stmt.body:
                expr = substitute_expr(raw_expr, if_subst)
                expr = inline_calls(expr, fn_table, depth + 1, max_depth)
                if_subst[target] = expr
            # The modified variables get a conditional expression:
            # if cond != 0 then <if_value> else <original_value>
            for target, _raw_expr in stmt.body:
                if_val = if_subst[target]
                orig_val = subst.get(target, IntLit(0))
                # Only update if the value actually changed
                if if_val is not orig_val:
                    subst[target] = if_val  # Simplified: take the if-branch value
                    # TODO: full conditional semantics would wrap in
                    # if-then-else, but for the model we inline the
                    # if-block as-is and let the outer ConditionalBlock
                    # handle it properly.
        else:
            target, raw_expr = stmt
            expr = substitute_expr(raw_expr, subst)
            expr = inline_calls(expr, fn_table, depth + 1, max_depth)
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
    def _resolve(e: Expr) -> Expr:
        for _ in range(10):
            e = substitute_expr(e, subst)
        return e

    if len(fn.rets) == 1:
        val = subst.get(fn.rets[0], IntLit(0))
        return _resolve(val)
    return tuple(_resolve(subst.get(r, IntLit(0))) for r in fn.rets)


def inline_calls(
    expr: Expr,
    fn_table: dict[str, YulFunction],
    depth: int = 0,
    max_depth: int = 20,
) -> Expr:
    """Recursively inline function calls in an expression.

    Walks the expression tree. When a ``Call`` targets a function in
    *fn_table*, its body is inlined via sequential substitution.
    ``__component_N`` wrappers (from multi-value ``let``) are resolved
    to the Nth return value of the inlined function.
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
            inner_args = tuple(inline_calls(a, fn_table, depth) for a in inner.args)
            if inner.name in fn_table:
                result = _inline_single_call(
                    fn_table[inner.name], inner_args, fn_table, depth + 1, max_depth,
                )
                if isinstance(result, tuple):
                    return result[idx] if idx < len(result) else expr
                return result  # single-return; component_0 = the value
            # Inner call not in table — rebuild with inlined args
            return Call(expr.name, (Call(inner.name, inner_args),))

        # Recurse into arguments
        args = tuple(inline_calls(a, fn_table, depth) for a in expr.args)

        # Direct call to a collected function
        if expr.name in fn_table:
            fn = fn_table[expr.name]
            result = _inline_single_call(fn, args, fn_table, depth + 1, max_depth)
            if isinstance(result, tuple):
                return result[0]  # single-call context; take first return
            return result

        return Call(expr.name, args)
    raise TypeError(f"Unsupported Expr node: {type(expr)}")


def _inline_yul_function(
    yf: YulFunction,
    fn_table: dict[str, YulFunction],
) -> YulFunction:
    """Apply ``inline_calls`` to every expression in a YulFunction."""
    new_assignments: list[RawStatement] = []
    for stmt in yf.assignments:
        if isinstance(stmt, ParsedIfBlock):
            new_cond = inline_calls(stmt.condition, fn_table)
            new_body: list[tuple[str, Expr]] = []
            for target, raw_expr in stmt.body:
                new_body.append((target, inline_calls(raw_expr, fn_table)))
            new_assignments.append(ParsedIfBlock(
                condition=new_cond,
                body=tuple(new_body),
            ))
        else:
            target, raw_expr = stmt
            new_assignments.append((target, inline_calls(raw_expr, fn_table)))
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

    for name in [*yf.params, yf.ret]:
        clean = demangle_var(name, yf.params, yf.ret, keep_solidity_locals=keep_solidity_locals)
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
        """Replace Var refs to Solidity-level vars with current Lean names.

        Called when a compiler temporary is copy-propagated.  By
        resolving Solidity-level ``Var`` nodes to their *current* Lean
        name at copy-propagation time we "freeze" the reference,
        preventing a later SSA rename of the same variable from
        changing what the expression points to.
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
            return Call(expr.name, new_args)
        return expr

    def _process_assignment(
        target: str, raw_expr: Expr, *, inside_conditional: bool = False,
    ) -> Assignment | None:
        """Process a single raw assignment through copy-prop and demangling.

        Returns an Assignment if the target is a real variable, or None if
        it was copy-propagated into ``subst``.
        """
        expr = substitute_expr(raw_expr, subst)

        clean = demangle_var(target, yf.params, yf.ret, keep_solidity_locals=keep_solidity_locals)
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

            body_assignments: list[Assignment] = []
            for target, raw_expr in stmt.body:
                clean = demangle_var(
                    target, yf.params, yf.ret,
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
                # Deduplicate while preserving order.
                seen_vars: set[str] = set()
                modified_list: list[str] = []
                for a in body_assignments:
                    if a.target not in seen_vars:
                        seen_vars.add(a.target)
                        modified_list.append(a.target)
                modified = tuple(modified_list)

                # Build else_vars from pre-if state (may differ from
                # modified_vars when SSA is active).
                else_vars_t = tuple(
                    pre_if_names.get(v, v) for v in modified_list
                )
                else_vars = (
                    else_vars_t if else_vars_t != modified else None
                )

                assignments.append(ConditionalBlock(
                    condition=cond,
                    assignments=tuple(body_assignments),
                    modified_vars=modified,
                    else_vars=else_vars,
                ))

                # After the if-block the Lean tuple-destructuring
                # creates fresh bindings with the base clean names.
                # Reset var_map and ssa_count accordingly so that
                # subsequent references and assignments are correct.
                modified_set = set(modified_list)
                for target_name, _ in stmt.body:
                    c = demangle_var(
                        target_name, yf.params, yf.ret,
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
    # Post-build validation: ensure the return variable was recognized.
    # If demangle_var failed to match the return variable's naming
    # pattern, the model would silently lose the output.
    # ------------------------------------------------------------------
    return_clean = var_map.get(yf.ret)
    if return_clean is None:
        raise ParseError(
            f"Return variable {yf.ret!r} of {sol_fn_name!r} was not "
            f"recognized as a real variable by demangle_var. The compiler "
            f"naming convention may have changed. Current patterns: "
            f"var_<name>_<digits> for param/return, usr$<name> for locals."
        )

    # param_names was saved before SSA processing; return_name uses
    # the final (possibly SSA-renamed) var_map entry.
    return_name = var_map[yf.ret]
    return FunctionModel(
        fn_name=sol_fn_name,
        assignments=tuple(assignments),
        param_names=param_names,
        return_name=return_name,
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
    return_name: str = "z",
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
            lines.append(f"    else {else_tup}")
        elif isinstance(stmt, Assignment):
            rhs = _emit_rhs(stmt.expr)
            lines.append(f"  let {stmt.target} := {rhs}")
        else:
            raise TypeError(f"Unsupported ModelStatement: {type(stmt)}")

    lines.append(f"  {return_name}")
    return "\n".join(lines)


def render_function_defs(models: list[FunctionModel], config: ModelConfig) -> str:
    parts: list[str] = []
    for model in models:
        model_base = config.model_names[model.fn_name]
        evm_name = f"{model_base}_evm"
        norm_name = model_base
        evm_body = build_model_body(
            model.assignments, evm=True, config=config,
            param_names=model.param_names, return_name=model.return_name,
        )
        norm_body = build_model_body(
            model.assignments, evm=False, config=config,
            param_names=model.param_names, return_name=model.return_name,
        )

        param_sig = " ".join(f"{p}" for p in model.param_names)
        parts.append(
            f"/-- Opcode-faithful auto-generated model of `{model.fn_name}` with uint256 EVM semantics. -/\n"
            f"def {evm_name} ({param_sig} : Nat) : Nat :=\n"
            f"{evm_body}\n"
        )
        parts.append(
            f"/-- Normalized auto-generated model of `{model.fn_name}` on Nat arithmetic. -/\n"
            f"def {norm_name} ({param_sig} : Nat) : Nat :=\n"
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

    return (
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
        f"{function_defs}\n"
        f"end {namespace}\n"
    )


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
    for sol_name in selected_functions:
        p = YulParser(tokens)
        np = config.n_params.get(sol_name) if config.n_params else None
        yf = p.find_function(sol_name, n_params=np)
        fn_map[yf.yul_name] = sol_name
        yul_functions[sol_name] = yf

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
