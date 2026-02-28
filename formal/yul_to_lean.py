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
class FunctionModel:
    fn_name: str
    assignments: tuple[Assignment, ...]


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

@dataclass
class YulFunction:
    """Parsed representation of a single Yul ``function`` definition."""
    yul_name: str
    param: str
    ret: str
    assignments: list[tuple[str, Expr]]


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

    def _parse_body_assignments(self) -> list[tuple[str, Expr]]:
        results: list[tuple[str, Expr]] = []

        while not self._at_end() and self._peek_kind() != "}":
            kind = self._peek_kind()

            if kind == "{":
                self._pop()
                results.extend(self._parse_body_assignments())
                self._expect("}")
                continue

            if kind == "ident" and self.tokens[self.i][1] == "let":
                self._pop()
                target = self._expect_ident()
                self._expect(":=")
                expr = self._parse_expr()
                results.append((target, expr))
                continue

            if kind == "ident" and self.tokens[self.i][1] == "leave":
                self._pop()
                continue

            if kind == "ident" and self.tokens[self.i][1] == "function":
                self._skip_function_def()
                continue

            if kind == "ident" and self.tokens[self.i][1] in ("if", "switch", "for"):
                stmt = self.tokens[self.i][1]
                raise ParseError(
                    f"Control flow statement '{stmt}' found in function body. "
                    f"Only straight-line code (let/bare assignments, leave, "
                    f"nested blocks, inner function definitions) is supported "
                    f"for Lean model generation. If the Solidity compiler "
                    f"introduced a branch, the generated model would silently "
                    f"omit it. Review the Yul IR and, if the control flow is "
                    f"semantically irrelevant, extend the parser to handle it."
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
        self._skip_until_matching_brace()

    def parse_function(self) -> YulFunction:
        fn_kw = self._expect_ident()
        assert fn_kw == "function", f"Expected 'function', got {fn_kw!r}"
        yul_name = self._expect_ident()
        self._expect("(")
        param = self._expect_ident()
        while self._peek_kind() == ",":
            self._pop()
            self._expect_ident()
        self._expect(")")
        self._expect("->")
        ret = self._expect_ident()
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
            param=param,
            ret=ret,
            assignments=assignments,
        )

    def find_function(self, sol_fn_name: str) -> YulFunction:
        """Find and parse ``function fun_{sol_fn_name}_<digits>(...)``.

        Raises on zero or duplicate matches.
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
        if len(matches) > 1:
            names = [self.tokens[m + 1][1] for m in matches]
            raise ParseError(
                f"Multiple Yul functions match '{sol_fn_name}': {names}. "
                f"Rename wrapper functions to avoid collisions "
                f"(e.g. prefix with 'wrap_')."
            )

        self.i = matches[0]
        return self.parse_function()


# ---------------------------------------------------------------------------
# Yul → FunctionModel conversion
# ---------------------------------------------------------------------------


def demangle_var(name: str, param_var: str, return_var: str) -> str | None:
    """Map a Yul variable name back to its Solidity-level name.

    Returns the cleaned name, or None if the variable is a compiler temporary
    that should be copy-propagated away.
    """
    if name == param_var or name == return_var:
        m = re.fullmatch(r"var_(\w+?)_\d+", name)
        return m.group(1) if m else name
    if name.startswith("usr$"):
        return name[4:]
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


def yul_function_to_model(
    yf: YulFunction,
    sol_fn_name: str,
    fn_map: dict[str, str],
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
    for target, _ in yf.assignments:
        assign_counts[target] += 1

    var_map: dict[str, str] = {}
    subst: dict[str, Expr] = {}

    for name in (yf.param, yf.ret):
        clean = demangle_var(name, yf.param, yf.ret)
        if clean:
            var_map[name] = clean

    assignments: list[Assignment] = []
    warned_multi: set[str] = set()

    for target, expr in yf.assignments:
        expr = substitute_expr(expr, subst)

        clean = demangle_var(target, yf.param, yf.ret)
        if clean is None:
            # ----------------------------------------------------------
            # Compiler temporary — copy-propagate.
            # Warn if it has multiple assignments: the sequential
            # substitution is semantically correct, but multi-assignment
            # temporaries are unusual and may signal a naming-convention
            # change that misclassified a real variable.
            # ----------------------------------------------------------
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
                subst[target] = expr
            continue

        var_map[target] = clean

        if isinstance(expr, IntLit) and expr.value == 0:
            continue

        expr = rename_expr(expr, var_map, fn_map)
        assignments.append(Assignment(target=clean, expr=expr))

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

    return FunctionModel(fn_name=sol_fn_name, assignments=tuple(assignments))


# ---------------------------------------------------------------------------
# Lean emission helpers
# ---------------------------------------------------------------------------

OP_TO_LEAN_HELPER = {
    "add": "evmAdd",
    "sub": "evmSub",
    "mul": "evmMul",
    "div": "evmDiv",
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

    # -- CLI defaults --
    default_source_label: str
    default_namespace: str
    default_output: str
    cli_description: str


# ---------------------------------------------------------------------------
# High-level pipeline (shared by both generators)
# ---------------------------------------------------------------------------


def build_model_body(
    assignments: tuple[Assignment, ...],
    *,
    evm: bool,
    config: ModelConfig,
) -> str:
    lines: list[str] = []
    norm_helpers = {**_BASE_NORM_HELPERS, **config.extra_norm_ops}

    if evm:
        lines.append("  let x := u256 x")
        call_map = {fn: f"{config.model_names[fn]}_evm" for fn in config.function_order}
        op_map = OP_TO_LEAN_HELPER
    else:
        call_map = dict(config.model_names)
        op_map = norm_helpers

    for a in assignments:
        rhs_expr = a.expr
        if not evm and config.norm_rewrite is not None:
            rhs_expr = config.norm_rewrite(rhs_expr)
        rhs = emit_expr(rhs_expr, op_helper_map=op_map, call_helper_map=call_map)
        lines.append(f"  let {a.target} := {rhs}")

    lines.append("  z")
    return "\n".join(lines)


def render_function_defs(models: list[FunctionModel], config: ModelConfig) -> str:
    parts: list[str] = []
    for model in models:
        model_base = config.model_names[model.fn_name]
        evm_name = f"{model_base}_evm"
        norm_name = model_base
        evm_body = build_model_body(model.assignments, evm=True, config=config)
        norm_body = build_model_body(model.assignments, evm=False, config=config)

        parts.append(
            f"/-- Opcode-faithful auto-generated model of `{model.fn_name}` with uint256 EVM semantics. -/\n"
            f"def {evm_name} (x : Nat) : Nat :=\n"
            f"{evm_body}\n"
        )
        parts.append(
            f"/-- Normalized auto-generated model of `{model.fn_name}` on Nat arithmetic. -/\n"
            f"def {norm_name} (x : Nat) : Nat :=\n"
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
        for a in model.assignments:
            raw_ops.extend(collect_ops(a.expr))
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

    fn_map: dict[str, str] = {}
    yul_functions: dict[str, YulFunction] = {}

    for sol_name in selected_functions:
        p = YulParser(tokens)
        yf = p.find_function(sol_name)
        fn_map[yf.yul_name] = sol_name
        yul_functions[sol_name] = yf

    models = [
        yul_function_to_model(yul_functions[fn], fn, fn_map)
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
        for a in model.assignments:
            raw_ops.extend(collect_ops(a.expr))
    opcodes = ordered_unique([OP_TO_OPCODE[name] for name in raw_ops])
    print(f"Modeled opcodes: {', '.join(opcodes)}")

    return 0
