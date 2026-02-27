#!/usr/bin/env python3
"""
Generate Lean models of Cbrt.sol directly from Solidity source.

This script extracts `_cbrt`, `cbrt`, and `cbrtUp` from `src/vendor/Cbrt.sol` and
emits Lean definitions for:
- opcode-faithful uint256 EVM semantics, and
- normalized Nat semantics.
"""

from __future__ import annotations

import argparse
import datetime as dt
import pathlib
import re
from dataclasses import dataclass


class ParseError(RuntimeError):
    pass


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


TOKEN_RE = re.compile(
    r"""
    (?P<ws>\s+)
  | (?P<num>0x[0-9a-fA-F]+|\d+)
  | (?P<ident>[A-Za-z_][A-Za-z0-9_]*)
  | (?P<sym>[(),])
""",
    re.VERBOSE,
)


DEFAULT_FUNCTION_ORDER = ("_cbrt", "cbrt", "cbrtUp")

MODEL_NAMES = {
    "_cbrt": "model_cbrt",
    "cbrt": "model_cbrt_floor",
    "cbrtUp": "model_cbrt_up",
}

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

OP_TO_NORM_HELPER = {
    "add": "normAdd",
    "sub": "normSub",
    "mul": "normMul",
    "div": "normDiv",
    "shl": "normShl",
    "shr": "normShr",
    "clz": "normClz",
    "bitLengthPlus1": "normBitLengthPlus1",
    "lt": "normLt",
    "gt": "normGt",
}


def validate_ident(name: str, *, what: str) -> None:
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
        raise ParseError(f"Invalid {what}: {name!r}")


class ExprParser:
    def __init__(self, s: str):
        self.s = s
        self.tokens = self._tokenize(s)
        self.i = 0

    def _tokenize(self, s: str) -> list[tuple[str, str]]:
        out: list[tuple[str, str]] = []
        pos = 0
        while pos < len(s):
            m = TOKEN_RE.match(s, pos)
            if not m:
                raise ParseError(f"Unexpected token near: {s[pos:pos+24]!r}")
            pos = m.end()
            kind = m.lastgroup
            text = m.group()
            if kind == "ws":
                continue
            out.append((kind, text))
        return out

    def _peek(self) -> tuple[str, str] | None:
        if self.i >= len(self.tokens):
            return None
        return self.tokens[self.i]

    def _pop(self) -> tuple[str, str]:
        tok = self._peek()
        if tok is None:
            raise ParseError("Unexpected end of expression")
        self.i += 1
        return tok

    def _expect_sym(self, sym: str) -> None:
        kind, text = self._pop()
        if kind != "sym" or text != sym:
            raise ParseError(f"Expected '{sym}', found {text!r}")

    def parse(self) -> Expr:
        expr = self.parse_expr()
        if self._peek() is not None:
            raise ParseError(f"Unexpected trailing token: {self._peek()!r}")
        return expr

    def parse_expr(self) -> Expr:
        kind, text = self._pop()
        if kind == "num":
            return IntLit(int(text, 0))
        if kind == "ident":
            if self._peek() == ("sym", "("):
                self._pop()
                args: list[Expr] = []
                if self._peek() != ("sym", ")"):
                    while True:
                        args.append(self.parse_expr())
                        if self._peek() == ("sym", ","):
                            self._pop()
                            continue
                        break
                self._expect_sym(")")
                return Call(text, tuple(args))
            return Var(text)
        raise ParseError(f"Unexpected token: {(kind, text)!r}")


def find_matching_brace(s: str, open_idx: int) -> int:
    if open_idx < 0 or open_idx >= len(s) or s[open_idx] != "{":
        raise ValueError("open_idx must point at '{'")
    depth = 0
    for i in range(open_idx, len(s)):
        ch = s[i]
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return i
    raise ParseError("Unbalanced braces")


def extract_function_body(source: str, fn_name: str) -> str:
    m = re.search(rf"\bfunction\s+{re.escape(fn_name)}\b", source)
    if not m:
        raise ParseError(f"Function {fn_name!r} not found")
    fn_open = source.find("{", m.end())
    if fn_open == -1:
        raise ParseError(f"Function {fn_name!r} opening brace not found")
    fn_close = find_matching_brace(source, fn_open)
    return source[fn_open + 1 : fn_close]


def split_function_body_and_assembly(fn_body: str) -> tuple[str, str]:
    am = re.search(r"\bassembly\b", fn_body)
    if not am:
        return fn_body, ""

    asm_open = fn_body.find("{", am.end())
    if asm_open == -1:
        raise ParseError("Assembly opening brace not found")
    asm_close = find_matching_brace(fn_body, asm_open)

    outer_body = fn_body[: am.start()] + fn_body[asm_close + 1 :]
    asm_body = fn_body[asm_open + 1 : asm_close]
    return outer_body, asm_body


def strip_line_comments(text: str) -> str:
    lines = []
    for raw in text.splitlines():
        lines.append(raw.split("//", 1)[0])
    return "\n".join(lines)


def iter_statements(text: str) -> list[str]:
    cleaned = strip_line_comments(text)
    out: list[str] = []
    for part in cleaned.split(";"):
        stmt = part.strip()
        if stmt:
            out.append(stmt)
    return out


def parse_assignment_stmt(stmt: str, *, op: str) -> Assignment | None:
    if op == ":=":
        if ":=" not in stmt:
            return None
        left, right = stmt.split(":=", 1)
        left = left.strip()
        right = right.strip()
        if left.startswith("let "):
            left = left[len("let ") :].strip()
    elif op == "=":
        if "=" not in stmt or ":=" in stmt:
            return None
        # Allow declarations like `uint256 z = ...` and plain `z = ...`.
        m = re.fullmatch(
            r"(?:[A-Za-z_][A-Za-z0-9_]*\s+)*([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.+)",
            stmt,
            re.DOTALL,
        )
        if not m:
            return None
        left = m.group(1)
        right = m.group(2).strip()
    else:
        raise ValueError(f"Unsupported assignment operator: {op!r}")

    if left.startswith("return "):
        return None
    validate_ident(left, what="assignment target")
    expr = ExprParser(right).parse()
    return Assignment(target=left, expr=expr)


def parse_assembly_assignments(asm_body: str) -> list[Assignment]:
    out: list[Assignment] = []
    for raw in asm_body.splitlines():
        stmt = raw.split("//", 1)[0].strip().rstrip(";")
        if not stmt:
            continue
        parsed = parse_assignment_stmt(stmt, op=":=")
        if parsed is not None:
            out.append(parsed)
    return out


def parse_solidity_assignments(body: str) -> list[Assignment]:
    out: list[Assignment] = []
    for stmt in iter_statements(body):
        if stmt.startswith("return "):
            continue
        parsed = parse_assignment_stmt(stmt, op="=")
        if parsed is not None:
            out.append(parsed)
    return out


def parse_function_model(source: str, fn_name: str) -> FunctionModel:
    fn_body = extract_function_body(source, fn_name)
    outer_body, asm_body = split_function_body_and_assembly(fn_body)

    assignments: list[Assignment] = []
    assignments.extend(parse_solidity_assignments(outer_body))
    assignments.extend(parse_assembly_assignments(asm_body))

    if not assignments:
        raise ParseError(f"No assignments parsed for function {fn_name!r}")

    return FunctionModel(fn_name=fn_name, assignments=tuple(assignments))


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


def rewrite_norm_ast(expr: Expr) -> Expr:
    """Rewrite sub(257, clz(arg)) → bitLengthPlus1(arg) for the Nat model.

    In Nat arithmetic, normSub 257 (normClz x) = 257 - (255 - log2 x) underflows
    for x ≥ 2^256 because 255 - log2 x truncates to 0.  normBitLengthPlus1(x)
    computes log2(x) + 2 directly, giving the correct value for all Nat.
    """
    if isinstance(expr, Call):
        args = tuple(rewrite_norm_ast(a) for a in expr.args)
        if (
            expr.name == "sub"
            and len(args) == 2
            and isinstance(args[0], IntLit)
            and args[0].value == 257
            and isinstance(args[1], Call)
            and args[1].name == "clz"
            and len(args[1].args) == 1
        ):
            return Call("bitLengthPlus1", args[1].args)
        return Call(expr.name, args)
    return expr


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


def build_model_body(assignments: tuple[Assignment, ...], *, evm: bool) -> str:
    lines: list[str] = []
    if evm:
        lines.append("  let x := u256 x")
        call_map = {
            "_cbrt": "model_cbrt_evm",
            "cbrt": "model_cbrt_floor_evm",
            "cbrtUp": "model_cbrt_up_evm",
        }
        op_map = OP_TO_LEAN_HELPER
    else:
        call_map = {
            "_cbrt": "model_cbrt",
            "cbrt": "model_cbrt_floor",
            "cbrtUp": "model_cbrt_up",
        }
        op_map = OP_TO_NORM_HELPER

    for a in assignments:
        rhs_expr = a.expr
        if not evm:
            rhs_expr = rewrite_norm_ast(rhs_expr)
        rhs = emit_expr(rhs_expr, op_helper_map=op_map, call_helper_map=call_map)
        lines.append(f"  let {a.target} := {rhs}")

    lines.append("  z")
    return "\n".join(lines)


def render_function_defs(models: list[FunctionModel]) -> str:
    parts: list[str] = []
    for model in models:
        model_base = MODEL_NAMES[model.fn_name]
        evm_name = f"{model_base}_evm"
        norm_name = model_base
        evm_body = build_model_body(model.assignments, evm=True)
        norm_body = build_model_body(model.assignments, evm=False)

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
) -> str:
    generated_at = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    modeled_functions = ", ".join(model.fn_name for model in models)

    raw_ops: list[str] = []
    for model in models:
        for a in model.assignments:
            raw_ops.extend(collect_ops(a.expr))
    opcodes = ordered_unique([OP_TO_OPCODE[name] for name in raw_ops])
    opcodes_line = ", ".join(opcodes)

    function_defs = render_function_defs(models)

    return (
        "import Init\n\n"
        f"namespace {namespace}\n\n"
        "/-- Auto-generated from Solidity Cbrt assembly and assignment flow. -/\n"
        f"-- Source: {source_path}\n"
        f"-- Modeled functions: {modeled_functions}\n"
        f"-- Generated by: formal/cbrt/generate_cbrt_model.py\n"
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
        "def normBitLengthPlus1 (value : Nat) : Nat :=\n"
        "  if value = 0 then 1 else Nat.log2 value + 2\n\n"
        "def normLt (a b : Nat) : Nat :=\n"
        "  if a < b then 1 else 0\n\n"
        "def normGt (a b : Nat) : Nat :=\n"
        "  if a > b then 1 else 0\n\n"
        f"{function_defs}\n"
        f"end {namespace}\n"
    )


def parse_function_selection(args: argparse.Namespace) -> tuple[str, ...]:
    selected: list[str] = []

    if args.function:
        selected.extend(args.function)
    if args.functions:
        for fn in args.functions.split(","):
            name = fn.strip()
            if name:
                selected.append(name)

    if not selected:
        selected = list(DEFAULT_FUNCTION_ORDER)

    allowed = set(DEFAULT_FUNCTION_ORDER)
    bad = [f for f in selected if f not in allowed]
    if bad:
        raise ParseError(f"Unsupported function(s): {', '.join(bad)}")

    # cbrt/cbrtUp depend on _cbrt.
    if ("cbrt" in selected or "cbrtUp" in selected) and "_cbrt" not in selected:
        selected.append("_cbrt")

    selected_set = set(selected)
    return tuple(fn for fn in DEFAULT_FUNCTION_ORDER if fn in selected_set)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate Lean model of Cbrt.sol functions from Solidity source"
    )
    parser.add_argument(
        "--solidity",
        default="src/vendor/Cbrt.sol",
        help="Path to Solidity source file containing Cbrt library",
    )
    parser.add_argument(
        "--functions",
        default="",
        help="Comma-separated function names to model (default: _cbrt,cbrt,cbrtUp)",
    )
    parser.add_argument(
        "--function",
        action="append",
        help="Optional repeatable function selector (compatible alias)",
    )
    parser.add_argument(
        "--namespace",
        default="CbrtGeneratedModel",
        help="Lean namespace for generated definitions",
    )
    parser.add_argument(
        "--output",
        default="formal/cbrt/CbrtProof/CbrtProof/GeneratedCbrtModel.lean",
        help="Output Lean file path",
    )
    args = parser.parse_args()

    validate_ident(args.namespace, what="Lean namespace")

    selected_functions = parse_function_selection(args)
    sol_path = pathlib.Path(args.solidity)
    source = sol_path.read_text()

    models = [parse_function_model(source, fn_name) for fn_name in selected_functions]

    lean_src = build_lean_source(
        models=models,
        source_path=args.solidity,
        namespace=args.namespace,
    )

    out_path = pathlib.Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(lean_src)

    print(f"Generated {out_path}")
    for model in models:
        print(f"Parsed {len(model.assignments)} assignments from {args.solidity}:{model.fn_name}")

    raw_ops: list[str] = []
    for model in models:
        for a in model.assignments:
            raw_ops.extend(collect_ops(a.expr))
    opcodes = ordered_unique([OP_TO_OPCODE[name] for name in raw_ops])
    print(f"Modeled opcodes: {', '.join(opcodes)}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
