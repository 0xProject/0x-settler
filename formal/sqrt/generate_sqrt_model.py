#!/usr/bin/env python3
"""
Generate a Lean model of `Sqrt._sqrt` directly from Solidity inline assembly.

The generated Lean code models the Yul/EVM operations used by `_sqrt` with uint256
semantics and emits a single definition that mirrors the assignment sequence.
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


TOKEN_RE = re.compile(
    r"""
    (?P<ws>\s+)
  | (?P<num>0x[0-9a-fA-F]+|\d+)
  | (?P<ident>[A-Za-z_][A-Za-z0-9_]*)
  | (?P<sym>[(),])
""",
    re.VERBOSE,
)


OP_TO_LEAN_HELPER = {
    "add": "evmAdd",
    "sub": "evmSub",
    "div": "evmDiv",
    "shl": "evmShl",
    "shr": "evmShr",
    "clz": "evmClz",
}

OP_TO_OPCODE = {
    "add": "ADD",
    "sub": "SUB",
    "div": "DIV",
    "shl": "SHL",
    "shr": "SHR",
    "clz": "CLZ",
}

OP_TO_NORM_HELPER = {
    "add": "normAdd",
    "sub": "normSub",
    "div": "normDiv",
    "shl": "normShl",
    "shr": "normShr",
    "clz": "normClz",
}


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
        tok = self._pop()
        kind, text = tok
        if kind == "num":
            return IntLit(int(text, 0))
        if kind == "ident":
            if self._peek() == ("sym", "("):
                self._pop()  # (
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
        raise ParseError(f"Unexpected token: {tok!r}")


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


def extract_function_assembly(source: str, fn_name: str) -> str:
    m = re.search(rf"\bfunction\s+{re.escape(fn_name)}\b", source)
    if not m:
        raise ParseError(f"Function {fn_name!r} not found")
    fn_open = source.find("{", m.end())
    if fn_open == -1:
        raise ParseError("Function body opening brace not found")
    fn_close = find_matching_brace(source, fn_open)
    fn_body = source[fn_open + 1 : fn_close]

    am = re.search(r"\bassembly\b", fn_body)
    if not am:
        raise ParseError(f"No inline assembly block found in function {fn_name!r}")
    asm_open = fn_body.find("{", am.end())
    if asm_open == -1:
        raise ParseError("Assembly opening brace not found")
    asm_close = find_matching_brace(fn_body, asm_open)
    return fn_body[asm_open + 1 : asm_close]


def parse_assignments(asm_body: str) -> list[Assignment]:
    out: list[Assignment] = []
    for raw in asm_body.splitlines():
        line = raw.split("//", 1)[0].strip()
        if not line or ":=" not in line:
            continue
        left, right = line.split(":=", 1)
        left = left.strip()
        right = right.strip().rstrip(";")
        if left.startswith("let "):
            left = left[len("let ") :].strip()
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", left):
            raise ParseError(f"Unsupported assignment target: {left!r}")
        expr = ExprParser(right).parse()
        out.append(Assignment(target=left, expr=expr))
    if not out:
        raise ParseError("No assembly assignments parsed")
    return out


def emit_lean_expr(expr: Expr) -> str:
    if isinstance(expr, IntLit):
        return str(expr.value)
    if isinstance(expr, Var):
        return expr.name
    if isinstance(expr, Call):
        helper = OP_TO_LEAN_HELPER.get(expr.name)
        if helper is None:
            raise ParseError(f"Unsupported call in Lean emitter: {expr.name!r}")
        args = " ".join(f"({emit_lean_expr(a)})" for a in expr.args)
        return f"{helper} {args}"
    raise TypeError(f"Unsupported Expr node: {type(expr)}")


def emit_norm_expr(expr: Expr) -> str:
    if isinstance(expr, IntLit):
        return str(expr.value)
    if isinstance(expr, Var):
        return expr.name
    if isinstance(expr, Call):
        helper = OP_TO_NORM_HELPER.get(expr.name)
        if helper is None:
            raise ParseError(f"Unsupported call in normalized emitter: {expr.name!r}")
        args = " ".join(f"({emit_norm_expr(a)})" for a in expr.args)
        return f"{helper} {args}"
    raise TypeError(f"Unsupported Expr node: {type(expr)}")


def collect_ops(expr: Expr) -> list[str]:
    out: list[str] = []
    if isinstance(expr, Call):
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


def build_lean_source(
    assignments: list[Assignment],
    opcodes: list[str],
    source_path: str,
    fn_name: str,
    namespace: str,
    model_name: str,
) -> str:
    generated_at = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    opcodes_line = ", ".join(opcodes)

    let_lines = ["  let x := u256 x"]
    for a in assignments:
        let_lines.append(f"  let {a.target} := {emit_lean_expr(a.expr)}")
    let_lines.append("  z")
    evm_model_body = "\n".join(let_lines)

    norm_lines = []
    for a in assignments:
        norm_lines.append(f"  let {a.target} := {emit_norm_expr(a.expr)}")
    norm_lines.append("  z")
    norm_model_body = "\n".join(norm_lines)

    return (
        "import Init\n\n"
        f"namespace {namespace}\n\n"
        "/-- Auto-generated from Solidity `_sqrt` assembly. -/\n"
        f"-- Source: {source_path}:{fn_name}\n"
        f"-- Generated by: formal/sqrt/generate_sqrt_model.py\n"
        f"-- Generated at (UTC): {generated_at}\n"
        f"-- Modeled opcodes/Yul builtins: {opcodes_line}\n\n"
        "def WORD_MOD : Nat := 2 ^ 256\n\n"
        "def u256 (x : Nat) : Nat :=\n"
        "  x % WORD_MOD\n\n"
        "def evmAdd (a b : Nat) : Nat :=\n"
        "  u256 (u256 a + u256 b)\n\n"
        "def evmSub (a b : Nat) : Nat :=\n"
        "  u256 (u256 a + WORD_MOD - u256 b)\n\n"
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
        "def normAdd (a b : Nat) : Nat := a + b\n\n"
        "def normSub (a b : Nat) : Nat := a - b\n\n"
        "def normDiv (a b : Nat) : Nat := a / b\n\n"
        "def normShl (shift value : Nat) : Nat := value <<< shift\n\n"
        "def normShr (shift value : Nat) : Nat := value / 2 ^ shift\n\n"
        "def normClz (value : Nat) : Nat :=\n"
        "  if value = 0 then 256 else 255 - Nat.log2 value\n\n"
        f"/-- Opcode-faithful auto-generated model of `{fn_name}` with uint256 EVM semantics. -/\n"
        f"def {model_name}_evm (x : Nat) : Nat :=\n"
        f"{evm_model_body}\n\n"
        f"/-- Normalized auto-generated model of `{fn_name}` on Nat arithmetic. -/\n"
        f"def {model_name} (x : Nat) : Nat :=\n"
        f"{norm_model_body}\n\n"
        f"end {namespace}\n"
    )


def default_model_name(fn_name: str) -> str:
    return f"model_{fn_name.lstrip('_')}"


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate Lean model of Sqrt._sqrt from Solidity inline assembly"
    )
    parser.add_argument(
        "--solidity",
        default="src/vendor/Sqrt.sol",
        help="Path to Solidity source file containing _sqrt",
    )
    parser.add_argument(
        "--function",
        default="_sqrt",
        help="Function name to model (default: _sqrt)",
    )
    parser.add_argument(
        "--namespace",
        default="SqrtGeneratedModel",
        help="Lean namespace for generated definitions",
    )
    parser.add_argument(
        "--model-name",
        default=None,
        help="Lean def name for generated model (default: model_<function>)",
    )
    parser.add_argument(
        "--output",
        default="formal/sqrt/SqrtProof/SqrtProof/GeneratedSqrtModel.lean",
        help="Output Lean file path",
    )
    args = parser.parse_args()

    model_name = args.model_name or default_model_name(args.function)
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", model_name):
        raise ParseError(f"Invalid Lean def name: {model_name!r}")
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", args.namespace):
        raise ParseError(f"Invalid Lean namespace: {args.namespace!r}")

    sol_path = pathlib.Path(args.solidity)
    source = sol_path.read_text()
    asm_body = extract_function_assembly(source, args.function)
    assignments = parse_assignments(asm_body)

    raw_ops: list[str] = []
    for a in assignments:
        raw_ops.extend(collect_ops(a.expr))
    opcodes = ordered_unique([OP_TO_OPCODE.get(name, name.upper()) for name in raw_ops])

    lean_src = build_lean_source(
        assignments=assignments,
        opcodes=opcodes,
        source_path=args.solidity,
        fn_name=args.function,
        namespace=args.namespace,
        model_name=model_name,
    )

    out_path = pathlib.Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(lean_src)

    print(f"Generated {out_path}")
    print(f"Parsed {len(assignments)} assignments from {args.solidity}:{args.function}")
    print(f"Modeled opcodes: {', '.join(opcodes)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
