"""
Tokenization for the staged Yul parser and selector pipeline.
"""

from __future__ import annotations

import re

from yul_ast import ParseError

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
  | (?P<other>.)
""",
    re.VERBOSE,
)


def tokenize_yul(source: str) -> list[tuple[str, str]]:
    """Tokenize Yul source into ``(kind, text)`` pairs."""
    out: list[tuple[str, str]] = []
    pos = 0
    while pos < len(source):
        m = YUL_TOKEN_RE.match(source, pos)
        if not m:
            raise ParseError(f"Unexpected tokenization failure at offset {pos}")
        pos = m.end()
        kind = m.lastgroup
        text = m.group()
        if kind in ("ws", "linecomment", "doccomment"):
            continue
        if kind == "hex":
            out.append(("num", text))
        elif kind == "assign":
            out.append((":=", text))
        elif kind == "arrow":
            out.append(("->", text))
        elif kind == "lbrace":
            out.append(("{", text))
        elif kind == "rbrace":
            out.append(("}", text))
        elif kind == "lparen":
            out.append(("(", text))
        elif kind == "rparen":
            out.append((")", text))
        elif kind == "comma":
            out.append((",", text))
        elif kind == "colon":
            out.append((":", text))
        elif kind == "ident":
            out.append(("ident", text))
        elif kind == "num":
            out.append(("num", text))
        elif kind == "string":
            out.append(("string", text))
        else:
            raise ParseError(
                f"tokenizer stuck: unexpected character in Yul input: {text!r}"
            )
    return out
