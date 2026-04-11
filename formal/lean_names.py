"""
Lean-facing identifier policy shared by naming, validation, and emission.
"""

from __future__ import annotations

import re
from collections.abc import Mapping

from evm_builtins import BASE_NORM_HELPERS, OP_TO_LEAN_HELPER

from yul_ast import ParseError

# Conservative subset of the fixed builtin command/term keywords from Lean 4's
# default parser, used to keep generated names away from the surface syntax we
# emit against. Source of truth:
# - https://github.com/leanprover/lean4/blob/master/src/Lean/Parser/Command.lean
# - https://github.com/leanprover/lean4/blob/master/src/Lean/Parser/Term.lean
# We do not try to model extension-defined keywords here.
LEAN_KEYWORDS: frozenset[str] = frozenset(
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

BASE_RESERVED_LEAN_NAMES: frozenset[str] = frozenset(
    {"u256", "WORD_MOD"} | set(OP_TO_LEAN_HELPER.values()) | LEAN_KEYWORDS
)
RESERVED_LEAN_NAMES: frozenset[str] = frozenset(
    set(BASE_RESERVED_LEAN_NAMES) | set(BASE_NORM_HELPERS.values())
)


def norm_reserved_lean_names(
    extra_norm_ops: Mapping[str, str] | None = None,
) -> frozenset[str]:
    extras = set(extra_norm_ops.values()) if extra_norm_ops is not None else set()
    return frozenset(set(BASE_NORM_HELPERS.values()) | extras)


def validate_ident(name: str, *, what: str) -> None:
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
        raise ParseError(f"Invalid {what}: {name!r}")
    if name in RESERVED_LEAN_NAMES:
        raise ParseError(f"Reserved Lean helper name used as {what}: {name!r}")
