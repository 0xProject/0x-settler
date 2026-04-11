"""Test-facing syntax helpers.

Production code should use ``yul_parser.SyntaxParser.parse_function_groups()``
and ``yul_resolve.resolve_module()`` directly.

This module keeps the old single-function parser/resolve conveniences behind an
explicit test boundary so they do not remain part of the production surface.
"""

from __future__ import annotations

from ..yul_ast import FunctionDef
from ..yul_parser import SyntaxParser as _SyntaxParser
from ..yul_resolve import ResolutionResult, resolve_module


class SyntaxParser(_SyntaxParser):
    """Test wrapper restoring single-function convenience methods."""

    def parse_function(self) -> FunctionDef:
        return self._parse_function_def()

    def parse_functions(self) -> list[FunctionDef]:
        groups = self.parse_function_groups()
        return groups[0] if groups else []


def resolve_function(
    func: FunctionDef,
    *,
    builtins: frozenset[str] = frozenset(),
) -> ResolutionResult:
    """Resolve one top-level function using production module semantics."""
    return resolve_module([func], builtins=builtins)[func.name]
