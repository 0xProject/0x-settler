"""
Pure syntax parser for Yul IR.

Produces ``yul_ast`` nodes without any semantic lowering, constant
folding, block flattening, alpha-renaming, or helper classification.
"""

from __future__ import annotations

import ast

from .yul_ast import (
    AssignStmt,
    Block,
    BlockStmt,
    CallExpr,
    ExprStmt,
    ForStmt,
    FunctionDef,
    FunctionDefStmt,
    IfStmt,
    IntExpr,
    LeaveStmt,
    LetStmt,
    NameExpr,
    ParseError,
    Span,
    StringExpr,
    SwitchCase,
    SwitchDefault,
    SwitchStmt,
    SynExpr,
    SynStmt,
)


class SyntaxParser:
    """Recursive-descent parser producing a pure syntax AST.

    No lowering, no constant folding, no block flattening, no helper
    classification. String literals stay as raw ``StringExpr`` tokens
    so later lowering can decode their literal contents explicitly.
    """

    def __init__(self, tokens: list[tuple[str, str]], *, token_offset: int = 0) -> None:
        self._tokens = tokens
        self._i = 0
        self._token_offset = token_offset

    # -- token primitives ---------------------------------------------------

    def _pos(self) -> int:
        return self._i + self._token_offset

    def _at_end(self) -> bool:
        return self._i >= len(self._tokens)

    def _peek(self) -> tuple[str, str] | None:
        if self._at_end():
            return None
        return self._tokens[self._i]

    def _peek_kind(self) -> str | None:
        tok = self._peek()
        return tok[0] if tok else None

    def _pop(self) -> tuple[str, str]:
        tok = self._peek()
        if tok is None:
            raise ParseError("Unexpected end of Yul token stream")
        self._i += 1
        return tok

    def _expect(self, kind: str) -> str:
        k, text = self._pop()
        if k != kind:
            raise ParseError(f"Expected {kind!r}, got {k!r} ({text!r})")
        return text

    def _expect_ident(self) -> str:
        return self._expect("ident")

    def _span_from(self, start: int) -> Span:
        return Span(start, self._pos())

    # -- lookahead ----------------------------------------------------------

    def _looks_like_assignment(self) -> bool:
        """Check if current position starts ``ident [, ident]* :=``."""
        if self._peek_kind() != "ident":
            return False
        j = self._i + 1
        while j < len(self._tokens) and self._tokens[j][0] == ",":
            j += 1
            if j >= len(self._tokens) or self._tokens[j][0] != "ident":
                return False
            j += 1
        return j < len(self._tokens) and self._tokens[j][0] == ":="

    # -- expressions --------------------------------------------------------

    def _parse_expr(self) -> SynExpr:
        start = self._pos()
        kind, text = self._pop()
        if kind == "num":
            return IntExpr(int(text, 0), self._span_from(start))
        if kind == "string":
            return StringExpr(
                text=text,
                decoded_bytes=_decode_string_literal(text),
                span=self._span_from(start),
            )
        if kind == "ident":
            if self._peek_kind() == "(":
                name_span = self._span_from(start)
                self._pop()  # consume '('
                args: list[SynExpr] = []
                if self._peek_kind() != ")":
                    while True:
                        args.append(self._parse_expr())
                        if self._peek_kind() == ",":
                            self._pop()
                            continue
                        break
                self._expect(")")
                return CallExpr(text, name_span, tuple(args), self._span_from(start))
            return NameExpr(text, self._span_from(start))
        raise ParseError(f"Expected expression, got {kind!r} ({text!r})")

    # -- statements ---------------------------------------------------------

    def _parse_let(self) -> LetStmt:
        start = self._pos()
        self._pop()  # consume 'let'
        targets: list[str] = []
        target_spans: list[Span] = []

        t_start = self._pos()
        targets.append(self._expect_ident())
        target_spans.append(self._span_from(t_start))

        while self._peek_kind() == ",":
            self._pop()
            t_start = self._pos()
            targets.append(self._expect_ident())
            target_spans.append(self._span_from(t_start))

        init: SynExpr | None = None
        if self._peek_kind() == ":=":
            self._pop()
            init = self._parse_expr()

        return LetStmt(
            tuple(targets), tuple(target_spans), init, self._span_from(start)
        )

    def _parse_assignment(self) -> AssignStmt:
        start = self._pos()
        targets: list[str] = []
        target_spans: list[Span] = []

        t_start = self._pos()
        targets.append(self._expect_ident())
        target_spans.append(self._span_from(t_start))

        while self._peek_kind() == ",":
            self._pop()
            t_start = self._pos()
            targets.append(self._expect_ident())
            target_spans.append(self._span_from(t_start))

        self._expect(":=")
        expr = self._parse_expr()
        return AssignStmt(
            tuple(targets), tuple(target_spans), expr, self._span_from(start)
        )

    def _parse_if(self) -> IfStmt:
        start = self._pos()
        self._pop()  # consume 'if'
        condition = self._parse_expr()
        body = self._parse_block()
        return IfStmt(condition, body, self._span_from(start))

    def _parse_switch(self) -> SwitchStmt:
        start = self._pos()
        self._pop()  # consume 'switch'
        discriminant = self._parse_expr()
        cases: list[SwitchCase] = []
        default: SwitchDefault | None = None

        while (
            not self._at_end()
            and self._peek_kind() == "ident"
            and self._tokens[self._i][1] in ("case", "default")
        ):
            branch_start = self._pos()
            branch = self._expect_ident()
            if branch == "case":
                value = self._parse_expr()
                body = self._parse_block()
                cases.append(SwitchCase(value, body, self._span_from(branch_start)))
            else:
                if default is not None:
                    raise ParseError("Duplicate 'default' in switch statement")
                body = self._parse_block()
                default = SwitchDefault(body, self._span_from(branch_start))

        return SwitchStmt(discriminant, tuple(cases), default, self._span_from(start))

    def _parse_for(self) -> ForStmt:
        start = self._pos()
        self._pop()  # consume 'for'
        init = self._parse_block()
        condition = self._parse_expr()
        post = self._parse_block()
        body = self._parse_block()
        return ForStmt(init, condition, post, body, self._span_from(start))

    def _parse_block(self) -> Block:
        start = self._pos()
        self._expect("{")
        stmts = self._parse_block_contents()
        self._expect("}")
        return Block(tuple(stmts), self._span_from(start))

    def _parse_block_contents(self) -> list[SynStmt]:
        stmts: list[SynStmt] = []
        while not self._at_end() and self._peek_kind() != "}":
            stmts.append(self._parse_stmt())
        return stmts

    def _parse_stmt(self) -> SynStmt:
        kind = self._peek_kind()

        if kind == "{":
            start = self._pos()
            block = self._parse_block()
            return BlockStmt(block, self._span_from(start))

        if kind == "ident":
            text = self._tokens[self._i][1]
            if text == "let":
                return self._parse_let()
            if text == "leave":
                start = self._pos()
                self._pop()
                return LeaveStmt(self._span_from(start))
            if text == "function":
                return self._parse_function_def_stmt()
            if text == "if":
                return self._parse_if()
            if text == "switch":
                return self._parse_switch()
            if text == "for":
                return self._parse_for()
            if self._looks_like_assignment():
                return self._parse_assignment()

        # Bare expression-statement.
        if kind in ("ident", "num", "string"):
            start = self._pos()
            expr = self._parse_expr()
            return ExprStmt(expr, self._span_from(start))

        tok = self._peek()
        raise ParseError(f"Unexpected statement start: {tok!r}")

    # -- function definitions -----------------------------------------------

    def _parse_function_def_stmt(self) -> FunctionDefStmt:
        start = self._pos()
        func = self._parse_function_def()
        return FunctionDefStmt(func, self._span_from(start))

    def _parse_function_def(self) -> FunctionDef:
        start = self._pos()
        fn_kw = self._expect_ident()
        if fn_kw != "function":
            raise ParseError(f"Expected 'function', got {fn_kw!r}")

        name_start = self._pos()
        name = self._expect_ident()
        name_span = self._span_from(name_start)

        self._expect("(")
        params: list[str] = []
        param_spans: list[Span] = []
        if self._peek_kind() != ")":
            p_start = self._pos()
            params.append(self._expect_ident())
            param_spans.append(self._span_from(p_start))
            while self._peek_kind() == ",":
                self._pop()
                p_start = self._pos()
                params.append(self._expect_ident())
                param_spans.append(self._span_from(p_start))
        self._expect(")")

        returns: list[str] = []
        return_spans: list[Span] = []
        if self._peek_kind() == "->":
            self._pop()
            r_start = self._pos()
            returns.append(self._expect_ident())
            return_spans.append(self._span_from(r_start))
            while self._peek_kind() == ",":
                self._pop()
                r_start = self._pos()
                returns.append(self._expect_ident())
                return_spans.append(self._span_from(r_start))

        body = self._parse_block()
        return FunctionDef(
            name=name,
            name_span=name_span,
            params=tuple(params),
            param_spans=tuple(param_spans),
            returns=tuple(returns),
            return_spans=tuple(return_spans),
            body=body,
            span=self._span_from(start),
        )

    # -- public API ---------------------------------------------------------

    def parse_function_groups(self) -> list[list[FunctionDef]]:
        """Parse function definitions grouped by brace-delimited scope.

        Each element of the returned list contains the sibling functions
        found within one lexical scope instance. Top-level functions
        share the root scope group even when separated by ``object`` or
        ``code`` blocks; functions inside distinct brace-delimited blocks
        form separate groups.

        Note: function-body braces are consumed by the recursive
        descent parser, so the explicit scope stack here only tracks
        non-function-body braces (object/code wrappers).
        """
        groups: list[list[FunctionDef]] = []
        scope_stack: list[list[FunctionDef]] = [[]]
        while not self._at_end():
            kind = self._peek_kind()
            if kind == "ident" and self._tokens[self._i][1] == "function":
                scope_funcs = scope_stack[-1]
                if not scope_funcs:
                    groups.append(scope_funcs)
                scope_funcs.append(self._parse_function_def())
            elif kind == "{":
                scope_stack.append([])
                self._pop()
            elif kind == "}":
                if len(scope_stack) == 1:
                    raise ParseError(
                        f"Unmatched closing brace at token index {self._pos()}"
                    )
                scope_stack.pop()
                self._pop()
            else:
                self._pop()
        if len(scope_stack) != 1:
            raise ParseError("Unterminated brace scope in Yul token stream")
        return groups


def _decode_string_literal(token_text: str) -> bytes:
    """Decode a tokenized Yul string literal into its raw byte payload."""
    try:
        decoded_obj: object = ast.literal_eval(token_text)
    except (SyntaxError, ValueError) as err:
        raise ParseError(f"Invalid Yul string literal {token_text!r}") from err
    if not isinstance(decoded_obj, str):
        raise ParseError(f"Invalid Yul string literal {token_text!r}")
    decoded = decoded_obj
    try:
        return decoded.encode("latin-1")
    except UnicodeEncodeError as err:
        raise ParseError(
            f"Yul string literal contains non-byte code point: {token_text!r}"
        ) from err
