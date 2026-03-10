import pathlib
import random
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

import yul_to_lean as ytl


def branch(
    assignments: tuple[ytl.Assignment, ...] | list[ytl.Assignment],
    outputs: tuple[str, ...] | list[str],
) -> ytl.ConditionalBranch:
    return ytl.ConditionalBranch(
        assignments=tuple(assignments),
        outputs=tuple(outputs),
    )


class HoistRepeatedModelCallsTest(unittest.TestCase):
    MODEL_CALLS = frozenset({"inner"})

    # Define ``inner`` as a proper FunctionModel: inner(x) = x*x + 1
    INNER_MODEL = ytl.FunctionModel(
        fn_name="inner",
        param_names=("x",),
        return_names=("ret",),
        assignments=(
            ytl.Assignment(
                "ret",
                ytl.Call(
                    "add",
                    (ytl.Call("mul", (ytl.Var("x"), ytl.Var("x"))), ytl.IntLit(1)),
                ),
            ),
        ),
    )

    def test_redefinition_blocks_cross_statement_hoist(self) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("p",),
            return_names=("out",),
            assignments=(
                ytl.Assignment("y", ytl.Var("p")),
                ytl.Assignment("a", ytl.Call("inner", (ytl.Var("y"),))),
                ytl.Assignment("y", ytl.Call("add", (ytl.Var("y"), ytl.Var("p")))),
                ytl.Assignment("b", ytl.Call("inner", (ytl.Var("y"),))),
                ytl.Assignment("out", ytl.Call("sub", (ytl.Var("b"), ytl.Var("a")))),
            ),
        )

        transformed = ytl.hoist_repeated_model_calls(
            model,
            model_call_names=self.MODEL_CALLS,
        )

        self._assert_well_scoped(transformed)
        for p in (1, 2, 7):
            self.assertEqual(
                self._eval_model(model, p=p),
                self._eval_model(transformed, p=p),
            )

    def test_branch_local_dependencies_stay_in_branch_scope(self) -> None:
        model = ytl.FunctionModel(
            fn_name="g",
            param_names=("p",),
            return_names=("out",),
            assignments=(
                ytl.ConditionalBlock(
                    condition=ytl.Var("p"),
                    output_vars=("y", "a"),
                    then_branch=branch(
                        (
                            ytl.Assignment(
                                "y", ytl.Call("add", (ytl.Var("p"), ytl.Var("p")))
                            ),
                            ytl.Assignment("a", ytl.Call("inner", (ytl.Var("y"),))),
                        ),
                        ("y", "a"),
                    ),
                    else_branch=branch(
                        (
                            ytl.Assignment(
                                "y", ytl.Call("add", (ytl.Var("p"), ytl.Var("p")))
                            ),
                            ytl.Assignment("a", ytl.Call("inner", (ytl.Var("y"),))),
                        ),
                        ("y", "a"),
                    ),
                ),
                ytl.Assignment("out", ytl.Var("a")),
            ),
        )

        transformed = ytl.hoist_repeated_model_calls(
            model,
            model_call_names=self.MODEL_CALLS,
        )

        self._assert_well_scoped(transformed)
        for p in (0, 1, 9):
            self.assertEqual(
                self._eval_model(model, p=p),
                self._eval_model(transformed, p=p),
            )

    def _assert_well_scoped(self, model: ytl.FunctionModel) -> None:
        self._assert_block_well_scoped(
            model.assignments,
            available=set(model.param_names),
        )

    def _assert_block_well_scoped(
        self,
        statements: tuple[ytl.ModelStatement, ...],
        *,
        available: set[str],
    ) -> set[str]:
        scope = set(available)

        for stmt in statements:
            if isinstance(stmt, ytl.Assignment):
                missing = ytl._expr_vars(stmt.expr) - scope
                self.assertFalse(
                    missing,
                    f"{stmt.target} uses undefined vars: {sorted(missing)}",
                )
                scope.add(stmt.target)
                continue

            if not isinstance(stmt, ytl.ConditionalBlock):
                raise TypeError(f"Unsupported statement: {type(stmt)}")

            missing = ytl._expr_vars(stmt.condition) - scope
            self.assertFalse(
                missing,
                f"conditional uses undefined vars: {sorted(missing)}",
            )

            then_scope = self._assert_block_well_scoped(
                stmt.then_branch.assignments,
                available=scope,
            )
            for var in stmt.then_branch.outputs:
                self.assertIn(var, then_scope, f"then-branch output {var} missing")

            else_scope = self._assert_block_well_scoped(
                stmt.else_branch.assignments,
                available=scope,
            )
            for var in stmt.else_branch.outputs:
                self.assertIn(var, else_scope, f"else-branch output {var} missing")

            scope.update(stmt.output_vars)

        return scope

    def _eval_model(self, model: ytl.FunctionModel, *, p: int) -> int:
        table = ytl.build_model_table([self.INNER_MODEL, model])
        result = ytl.evaluate_function_model(model, (p,), model_table=table)
        if len(result) != 1:
            raise AssertionError("test helper expects single-return models")
        return result[0]


class FailClosedTranslatorTest(unittest.TestCase):
    def test_tokenize_yul_rejects_malformed_input(self) -> None:
        with self.assertRaisesRegex(ytl.ParseError, "tokenizer stuck"):
            ytl.tokenize_yul("function fun_bad_1() { let x := 1 @ }")

    def test_parse_function_rejects_non_function_keyword(self) -> None:
        parser = ytl.YulParser([("ident", "not_function")])

        with self.assertRaisesRegex(ytl.ParseError, "Expected 'function'"):
            parser.parse_function()

    def test_parse_function_rejects_unrecognized_statement_start(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_bad_1() -> z {
                "oops"
                z := 1
            }
            """)

        with self.assertRaisesRegex(ytl.ParseError, "Unsupported statement start"):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_rejects_conditional_memory_write(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_bad_1(x) -> z {
                if x {
                    mstore(0, x)
                }
                z := x
            }
            """)

        with self.assertRaisesRegex(ytl.ParseError, "Conditional memory write"):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_rejects_for_loop(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_bad_1(x) -> z {
                for { } 1 { } {
                    z := x
                }
            }
            """)

        with self.assertRaisesRegex(ytl.ParseError, "Control flow statement 'for'"):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_rejects_switch_without_default(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_bad_1(x) -> z {
                switch x
                case 0 {
                    z := 1
                }
            }
            """)

        with self.assertRaisesRegex(
            ytl.ParseError, "switch must have exactly 'case 0' \\+ 'default'"
        ):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_rejects_switch_with_nonzero_case(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_bad_1(x) -> z {
                switch x
                case 1 {
                    z := 1
                }
                default {
                    z := 2
                }
            }
            """)

        with self.assertRaisesRegex(ytl.ParseError, "switch case value .* is not 0"):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_rejects_switch_with_default_before_case(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_bad_1(x) -> z {
                switch x
                default {
                    z := 2
                }
                case 0 {
                    z := 1
                }
            }
            """)

        with self.assertRaisesRegex(
            ytl.ParseError, "'default' must be the last branch"
        ):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_rejects_nested_switch_inside_if_body(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_bad_1(x) -> z {
                if x {
                    switch and(x, 1)
                    case 0 {
                        z := 1
                    }
                    default {
                        z := 2
                    }
                }
                z := 3
            }
            """)

        with self.assertRaisesRegex(
            ytl.ParseError, "Control flow statement 'switch' found in if-body"
        ):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_rejects_nested_if_inside_switch_branch(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_bad_1(x) -> z {
                switch x
                case 0 {
                    if x {
                        z := 1
                    }
                }
                default {
                    z := 2
                }
            }
            """)

        with self.assertRaisesRegex(
            ytl.ParseError, "Control flow statement 'if' found in switch branch"
        ):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_inlines_bare_block_let_vars(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_ok_1(var_x_1) -> var_z_2 {
                {
                    let tmp := var_x_1
                    var_z_2 := add(tmp, tmp)
                }
            }
            """)

        yf = ytl.YulParser(tokens).parse_function()
        # ``let tmp`` is block-scoped and inlined into the reassignment.
        expected: list[ytl.RawStatement] = [
            ytl.PlainAssignment(
                "var_z_2",
                ytl.Call("add", (ytl.Var("var_x_1"), ytl.Var("var_x_1"))),
            ),
        ]
        self.assertEqual(yf.assignments, expected)

    def test_parse_function_inlines_nested_bare_blocks(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_ok_1(var_x_1) -> var_z_2 {
                {
                    let a := var_x_1
                    {
                        let b := add(a, a)
                        var_z_2 := mul(b, a)
                    }
                }
            }
            """)

        yf = ytl.YulParser(tokens).parse_function()
        # Both ``a`` and ``b`` are block-scoped.  The inner block inlines
        # ``b`` first, then the outer block inlines ``a`` into the result.
        expected: list[ytl.RawStatement] = [
            ytl.PlainAssignment(
                "var_z_2",
                ytl.Call(
                    "mul",
                    (
                        ytl.Call("add", (ytl.Var("var_x_1"), ytl.Var("var_x_1"))),
                        ytl.Var("var_x_1"),
                    ),
                ),
            ),
        ]
        self.assertEqual(yf.assignments, expected)

    def test_bare_block_inner_scope_shadows_outer(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_f_1(var_x_1) -> var_z_2 {
                {
                    let tmp := var_x_1
                    {
                        let tmp := add(tmp, tmp)
                        var_z_2 := mul(tmp, var_x_1)
                    }
                }
            }
            """)

        yf = ytl.YulParser(tokens).parse_function()
        # Inner ``let tmp`` shadows the outer one.  The inner RHS
        # ``add(tmp, tmp)`` references the outer ``tmp`` (not yet
        # substituted at that level), so after both levels inline:
        #   inner: z = mul(add(tmp, tmp), x)
        #   outer: z = mul(add(x, x), x)
        expected: list[ytl.RawStatement] = [
            ytl.PlainAssignment(
                "var_z_2",
                ytl.Call(
                    "mul",
                    (
                        ytl.Call(
                            "add",
                            (ytl.Var("var_x_1"), ytl.Var("var_x_1")),
                        ),
                        ytl.Var("var_x_1"),
                    ),
                ),
            ),
        ]
        self.assertEqual(yf.assignments, expected)

    def test_bare_block_sibling_scopes_same_name(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_f_1(var_x_1) -> var_z_2 {
                {
                    let tmp := add(var_x_1, 1)
                    var_z_2 := tmp
                }
                {
                    let tmp := mul(var_z_2, 2)
                    var_z_2 := tmp
                }
            }
            """)

        yf = ytl.YulParser(tokens).parse_function()
        # Each sibling block has its own ``tmp`` that is independently
        # inlined.  The second block's ``var_z_2`` on the RHS refers to
        # the outer-scope variable, not the first block's ``tmp``.
        expected: list[ytl.RawStatement] = [
            ytl.PlainAssignment(
                "var_z_2", ytl.Call("add", (ytl.Var("var_x_1"), ytl.IntLit(1)))
            ),
            ytl.PlainAssignment(
                "var_z_2",
                ytl.Call("mul", (ytl.Var("var_z_2"), ytl.IntLit(2))),
            ),
        ]
        self.assertEqual(yf.assignments, expected)

    def test_bare_block_outer_defines_after_inner_closes(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_f_1(var_x_1) -> var_z_2 {
                {
                    {
                        let tmp := add(var_x_1, 1)
                        var_z_2 := tmp
                    }
                    let tmp := mul(var_z_2, 3)
                    var_z_2 := tmp
                }
            }
            """)

        yf = ytl.YulParser(tokens).parse_function()
        # The inner block's ``tmp`` is fully inlined and gone before the
        # outer block declares its own ``tmp`` with the same name.
        expected: list[ytl.RawStatement] = [
            ytl.PlainAssignment(
                "var_z_2", ytl.Call("add", (ytl.Var("var_x_1"), ytl.IntLit(1)))
            ),
            ytl.PlainAssignment(
                "var_z_2",
                ytl.Call("mul", (ytl.Var("var_z_2"), ytl.IntLit(3))),
            ),
        ]
        self.assertEqual(yf.assignments, expected)

    def test_bare_block_if_merges_block_local_into_ite(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_f_1(var_x_1, var_c_2) -> var_z_3 {
                {
                    let tmp := var_x_1
                    if var_c_2 {
                        tmp := add(tmp, 1)
                    }
                    var_z_3 := tmp
                }
            }
            """)

        yf = ytl.YulParser(tokens).parse_function()
        # ``tmp`` is block-local.  The if-block modifies it, so after
        # flattening ``tmp`` should be an ``__ite`` conditional expression,
        # and the final assignment should inline it.
        self.assertEqual(len(yf.assignments), 1)
        stmt = yf.assignments[0]
        self.assertIsInstance(stmt, ytl.PlainAssignment)
        assert isinstance(stmt, ytl.PlainAssignment)
        self.assertEqual(stmt.target, "var_z_3")
        # The expression should be __ite(c, add(x, 1), x)
        self.assertIsInstance(stmt.expr, ytl.Call)
        assert isinstance(stmt.expr, ytl.Call)
        self.assertEqual(stmt.expr.name, "__ite")

    def test_bare_block_switch_merges_block_local_into_ite(self) -> None:
        yul = """
            function fun_f_1(var_x_1, var_c_2) -> var_z_3 {
                {
                    let tmp := var_x_1
                    switch var_c_2
                    case 0 {
                        tmp := add(tmp, 1)
                    }
                    default {
                        tmp := add(tmp, 2)
                    }
                    var_z_3 := tmp
                }
            }
        """
        config = make_model_config(("f",))
        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        # f(10, 0) -> z = 10 + 1 = 11
        self.assertEqual(ytl.evaluate_function_model(model, (10, 0)), (11,))
        # f(10, 1) -> z = 10 + 2 = 12
        self.assertEqual(ytl.evaluate_function_model(model, (10, 1)), (12,))

    def test_parse_function_allows_top_level_leave(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_f_1() -> var_z_2 {
                var_z_2 := 1
                leave
                var_z_2 := 2
            }
            """)

        yf = ytl.YulParser(tokens).parse_function()
        # Dead code after ``leave`` is skipped.
        expected: list[ytl.RawStatement] = [
            ytl.PlainAssignment("var_z_2", ytl.IntLit(1))
        ]
        self.assertEqual(yf.assignments, expected)

    def test_parse_function_lowers_multi_return_let_to_component_wrappers(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_target_1(var_x_1) -> var_z_2 {
                let usr$lhs, usr$rhs := fun_pair_2(var_x_1)
                var_z_2 := add(usr$lhs, usr$rhs)
            }
            """)

        parsed = ytl.YulParser(tokens).parse_function()

        expected_assignments: list[ytl.RawStatement] = [
            ytl.PlainAssignment(
                "usr$lhs",
                ytl.Call(
                    "__component_0_2",
                    (ytl.Call("fun_pair_2", (ytl.Var("var_x_1"),)),),
                ),
            ),
            ytl.PlainAssignment(
                "usr$rhs",
                ytl.Call(
                    "__component_1_2",
                    (ytl.Call("fun_pair_2", (ytl.Var("var_x_1"),)),),
                ),
            ),
            ytl.PlainAssignment(
                "var_z_2",
                ytl.Call("add", (ytl.Var("usr$lhs"), ytl.Var("usr$rhs"))),
            ),
        ]

        self.assertEqual(parsed.assignments, expected_assignments)

    def test_collect_all_functions_records_rejected_helper_and_inlining_fails(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_target_1(x) -> z {
                z := bad_helper(x)
            }

            function bad_helper(a) -> b {
                for { } 1 { } { }
            }
            """)
        collection = ytl.YulParser(tokens).collect_all_functions()
        target = collection.functions["fun_target_1"]

        self.assertIn("bad_helper", collection.rejected)
        with self.assertRaisesRegex(
            ytl.ParseError, "Cannot inline helper 'bad_helper'"
        ):
            ytl._inline_yul_function(
                target,
                collection.functions,
                unsupported_function_errors=collection.rejected,
            )

    def test_yul_function_to_model_rejects_demangled_signature_collision(
        self,
    ) -> None:
        yf = ytl.YulFunction(
            yul_name="f",
            params=["var_x_1"],
            rets=["var_x_2"],
            assignments=[
                ytl.PlainAssignment("var_x_2", ytl.IntLit(1)),
            ],
        )

        with self.assertRaisesRegex(ytl.ParseError, "both demangle to 'x'"):
            ytl.yul_function_to_model(yf, "f", {})

    def test_inline_calls_rejects_depth_overflow(self) -> None:
        fn_table = {
            "f": ytl.YulFunction(
                yul_name="f",
                params=["x"],
                rets=["r"],
                assignments=[ytl.PlainAssignment("r", ytl.Call("g", (ytl.Var("x"),)))],
            ),
        }

        with self.assertRaisesRegex(ytl.ParseError, "max_depth=0"):
            ytl.inline_calls(ytl.Call("f", (ytl.IntLit(1),)), fn_table, max_depth=0)

    def test_inline_calls_rejects_multi_return_in_scalar_context(self) -> None:
        fn_table = {
            "pair": ytl.YulFunction(
                yul_name="pair",
                params=[],
                rets=["a", "b"],
                assignments=[],
            ),
        }

        with self.assertRaisesRegex(ytl.ParseError, "single-value context"):
            ytl.inline_calls(ytl.Call("pair", ()), fn_table)

    def test_inline_calls_rejects_helper_call_with_wrong_arity(self) -> None:
        fn_table = {
            "id": ytl.YulFunction(
                yul_name="id",
                params=["x"],
                rets=["r"],
                assignments=[ytl.PlainAssignment("r", ytl.Var("x"))],
            ),
        }

        with self.assertRaisesRegex(
            ytl.ParseError,
            r"Cannot inline helper 'id': expected 1 argument\(s\), got 2",
        ):
            ytl.inline_calls(ytl.Call("id", (ytl.IntLit(1), ytl.IntLit(2))), fn_table)

    def test_inline_calls_rejects_wrong_arity_for_exact_from_helper(self) -> None:
        fn_table = {
            "from512": ytl.YulFunction(
                yul_name="from512",
                params=["ptr", "hi", "lo"],
                rets=["out"],
                assignments=[
                    ytl.PlainAssignment("out", ytl.IntLit(0)),
                    ytl.MemoryWrite(ytl.Var("ptr"), ytl.Var("hi")),
                    ytl.MemoryWrite(
                        ytl.Call("add", (ytl.Var("ptr"), ytl.IntLit(32))),
                        ytl.Var("lo"),
                    ),
                    ytl.PlainAssignment("out", ytl.Var("ptr")),
                ],
            ),
        }

        with self.assertRaisesRegex(
            ytl.ParseError,
            r"Cannot inline helper 'from512': expected 3 argument\(s\), got 4",
        ):
            ytl.inline_calls(
                ytl.Call(
                    "from512",
                    (ytl.IntLit(0), ytl.IntLit(1), ytl.IntLit(2), ytl.IntLit(3)),
                ),
                fn_table,
            )

    def test_inline_calls_rejects_invalid_component_projection(self) -> None:
        fn_table = {
            "single": ytl.YulFunction(
                yul_name="single",
                params=[],
                rets=["a"],
                assignments=[],
            ),
        }
        expr = ytl.Call("__component_1_2", (ytl.Call("single", ()),))

        with self.assertRaisesRegex(ytl.ParseError, "expects 2 return values"):
            ytl.inline_calls(expr, fn_table)

    def test_yul_function_to_model_rejects_multi_assigned_temporary(self) -> None:
        yf = ytl.YulFunction(
            yul_name="f",
            params=["arg"],
            rets=["ret"],
            assignments=[
                ytl.PlainAssignment("tmp", ytl.IntLit(1)),
                ytl.PlainAssignment("tmp", ytl.IntLit(2)),
                ytl.PlainAssignment("ret", ytl.Var("tmp")),
            ],
        )

        with self.assertRaisesRegex(
            ytl.ParseError, "classified as a compiler temporary"
        ):
            ytl.yul_function_to_model(yf, "f", {})

    def test_inline_yul_function_rejects_helper_memory_write(
        self,
    ) -> None:
        helper = ytl.YulFunction(
            yul_name="store_helper",
            params=["arg"],
            rets=["ret"],
            assignments=[
                ytl.MemoryWrite(ytl.IntLit(0), ytl.Var("arg")),
                ytl.PlainAssignment("ret", ytl.Var("arg")),
            ],
        )
        target = ytl.YulFunction(
            yul_name="target",
            params=["flag", "x"],
            rets=["ret"],
            assignments=[
                ytl.ParsedIfBlock(
                    condition=ytl.Var("flag"),
                    body=(
                        ytl.PlainAssignment(
                            "ret", ytl.Call("store_helper", (ytl.Var("x"),))
                        ),
                    ),
                ),
            ],
        )

        with self.assertRaisesRegex(
            ytl.ParseError,
            "helper memory writes are unsupported",
        ):
            ytl._inline_yul_function(target, {"store_helper": helper})

    def test_inline_yul_function_preserves_else_body(self) -> None:
        helper = ytl.YulFunction(
            yul_name="inc",
            params=["arg"],
            rets=["ret"],
            assignments=[
                ytl.PlainAssignment(
                    "ret", ytl.Call("add", (ytl.Var("arg"), ytl.IntLit(1)))
                )
            ],
        )
        target = ytl.YulFunction(
            yul_name="target",
            params=["flag", "x"],
            rets=["ret"],
            assignments=[
                ytl.ParsedIfBlock(
                    condition=ytl.Var("flag"),
                    body=(
                        ytl.PlainAssignment("ret", ytl.Call("inc", (ytl.Var("x"),))),
                    ),
                    else_body=(ytl.PlainAssignment("ret", ytl.Var("x")),),
                ),
            ],
        )

        inlined = ytl._inline_yul_function(target, {"inc": helper})

        expected_assignments: list[ytl.RawStatement] = [
            ytl.ParsedIfBlock(
                condition=ytl.Var("flag"),
                body=(
                    ytl.PlainAssignment(
                        "ret", ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1)))
                    ),
                ),
                else_body=(ytl.PlainAssignment("ret", ytl.Var("x")),),
            ),
        ]

        self.assertEqual(inlined.assignments, expected_assignments)


def make_model_config(
    function_order: tuple[str, ...],
    *,
    hoist_repeated_calls: frozenset[str] = frozenset(),
    skip_prune: frozenset[str] = frozenset(),
    keep_solidity_locals: bool = False,
    exact_yul_names: dict[str, str] | None = None,
    n_params: dict[str, int] | None = None,
) -> ytl.ModelConfig:
    return ytl.ModelConfig(
        function_order=function_order,
        model_names={fn: f"model_{fn}" for fn in function_order},
        header_comment="test",
        generator_label="formal/test_yul_to_lean.py",
        extra_norm_ops={},
        extra_lean_defs="",
        norm_rewrite=None,
        inner_fn=function_order[0],
        n_params=n_params,
        exact_yul_names=exact_yul_names,
        keep_solidity_locals=keep_solidity_locals,
        hoist_repeated_calls=hoist_repeated_calls,
        skip_prune=skip_prune,
        default_source_label="test",
        default_namespace="Test",
        default_output="",
        cli_description="test",
    )


class ModelEquivalenceTestCase(unittest.TestCase):
    INTERESTING_VALUES: tuple[int, ...] = (
        0,
        1,
        2,
        3,
        7,
        8,
        9,
        10,
        11,
        31,
        32,
        33,
        255,
        256,
        257,
        511,
        (1 << 255) - 1,
        1 << 255,
        ytl.WORD_MOD - 1,
        ytl.WORD_MOD,
        ytl.WORD_MOD + 1,
        ytl.WORD_MOD + 255,
    )

    def assertModelsEquivalent(
        self,
        before: ytl.FunctionModel,
        after: ytl.FunctionModel,
        *,
        before_table: dict[str, ytl.FunctionModel] | None = None,
        after_table: dict[str, ytl.FunctionModel] | None = None,
        random_cases: int = 64,
        seed: int = 0,
    ) -> None:
        self.assertEqual(
            len(before.param_names),
            len(after.param_names),
            "equivalence fuzzer requires matching arity",
        )

        if before_table is None:
            before_table = ytl.build_model_table([before])
        if after_table is None:
            after_table = ytl.build_model_table([after])

        ytl.validate_function_model(before)
        ytl.validate_function_model(after)

        for args in self._equivalence_cases(
            len(before.param_names), seed=seed, random_cases=random_cases
        ):
            before_result = ytl.evaluate_function_model(
                before,
                args,
                model_table=before_table,
            )
            after_result = ytl.evaluate_function_model(
                after,
                args,
                model_table=after_table,
            )
            self.assertEqual(
                before_result,
                after_result,
                f"model mismatch for args={args}",
            )

    def _equivalence_cases(
        self,
        arity: int,
        *,
        seed: int,
        random_cases: int,
    ) -> list[tuple[int, ...]]:
        cases: list[tuple[int, ...]] = []
        values = self.INTERESTING_VALUES

        if arity == 0:
            cases.append(())
        elif arity == 1:
            cases.extend((value,) for value in values)
        elif arity == 2:
            pair_values: tuple[int, ...] = (*values[:8], *values[-3:])
            cases.extend((left, right) for left in pair_values for right in pair_values)
        else:
            for offset in range(len(values)):
                cases.append(
                    tuple(values[(offset + i) % len(values)] for i in range(arity))
                )
            for hot_index in range(arity):
                cases.append(
                    tuple(values[-1] if i == hot_index else 0 for i in range(arity))
                )

        rng = random.Random(seed)
        for _ in range(random_cases):
            cases.append(tuple(rng.getrandbits(300) for _ in range(arity)))

        deduped: list[tuple[int, ...]] = []
        seen: set[tuple[int, ...]] = set()
        for args in cases:
            if args in seen:
                continue
            seen.add(args)
            deduped.append(args)
        return deduped


class TranslationPipelineTest(unittest.TestCase):
    SIMPLE_CONFIG = make_model_config(("f",))
    SIMPLE_YUL = """
        function fun_f_1(var_x_1) -> var_z_2 {
            let usr$tmp := 0
            let usr$dead := 7
            var_z_2 := 0
            var_z_2 := add(var_x_1, 1)
        }
    """
    MULTI_RETURN_REBIND_CONFIG = make_model_config(("outer",))
    MULTI_RETURN_REBIND_YUL = """
        function fun_outer_1(var_x_hi_1, var_x_lo_2) -> var_r_3 {
            let expr_1_component_1, expr_1_component_2, expr_1_component_3 := fun_pair_2(var_x_hi_1, var_x_lo_2)
            var_x_lo_2 := expr_1_component_3
            var_x_hi_1 := expr_1_component_2
            var_r_3 := sub(var_x_hi_1, var_x_lo_2)
        }

        function fun_pair_2(var_a_4, var_b_5) -> var_drop_6, var_hi_7, var_lo_8 {
            var_lo_8 := add(var_b_5, 1)
            var_hi_7 := add(var_a_4, var_b_5)
        }
    """
    NESTED_MEMORY_ALIAS_CONFIG = make_model_config(("target",))
    NESTED_MEMORY_ALIAS_LOCAL_YUL = """
        function fun_target_0(var_x_1) -> var_z_2 {
            let usr$base := 0
            let usr$tmp := fun_outer_1(usr$base, var_x_1)
            var_z_2 := mload(usr$tmp)
        }

        function fun_outer_1(var_r_3, var_x_4) -> var_out_5 {
            let expr_self := var_r_3
            var_out_5 := fun_inner_2(expr_self, var_x_4)
        }

        function fun_inner_2(var_r_6, var_x_7) -> var_out_8 {
            mstore(var_r_6, var_x_7)
            var_out_8 := var_r_6
        }
    """
    NESTED_MEMORY_ALIAS_TEMP_YUL = """
        function fun_target_0(var_x_1) -> var_z_2 {
            let usr$base := 0
            let expr_1 := fun_outer_1(usr$base, var_x_1)
            var_z_2 := mload(expr_1)
        }

        function fun_outer_1(var_r_3, var_x_4) -> var_out_5 {
            let expr_self := var_r_3
            var_out_5 := fun_inner_2(expr_self, var_x_4)
        }

        function fun_inner_2(var_r_6, var_x_7) -> var_out_8 {
            mstore(var_r_6, var_x_7)
            var_out_8 := var_r_6
        }
    """
    TOP_LEVEL_MEMORY_READ_HELPER_CONFIG = make_model_config(("target",))
    TOP_LEVEL_MEMORY_READ_HELPER_YUL = """
        function fun_target_0(var_x_1) -> var_z_2 {
            let usr$base := 0
            mstore(usr$base, var_x_1)
            var_z_2 := fun_read_1(usr$base)
        }

        function fun_read_1(var_ptr_2) -> var_out_3 {
            var_out_3 := mload(var_ptr_2)
        }
    """
    FROM_HELPER_CONFIG = make_model_config(("target",))
    FROM_HELPER_YUL = """
        function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
            let usr$ptr := fun_from_1(0, var_x_hi_1, var_x_lo_2)
            var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
        }

        function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
            var_r_out_7 := 0
            mstore(var_r_4, var_x_hi_5)
            mstore(add(0x20, var_r_4), var_x_lo_6)
            var_r_out_7 := var_r_4
        }
    """
    LEAVE_HELPER_CONFIG = make_model_config(("target",))
    LEAVE_HELPER_YUL = """
        function fun_target_1(var_x_1) -> var_z_2 {
            var_z_2 := fun_helper_2(var_x_1)
        }

        function fun_helper_2(var_x_3) -> var_z_4 {
            var_z_4 := 1
            if var_x_3 {
                var_z_4 := 7
                leave
            }
            var_z_4 := 9
        }
    """
    LEAVE_HELPER_DEAD_CODE_YUL = """
        function fun_target_1(var_x_1) -> var_z_2 {
            var_z_2 := fun_helper_2(var_x_1)
        }

        function fun_helper_2(var_x_3) -> var_z_4 {
            var_z_4 := 1
            if var_x_3 {
                var_z_4 := 7
                leave
                var_z_4 := 8
            }
            var_z_4 := 9
        }
    """
    PLAIN_IF_HELPER_CONFIG = make_model_config(("target",))
    PLAIN_IF_HELPER_YUL = """
        function fun_target_1(var_flag_1, var_x_2) -> var_z_3 {
            var_z_3 := fun_helper_2(var_flag_1, var_x_2)
        }

        function fun_helper_2(var_flag_4, var_x_5) -> var_z_6 {
            var_z_6 := var_x_5
            if var_flag_4 {
                var_z_6 := add(var_x_5, 1)
            }
        }
    """
    TOP_LEVEL_LEAVE_CONFIG = make_model_config(("target",))
    TOP_LEVEL_LEAVE_YUL = """
        function fun_target_1(var_x_1) -> var_z_2 {
            var_z_2 := 1
            if var_x_1 {
                var_z_2 := 7
                leave
            }
            var_z_2 := 9
        }
    """
    MULTI_LEAVE_HELPER_CONFIG = make_model_config(("target",))
    MULTI_LEAVE_HELPER_YUL = """
        function fun_target_1(var_a_1, var_b_2) -> var_z_3 {
            var_z_3 := fun_helper_2(var_a_1, var_b_2)
        }

        function fun_helper_2(var_a_4, var_b_5) -> var_z_6 {
            var_z_6 := 1
            if var_a_4 {
                var_z_6 := 7
                leave
            }
            if var_b_5 {
                var_z_6 := 8
                leave
            }
            var_z_6 := 9
        }
    """
    CONDITIONAL_BRANCH_ISOLATION_CONFIG = make_model_config(("f",))
    CONDITIONAL_BRANCH_ISOLATION_YUL = """
        function fun_f_1(var_x_1, var_c_2) -> var_z_3 {
            var_z_3 := 0
            var_x_1 := add(var_x_1, 1)
            switch var_c_2
            case 0 {
                var_z_3 := add(var_x_1, 2)
            }
            default {
                var_x_1 := 7
            }
            var_z_3 := add(var_z_3, var_x_1)
        }
    """
    SEQUENTIAL_CONTROL_FLOW_CONFIG = make_model_config(("f",))
    SEQUENTIAL_CONTROL_FLOW_YUL = """
        function fun_f_1(var_x_1, var_y_2) -> var_z_3 {
            var_z_3 := 1
            if var_x_1 {
                var_z_3 := 5
            }
            switch var_y_2
            case 0 {
                var_z_3 := add(var_z_3, 10)
            }
            default {
                var_z_3 := add(var_z_3, 20)
            }
        }
    """

    def test_validate_function_model_rejects_out_of_scope_var(self) -> None:
        bad_model = ytl.FunctionModel(
            fn_name="bad",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ytl.Assignment(
                    "z",
                    ytl.Call("add", (ytl.Var("x"), ytl.Var("missing"))),
                ),
            ),
        )

        with self.assertRaisesRegex(ytl.ParseError, "out-of-scope"):
            ytl.validate_function_model(bad_model)

    def test_translate_yul_to_models_raw_preserves_zero_and_dead_assignments(
        self,
    ) -> None:
        result = ytl.translate_yul_to_models(
            self.SIMPLE_YUL,
            self.SIMPLE_CONFIG,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(result.pipeline, ytl.RAW_TRANSLATION_PIPELINE)
        assignment_targets: list[str] = [
            stmt.target
            for stmt in model.assignments
            if isinstance(stmt, ytl.Assignment)
        ]
        expected_targets: list[str] = ["tmp", "dead", "z", "z_1"]
        self.assertEqual(assignment_targets, expected_targets)
        self.assertEqual(model.return_names, ("z_1",))

    def test_translate_yul_to_models_defaults_to_optimized_pipeline(self) -> None:
        default_result = ytl.translate_yul_to_models(
            self.SIMPLE_YUL,
            self.SIMPLE_CONFIG,
        )
        explicit_result = ytl.translate_yul_to_models(
            self.SIMPLE_YUL,
            self.SIMPLE_CONFIG,
            pipeline=ytl.OPTIMIZED_TRANSLATION_PIPELINE,
        )

        self.assertEqual(default_result.pipeline, ytl.OPTIMIZED_TRANSLATION_PIPELINE)
        self.assertEqual(default_result.models, explicit_result.models)
        model = default_result.models[0]
        self.assertEqual(
            model.assignments,
            (ytl.Assignment("z_1", ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1)))),),
        )

    def test_render_function_defs_uses_demangled_ssa_names(self) -> None:
        result = ytl.translate_yul_to_models(
            self.SIMPLE_YUL,
            self.SIMPLE_CONFIG,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        rendered = ytl.render_function_defs([model], self.SIMPLE_CONFIG)

        self.assertIn("def model_f_evm (x : Nat) : Nat :=", rendered)
        self.assertIn("let x := u256 x", rendered)
        self.assertIn("let dead := 7", rendered)
        self.assertIn("let z := 0", rendered)
        self.assertIn("let z_1 := evmAdd (x) (1)", rendered)
        self.assertNotIn("usr$tmp", rendered)
        self.assertNotIn("var_z_2", rendered)

    def test_render_function_defs_supports_zero_argument_models(self) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            assignments=(ytl.Assignment("z", ytl.IntLit(1)),),
            param_names=(),
            return_names=("z",),
        )

        rendered = ytl.render_function_defs([model], self.SIMPLE_CONFIG)

        self.assertIn("def model_f_evm : Nat :=", rendered)
        self.assertIn("def model_f : Nat :=", rendered)
        self.assertNotIn("( : Nat)", rendered)

    def test_apply_optional_model_transforms_skips_hoisting_in_raw_pipeline(
        self,
    ) -> None:
        model = ytl.FunctionModel(
            fn_name="outer",
            param_names=("p",),
            return_names=("out",),
            assignments=(
                ytl.Assignment("a", ytl.Call("inner", (ytl.Var("p"),))),
                ytl.Assignment("b", ytl.Call("inner", (ytl.Var("p"),))),
                ytl.Assignment("out", ytl.Call("sub", (ytl.Var("a"), ytl.Var("b")))),
            ),
        )
        config = make_model_config(
            ("inner", "outer"),
            hoist_repeated_calls=frozenset({"outer"}),
        )

        raw_models = ytl.apply_optional_model_transforms(
            [model],
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        optimized_models = ytl.apply_optional_model_transforms(
            [model],
            config,
            pipeline=ytl.OPTIMIZED_TRANSLATION_PIPELINE,
        )

        expected_models: list[ytl.FunctionModel] = [model]
        self.assertEqual(raw_models, expected_models)
        self.assertNotEqual(optimized_models, expected_models)
        first_stmt = optimized_models[0].assignments[0]
        self.assertIsInstance(first_stmt, ytl.Assignment)
        assert isinstance(first_stmt, ytl.Assignment)
        self.assertRegex(first_stmt.target, r"^_cse_\d+$")

    def test_multi_return_rebinding_keeps_old_argument_binding_for_later_components(
        self,
    ) -> None:
        result = ytl.translate_yul_to_models(
            self.MULTI_RETURN_REBIND_YUL,
            self.MULTI_RETURN_REBIND_CONFIG,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        assignments = [
            stmt for stmt in model.assignments if isinstance(stmt, ytl.Assignment)
        ]
        self.assertEqual(len(assignments), 3)
        x_lo_update, x_hi_update, _ = assignments

        self.assertNotIn(
            x_lo_update.target,
            ytl._expr_vars(x_hi_update.expr),
            "later rebound component unexpectedly captured the already-updated "
            "argument value instead of the pre-call binding",
        )

    def test_multi_return_rebinding_matches_simultaneous_assignment_semantics(
        self,
    ) -> None:
        result = ytl.translate_yul_to_models(
            self.MULTI_RETURN_REBIND_YUL,
            self.MULTI_RETURN_REBIND_CONFIG,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        for x_hi, x_lo in ((7, 11), (0, 3), (123, 0), (ytl.WORD_MOD - 1, 9)):
            with self.subTest(x_hi=x_hi, x_lo=x_lo):
                actual = ytl.evaluate_function_model(model, (x_hi, x_lo))
                expected = ((x_hi - 1) % ytl.WORD_MOD,)
                self.assertEqual(actual, expected)

    def test_ssa_renaming_rejects_collision_with_other_demangled_name(self) -> None:
        yf = ytl.YulFunction(
            yul_name="f",
            params=["var_x_1"],
            rets=["var_z_2"],
            assignments=[
                ytl.PlainAssignment(
                    "var_x_1", ytl.Call("add", (ytl.Var("var_x_1"), ytl.IntLit(1)))
                ),
                ytl.PlainAssignment("usr$x_1", ytl.IntLit(7)),
                ytl.PlainAssignment("var_z_2", ytl.Var("usr$x_1")),
            ],
        )

        with self.assertRaisesRegex(ytl.ParseError, "collides with the demangled name"):
            ytl.yul_function_to_model(yf, "f", {})

    def test_ssa_renaming_avoids_reuse_after_conditional_reset(self) -> None:
        yul = """
            function fun_f_1(var_x_1, var_c_2) -> var_z_3 {
                var_z_3 := add(var_x_1, 1)
                var_z_3 := add(var_z_3, var_x_1)
                switch var_c_2
                case 0 {
                    var_z_3 := mul(var_z_3, 2)
                }
                default {
                    var_z_3 := mul(var_z_3, 3)
                    var_x_1 := add(var_x_1, 2)
                }
                var_z_3 := add(var_z_3, var_x_1)
            }
        """
        config = make_model_config(("f",))
        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        # Check no duplicate targets in straight-line assignments.
        targets: list[str] = []
        for stmt in model.assignments:
            if isinstance(stmt, ytl.Assignment):
                targets.append(stmt.target)
        self.assertEqual(
            len(targets), len(set(targets)), f"duplicate targets: {targets}"
        )

        # f(10, 0): z = add(10,1) = 11; z = add(11,10) = 21;
        #   case 0: z = mul(21,2) = 42; z = add(42,10) = 52 => but x unchanged
        #   continuation: z = add(42, 10) = 52  ...wait let me compute carefully
        # Actually, after switch, var_z_3 and var_x_1 are modified by
        # the conditional block.  For c=0: z=21*2=42, x=10; z=42+10=52
        # For c=1: z=21*3=63, x=10+2=12; z=63+12=75
        self.assertEqual(ytl.evaluate_function_model(model, (10, 0)), (52,))
        self.assertEqual(ytl.evaluate_function_model(model, (10, 1)), (75,))

    def test_translate_yul_to_models_rejects_nested_helper_memory_write_through_local(
        self,
    ) -> None:
        with self.assertRaisesRegex(
            ytl.ParseError,
            "helper memory writes are unsupported",
        ):
            ytl.translate_yul_to_models(
                self.NESTED_MEMORY_ALIAS_LOCAL_YUL,
                self.NESTED_MEMORY_ALIAS_CONFIG,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_nested_helper_memory_write_through_temp(
        self,
    ) -> None:
        with self.assertRaisesRegex(
            ytl.ParseError,
            "helper memory writes are unsupported",
        ):
            ytl.translate_yul_to_models(
                self.NESTED_MEMORY_ALIAS_TEMP_YUL,
                self.NESTED_MEMORY_ALIAS_CONFIG,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_allows_top_level_memory_write_with_helper_mload(
        self,
    ) -> None:
        result = ytl.translate_yul_to_models(
            self.TOP_LEVEL_MEMORY_READ_HELPER_YUL,
            self.TOP_LEVEL_MEMORY_READ_HELPER_CONFIG,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        for x in (0, 1, 7, 32, ytl.WORD_MOD - 1):
            with self.subTest(x=x):
                self.assertEqual(
                    ytl.evaluate_function_model(model, (x,)),
                    (x,),
                )

    def test_translate_yul_to_models_allows_exact_from_helper(
        self,
    ) -> None:
        result = ytl.translate_yul_to_models(
            self.FROM_HELPER_YUL,
            self.FROM_HELPER_CONFIG,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        cases = {
            (0, 0): (0,),
            (1, 0): (1,),
            (0, 7): (7,),
            (5, 11): (16,),
            (ytl.WORD_MOD - 1, 3): (2,),
        }
        for args, expected in cases.items():
            with self.subTest(args=args):
                self.assertEqual(
                    ytl.evaluate_function_model(model, args),
                    expected,
                )

    def test_translate_yul_to_models_lowers_inlined_leave(self) -> None:
        result = ytl.translate_yul_to_models(
            self.LEAVE_HELPER_YUL,
            self.LEAVE_HELPER_CONFIG,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (9,))
        self.assertEqual(ytl.evaluate_function_model(model, (1,)), (7,))
        self.assertEqual(ytl.evaluate_function_model(model, (ytl.WORD_MOD - 1,)), (7,))

    def test_translate_yul_to_models_ignores_dead_code_after_inlined_leave(
        self,
    ) -> None:
        result = ytl.translate_yul_to_models(
            self.LEAVE_HELPER_DEAD_CODE_YUL,
            self.LEAVE_HELPER_CONFIG,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (9,))
        self.assertEqual(ytl.evaluate_function_model(model, (1,)), (7,))

    def test_translate_yul_to_models_lowers_plain_inlined_if(self) -> None:
        result = ytl.translate_yul_to_models(
            self.PLAIN_IF_HELPER_YUL,
            self.PLAIN_IF_HELPER_CONFIG,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (0, 5)), (5,))
        self.assertEqual(ytl.evaluate_function_model(model, (1, 5)), (6,))
        self.assertEqual(
            ytl.evaluate_function_model(model, (ytl.WORD_MOD - 1, 5)),
            (6,),
        )

    def test_translate_yul_to_models_rejects_top_level_leave(
        self,
    ) -> None:
        with self.assertRaisesRegex(
            ytl.ParseError,
            "contains 'leave' in direct model generation",
        ):
            ytl.translate_yul_to_models(
                self.TOP_LEVEL_LEAVE_YUL,
                self.TOP_LEVEL_LEAVE_CONFIG,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_multiple_inlined_leave_sites(
        self,
    ) -> None:
        with self.assertRaisesRegex(
            ytl.ParseError,
            "contains multiple leave sites",
        ):
            ytl.translate_yul_to_models(
                self.MULTI_LEAVE_HELPER_YUL,
                self.MULTI_LEAVE_HELPER_CONFIG,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_isolates_conditional_branch_state(
        self,
    ) -> None:
        result = ytl.translate_yul_to_models(
            self.CONDITIONAL_BRANCH_ISOLATION_YUL,
            self.CONDITIONAL_BRANCH_ISOLATION_CONFIG,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        cases = {
            (0, 0): (4,),
            (5, 0): (14,),
            (0, 1): (7,),
            (5, 1): (7,),
        }
        for args, expected in cases.items():
            with self.subTest(args=args):
                self.assertEqual(
                    ytl.evaluate_function_model(model, args),
                    expected,
                )

    def test_translate_yul_to_models_handles_sequential_if_and_switch_scoping(
        self,
    ) -> None:
        result = ytl.translate_yul_to_models(
            self.SEQUENTIAL_CONTROL_FLOW_YUL,
            self.SEQUENTIAL_CONTROL_FLOW_CONFIG,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        cases = {
            (0, 0): (11,),
            (1, 0): (15,),
            (0, 1): (21,),
            (1, 1): (25,),
        }
        for args, expected in cases.items():
            with self.subTest(args=args):
                self.assertEqual(
                    ytl.evaluate_function_model(model, args),
                    expected,
                )


class ExplicitMemoryModelTest(unittest.TestCase):
    def test_yul_function_to_model_resolves_sequential_memory_slots(self) -> None:
        yf = ytl.YulFunction(
            yul_name="f",
            params=["var_x_1"],
            rets=["var_z_2"],
            assignments=[
                ytl.PlainAssignment("usr$base", ytl.IntLit(0)),
                ytl.PlainAssignment("usr$offset", ytl.IntLit(32)),
                ytl.MemoryWrite(ytl.Var("usr$base"), ytl.Var("var_x_1")),
                ytl.MemoryWrite(
                    ytl.Call("add", (ytl.Var("usr$base"), ytl.Var("usr$offset"))),
                    ytl.Call("mload", (ytl.Var("usr$base"),)),
                ),
                ytl.PlainAssignment(
                    "var_z_2",
                    ytl.Call(
                        "mload",
                        (
                            ytl.Call(
                                "add", (ytl.Var("usr$base"), ytl.Var("usr$offset"))
                            ),
                        ),
                    ),
                ),
            ],
        )

        model = ytl.yul_function_to_model(yf, "f", {})

        self.assertEqual(
            model.assignments,
            (
                ytl.Assignment("base", ytl.IntLit(0)),
                ytl.Assignment("offset", ytl.IntLit(32)),
                ytl.Assignment("z", ytl.Var("x")),
            ),
        )
        self.assertEqual(model.return_names, ("z",))

    def test_yul_function_to_model_rejects_duplicate_memory_address(self) -> None:
        yf = ytl.YulFunction(
            yul_name="f",
            params=["var_x_1"],
            rets=["var_z_2"],
            assignments=[
                ytl.PlainAssignment("usr$base", ytl.IntLit(0)),
                ytl.MemoryWrite(ytl.Var("usr$base"), ytl.Var("var_x_1")),
                ytl.MemoryWrite(ytl.Var("usr$base"), ytl.Var("var_x_1")),
                ytl.PlainAssignment("var_z_2", ytl.Var("var_x_1")),
            ],
        )

        with self.assertRaisesRegex(ytl.ParseError, "Multiple mstore writes"):
            ytl.yul_function_to_model(yf, "f", {})

    def test_yul_function_to_model_rejects_missing_memory_store(self) -> None:
        yf = ytl.YulFunction(
            yul_name="f",
            params=["var_x_1"],
            rets=["var_z_2"],
            assignments=[
                ytl.PlainAssignment("usr$base", ytl.IntLit(0)),
                ytl.PlainAssignment(
                    "var_z_2", ytl.Call("mload", (ytl.Var("usr$base"),))
                ),
            ],
        )

        with self.assertRaisesRegex(ytl.ParseError, "matching prior mstore"):
            ytl.yul_function_to_model(yf, "f", {})

    def test_yul_function_to_model_rejects_non_constant_memory_address(self) -> None:
        yf = ytl.YulFunction(
            yul_name="f",
            params=["var_x_1"],
            rets=["var_z_2"],
            assignments=[
                ytl.MemoryWrite(ytl.Var("var_x_1"), ytl.IntLit(7)),
                ytl.PlainAssignment("var_z_2", ytl.IntLit(0)),
            ],
        )

        with self.assertRaisesRegex(ytl.ParseError, "non-constant address"):
            ytl.yul_function_to_model(yf, "f", {})

    def test_yul_function_to_model_rejects_unaligned_memory_store(self) -> None:
        yf = ytl.YulFunction(
            yul_name="f",
            params=["var_x_1"],
            rets=["var_z_2"],
            assignments=[
                ytl.MemoryWrite(ytl.IntLit(1), ytl.Var("var_x_1")),
                ytl.PlainAssignment("var_z_2", ytl.IntLit(0)),
            ],
        )

        with self.assertRaisesRegex(ytl.ParseError, "unaligned address 1"):
            ytl.yul_function_to_model(yf, "f", {})

    def test_yul_function_to_model_rejects_unaligned_memory_load(self) -> None:
        yf = ytl.YulFunction(
            yul_name="f",
            params=["var_x_1"],
            rets=["var_z_2"],
            assignments=[
                ytl.MemoryWrite(ytl.IntLit(0), ytl.Var("var_x_1")),
                ytl.PlainAssignment("var_z_2", ytl.Call("mload", (ytl.IntLit(1),))),
            ],
        )

        with self.assertRaisesRegex(ytl.ParseError, "unaligned address 1"):
            ytl.yul_function_to_model(yf, "f", {})


class RestrictedIRInterpreterTest(ModelEquivalenceTestCase):
    def test_evaluate_function_model_preserves_passthrough_when_if_is_false(
        self,
    ) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("out",),
            assignments=(
                ytl.Assignment("out", ytl.Call("add", (ytl.Var("x"), ytl.IntLit(5)))),
                ytl.ConditionalBlock(
                    condition=ytl.IntLit(0),
                    output_vars=("out",),
                    then_branch=branch(
                        (ytl.Assignment("out", ytl.IntLit(99)),),
                        ("out",),
                    ),
                    else_branch=branch((), ("out",)),
                ),
            ),
        )

        result = ytl.evaluate_function_model(model, (7,))

        self.assertEqual(result, (12,))

    def test_validate_function_model_rejects_undefined_conditional_branch_output(
        self,
    ) -> None:
        bad_model = ytl.FunctionModel(
            fn_name="bad_cond",
            param_names=("x",),
            return_names=("out",),
            assignments=(
                ytl.ConditionalBlock(
                    condition=ytl.Var("x"),
                    output_vars=("tmp",),
                    then_branch=branch((), ("missing",)),
                    else_branch=branch((), ("x",)),
                ),
                ytl.Assignment("out", ytl.Var("tmp")),
            ),
        )

        with self.assertRaisesRegex(ytl.ParseError, "undefined then-branch outputs"):
            ytl.validate_function_model(bad_model)

    def test_evaluate_function_model_supports_multi_return_projection(self) -> None:
        pair = ytl.FunctionModel(
            fn_name="pair",
            param_names=("x", "y"),
            return_names=("a", "b"),
            assignments=(
                ytl.Assignment("a", ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1)))),
                ytl.Assignment("b", ytl.Call("mul", (ytl.Var("y"), ytl.IntLit(2)))),
            ),
        )
        outer = ytl.FunctionModel(
            fn_name="outer",
            param_names=("x", "y"),
            return_names=("out",),
            assignments=(
                ytl.Assignment(
                    "lhs",
                    ytl.Call(
                        "__component_0_2",
                        (ytl.Call("pair", (ytl.Var("x"), ytl.Var("y"))),),
                    ),
                ),
                ytl.Assignment(
                    "rhs",
                    ytl.Call(
                        "__component_1_2",
                        (ytl.Call("pair", (ytl.Var("x"), ytl.Var("y"))),),
                    ),
                ),
                ytl.Assignment(
                    "out", ytl.Call("add", (ytl.Var("lhs"), ytl.Var("rhs")))
                ),
            ),
        )
        table = ytl.build_model_table([pair, outer])

        result = ytl.evaluate_function_model(outer, (3, 5), model_table=table)

        self.assertEqual(result, (14,))

    def test_evaluate_function_model_rejects_recursive_model_call_cycle(self) -> None:
        model = ytl.FunctionModel(
            fn_name="loop",
            param_names=("x",),
            return_names=("out",),
            assignments=(ytl.Assignment("out", ytl.Call("loop", (ytl.Var("x"),))),),
        )

        with self.assertRaisesRegex(ytl.EvaluationError, "Recursive model call cycle"):
            ytl.evaluate_function_model(
                model,
                (1,),
                model_table=ytl.build_model_table([model]),
            )


class ModelEquivalenceFuzzerTest(ModelEquivalenceTestCase):
    UNARY_OPS = ("not", "clz")
    BINARY_OPS = (
        "add",
        "sub",
        "mul",
        "div",
        "mod",
        "and",
        "or",
        "eq",
        "lt",
        "gt",
        "shl",
        "shr",
    )
    TERNARY_OPS = ("mulmod",)

    def _random_scalar(self, rng: random.Random) -> int:
        if rng.random() < 0.7:
            return rng.choice(self.INTERESTING_VALUES)
        return rng.getrandbits(320)

    def _random_expr(
        self,
        rng: random.Random,
        available: tuple[str, ...],
        *,
        depth: int,
    ) -> ytl.Expr:
        if depth <= 0 or rng.random() < 0.3:
            if available and rng.random() < 0.6:
                return ytl.Var(rng.choice(available))
            return ytl.IntLit(self._random_scalar(rng))

        kind = rng.random()
        if kind < 0.2 and available:
            return ytl.Var(rng.choice(available))
        if kind < 0.35:
            return ytl.IntLit(self._random_scalar(rng))
        if kind < 0.55:
            op = rng.choice(self.UNARY_OPS)
            return ytl.Call(
                op,
                (self._random_expr(rng, available, depth=depth - 1),),
            )
        if kind < 0.9:
            op = rng.choice(self.BINARY_OPS)
            return ytl.Call(
                op,
                (
                    self._random_expr(rng, available, depth=depth - 1),
                    self._random_expr(rng, available, depth=depth - 1),
                ),
            )
        op = rng.choice(self.TERNARY_OPS)
        return ytl.Call(
            op,
            (
                self._random_expr(rng, available, depth=depth - 1),
                self._random_expr(rng, available, depth=depth - 1),
                self._random_expr(rng, available, depth=depth - 1),
            ),
        )

    def _build_random_dce_model(self, seed: int) -> ytl.FunctionModel:
        rng = random.Random(seed)
        params = ("p0", "p1", "p2")
        assignments: list[ytl.ModelStatement] = []
        outer_scope = list(params)
        mutable_scope: list[str] = []
        next_idx = 0

        def new_name(prefix: str) -> str:
            nonlocal next_idx
            next_idx += 1
            return f"{prefix}_{seed}_{next_idx}"

        for _ in range(2):
            name = new_name("v")
            assignments.append(
                ytl.Assignment(
                    name, self._random_expr(rng, tuple(outer_scope), depth=2)
                )
            )
            outer_scope.append(name)
            mutable_scope.append(name)

        for _ in range(rng.randint(5, 8)):
            if mutable_scope and rng.random() < 0.45:
                modified = tuple(
                    rng.sample(
                        mutable_scope, k=rng.randint(1, min(2, len(mutable_scope)))
                    )
                )
                then_assignments: list[ytl.Assignment] = []
                else_assignments: list[ytl.Assignment] | None = (
                    [] if rng.random() < 0.65 else None
                )

                if rng.random() < 0.35:
                    then_assignments.append(
                        ytl.Assignment(
                            new_name("then_dead"),
                            self._random_expr(rng, tuple(outer_scope), depth=2),
                        )
                    )

                for target in modified:
                    then_assignments.append(
                        ytl.Assignment(
                            target,
                            self._random_expr(rng, tuple(outer_scope), depth=3),
                        )
                    )

                if else_assignments is not None:
                    if rng.random() < 0.35:
                        else_assignments.append(
                            ytl.Assignment(
                                new_name("else_dead"),
                                self._random_expr(rng, tuple(outer_scope), depth=2),
                            )
                        )
                    assigned_else = False
                    for target in modified:
                        if rng.random() < 0.65:
                            else_assignments.append(
                                ytl.Assignment(
                                    target,
                                    self._random_expr(rng, tuple(outer_scope), depth=3),
                                )
                            )
                            assigned_else = True
                    if not assigned_else and rng.random() < 0.5:
                        else_assignments = None

                assignments.append(
                    ytl.ConditionalBlock(
                        condition=self._random_expr(rng, tuple(outer_scope), depth=2),
                        output_vars=modified,
                        then_branch=branch(tuple(then_assignments), modified),
                        else_branch=branch(
                            (
                                tuple(else_assignments)
                                if else_assignments is not None
                                else ()
                            ),
                            modified,
                        ),
                    )
                )
                continue

            if rng.random() < 0.35 and mutable_scope:
                target = rng.choice(mutable_scope)
            else:
                target = new_name("v")
            assignments.append(
                ytl.Assignment(
                    target,
                    self._random_expr(rng, tuple(outer_scope), depth=3),
                )
            )
            if target not in outer_scope:
                outer_scope.append(target)
                mutable_scope.append(target)

            if rng.random() < 0.25:
                dead_name = new_name("dead")
                assignments.append(
                    ytl.Assignment(
                        dead_name,
                        self._random_expr(rng, tuple(outer_scope), depth=2),
                    )
                )
                outer_scope.append(dead_name)
                mutable_scope.append(dead_name)

        return_pool = tuple(outer_scope)
        return_count = min(2 if rng.random() < 0.35 else 1, len(return_pool))
        return_names = tuple(rng.sample(return_pool, k=return_count))
        model = ytl.FunctionModel(
            fn_name=f"random_dce_{seed}",
            param_names=params,
            return_names=return_names,
            assignments=tuple(assignments),
        )
        ytl.validate_function_model(model)
        return model

    def _build_random_cse_suite(
        self,
        seed: int,
    ) -> tuple[dict[str, ytl.FunctionModel], ytl.FunctionModel]:
        rng = random.Random(seed)
        c1 = self._random_scalar(rng)
        c2 = self._random_scalar(rng)
        threshold = self._random_scalar(rng)

        inner_square = ytl.FunctionModel(
            fn_name="inner_square",
            param_names=("x",),
            return_names=("ret",),
            assignments=(
                ytl.Assignment(
                    "ret",
                    ytl.Call(
                        "add",
                        (
                            ytl.Call("mul", (ytl.Var("x"), ytl.Var("x"))),
                            ytl.IntLit(c1),
                        ),
                    ),
                ),
            ),
        )
        inner_mix = ytl.FunctionModel(
            fn_name="inner_mix",
            param_names=("x", "y"),
            return_names=("ret",),
            assignments=(
                ytl.Assignment(
                    "ret",
                    ytl.Call(
                        "add",
                        (
                            ytl.Call("or", (ytl.Var("x"), ytl.Var("y"))),
                            ytl.Call("and", (ytl.Var("x"), ytl.IntLit(c2))),
                        ),
                    ),
                ),
            ),
        )

        cond_threshold = ytl.IntLit(threshold)
        global_call = ytl.Call("inner_square", (ytl.Var("p"),))
        global_pair_call = ytl.Call("inner_mix", (ytl.Var("p"), ytl.Var("q")))
        local_call = ytl.Call("inner_mix", (ytl.Var("base"), ytl.Var("q")))
        outer = ytl.FunctionModel(
            fn_name=f"outer_{seed}",
            param_names=("p", "q"),
            return_names=("out",),
            assignments=(
                ytl.Assignment("base", self._random_expr(rng, ("p", "q"), depth=2)),
                ytl.Assignment(
                    "acc",
                    ytl.Call(
                        "add",
                        (
                            global_call,
                            global_call,
                        ),
                    ),
                ),
                ytl.ConditionalBlock(
                    condition=ytl.Call("gt", (ytl.Var("p"), cond_threshold)),
                    output_vars=("tmp", "acc"),
                    then_branch=branch(
                        (
                            ytl.Assignment(
                                "tmp",
                                ytl.Call("sub", (local_call, local_call)),
                            ),
                            ytl.Assignment(
                                "acc",
                                ytl.Call("add", (ytl.Var("acc"), global_pair_call)),
                            ),
                        ),
                        ("tmp", "acc"),
                    ),
                    else_branch=branch(
                        (
                            ytl.Assignment(
                                "tmp",
                                ytl.Call("add", (global_call, global_pair_call)),
                            ),
                        ),
                        ("tmp", "acc"),
                    ),
                ),
                ytl.Assignment(
                    "out",
                    ytl.Call("add", (ytl.Var("acc"), ytl.Var("tmp"))),
                ),
            ),
        )

        helpers = ytl.build_model_table([inner_square, inner_mix])
        ytl.validate_function_model(outer)
        return helpers, outer

    def test_prune_dead_assignments_is_semantics_preserving(self) -> None:
        before = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("out",),
            assignments=(
                ytl.Assignment("dead", ytl.Call("add", (ytl.Var("x"), ytl.IntLit(9)))),
                ytl.Assignment("live", ytl.Call("mul", (ytl.Var("x"), ytl.IntLit(3)))),
                ytl.Assignment(
                    "out", ytl.Call("sub", (ytl.Var("live"), ytl.IntLit(1)))
                ),
            ),
        )

        after = ytl._prune_dead_assignments(before)

        self.assertModelsEquivalent(before, after, seed=19)

    def test_prune_dead_assignments_preserves_if_passthrough_inputs(self) -> None:
        before = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("out",),
            assignments=(
                ytl.Assignment("tmp", ytl.IntLit(0)),
                ytl.ConditionalBlock(
                    condition=ytl.Call("gt", (ytl.Var("x"), ytl.IntLit(10))),
                    output_vars=("tmp",),
                    then_branch=branch(
                        (
                            ytl.Assignment(
                                "tmp", ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1)))
                            ),
                        ),
                        ("tmp",),
                    ),
                    else_branch=branch((), ("tmp",)),
                ),
                ytl.Assignment("out", ytl.Call("add", (ytl.Var("tmp"), ytl.IntLit(1)))),
            ),
        )

        after = ytl._prune_dead_assignments(before)

        ytl.validate_function_model(after)
        self.assertModelsEquivalent(before, after, seed=21)

    def test_hoist_repeated_model_calls_is_semantics_preserving(self) -> None:
        inner = ytl.FunctionModel(
            fn_name="inner",
            param_names=("p",),
            return_names=("ret",),
            assignments=(
                ytl.Assignment(
                    "ret",
                    ytl.Call(
                        "add",
                        (ytl.Call("mul", (ytl.Var("p"), ytl.Var("p"))), ytl.IntLit(1)),
                    ),
                ),
            ),
        )
        outer = ytl.FunctionModel(
            fn_name="outer",
            param_names=("p",),
            return_names=("out",),
            assignments=(
                ytl.Assignment("a", ytl.Call("inner", (ytl.Var("p"),))),
                ytl.Assignment("b", ytl.Call("inner", (ytl.Var("p"),))),
                ytl.Assignment("out", ytl.Call("sub", (ytl.Var("b"), ytl.Var("a")))),
            ),
        )

        transformed = ytl.hoist_repeated_model_calls(
            outer,
            model_call_names=frozenset({"inner"}),
        )

        self.assertModelsEquivalent(
            outer,
            transformed,
            before_table=ytl.build_model_table([inner, outer]),
            after_table=ytl.build_model_table([inner, transformed]),
            seed=23,
        )

    def test_randomized_dead_assignment_pruning_family(self) -> None:
        for seed in range(16):
            before = self._build_random_dce_model(seed)
            after = ytl._prune_dead_assignments(before)

            ytl.validate_function_model(after)
            self.assertModelsEquivalent(
                before,
                after,
                seed=1000 + seed,
                random_cases=96,
            )

    def test_randomized_hoist_repeated_model_calls_family(self) -> None:
        for seed in range(16):
            helper_table, before = self._build_random_cse_suite(seed)
            transformed = ytl.hoist_repeated_model_calls(
                before,
                model_call_names=frozenset(helper_table),
            )

            ytl.validate_function_model(transformed)
            self.assertModelsEquivalent(
                before,
                transformed,
                before_table={**helper_table, before.fn_name: before},
                after_table={**helper_table, before.fn_name: transformed},
                seed=2000 + seed,
                random_cases=96,
            )

    def test_raw_and_optimized_pipelines_are_semantics_equivalent(self) -> None:
        yul = """
            function fun_inner_1(var_x_1) -> var_z_2 {
                var_z_2 := add(var_x_1, 9)
            }

            function fun_outer_2(var_x_1) -> var_z_2 {
                let usr$tmp := 0
                let usr$dead := add(var_x_1, 99)
                let usr$a := fun_inner_1(var_x_1)
                let usr$b := fun_inner_1(var_x_1)
                if gt(var_x_1, 10) {
                    usr$tmp := add(usr$a, usr$b)
                }
                var_z_2 := add(usr$tmp, 1)
            }
        """
        config = make_model_config(
            ("inner", "outer"),
            hoist_repeated_calls=frozenset({"outer"}),
        )

        raw_result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        optimized_result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.OPTIMIZED_TRANSLATION_PIPELINE,
        )

        raw_table = ytl.build_model_table(raw_result.models)
        optimized_table = ytl.build_model_table(optimized_result.models)
        self.assertModelsEquivalent(
            raw_table["inner"],
            optimized_table["inner"],
            before_table=raw_table,
            after_table=optimized_table,
            seed=29,
        )
        self.assertModelsEquivalent(
            raw_table["outer"],
            optimized_table["outer"],
            before_table=raw_table,
            after_table=optimized_table,
            seed=31,
        )

    def test_randomized_translated_pipeline_equivalence_family(self) -> None:
        config = make_model_config(
            ("inner", "outer"),
            hoist_repeated_calls=frozenset({"outer"}),
        )

        for seed in range(12):
            bias = self.INTERESTING_VALUES[seed % len(self.INTERESTING_VALUES)]
            threshold = self.INTERESTING_VALUES[
                (seed + 4) % len(self.INTERESTING_VALUES)
            ]
            tweak = self.INTERESTING_VALUES[(seed + 9) % len(self.INTERESTING_VALUES)]
            yul = f"""
                function fun_inner_1(var_x_1) -> var_z_2 {{
                    var_z_2 := add(mul(var_x_1, var_x_1), {bias})
                }}

                function fun_outer_2(var_x_1) -> var_z_2 {{
                    let usr$tmp := 0
                    let usr$dead := add(var_x_1, {tweak})
                    let usr$lhs := fun_inner_1(var_x_1)
                    let usr$rhs := fun_inner_1(var_x_1)
                    if gt(var_x_1, {threshold}) {{
                        usr$tmp := add(usr$lhs, usr$rhs)
                    }}
                    switch and(var_x_1, 1)
                    case 0 {{
                        usr$lhs := sub(usr$tmp, {bias})
                    }}
                    default {{
                        usr$lhs := add(usr$tmp, {tweak})
                    }}
                    var_z_2 := add(usr$lhs, 1)
                }}
            """

            raw_result = ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )
            optimized_result = ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.OPTIMIZED_TRANSLATION_PIPELINE,
            )

            raw_table = ytl.build_model_table(raw_result.models)
            optimized_table = ytl.build_model_table(optimized_result.models)
            self.assertModelsEquivalent(
                raw_table["inner"],
                optimized_table["inner"],
                before_table=raw_table,
                after_table=optimized_table,
                seed=3000 + seed,
                random_cases=96,
            )
            self.assertModelsEquivalent(
                raw_table["outer"],
                optimized_table["outer"],
                before_table=raw_table,
                after_table=optimized_table,
                seed=4000 + seed,
                random_cases=96,
            )


# ---------------------------------------------------------------------------
# Step 1 tests: _try_const_eval delegation to _eval_builtin
# ---------------------------------------------------------------------------


class TryConstEvalTest(unittest.TestCase):
    def test_try_const_eval_folds_all_builtin_ops(self) -> None:
        # mul
        self.assertEqual(
            ytl._try_const_eval(ytl.Call("mul", (ytl.IntLit(3), ytl.IntLit(7)))),
            21,
        )
        # div
        self.assertEqual(
            ytl._try_const_eval(ytl.Call("div", (ytl.IntLit(20), ytl.IntLit(3)))),
            6,
        )
        # mod
        self.assertEqual(
            ytl._try_const_eval(ytl.Call("mod", (ytl.IntLit(10), ytl.IntLit(3)))),
            1,
        )
        # not
        self.assertEqual(
            ytl._try_const_eval(ytl.Call("not", (ytl.IntLit(0),))),
            ytl.WORD_MOD - 1,
        )
        # shl
        self.assertEqual(
            ytl._try_const_eval(ytl.Call("shl", (ytl.IntLit(8), ytl.IntLit(1)))),
            256,
        )
        # shr
        self.assertEqual(
            ytl._try_const_eval(ytl.Call("shr", (ytl.IntLit(4), ytl.IntLit(256)))),
            16,
        )
        # eq
        self.assertEqual(
            ytl._try_const_eval(ytl.Call("eq", (ytl.IntLit(5), ytl.IntLit(5)))),
            1,
        )
        # lt
        self.assertEqual(
            ytl._try_const_eval(ytl.Call("lt", (ytl.IntLit(3), ytl.IntLit(7)))),
            1,
        )
        # gt
        self.assertEqual(
            ytl._try_const_eval(ytl.Call("gt", (ytl.IntLit(7), ytl.IntLit(3)))),
            1,
        )
        # and / or
        self.assertEqual(
            ytl._try_const_eval(ytl.Call("and", (ytl.IntLit(0xFF), ytl.IntLit(0x0F)))),
            0x0F,
        )
        self.assertEqual(
            ytl._try_const_eval(ytl.Call("or", (ytl.IntLit(0xF0), ytl.IntLit(0x0F)))),
            0xFF,
        )
        # clz
        self.assertEqual(
            ytl._try_const_eval(ytl.Call("clz", (ytl.IntLit(1),))),
            255,
        )
        # mulmod
        self.assertEqual(
            ytl._try_const_eval(
                ytl.Call("mulmod", (ytl.IntLit(3), ytl.IntLit(5), ytl.IntLit(7)))
            ),
            1,
        )

    def test_try_const_eval_returns_none_for_variables(self) -> None:
        self.assertIsNone(ytl._try_const_eval(ytl.Var("x")))
        self.assertIsNone(
            ytl._try_const_eval(ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1))))
        )
        self.assertIsNone(
            ytl._try_const_eval(ytl.Call("mul", (ytl.IntLit(2), ytl.Var("y"))))
        )

    def test_ite_constant_condition_folds(self) -> None:
        # __ite(1, 5, 3) → 5 (true branch)
        self.assertEqual(
            ytl._try_const_eval(
                ytl.Call("__ite", (ytl.IntLit(1), ytl.IntLit(5), ytl.IntLit(3)))
            ),
            5,
        )
        # __ite(0, 5, 3) → 3 (false branch)
        self.assertEqual(
            ytl._try_const_eval(
                ytl.Call("__ite", (ytl.IntLit(0), ytl.IntLit(5), ytl.IntLit(3)))
            ),
            3,
        )

    def test_ite_constant_condition_nonconstant_branch(self) -> None:
        # __ite(1, Var("x"), 3) → None (selected branch is non-constant)
        self.assertIsNone(
            ytl._try_const_eval(
                ytl.Call("__ite", (ytl.IntLit(1), ytl.Var("x"), ytl.IntLit(3)))
            )
        )
        # __ite(0, 5, Var("x")) → None (selected branch is non-constant)
        self.assertIsNone(
            ytl._try_const_eval(
                ytl.Call("__ite", (ytl.IntLit(0), ytl.IntLit(5), ytl.Var("x")))
            )
        )

    def test_ite_nonconstant_dead_branch_still_folds(self) -> None:
        # __ite(1, 5, Var("x")) → 5 (dead else-branch is non-constant)
        self.assertEqual(
            ytl._try_const_eval(
                ytl.Call("__ite", (ytl.IntLit(1), ytl.IntLit(5), ytl.Var("x")))
            ),
            5,
        )
        # __ite(0, Var("x"), 3) → 3 (dead then-branch is non-constant)
        self.assertEqual(
            ytl._try_const_eval(
                ytl.Call("__ite", (ytl.IntLit(0), ytl.Var("x"), ytl.IntLit(3)))
            ),
            3,
        )
        # __ite(42, 10, Var("y")) → 10 (non-zero condition, dead branch has variable)
        self.assertEqual(
            ytl._try_const_eval(
                ytl.Call("__ite", (ytl.IntLit(42), ytl.IntLit(10), ytl.Var("y")))
            ),
            10,
        )

    def test_op_to_lean_helper_keys_match_op_to_opcode(self) -> None:
        lean_helpers: dict[str, str] = ytl.OP_TO_LEAN_HELPER
        opcodes: dict[str, str] = ytl.OP_TO_OPCODE
        lean_helper_keys: list[str] = sorted(lean_helpers)
        opcode_keys: list[str] = sorted(opcodes)
        self.assertEqual(lean_helper_keys, opcode_keys)

    def test_op_to_lean_helper_keys_match_base_norm_helpers(self) -> None:
        lean_helper_keys: list[str] = sorted(ytl.OP_TO_LEAN_HELPER)
        norm_helper_keys: list[str] = sorted(ytl._BASE_NORM_HELPERS)
        self.assertEqual(lean_helper_keys, norm_helper_keys)


# ---------------------------------------------------------------------------
# Step 1b tests: _simplify_ite constant-condition elimination
# ---------------------------------------------------------------------------


def _expr_contains_ite(expr: ytl.Expr) -> bool:
    """Return True if *expr* contains any ``__ite`` Call node."""
    if isinstance(expr, ytl.Call):
        if expr.name == "__ite":
            return True
        return any(_expr_contains_ite(arg) for arg in expr.args)
    return False


def _model_contains_ite(model: ytl.FunctionModel) -> bool:
    """Return True if any expression in *model* contains an ``__ite`` node."""
    for stmt in model.assignments:
        if isinstance(stmt, ytl.Assignment):
            if _expr_contains_ite(stmt.expr):
                return True
        elif isinstance(stmt, ytl.ConditionalBlock):
            if _expr_contains_ite(stmt.condition):
                return True
            for a in stmt.then_branch.assignments:
                if _expr_contains_ite(a.expr):
                    return True
            for a in stmt.else_branch.assignments:
                if _expr_contains_ite(a.expr):
                    return True
    return False


class SimplifyIteTest(unittest.TestCase):
    """Tests for _simplify_ite and its effect on inlining."""

    # -- Unit tests for _simplify_ite directly --

    def test_constant_true_returns_if_val(self) -> None:
        result = ytl._simplify_ite(ytl.IntLit(1), ytl.Var("a"), ytl.Var("b"))
        self.assertEqual(result, ytl.Var("a"))

    def test_constant_nonzero_returns_if_val(self) -> None:
        result = ytl._simplify_ite(ytl.IntLit(42), ytl.Var("a"), ytl.Var("b"))
        self.assertEqual(result, ytl.Var("a"))

    def test_constant_false_returns_else_val(self) -> None:
        result = ytl._simplify_ite(ytl.IntLit(0), ytl.Var("a"), ytl.Var("b"))
        self.assertEqual(result, ytl.Var("b"))

    def test_equal_branches_returns_value(self) -> None:
        result = ytl._simplify_ite(ytl.Var("c"), ytl.IntLit(5), ytl.IntLit(5))
        self.assertEqual(result, ytl.IntLit(5))

    def test_equal_branches_with_variable_condition(self) -> None:
        expr = ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1)))
        result = ytl._simplify_ite(ytl.Var("c"), expr, expr)
        self.assertEqual(result, expr)

    def test_variable_condition_emits_ite(self) -> None:
        result = ytl._simplify_ite(ytl.Var("c"), ytl.Var("a"), ytl.Var("b"))
        self.assertEqual(
            result, ytl.Call("__ite", (ytl.Var("c"), ytl.Var("a"), ytl.Var("b")))
        )

    def test_computed_constant_condition_folds(self) -> None:
        # eq(5, 5) evaluates to 1, so the true branch is selected.
        cond = ytl.Call("eq", (ytl.IntLit(5), ytl.IntLit(5)))
        result = ytl._simplify_ite(cond, ytl.Var("a"), ytl.Var("b"))
        self.assertEqual(result, ytl.Var("a"))

    def test_computed_zero_condition_folds(self) -> None:
        # eq(3, 5) evaluates to 0, so the else branch is selected.
        cond = ytl.Call("eq", (ytl.IntLit(3), ytl.IntLit(5)))
        result = ytl._simplify_ite(cond, ytl.Var("a"), ytl.Var("b"))
        self.assertEqual(result, ytl.Var("b"))

    # -- Integration: inlining a helper with constant-condition if-block --

    CONST_IF_HELPER_CONFIG = make_model_config(("target",))
    CONST_IF_HELPER_YUL = """
        function fun_target_1(var_x_1) -> var_z_2 {
            var_z_2 := fun_helper_2(var_x_1)
        }

        function fun_helper_2(var_x_3) -> var_z_4 {
            var_z_4 := var_x_3
            if 1 {
                var_z_4 := add(var_x_3, 10)
            }
        }
    """

    def test_inline_constant_true_if_eliminates_ite(self) -> None:
        result = ytl.translate_yul_to_models(
            self.CONST_IF_HELPER_YUL,
            self.CONST_IF_HELPER_CONFIG,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        self.assertFalse(
            _model_contains_ite(model),
            "Expected no __ite nodes when if-condition is constant 1",
        )
        # Semantics: always takes the if-body (add x 10)
        self.assertEqual(ytl.evaluate_function_model(model, (5,)), (15,))
        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (10,))

    CONST_FALSE_IF_HELPER_YUL = """
        function fun_target_1(var_x_1) -> var_z_2 {
            var_z_2 := fun_helper_2(var_x_1)
        }

        function fun_helper_2(var_x_3) -> var_z_4 {
            var_z_4 := var_x_3
            if 0 {
                var_z_4 := add(var_x_3, 10)
            }
        }
    """

    def test_inline_constant_false_if_eliminates_ite(self) -> None:
        result = ytl.translate_yul_to_models(
            self.CONST_FALSE_IF_HELPER_YUL,
            self.CONST_IF_HELPER_CONFIG,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        self.assertFalse(
            _model_contains_ite(model),
            "Expected no __ite nodes when if-condition is constant 0",
        )
        # Semantics: never takes the if-body, z = x
        self.assertEqual(ytl.evaluate_function_model(model, (5,)), (5,))
        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (0,))

    # -- Integration: inlining a helper with constant-condition leave --

    CONST_LEAVE_HELPER_CONFIG = make_model_config(("target",))
    CONST_LEAVE_HELPER_YUL = """
        function fun_target_1(var_x_1) -> var_z_2 {
            var_z_2 := fun_helper_2(var_x_1)
        }

        function fun_helper_2(var_x_3) -> var_z_4 {
            var_z_4 := 1
            if 1 {
                var_z_4 := 7
                leave
            }
            var_z_4 := 9
        }
    """

    def test_inline_constant_true_leave_eliminates_ite(self) -> None:
        result = ytl.translate_yul_to_models(
            self.CONST_LEAVE_HELPER_YUL,
            self.CONST_LEAVE_HELPER_CONFIG,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        self.assertFalse(
            _model_contains_ite(model),
            "Expected no __ite nodes when leave condition is constant 1",
        )
        # Always takes the leave path: z = 7
        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (7,))
        self.assertEqual(ytl.evaluate_function_model(model, (1,)), (7,))

    CONST_FALSE_LEAVE_HELPER_YUL = """
        function fun_target_1(var_x_1) -> var_z_2 {
            var_z_2 := fun_helper_2(var_x_1)
        }

        function fun_helper_2(var_x_3) -> var_z_4 {
            var_z_4 := 1
            if 0 {
                var_z_4 := 7
                leave
            }
            var_z_4 := 9
        }
    """

    def test_inline_constant_false_leave_eliminates_ite(self) -> None:
        result = ytl.translate_yul_to_models(
            self.CONST_FALSE_LEAVE_HELPER_YUL,
            self.CONST_LEAVE_HELPER_CONFIG,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        self.assertFalse(
            _model_contains_ite(model),
            "Expected no __ite nodes when leave condition is constant 0",
        )
        # Never takes the leave path: z = 9
        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (9,))
        self.assertEqual(ytl.evaluate_function_model(model, (1,)), (9,))

    # -- Integration: inlining a helper with constant-condition switch --

    CONST_SWITCH_HELPER_CONFIG = make_model_config(("target",))
    CONST_SWITCH_HELPER_YUL = """
        function fun_target_1(var_x_1) -> var_z_2 {
            var_z_2 := fun_helper_2(var_x_1)
        }

        function fun_helper_2(var_x_3) -> var_z_4 {
            var_z_4 := var_x_3
            switch 1
            case 0 {
                var_z_4 := add(var_x_3, 10)
            }
            default {
                var_z_4 := add(var_x_3, 20)
            }
        }
    """

    def test_inline_constant_switch_eliminates_ite(self) -> None:
        result = ytl.translate_yul_to_models(
            self.CONST_SWITCH_HELPER_YUL,
            self.CONST_SWITCH_HELPER_CONFIG,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        self.assertFalse(
            _model_contains_ite(model),
            "Expected no __ite nodes when switch condition is constant 1",
        )
        # switch 1 → default branch: z = x + 20
        self.assertEqual(ytl.evaluate_function_model(model, (5,)), (25,))
        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (20,))

    # -- Variable condition still produces __ite --

    def test_variable_condition_preserves_ite(self) -> None:
        """Sanity check: non-constant conditions still produce __ite."""
        result = ytl.translate_yul_to_models(
            TranslationPipelineTest.LEAVE_HELPER_YUL,
            TranslationPipelineTest.LEAVE_HELPER_CONFIG,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        self.assertTrue(
            _model_contains_ite(model),
            "Expected __ite nodes when condition depends on input",
        )
        # Semantics still correct
        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (9,))
        self.assertEqual(ytl.evaluate_function_model(model, (1,)), (7,))


# ---------------------------------------------------------------------------
# Step 2 tests: standalone _eval_builtin EVM correctness
# ---------------------------------------------------------------------------


class EvalBuiltinCorrectnessTest(unittest.TestCase):
    def test_add_wraps(self) -> None:
        self.assertEqual(ytl._eval_builtin("add", (ytl.WORD_MOD - 1, 1)), 0)

    def test_sub_wraps(self) -> None:
        self.assertEqual(ytl._eval_builtin("sub", (0, 1)), ytl.WORD_MOD - 1)

    def test_mul_wraps(self) -> None:
        self.assertEqual(
            ytl._eval_builtin("mul", (ytl.WORD_MOD - 1, ytl.WORD_MOD - 1)), 1
        )

    def test_div_by_zero(self) -> None:
        self.assertEqual(ytl._eval_builtin("div", (7, 0)), 0)

    def test_mod_by_zero(self) -> None:
        self.assertEqual(ytl._eval_builtin("mod", (7, 0)), 0)

    def test_not_complement(self) -> None:
        self.assertEqual(ytl._eval_builtin("not", (0,)), ytl.WORD_MOD - 1)

    def test_shl_boundary(self) -> None:
        self.assertEqual(ytl._eval_builtin("shl", (255, 1)), 1 << 255)
        self.assertEqual(ytl._eval_builtin("shl", (256, 1)), 0)

    def test_shr_boundary(self) -> None:
        self.assertEqual(ytl._eval_builtin("shr", (255, 1 << 255)), 1)
        self.assertEqual(ytl._eval_builtin("shr", (256, 1 << 255)), 0)

    def test_clz_edges(self) -> None:
        self.assertEqual(ytl._eval_builtin("clz", (0,)), 256)
        self.assertEqual(ytl._eval_builtin("clz", (1,)), 255)
        self.assertEqual(ytl._eval_builtin("clz", (1 << 255,)), 0)

    def test_lt_gt_boolean(self) -> None:
        self.assertIn(ytl._eval_builtin("lt", (3, 7)), (0, 1))
        self.assertEqual(ytl._eval_builtin("lt", (3, 7)), 1)
        self.assertEqual(ytl._eval_builtin("lt", (7, 3)), 0)
        self.assertEqual(ytl._eval_builtin("gt", (7, 3)), 1)
        self.assertEqual(ytl._eval_builtin("gt", (3, 7)), 0)

    def test_mulmod_by_zero(self) -> None:
        self.assertEqual(ytl._eval_builtin("mulmod", (3, 5, 0)), 0)
        # (WORD_MOD-1)^2 mod (WORD_MOD-1) = 0
        self.assertEqual(
            ytl._eval_builtin(
                "mulmod", (ytl.WORD_MOD - 1, ytl.WORD_MOD - 1, ytl.WORD_MOD - 1)
            ),
            0,
        )
        # Standard case: 3*5 mod 7 = 1
        self.assertEqual(ytl._eval_builtin("mulmod", (3, 5, 7)), 1)

    def test_unsupported_op_raises(self) -> None:
        with self.assertRaises(ytl.EvaluationError):
            ytl._eval_builtin("fake_op", (1, 2))

    def test_wrong_arity_raises(self) -> None:
        with self.assertRaises(ytl.EvaluationError):
            ytl._eval_builtin("add", (1,))


# ---------------------------------------------------------------------------
# Step 3 tests: validate_function_model structural invariants
# ---------------------------------------------------------------------------


class ValidateFunctionModelTest(unittest.TestCase):
    def test_validate_rejects_duplicate_param_names(self) -> None:
        model = ytl.FunctionModel(
            fn_name="bad",
            param_names=("x", "x"),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.Var("x")),),
        )
        with self.assertRaisesRegex(ytl.ParseError, "duplicate param"):
            ytl.validate_function_model(model)

    def test_validate_rejects_duplicate_return_names(self) -> None:
        model = ytl.FunctionModel(
            fn_name="bad",
            param_names=("x",),
            return_names=("z", "z"),
            assignments=(ytl.Assignment("z", ytl.Var("x")),),
        )
        with self.assertRaisesRegex(ytl.ParseError, "duplicate return"):
            ytl.validate_function_model(model)

    def test_validate_allows_param_return_overlap_in_restricted_ir(self) -> None:
        model = ytl.FunctionModel(
            fn_name="identity",
            param_names=("x",),
            return_names=("x",),
            assignments=(),
        )
        ytl.validate_function_model(model)
        self.assertEqual(ytl.evaluate_function_model(model, (7,)), (7,))

    def test_validate_rejects_duplicate_conditional_output_vars(self) -> None:
        model = ytl.FunctionModel(
            fn_name="bad",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ytl.ConditionalBlock(
                    condition=ytl.Var("x"),
                    output_vars=("a", "a"),
                    then_branch=ytl.ConditionalBranch(
                        assignments=(ytl.Assignment("a", ytl.IntLit(1)),),
                        outputs=("a", "a"),
                    ),
                    else_branch=ytl.ConditionalBranch(
                        assignments=(ytl.Assignment("a", ytl.IntLit(2)),),
                        outputs=("a", "a"),
                    ),
                ),
                ytl.Assignment("z", ytl.Var("a")),
            ),
        )
        with self.assertRaisesRegex(
            ytl.ParseError, "duplicate conditional output_vars"
        ):
            ytl.validate_function_model(model)

    def test_validate_rejects_invalid_ident_in_param(self) -> None:
        model = ytl.FunctionModel(
            fn_name="bad",
            param_names=("123bad",),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.IntLit(0)),),
        )
        with self.assertRaisesRegex(ytl.ParseError, "Invalid.*param"):
            ytl.validate_function_model(model)


# ---------------------------------------------------------------------------
# Step 6a tests: collect_ops_from_statement
# ---------------------------------------------------------------------------


class CollectOpsTest(unittest.TestCase):
    def test_collects_ops_from_else_branch(self) -> None:
        stmt = ytl.ConditionalBlock(
            condition=ytl.IntLit(1),
            output_vars=("out",),
            then_branch=branch(
                (ytl.Assignment("out", ytl.IntLit(0)),),
                ("out",),
            ),
            else_branch=branch(
                (
                    ytl.Assignment(
                        "out", ytl.Call("mul", (ytl.IntLit(3), ytl.IntLit(7)))
                    ),
                ),
                ("out",),
            ),
        )
        ops = ytl.collect_ops_from_statement(stmt)
        self.assertIn("mul", ops)

    def test_collects_ops_from_condition(self) -> None:
        stmt = ytl.ConditionalBlock(
            condition=ytl.Call("gt", (ytl.IntLit(5), ytl.IntLit(3))),
            output_vars=("out",),
            then_branch=branch(
                (ytl.Assignment("out", ytl.IntLit(1)),),
                ("out",),
            ),
            else_branch=branch(
                (ytl.Assignment("out", ytl.IntLit(0)),),
                ("out",),
            ),
        )
        ops = ytl.collect_ops_from_statement(stmt)
        self.assertIn("gt", ops)


# ---------------------------------------------------------------------------
# Step 6b tests: emit_expr
# ---------------------------------------------------------------------------


class EmitExprTest(unittest.TestCase):
    OP_MAP = ytl.OP_TO_LEAN_HELPER
    CALL_MAP: dict[str, str] = {}

    def _emit(self, expr: ytl.Expr) -> str:
        return ytl.emit_expr(expr, helper_map={**self.OP_MAP, **self.CALL_MAP})

    def test_emit_intlit(self) -> None:
        self.assertEqual(self._emit(ytl.IntLit(42)), "42")

    def test_emit_var(self) -> None:
        self.assertEqual(self._emit(ytl.Var("x")), "x")

    def test_emit_builtin_call(self) -> None:
        result = self._emit(ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1))))
        self.assertEqual(result, "evmAdd (x) (1)")

    def test_emit_ite(self) -> None:
        result = self._emit(
            ytl.Call("__ite", (ytl.Var("c"), ytl.IntLit(1), ytl.IntLit(0)))
        )
        self.assertIn("if", result)
        self.assertIn("then", result)
        self.assertIn("else", result)

    def test_emit_component_projection(self) -> None:
        inner = ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1)))
        result = self._emit(ytl.Call("__component_0_2", (inner,)))
        self.assertIn(".1", result)

    def test_emit_unknown_call_raises(self) -> None:
        with self.assertRaises(ytl.ParseError):
            self._emit(ytl.Call("totally_unknown_func", (ytl.IntLit(1),)))


# ---------------------------------------------------------------------------
# Step 6c: __ite generation in fuzzer + Step 6d: multi-return projection
# ---------------------------------------------------------------------------


class ExtendedFuzzerTest(ModelEquivalenceTestCase):
    UNARY_OPS = ("not", "clz")
    BINARY_OPS = (
        "add",
        "sub",
        "mul",
        "div",
        "mod",
        "and",
        "or",
        "eq",
        "lt",
        "gt",
        "shl",
        "shr",
    )
    TERNARY_OPS = ("mulmod",)

    def _random_scalar(self, rng: random.Random) -> int:
        if rng.random() < 0.7:
            return rng.choice(self.INTERESTING_VALUES)
        return rng.getrandbits(320)

    def _random_expr(
        self,
        rng: random.Random,
        available: tuple[str, ...],
        *,
        depth: int,
    ) -> ytl.Expr:
        if depth <= 0 or rng.random() < 0.3:
            if available and rng.random() < 0.6:
                return ytl.Var(rng.choice(available))
            return ytl.IntLit(self._random_scalar(rng))

        kind = rng.random()
        if kind < 0.15 and available:
            return ytl.Var(rng.choice(available))
        if kind < 0.30:
            return ytl.IntLit(self._random_scalar(rng))
        # __ite generation (5% probability at depth > 0)
        if kind < 0.35:
            cond = self._random_expr(rng, available, depth=depth - 1)
            a = self._random_expr(rng, available, depth=depth - 1)
            b = self._random_expr(rng, available, depth=depth - 1)
            return ytl.Call("__ite", (cond, a, b))
        if kind < 0.50:
            op = rng.choice(self.UNARY_OPS)
            return ytl.Call(op, (self._random_expr(rng, available, depth=depth - 1),))
        if kind < 0.90:
            op = rng.choice(self.BINARY_OPS)
            return ytl.Call(
                op,
                (
                    self._random_expr(rng, available, depth=depth - 1),
                    self._random_expr(rng, available, depth=depth - 1),
                ),
            )
        op = rng.choice(self.TERNARY_OPS)
        return ytl.Call(
            op,
            (
                self._random_expr(rng, available, depth=depth - 1),
                self._random_expr(rng, available, depth=depth - 1),
                self._random_expr(rng, available, depth=depth - 1),
            ),
        )

    def test_randomized_ite_dce_equivalence(self) -> None:
        """DCE on models containing __ite expressions preserves semantics."""
        for seed in range(12):
            rng = random.Random(seed + 7000)
            params = ("p0", "p1")
            assignments: list[ytl.ModelStatement] = []
            scope = list(params)
            for i in range(6):
                name = f"v_{seed}_{i}"
                assignments.append(
                    ytl.Assignment(name, self._random_expr(rng, tuple(scope), depth=3))
                )
                scope.append(name)

            before = ytl.FunctionModel(
                fn_name=f"ite_dce_{seed}",
                param_names=params,
                return_names=(scope[-1],),
                assignments=tuple(assignments),
            )
            ytl.validate_function_model(before)
            after = ytl._prune_dead_assignments(before)
            self.assertModelsEquivalent(
                before, after, seed=7000 + seed, random_cases=64
            )

    def test_randomized_multi_return_projection_equivalence(self) -> None:
        """Build a 2-return helper + outer using __component projections, verify DCE."""
        for seed in range(8):
            rng = random.Random(seed + 8000)

            helper = ytl.FunctionModel(
                fn_name="helper",
                param_names=("a", "b"),
                return_names=("r0", "r1"),
                assignments=(
                    ytl.Assignment(
                        "r0",
                        self._random_expr(rng, ("a", "b"), depth=2),
                    ),
                    ytl.Assignment(
                        "r1",
                        self._random_expr(rng, ("a", "b"), depth=2),
                    ),
                ),
            )

            outer = ytl.FunctionModel(
                fn_name="outer",
                param_names=("x", "y"),
                return_names=("out",),
                assignments=(
                    ytl.Assignment(
                        "lhs",
                        ytl.Call(
                            "__component_0_2",
                            (ytl.Call("helper", (ytl.Var("x"), ytl.Var("y"))),),
                        ),
                    ),
                    ytl.Assignment(
                        "rhs",
                        ytl.Call(
                            "__component_1_2",
                            (ytl.Call("helper", (ytl.Var("x"), ytl.Var("y"))),),
                        ),
                    ),
                    ytl.Assignment(
                        "dead",
                        self._random_expr(rng, ("x", "y"), depth=2),
                    ),
                    ytl.Assignment(
                        "out",
                        ytl.Call("add", (ytl.Var("lhs"), ytl.Var("rhs"))),
                    ),
                ),
            )

            table = ytl.build_model_table([helper, outer])
            ytl.validate_function_model(outer)
            after = ytl._prune_dead_assignments(outer)
            ytl.validate_function_model(after)

            self.assertModelsEquivalent(
                outer,
                after,
                before_table=table,
                after_table={**table, "outer": after},
                seed=8000 + seed,
                random_cases=64,
            )


class FunctionSelectionTest(unittest.TestCase):
    EXACT_SELECTION_YUL = """
        function helper(var_x_1) -> var_z_2 {
            var_z_2 := add(var_x_1, 100)
        }

        function fun_pick_1(var_x_3) -> var_z_4 {
            var_z_4 := helper(var_x_3)
        }

        function fun_pick_2(var_x_5) -> var_z_6 {
            var_z_6 := sub(var_x_5, 1)
        }
    """

    def test_find_function_rejects_ambiguous_homonyms_without_disambiguator(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_dup_1(var_x_1) -> var_z_2 {
                var_z_2 := add(var_x_1, 1)
            }

            function fun_dup_2(var_x_3) -> var_z_4 {
                var_z_4 := sub(var_x_3, 1)
            }
            """)

        with self.assertRaisesRegex(
            ytl.ParseError, "Multiple Yul functions match 'dup'"
        ):
            ytl.YulParser(tokens).find_function("dup")

    def test_find_function_uses_param_count_to_disambiguate(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_dup_1(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_dup_2(var_x_3, var_y_4) -> var_z_5 {
                var_z_5 := add(var_x_3, var_y_4)
            }
            """)

        found = ytl.YulParser(tokens).find_function("dup", n_params=2)

        self.assertEqual(found.yul_name, "fun_dup_2")

    def test_find_function_prefers_candidate_referencing_known_yul_name(self) -> None:
        tokens = ytl.tokenize_yul("""
            function helper(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_pick_1(var_x_3) -> var_z_4 {
                var_z_4 := helper(var_x_3)
            }

            function fun_pick_2(var_x_5) -> var_z_6 {
                var_z_6 := add(var_x_5, 1)
            }
            """)

        found = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
        )

        self.assertEqual(found.yul_name, "fun_pick_1")

    def test_find_function_exclude_known_selects_leaf_candidate(self) -> None:
        tokens = ytl.tokenize_yul("""
            function helper(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_pick_1(var_x_3) -> var_z_4 {
                var_z_4 := helper(var_x_3)
            }

            function fun_pick_2(var_x_5) -> var_z_6 {
                var_z_6 := add(var_x_5, 1)
            }
            """)

        found = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
            exclude_known=True,
        )

        self.assertEqual(found.yul_name, "fun_pick_2")

    def test_find_exact_function_returns_named_definition(self) -> None:
        tokens = ytl.tokenize_yul(self.EXACT_SELECTION_YUL)

        found = ytl.YulParser(tokens).find_exact_function("fun_pick_2")

        self.assertEqual(found.yul_name, "fun_pick_2")

    def test_find_exact_function_rejects_missing_name(self) -> None:
        tokens = ytl.tokenize_yul(self.EXACT_SELECTION_YUL)

        with self.assertRaisesRegex(
            ytl.ParseError, "Exact Yul function 'fun_missing_9' not found"
        ):
            ytl.YulParser(tokens).find_exact_function("fun_missing_9")

    def test_prepare_translation_uses_exact_yul_name_selection(self) -> None:
        config = make_model_config(
            ("pick",),
            exact_yul_names={"pick": "fun_pick_2"},
        )

        result = ytl.translate_yul_to_models(
            self.EXACT_SELECTION_YUL,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        expected_fn_map: dict[str, str] = {"fun_pick_2": "pick"}
        self.assertEqual(result.preparation.fn_map, expected_fn_map)
        model = result.models[0]
        self.assertEqual(model.fn_name, "pick")
        self.assertEqual(ytl.evaluate_function_model(model, (7,)), (6,))

    def test_prepare_translation_exact_yul_name_rejects_param_mismatch(self) -> None:
        config = make_model_config(
            ("pick",),
            exact_yul_names={"pick": "fun_pick_2"},
            n_params={"pick": 1},
        )
        yul = """
            function fun_pick_2(var_x_1, var_y_2) -> var_z_3 {
                var_z_3 := add(var_x_1, var_y_2)
            }
            """

        with self.assertRaisesRegex(
            ytl.ParseError,
            "Exact Yul function 'fun_pick_2' with 1 parameter\\(s\\) not found",
        ):
            ytl.prepare_translation(yul, config)


class ResolvedTranslatorRegressionTest(unittest.TestCase):
    def test_translate_yul_to_models_rejects_target_expression_statements(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_x_1) -> var_z_2 {
                add(var_x_1, 1)
                var_z_2 := 7
            }
            """

        with self.assertRaisesRegex(
            ytl.ParseError,
            "unhandled expression-statement",
        ):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_keeps_helper_resolution_object_local(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            object "A" {
                function fun_f_1() -> var_z_1 {
                    var_z_1 := helper()
                }

                function helper() -> var_r_2 {
                    var_r_2 := 1
                }
            }

            object "B" {
                function helper() -> var_r_3 {
                    var_r_3 := 2
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(
            ytl.evaluate_function_model(result.models[0], ()),
            (1,),
        )

    def test_translate_yul_to_models_threads_block_local_branch_updates(
        self,
    ) -> None:
        config = make_model_config(("f",), keep_solidity_locals=True)
        yul = """
            function fun_f_1(var_x_1) -> var_z_1 {
                var_z_1 := 0
                {
                    let var_a_2 := 1
                    if var_x_1 {
                        var_a_2 := 2
                        var_z_1 := var_a_2
                    }
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(
            ytl.evaluate_function_model(result.models[0], (0,)),
            (0,),
        )
        self.assertEqual(
            ytl.evaluate_function_model(result.models[0], (1,)),
            (2,),
        )

    def test_yul_function_to_model_zero_initializes_return_var_in_if_else_join(
        self,
    ) -> None:
        yul = """
            function fun_f_1(var_x_1) -> var_z_1 {
                if var_x_1 {
                    var_z_1 := 1
                }
            }
            """
        fn = ytl.YulParser(ytl.tokenize_yul(yul)).parse_function()

        model = ytl.yul_function_to_model(fn, "f", {})

        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (0,))
        self.assertEqual(ytl.evaluate_function_model(model, (1,)), (1,))

    def test_find_function_treats_nested_definition_as_reference(self) -> None:
        # A nested function *definition* named ``helper`` inside fun_pick_1
        # should NOT count as a reference to the outer ``helper``.  Only
        # fun_pick_2 actually calls ``helper``, so it should be selected
        # unambiguously.
        tokens = ytl.tokenize_yul("""
            function helper(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_pick_1(var_x_3) -> var_z_4 {
                function helper(var_y_5) -> var_w_6 {
                    var_w_6 := var_y_5
                }
                var_z_4 := var_x_3
            }

            function fun_pick_2(var_x_7) -> var_z_8 {
                var_z_8 := helper(var_x_7)
            }
            """)

        func = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
        )
        self.assertEqual(func.yul_name, "fun_pick_2")

    def test_translate_yul_to_models_scopes_helpers_per_selected_target_object(
        self,
    ) -> None:
        config = make_model_config(("f", "g"))
        yul = """
            object "A" {
                function fun_f_1() -> var_z_1 {
                    var_z_1 := helperA()
                }

                function helperA() -> var_r_2 {
                    var_r_2 := 11
                }
            }

            object "B" {
                function fun_g_1() -> var_z_3 {
                    var_z_3 := helperB()
                }

                function helperB() -> var_r_4 {
                    var_r_4 := 22
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        models = {model.fn_name: model for model in result.models}

        self.assertEqual(ytl.evaluate_function_model(models["f"], ()), (11,))
        self.assertEqual(ytl.evaluate_function_model(models["g"], ()), (22,))

    def test_translate_yul_to_models_zero_initializes_return_before_later_reassignment(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_1 {
                if 1 {
                    var_z_1 := 7
                }
                var_z_1 := add(var_z_1, 1)
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(
            ytl.evaluate_function_model(result.models[0], ()),
            (8,),
        )

    def test_translate_yul_to_models_zero_initializes_return_before_self_read(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_1 {
                var_z_1 := add(var_z_1, 1)
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(
            ytl.evaluate_function_model(result.models[0], ()),
            (1,),
        )

    def test_translate_yul_to_models_zero_initializes_return_before_localized_read(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_1 {
                let var_y_2 := add(var_z_1, 1)
                var_z_1 := var_y_2
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(
            ytl.evaluate_function_model(result.models[0], ()),
            (1,),
        )

    def test_translate_yul_to_models_skips_unneeded_zero_init_after_branch_write(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1) -> var_z_1 {
                switch var_c_1
                case 0 {
                    var_z_1 := 8
                }
                default {
                    var_z_1 := 7
                    let var_y_2 := add(var_z_1, 1)
                    var_z_1 := var_y_2
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(
            result.models[0].assignments,
            (
                ytl.ConditionalBlock(
                    condition=ytl.Var("c"),
                    output_vars=("z",),
                    then_branch=branch(
                        (
                            ytl.Assignment("z", ytl.IntLit(7)),
                            ytl.Assignment(
                                "z",
                                ytl.Call(
                                    "add",
                                    (ytl.Var("z"), ytl.IntLit(1)),
                                ),
                            ),
                        ),
                        ("z",),
                    ),
                    else_branch=branch(
                        (ytl.Assignment("z", ytl.IntLit(8)),),
                        ("z",),
                    ),
                ),
            ),
        )

    def test_translate_yul_to_models_scopes_helpers_for_selected_later_duplicate_symbol(
        self,
    ) -> None:
        config = make_model_config(("inner", "outer"))
        yul = """
            object "A" {
                function fun_outer_1() -> var_z_1 {
                    var_z_1 := 5
                }
            }

            object "B" {
                function fun_inner_2() -> var_i_1 {
                    var_i_1 := 7
                }

                function fun_outer_1() -> var_z_2 {
                    let usr$tmp := fun_inner_2()
                    var_z_2 := helperB()
                }

                function helperB() -> var_r_3 {
                    var_r_3 := 22
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        models = {model.fn_name: model for model in result.models}
        table = ytl.build_model_table(result.models)

        self.assertEqual(
            ytl.evaluate_function_model(models["inner"], (), model_table=table),
            (7,),
        )
        self.assertEqual(
            ytl.evaluate_function_model(models["outer"], (), model_table=table),
            (22,),
        )


class KnownTranslatorBugRegressionTest(unittest.TestCase):
    # These are known-bad translator behaviors found during review.
    # They should fail loudly until the implementation is fixed.

    def test_find_function_ignores_dead_deeper_nested_helper_dependencies(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function helper(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_pick_1(var_x_3) -> var_z_4 {
                function mid(var_y_5) -> var_w_6 {
                    function inner(var_q_7) -> var_r_8 {
                        var_r_8 := helper(var_q_7)
                    }
                    var_w_6 := 111
                }
                var_z_4 := mid(var_x_3)
            }

            function fun_pick_2(var_x_9) -> var_z_10 {
                var_z_10 := helper(var_x_9)
            }
            """)

        func = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
        )

        self.assertEqual(func.yul_name, "fun_pick_2")

    def test_find_function_tracks_transitive_nested_local_helper_dependencies(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function helper(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_pick_1(var_x_3) -> var_z_4 {
                function nested(var_y_5) -> var_w_6 {
                    var_w_6 := helper(var_y_5)
                }
                var_z_4 := nested(var_x_3)
            }

            function fun_pick_2(var_x_7) -> var_z_8 {
                var_z_8 := var_x_7
            }
            """)

        func = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
        )

        self.assertEqual(func.yul_name, "fun_pick_1")

    def test_find_function_tracks_transitive_nested_helper_called_before_definition(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function helper(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_pick_1(var_x_3) -> var_z_4 {
                var_z_4 := nested(var_x_3)
                function nested(var_y_5) -> var_w_6 {
                    var_w_6 := helper(var_y_5)
                }
            }

            function fun_pick_2(var_x_7) -> var_z_8 {
                var_z_8 := 222
            }
            """)

        func = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
        )

        self.assertEqual(func.yul_name, "fun_pick_1")

    def test_translate_yul_to_models_dispatches_modeled_function_named_like_builtin(
        self,
    ) -> None:
        config = make_model_config(("f", "add"))
        yul = """
            function fun_f_1(var_x_1, var_y_2) -> var_z_3 {
                var_z_3 := fun_add_2(var_x_1, var_y_2)
            }

            function fun_add_2(var_a_4, var_b_5) -> var_r_6 {
                var_r_6 := 42
            }
            """

        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_find_function_ignores_nested_local_function_references(self) -> None:
        tokens = ytl.tokenize_yul("""
            function helper(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_pick_1(var_x_3) -> var_z_4 {
                function nested(var_y_5) -> var_w_6 {
                    var_w_6 := helper(var_y_5)
                }
                var_z_4 := 111
            }

            function fun_pick_2(var_x_7) -> var_z_8 {
                var_z_8 := 222
            }
            """)

        with self.assertRaisesRegex(
            ytl.ParseError,
            "Multiple Yul functions match 'pick'",
        ):
            ytl.YulParser(tokens).find_function(
                "pick",
                known_yul_names={"helper"},
            )

    def test_validate_function_model_rejects_reserved_lean_helper_binder_names(
        self,
    ) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("u256",),
            return_names=("z",),
            assignments=(
                ytl.Assignment(
                    "z",
                    ytl.Call("add", (ytl.Var("u256"), ytl.IntLit(1))),
                ),
            ),
        )

        with self.assertRaises(ytl.ParseError):
            ytl.validate_function_model(model)

    def test_build_lean_source_rejects_extra_norm_helper_binder_collisions(
        self,
    ) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("normBitLengthPlus1",),
            return_names=("z",),
            assignments=(
                ytl.Assignment("z", ytl.Var("normBitLengthPlus1")),
            ),
        )
        config = ytl.ModelConfig(
            function_order=("f",),
            model_names={"f": "model_f"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={"bitLengthPlus1": "normBitLengthPlus1"},
            extra_lean_defs=(
                "def normBitLengthPlus1 (x : Nat) : Nat := x + 1"
            ),
            norm_rewrite=lambda expr: ytl.Call("bitLengthPlus1", (expr,)),
            inner_fn="f",
            n_params=None,
            exact_yul_names=None,
            keep_solidity_locals=False,
            hoist_repeated_calls=frozenset(),
            skip_prune=frozenset(),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )

        with self.assertRaises(ytl.ParseError):
            ytl.build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_rejects_extra_norm_helper_collisions_in_conditional_branch_targets(
        self,
    ) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("p",),
            return_names=("z",),
            assignments=(
                ytl.ConditionalBlock(
                    condition=ytl.Var("p"),
                    output_vars=("tmp",),
                    then_branch=ytl.ConditionalBranch(
                        assignments=(
                            ytl.Assignment(
                                "normBitLengthPlus1",
                                ytl.IntLit(1),
                            ),
                            ytl.Assignment("tmp", ytl.Var("p")),
                        ),
                        outputs=("tmp",),
                    ),
                    else_branch=ytl.ConditionalBranch(
                        assignments=(
                            ytl.Assignment(
                                "normBitLengthPlus1",
                                ytl.IntLit(2),
                            ),
                            ytl.Assignment("tmp", ytl.Var("p")),
                        ),
                        outputs=("tmp",),
                    ),
                ),
                ytl.Assignment("z", ytl.Var("tmp")),
            ),
        )
        config = ytl.ModelConfig(
            function_order=("f",),
            model_names={"f": "model_f"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={"bitLengthPlus1": "normBitLengthPlus1"},
            extra_lean_defs=(
                "def normBitLengthPlus1 (x : Nat) : Nat := x + 1"
            ),
            norm_rewrite=lambda expr: ytl.Call("bitLengthPlus1", (expr,)),
            inner_fn="f",
            n_params=None,
            exact_yul_names=None,
            keep_solidity_locals=False,
            hoist_repeated_calls=frozenset(),
            skip_prune=frozenset(),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )

        with self.assertRaises(ytl.ParseError):
            ytl.build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_rejects_extra_norm_helper_collisions_in_conditional_output_vars(
        self,
    ) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("p",),
            return_names=("z",),
            assignments=(
                ytl.ConditionalBlock(
                    condition=ytl.Var("p"),
                    output_vars=("normBitLengthPlus1",),
                    then_branch=ytl.ConditionalBranch(
                        assignments=(),
                        outputs=("p",),
                    ),
                    else_branch=ytl.ConditionalBranch(
                        assignments=(),
                        outputs=("p",),
                    ),
                ),
                ytl.Assignment("z", ytl.Var("normBitLengthPlus1")),
            ),
        )
        config = ytl.ModelConfig(
            function_order=("f",),
            model_names={"f": "model_f"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={"bitLengthPlus1": "normBitLengthPlus1"},
            extra_lean_defs=(
                "def normBitLengthPlus1 (x : Nat) : Nat := x + 1"
            ),
            norm_rewrite=lambda expr: ytl.Call("bitLengthPlus1", (expr,)),
            inner_fn="f",
            n_params=None,
            exact_yul_names=None,
            keep_solidity_locals=False,
            hoist_repeated_calls=frozenset(),
            skip_prune=frozenset(),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )

        with self.assertRaises(ytl.ParseError):
            ytl.build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_translate_yul_to_models_rejects_zero_return_functions(self) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_x_1) {
                let usr$tmp := add(var_x_1, 1)
            }
            """

        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )


class KnownOptimizerBugRegressionTest(ModelEquivalenceTestCase):
    # These are known-bad optimizer behaviors found during review.
    # They should fail loudly until the implementation is fixed.

    def test_hoist_repeated_model_calls_avoids_conditional_output_name_collisions(
        self,
    ) -> None:
        inner = ytl.FunctionModel(
            fn_name="inner",
            param_names=("x",),
            return_names=("ret",),
            assignments=(
                ytl.Assignment(
                    "ret",
                    ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1))),
                ),
            ),
        )
        before = ytl.FunctionModel(
            fn_name="f",
            param_names=("p",),
            return_names=("out",),
            assignments=(
                ytl.ConditionalBlock(
                    condition=ytl.Var("p"),
                    output_vars=("_cse_1",),
                    then_branch=ytl.ConditionalBranch(
                        assignments=(),
                        outputs=("p",),
                    ),
                    else_branch=ytl.ConditionalBranch(
                        assignments=(),
                        outputs=("p",),
                    ),
                ),
                ytl.Assignment("a", ytl.Call("inner", (ytl.Var("p"),))),
                ytl.Assignment(
                    "b",
                    ytl.Call(
                        "add",
                        (
                            ytl.Var("_cse_1"),
                            ytl.Call("inner", (ytl.Var("p"),)),
                        ),
                    ),
                ),
                ytl.Assignment("out", ytl.Var("b")),
            ),
        )

        after = ytl.hoist_repeated_model_calls(
            before,
            model_call_names=frozenset({"inner"}),
        )

        self.assertModelsEquivalent(
            before,
            after,
            before_table=ytl.build_model_table([inner, before]),
            after_table=ytl.build_model_table([inner, after]),
        )

    def test_hoist_repeated_model_calls_avoids_parameter_name_collisions(
        self,
    ) -> None:
        inner = ytl.FunctionModel(
            fn_name="inner",
            param_names=("x",),
            return_names=("ret",),
            assignments=(
                ytl.Assignment(
                    "ret",
                    ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1))),
                ),
            ),
        )
        before = ytl.FunctionModel(
            fn_name="f",
            param_names=("_cse_1", "p"),
            return_names=("out",),
            assignments=(
                ytl.Assignment("a", ytl.Call("inner", (ytl.Var("p"),))),
                ytl.Assignment(
                    "b",
                    ytl.Call(
                        "add",
                        (
                            ytl.Var("_cse_1"),
                            ytl.Call("inner", (ytl.Var("p"),)),
                        ),
                    ),
                ),
                ytl.Assignment("out", ytl.Var("b")),
            ),
        )

        after = ytl.hoist_repeated_model_calls(
            before,
            model_call_names=frozenset({"inner"}),
        )

        self.assertModelsEquivalent(
            before,
            after,
            before_table=ytl.build_model_table([inner, before]),
            after_table=ytl.build_model_table([inner, after]),
        )

    def test_hoist_repeated_model_calls_preserves_multi_return_component_projections(
        self,
    ) -> None:
        pair = ytl.FunctionModel(
            fn_name="pair",
            param_names=("x",),
            return_names=("lhs", "rhs"),
            assignments=(
                ytl.Assignment("lhs", ytl.Var("x")),
                ytl.Assignment(
                    "rhs",
                    ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1))),
                ),
            ),
        )
        before = ytl.FunctionModel(
            fn_name="f",
            param_names=("p",),
            return_names=("out",),
            assignments=(
                ytl.Assignment(
                    "out",
                    ytl.Call(
                        "add",
                        (
                            ytl.Call(
                                "__component_0_2",
                                (ytl.Call("pair", (ytl.Var("p"),)),),
                            ),
                            ytl.Call(
                                "__component_0_2",
                                (ytl.Call("pair", (ytl.Var("p"),)),),
                            ),
                        ),
                    ),
                ),
            ),
        )

        after = ytl.hoist_repeated_model_calls(
            before,
            model_call_names=frozenset({"pair"}),
        )

        self.assertModelsEquivalent(
            before,
            after,
            before_table=ytl.build_model_table([pair, before]),
            after_table=ytl.build_model_table([pair, after]),
        )

    def test_hoist_repeated_model_calls_avoids_generated_name_collisions(
        self,
    ) -> None:
        inner = ytl.FunctionModel(
            fn_name="inner",
            param_names=("x",),
            return_names=("ret",),
            assignments=(
                ytl.Assignment(
                    "ret",
                    ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1))),
                ),
            ),
        )
        before = ytl.FunctionModel(
            fn_name="f",
            param_names=("p",),
            return_names=("out",),
            assignments=(
                ytl.Assignment("_cse_1", ytl.IntLit(99)),
                ytl.Assignment("a", ytl.Call("inner", (ytl.Var("p"),))),
                ytl.Assignment(
                    "b",
                    ytl.Call(
                        "add",
                        (
                            ytl.Var("_cse_1"),
                            ytl.Call("inner", (ytl.Var("p"),)),
                        ),
                    ),
                ),
                ytl.Assignment("out", ytl.Var("b")),
            ),
        )

        after = ytl.hoist_repeated_model_calls(
            before,
            model_call_names=frozenset({"inner"}),
        )

        self.assertModelsEquivalent(
            before,
            after,
            before_table=ytl.build_model_table([inner, before]),
            after_table=ytl.build_model_table([inner, after]),
        )


class LeanSourceDeterminismTest(unittest.TestCase):
    CONFIG = make_model_config(("f",))

    def test_build_lean_source_is_deterministic(self) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ytl.Assignment("z", ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1)))),
            ),
        )

        src1 = ytl.build_lean_source(
            models=[model],
            source_path="test-source",
            namespace="Test",
            config=self.CONFIG,
        )
        src2 = ytl.build_lean_source(
            models=[model],
            source_path="test-source",
            namespace="Test",
            config=self.CONFIG,
        )

        self.assertEqual(src1, src2)
        self.assertNotIn("Generated at (UTC)", src1)


if __name__ == "__main__":
    unittest.main()
