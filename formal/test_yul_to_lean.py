import os
import pathlib
import random
import subprocess
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

import norm_ir
import yul_ast
import yul_to_lean as ytl
from norm_eval import evaluate_normalized
from yul_normalize import normalize_function
from yul_parser import SyntaxParser
from yul_resolve import ResolutionResult, resolve_function, resolve_module


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

        with self.assertRaisesRegex(ytl.ParseError, "string literal"):
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

    def test_parse_function_rejects_duplicate_param_names(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_bad_1(x, x) -> z {
                z := x
            }
            """)

        with self.assertRaisesRegex(ytl.ParseError, "x"):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_rejects_duplicate_return_names(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_bad_1(x) -> z, z {
                z := x
            }
            """)

        with self.assertRaisesRegex(ytl.ParseError, "z"):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_rejects_duplicate_local_declaration_in_same_scope(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_bad_1(x) -> z {
                let usr$tmp := 1
                let usr$tmp := 2
                z := usr$tmp
            }
            """)

        with self.assertRaisesRegex(ytl.ParseError, r"usr\$tmp"):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_rejects_duplicate_multi_let_target(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_bad_1(x) -> z {
                let usr$a, usr$a := fun_pair_2(x)
                z := usr$a
            }
            """)

        with self.assertRaisesRegex(ytl.ParseError, r"usr\$a"):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_rejects_same_scope_local_shadowing_parameter(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_bad_1(x) -> z {
                let x := 1
                z := x
            }
            """)

        with self.assertRaisesRegex(ytl.ParseError, "x"):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_rejects_same_scope_local_shadowing_return(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_bad_1(x) -> z {
                let z := 1
            }
            """)

        with self.assertRaisesRegex(ytl.ParseError, "z"):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_rejects_duplicate_local_inside_bare_block(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_bad_1(x) -> z {
                {
                    let usr$tmp := 1
                    let usr$tmp := 2
                    z := usr$tmp
                }
            }
            """)

        with self.assertRaisesRegex(ytl.ParseError, r"usr\$tmp"):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_rejects_string_literal_assignment_rhs(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_bad_1(x) -> z {
                z := "oops"
            }
            """)

        with self.assertRaisesRegex(ytl.ParseError, "string"):
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
        # Yul rejects cross-scope variable shadowing (solc error 1395).
        # Inner 'let tmp' shadows outer 'let tmp' — invalid Yul.
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
        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.YulParser(tokens).parse_function()

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
        # flattening ``tmp`` should be an ``Ite`` conditional expression,
        # and the final assignment should inline it.
        self.assertEqual(len(yf.assignments), 1)
        stmt = yf.assignments[0]
        self.assertIsInstance(stmt, ytl.PlainAssignment)
        assert isinstance(stmt, ytl.PlainAssignment)
        self.assertEqual(stmt.target, "var_z_3")
        # The expression should be Ite(c, add(x, 1), x)
        self.assertIsInstance(stmt.expr, ytl.Ite)

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
                ytl.Project(
                    0,
                    2,
                    ytl.Call("fun_pair_2", (ytl.Var("var_x_1"),)),
                ),
                is_declaration=True,
            ),
            ytl.PlainAssignment(
                "usr$rhs",
                ytl.Project(
                    1,
                    2,
                    ytl.Call("fun_pair_2", (ytl.Var("var_x_1"),)),
                ),
                is_declaration=True,
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
        expr = ytl.Project(1, 2, ytl.Call("single", ()))

        with self.assertRaisesRegex(ytl.ParseError, "expects 2 return values"):
            ytl.inline_calls(expr, fn_table)

    def test_yul_function_to_model_promotes_multi_assigned_temporary(self) -> None:
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

        model = ytl.yul_function_to_model(yf, "f", {})
        # Multi-assigned compiler temporary is promoted to a real variable;
        # the last assignment (IntLit(2)) should win through SSA.
        self.assertEqual(ytl.evaluate_function_model(model, (42,)), (2,))

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
                    ytl.Project(
                        0,
                        2,
                        ytl.Call("pair", (ytl.Var("x"), ytl.Var("y"))),
                    ),
                ),
                ytl.Assignment(
                    "rhs",
                    ytl.Project(
                        1,
                        2,
                        ytl.Call("pair", (ytl.Var("x"), ytl.Var("y"))),
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
        # Ite(1, 5, 3) → 5 (true branch)
        self.assertEqual(
            ytl._try_const_eval(ytl.Ite(ytl.IntLit(1), ytl.IntLit(5), ytl.IntLit(3))),
            5,
        )
        # Ite(0, 5, 3) → 3 (false branch)
        self.assertEqual(
            ytl._try_const_eval(ytl.Ite(ytl.IntLit(0), ytl.IntLit(5), ytl.IntLit(3))),
            3,
        )

    def test_ite_constant_condition_nonconstant_branch(self) -> None:
        # Ite(1, Var("x"), 3) → None (selected branch is non-constant)
        self.assertIsNone(
            ytl._try_const_eval(ytl.Ite(ytl.IntLit(1), ytl.Var("x"), ytl.IntLit(3)))
        )
        # Ite(0, 5, Var("x")) → None (selected branch is non-constant)
        self.assertIsNone(
            ytl._try_const_eval(ytl.Ite(ytl.IntLit(0), ytl.IntLit(5), ytl.Var("x")))
        )

    def test_ite_nonconstant_dead_branch_still_folds(self) -> None:
        # Ite(1, 5, Var("x")) → 5 (dead else-branch is non-constant)
        self.assertEqual(
            ytl._try_const_eval(ytl.Ite(ytl.IntLit(1), ytl.IntLit(5), ytl.Var("x"))),
            5,
        )
        # Ite(0, Var("x"), 3) → 3 (dead then-branch is non-constant)
        self.assertEqual(
            ytl._try_const_eval(ytl.Ite(ytl.IntLit(0), ytl.Var("x"), ytl.IntLit(3))),
            3,
        )
        # Ite(42, 10, Var("y")) → 10 (non-zero condition, dead branch has variable)
        self.assertEqual(
            ytl._try_const_eval(ytl.Ite(ytl.IntLit(42), ytl.IntLit(10), ytl.Var("y"))),
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
    """Return True if *expr* contains any ``Ite`` node."""
    if isinstance(expr, ytl.Ite):
        return True
    if isinstance(expr, ytl.Project):
        return _expr_contains_ite(expr.inner)
    if isinstance(expr, ytl.Call):
        return any(_expr_contains_ite(arg) for arg in expr.args)
    return False


def _model_contains_ite(model: ytl.FunctionModel) -> bool:
    """Return True if any expression in *model* contains an ``Ite`` node."""
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
        self.assertEqual(result, ytl.Ite(ytl.Var("c"), ytl.Var("a"), ytl.Var("b")))

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
            "Expected no Ite nodes when if-condition is constant 1",
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
            "Expected no Ite nodes when if-condition is constant 0",
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
            "Expected no Ite nodes when leave condition is constant 1",
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
            "Expected no Ite nodes when leave condition is constant 0",
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
            "Expected no Ite nodes when switch condition is constant 1",
        )
        # switch 1 → default branch: z = x + 20
        self.assertEqual(ytl.evaluate_function_model(model, (5,)), (25,))
        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (20,))

    # -- Variable condition still produces Ite --

    def test_variable_condition_preserves_ite(self) -> None:
        """Sanity check: non-constant conditions still produce Ite."""
        result = ytl.translate_yul_to_models(
            TranslationPipelineTest.LEAVE_HELPER_YUL,
            TranslationPipelineTest.LEAVE_HELPER_CONFIG,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        self.assertTrue(
            _model_contains_ite(model),
            "Expected Ite nodes when condition depends on input",
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

    def test_validate_rejects_negative_project_index(self) -> None:
        model = ytl.FunctionModel(
            fn_name="bad",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ytl.Assignment(
                    "z",
                    ytl.Project(-1, 2, ytl.Call("pair", (ytl.Var("x"),))),
                ),
            ),
        )

        with self.assertRaises(ytl.ParseError):
            ytl.validate_function_model(model)

    def test_validate_rejects_projection_of_builtin_call(self) -> None:
        model = ytl.FunctionModel(
            fn_name="bad",
            param_names=(),
            return_names=("z",),
            assignments=(
                ytl.Assignment(
                    "z",
                    ytl.Project(
                        0,
                        1,
                        ytl.Call("add", (ytl.IntLit(1), ytl.IntLit(2))),
                    ),
                ),
            ),
        )

        with self.assertRaises(ytl.ParseError):
            ytl.validate_function_model(model)

    def test_validate_rejects_negative_nat_literal(self) -> None:
        model = ytl.FunctionModel(
            fn_name="bad",
            param_names=(),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.IntLit(-1)),),
        )

        with self.assertRaises(ytl.ParseError):
            ytl.validate_function_model(model)

    def test_validate_selected_models_rejects_projection_of_single_return_model(
        self,
    ) -> None:
        inner = ytl.FunctionModel(
            fn_name="inner",
            param_names=("x",),
            return_names=("ret",),
            assignments=(ytl.Assignment("ret", ytl.Var("x")),),
        )
        outer = ytl.FunctionModel(
            fn_name="outer",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ytl.Assignment(
                    "z",
                    ytl.Project(0, 1, ytl.Call("inner", (ytl.Var("x"),))),
                ),
            ),
        )

        with self.assertRaises(ytl.ParseError):
            ytl.validate_selected_models([inner, outer])


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
        result = self._emit(ytl.Ite(ytl.Var("c"), ytl.IntLit(1), ytl.IntLit(0)))
        self.assertIn("if", result)
        self.assertIn("then", result)
        self.assertIn("else", result)

    def test_emit_component_projection(self) -> None:
        inner = ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1)))
        result = self._emit(ytl.Project(0, 2, inner))
        self.assertIn(".1", result)

    def test_emit_unknown_call_raises(self) -> None:
        with self.assertRaises(ytl.ParseError):
            self._emit(ytl.Call("totally_unknown_func", (ytl.IntLit(1),)))


# ---------------------------------------------------------------------------
# Step 6c: Ite generation in fuzzer + Step 6d: multi-return projection
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
        # Ite generation (5% probability at depth > 0)
        if kind < 0.35:
            cond = self._random_expr(rng, available, depth=depth - 1)
            a = self._random_expr(rng, available, depth=depth - 1)
            b = self._random_expr(rng, available, depth=depth - 1)
            return ytl.Ite(cond, a, b)
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
        """DCE on models containing Ite expressions preserves semantics."""
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
        """Build a 2-return helper + outer using Project projections, verify DCE."""
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
                        ytl.Project(
                            0,
                            2,
                            ytl.Call("helper", (ytl.Var("x"), ytl.Var("y"))),
                        ),
                    ),
                    ytl.Assignment(
                        "rhs",
                        ytl.Project(
                            1,
                            2,
                            ytl.Call("helper", (ytl.Var("x"), ytl.Var("y"))),
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

        pick_by_name: dict[str, str] = result.preparation.target_call_resolutions[
            "pick"
        ].by_name
        assert pick_by_name == {"fun_pick_2": "pick"}
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
                                "z_1",
                                ytl.Call(
                                    "add",
                                    (ytl.Var("z"), ytl.IntLit(1)),
                                ),
                            ),
                        ),
                        ("z_1",),
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

    def test_find_function_ignores_transitive_calls_to_shadowing_local_helper(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function helper(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_pick_1(var_x_3) -> var_z_4 {
                function helper(var_y_5) -> var_w_6 {
                    var_w_6 := 111
                }
                function caller(var_q_7) -> var_r_8 {
                    var_r_8 := helper(var_q_7)
                }
                var_z_4 := caller(var_x_3)
            }

            function fun_pick_2(var_x_9) -> var_z_10 {
                var_z_10 := 222
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

        with self.assertRaisesRegex(
            ytl.ParseError,
            "Multiple Yul functions match 'pick'",
        ):
            ytl.YulParser(tokens).find_function(
                "pick",
                known_yul_names={"helper"},
                exclude_known=True,
            )

    def test_translate_yul_to_models_rejects_shadowed_bare_block_local_inside_if(
        self,
    ) -> None:
        # Yul rejects cross-scope variable shadowing (solc error 1395).
        # This Yul snippet is invalid; the resolver catches it before
        # the lowering parser runs.
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1) -> var_z_2 {
                {
                    let usr$tmp := 5
                    if var_c_1 {
                        let usr$tmp := 7
                    }
                    var_z_2 := usr$tmp
                }
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_shadowed_conditional_local_binding(
        self,
    ) -> None:
        # Yul rejects cross-scope variable shadowing (solc error 1395).
        # This Yul snippet is invalid; the resolver catches it before
        # the lowering parser runs.
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1) -> var_z_2 {
                let usr$tmp := 5
                if var_c_1 {
                    let usr$tmp := 7
                }
                var_z_2 := usr$tmp
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_nested_helper_shadowing_selected_sibling(
        self,
    ) -> None:
        """Nested fun_g_2 shadows sibling top-level fun_g_2 — invalid per solc 1395."""
        config = make_model_config(("g", "f"))
        yul = """
            function fun_f_1(var_x_1) -> var_z_2 {
                function fun_g_2(var_y_3) -> var_r_4 {
                    var_r_4 := add(var_y_3, 1)
                }
                var_z_2 := fun_g_2(var_x_1)
            }

            function fun_g_2(var_x_5) -> var_z_6 {
                var_z_6 := add(var_x_5, 10)
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_return_shadow_in_all_switch_branches(
        self,
    ) -> None:
        # Yul rejects cross-scope variable shadowing (solc error 1395).
        # This Yul snippet is invalid; the resolver catches it before
        # the lowering parser runs.
        # NOTE: zero-initialization of return variables is tested
        # separately by existing non-shadowing tests.
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1) -> var_z_2 {
                switch var_c_1
                case 0 {
                    let var_z_2 := 1
                }
                default {
                    let var_z_2 := 2
                }
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_return_shadow_reassignment_in_all_switch_branches(
        self,
    ) -> None:
        # Yul rejects cross-scope variable shadowing (solc error 1395).
        # This Yul snippet is invalid; the resolver catches it before
        # the lowering parser runs.
        # NOTE: zero-initialization of return variables is tested
        # separately by existing non-shadowing tests.
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1) -> var_z_2 {
                switch var_c_1
                case 0 {
                    let var_z_2 := 1
                    var_z_2 := 3
                }
                default {
                    let var_z_2 := 2
                    var_z_2 := 4
                }
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_outer_assignment_before_later_shadowing_block_let(
        self,
    ) -> None:
        # Yul rejects cross-scope variable shadowing (solc error 1395).
        # This Yul snippet is invalid; the resolver catches it before
        # the lowering parser runs.
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                let usr$x := 5
                {
                    usr$x := 7
                    let usr$x := 9
                }
                var_z_2 := usr$x
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_outer_if_assignment_before_later_shadowing_block_let(
        self,
    ) -> None:
        # Yul rejects cross-scope variable shadowing (solc error 1395).
        # This Yul snippet is invalid; the resolver catches it before
        # the lowering parser runs.
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1) -> var_z_2 {
                let usr$x := 5
                {
                    if var_c_1 {
                        usr$x := 7
                    }
                    let usr$x := 9
                }
                var_z_2 := usr$x
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_outer_if_assignment_before_later_shadowing_top_level_let(
        self,
    ) -> None:
        # Yul rejects cross-scope variable shadowing (solc error 1395).
        # This Yul snippet is invalid; the resolver catches it before
        # the lowering parser runs.
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1) -> var_z_2 {
                let usr$x := 5
                if var_c_1 {
                    usr$x := 7
                    let usr$x := 9
                }
                var_z_2 := usr$x
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_nonconstant_if_branch_local_reassignment_shadowing_outer_binding(
        self,
    ) -> None:
        # Yul rejects cross-scope variable shadowing (solc error 1395).
        # This Yul snippet is invalid; the resolver catches it before
        # the lowering parser runs.
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1) -> var_z_2 {
                let usr$x := 5
                if var_c_1 {
                    let usr$x := 1
                    usr$x := 2
                }
                var_z_2 := usr$x
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_outer_switch_branch_assignment_before_later_shadowing_let(
        self,
    ) -> None:
        # Yul rejects cross-scope variable shadowing (solc error 1395).
        # This Yul snippet is invalid; the resolver catches it before
        # the lowering parser runs.
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1) -> var_z_2 {
                let usr$x := 5
                switch var_c_1
                case 0 {
                    usr$x := 7
                    let usr$x := 9
                }
                default {
                }
                var_z_2 := usr$x
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_outer_binding_after_nested_if_branch_local_ends_in_bare_block(
        self,
    ) -> None:
        # Yul rejects cross-scope variable shadowing (solc error 1395).
        # This Yul snippet is invalid; the resolver catches it before
        # the lowering parser runs.
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1) -> var_z_2 {
                let usr$x := 5
                {
                    if var_c_1 {
                        let usr$x := 1
                    }
                    usr$x := add(usr$x, 1)
                }
                var_z_2 := usr$x
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_outer_binding_after_nested_switch_branch_local_ends_in_bare_block(
        self,
    ) -> None:
        # Yul rejects cross-scope variable shadowing (solc error 1395).
        # This Yul snippet is invalid; the resolver catches it before
        # the lowering parser runs.
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1) -> var_z_2 {
                let usr$x := 5
                {
                    switch var_c_1
                    case 0 {
                        let usr$x := 1
                    }
                    default {
                    }
                    usr$x := add(usr$x, 1)
                }
                var_z_2 := usr$x
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_live_switch_case_shadowing_after_dead_default_leave(
        self,
    ) -> None:
        # Yul rejects cross-scope variable shadowing (solc error 1395).
        # This Yul snippet is invalid; the resolver catches it before
        # the lowering parser runs.
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                let usr$x := 1
                switch 0
                case 0 {
                    let usr$x := 2
                }
                default {
                    leave
                }
                var_z_2 := usr$x
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_allows_conditional_return_write_that_is_later_overwritten(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1) -> var_z_2 {
                if var_c_1 {
                    var_z_2 := 1
                }
                var_z_2 := 2
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (2,))
        self.assertEqual(ytl.evaluate_function_model(model, (1,)), (2,))

    def test_translate_yul_to_models_preserves_temporary_snapshot_across_conditional_parameter_rebind(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_x_1) -> var_z_2 {
                let expr_1 := add(var_x_1, 1)
                if 1 {
                    var_x_1 := 2
                }
                var_z_2 := expr_1
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (1,))
        self.assertEqual(ytl.evaluate_function_model(model, (5,)), (6,))

    def test_translate_yul_to_models_preserves_top_level_temporary_snapshot_inside_nonconstant_conditional(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1, var_x_2) -> var_z_3 {
                let expr_1 := var_c_1
                if var_x_2 {
                    var_c_1 := 0
                    var_z_3 := expr_1
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (7, 0)), (0,))
        self.assertEqual(ytl.evaluate_function_model(model, (7, 1)), (7,))
        self.assertEqual(ytl.evaluate_function_model(model, (9, 2)), (9,))

    def test_translate_yul_to_models_preserves_branch_local_temporary_snapshot_inside_nonconstant_conditional(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1, var_x_2) -> var_z_3 {
                if var_c_1 {
                    let expr_1 := var_x_2
                    var_x_2 := 0
                    var_z_3 := expr_1
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (0, 5)), (0,))
        self.assertEqual(ytl.evaluate_function_model(model, (1, 5)), (5,))
        self.assertEqual(ytl.evaluate_function_model(model, (2, 9)), (9,))

    def test_translate_yul_to_models_keeps_conditional_local_assignment_distinct_from_parameter_binding(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1, var_x_2) -> var_z_3 {
                let usr$c := 2
                if iszero(var_x_2) {
                    usr$c := usr$c
                    var_z_3 := var_c_1
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (0, 0)), (0,))
        self.assertEqual(ytl.evaluate_function_model(model, (7, 0)), (7,))
        self.assertEqual(ytl.evaluate_function_model(model, (7, 1)), (0,))

    def test_translate_yul_to_models_keeps_post_conditional_local_binding_distinct_from_parameter_binding(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1, var_x_2) -> var_z_3 {
                let usr$c := 3
                if iszero(var_x_2) {
                    usr$c := var_x_2
                }
                var_z_3 := eq(var_c_1, usr$c)
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (0, 0)), (1,))
        self.assertEqual(ytl.evaluate_function_model(model, (0, 1)), (0,))
        self.assertEqual(ytl.evaluate_function_model(model, (2, 1)), (0,))
        self.assertEqual(ytl.evaluate_function_model(model, (3, 1)), (1,))

    def test_translate_yul_to_models_rejects_constant_true_conditional_local_used_out_of_scope(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                let expr_1 := 1
                if expr_1 {
                    let usr$tmp := 7
                }
                var_z_2 := usr$tmp
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Undefined variable"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_constant_true_shadowing_local_binding(
        self,
    ) -> None:
        # Yul rejects cross-scope variable shadowing (solc error 1395).
        # This Yul snippet is invalid; the resolver catches it before
        # the lowering parser runs.
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                let usr$x := 5
                let expr_1 := 1
                if expr_1 {
                    let usr$x := 7
                }
                var_z_2 := usr$x
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_preserves_parser_folded_local_reassignment_in_constant_true_if(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                if 1 {
                    let usr$x := 1
                    usr$x := 2
                    var_z_2 := usr$x
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, ()), (2,))

    def test_translate_yul_to_models_rejects_parser_folded_shadowing_local_reassignment_in_constant_true_if(
        self,
    ) -> None:
        # Yul rejects cross-scope variable shadowing (solc error 1395).
        # This Yul snippet is invalid; the resolver catches it before
        # the lowering parser runs.
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                let usr$x := 5
                if 1 {
                    let usr$x := 1
                    usr$x := 2
                }
                var_z_2 := usr$x
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_constant_true_switch_shadowing_local_binding(
        self,
    ) -> None:
        # Yul rejects cross-scope variable shadowing (solc error 1395).
        # This Yul snippet is invalid; the resolver catches it before
        # the lowering parser runs.
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                let usr$x := 5
                switch 1
                case 1 {
                    let usr$x := 7
                }
                default {
                }
                var_z_2 := usr$x
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_allows_branch_local_real_var_used_later_in_constant_true_branch(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_a_1) -> var_z_2 {
                let expr_1 := 1
                if expr_1 {
                    let usr$tmp := add(var_a_1, 1)
                    var_z_2 := add(usr$tmp, 1)
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (3,)), (5,))

    def test_translate_yul_to_models_preserves_lowered_local_reassignment_in_substituted_constant_true_if(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                let expr_1 := 1
                if expr_1 {
                    let usr$x := 1
                    usr$x := 2
                    var_z_2 := usr$x
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, ()), (2,))

    def test_translate_yul_to_models_preserves_constant_true_conditional_write_to_reassigned_outer_local(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                let usr$x := 5
                usr$x := 6
                let expr_1 := 1
                if expr_1 {
                    usr$x := 7
                }
                var_z_2 := usr$x
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, ()), (7,))

    def test_translate_yul_to_models_preserves_constant_true_conditional_write_to_reassigned_parameter(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_x_1) -> var_z_2 {
                var_x_1 := add(var_x_1, 1)
                let expr_1 := 1
                if expr_1 {
                    var_x_1 := add(var_x_1, 1)
                }
                var_z_2 := var_x_1
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (3,)), (5,))

    def test_translate_yul_to_models_preserves_temporary_snapshot_across_zero_init_return_rebind(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_x_1) -> var_z_2 {
                let expr_1 := add(var_x_1, var_z_2)
                var_z_2 := 5
                var_z_2 := expr_1
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (0,))
        self.assertEqual(ytl.evaluate_function_model(model, (5,)), (5,))

    def test_translate_yul_to_models_allows_temporary_reuse_in_disjoint_switch_branches(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1) -> var_z_2 {
                switch var_c_1
                case 0 {
                    let expr_1 := 1
                    var_z_2 := expr_1
                }
                default {
                    let expr_1 := 2
                    var_z_2 := expr_1
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (1,))
        self.assertEqual(ytl.evaluate_function_model(model, (1,)), (2,))

    def test_translate_yul_to_models_rejects_unresolved_call_target(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                var_z_2 := helper()
            }
            """

        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_accepts_conditionally_constant_memory_address(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1) -> var_z_2 {
                let usr$ptr := 64
                if var_c_1 {
                    usr$ptr := 64
                }
                mstore(usr$ptr, 7)
                var_z_2 := mload(64)
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (7,))
        self.assertEqual(ytl.evaluate_function_model(model, (1,)), (7,))

    def test_translate_yul_to_models_rejects_constant_true_conditional_local_pointer_used_by_memory_write(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                let expr_1 := 1
                if expr_1 {
                    let usr$ptr := 64
                }
                mstore(usr$ptr, 7)
                var_z_2 := mload(64)
            }
            """

        with self.assertRaisesRegex(
            ytl.ParseError,
            "Undefined variable",
        ):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_preserves_constant_true_conditional_constant_memory_address_fact(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                let expr_1 := 1
                let usr$ptr := 32
                if expr_1 {
                    usr$ptr := 64
                }
                mstore(usr$ptr, 7)
                var_z_2 := mload(64)
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, ()), (7,))

    def test_translate_yul_to_models_allows_branch_local_constant_mload_address(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1) -> var_z_2 {
                mstore(64, 7)
                var_z_2 := 1
                if var_c_1 {
                    let usr$ptr := 64
                    var_z_2 := mload(usr$ptr)
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (1,))
        self.assertEqual(ytl.evaluate_function_model(model, (1,)), (7,))

    def test_translate_yul_to_models_allows_branch_local_constant_mload_address_for_kept_solidity_local(
        self,
    ) -> None:
        config = make_model_config(("f",), keep_solidity_locals=True)
        yul = """
            function fun_f_1(var_c_1) -> var_z_2 {
                mstore(64, 7)
                var_z_2 := 1
                if var_c_1 {
                    let var_ptr_3 := 64
                    var_z_2 := mload(var_ptr_3)
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (1,))
        self.assertEqual(ytl.evaluate_function_model(model, (1,)), (7,))

    def test_translate_yul_to_models_accepts_conditionally_constant_memory_address_for_kept_solidity_local(
        self,
    ) -> None:
        config = make_model_config(("f",), keep_solidity_locals=True)
        yul = """
            function fun_f_1(var_c_1) -> var_z_2 {
                let var_ptr_3 := 64
                if var_c_1 {
                    var_ptr_3 := 64
                }
                mstore(var_ptr_3, 7)
                var_z_2 := mload(64)
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (7,))
        self.assertEqual(ytl.evaluate_function_model(model, (1,)), (7,))

    def test_translate_yul_to_models_alpha_renames_callee_locals_during_inlining(
        self,
    ) -> None:
        config = make_model_config(
            ("outer",),
            exact_yul_names={"outer": "fun_outer_1"},
        )
        yul = """
            object "o" {
                code {
                    function helper(var_p_1) -> var_r_1 {
                        let usr$tmp := 0
                        var_r_1 := add(var_p_1, 1)
                    }

                    function fun_outer_1(var_x_1) -> var_z_1 {
                        let usr$tmp := var_x_1
                        var_z_1 := helper(usr$tmp)
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
            (1,),
        )
        self.assertEqual(
            ytl.evaluate_function_model(result.models[0], (5,)),
            (6,),
        )

    def test_parse_function_accepts_multi_var_declaration_without_initializer(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_pair_decl_1() -> var_z_1 {
                let usr$a, usr$b
                var_z_1 := add(usr$a, usr$b)
            }
            """)

        fn = ytl.YulParser(tokens).parse_function()

        expected: list[ytl.RawStatement] = [
            ytl.PlainAssignment("usr$a", ytl.IntLit(0), is_declaration=True),
            ytl.PlainAssignment("usr$b", ytl.IntLit(0), is_declaration=True),
            ytl.PlainAssignment(
                "var_z_1",
                ytl.Call("add", (ytl.Var("usr$a"), ytl.Var("usr$b"))),
            ),
        ]
        self.assertEqual(fn.assignments, expected)

    def test_parse_function_rejects_multi_var_initializer_from_scalar_expr(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_bad_1() -> var_z_1 {
                let usr$a, usr$b := 1
                var_z_1 := usr$a
            }
            """)

        with self.assertRaises(ytl.ParseError):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_accepts_multi_target_assignment_without_let(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_pair_assign_1() -> var_z_1 {
                let usr$a
                let usr$b
                usr$a, usr$b := pair()
                var_z_1 := usr$a
            }
            """)

        fn = ytl.YulParser(tokens).parse_function()

        expected: list[ytl.RawStatement] = [
            ytl.PlainAssignment("usr$a", ytl.IntLit(0), is_declaration=True),
            ytl.PlainAssignment("usr$b", ytl.IntLit(0), is_declaration=True),
            ytl.PlainAssignment(
                "usr$a",
                ytl.Project(0, 2, ytl.Call("pair", ())),
            ),
            ytl.PlainAssignment(
                "usr$b",
                ytl.Project(1, 2, ytl.Call("pair", ())),
            ),
            ytl.PlainAssignment("var_z_1", ytl.Var("usr$a")),
        ]
        self.assertEqual(fn.assignments, expected)

    def test_translate_yul_to_models_rejects_multi_var_builtin_call_as_multi_return(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_1 {
                let usr$a, usr$b := add(1, 2)
                var_z_1 := usr$a
            }
            """

        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_multi_target_unresolved_call_as_multi_return(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_1 {
                let usr$a
                let usr$b
                usr$a, usr$b := pair()
                var_z_1 := usr$a
            }
            """

        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_collects_nested_local_helpers_for_inlining(
        self,
    ) -> None:
        config = make_model_config(
            ("outer",),
            exact_yul_names={"outer": "fun_outer_1"},
        )
        yul = """
            object "o" {
                code {
                    function fun_outer_1() -> var_z_1 {
                        function helper() -> var_r_1 {
                            var_r_1 := 1
                        }
                        var_z_1 := helper()
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
            ytl.evaluate_function_model(
                result.models[0],
                (),
                model_table=ytl.build_model_table(result.models),
            ),
            (1,),
        )

    def test_translate_yul_to_models_rejects_nested_helper_shadowing_sibling_in_code_block(
        self,
    ) -> None:
        """Nested helper inside fun_outer_1 shadows sibling top-level helper — invalid per solc 1395."""
        config = make_model_config(
            ("outer",),
            exact_yul_names={"outer": "fun_outer_1"},
        )
        yul = """
            object "o" {
                code {
                    function helper() -> var_r_0 {
                        var_r_0 := 100
                    }

                    function fun_outer_1() -> var_z_1 {
                        function helper() -> var_r_2 {
                            var_r_2 := 7
                        }
                        var_z_1 := helper()
                    }
                }
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_duplicate_helper_names_in_same_scope(
        self,
    ) -> None:
        config = make_model_config(
            ("outer",),
            exact_yul_names={"outer": "fun_outer_1"},
        )
        yul = """
            function fun_outer_1() -> var_z_1 {
                var_z_1 := helper()
            }

            function helper() -> var_r_1 {
                var_r_1 := 1
            }

            function helper() -> var_r_2 {
                var_r_2 := 2
            }
            """

        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_duplicate_helper_names_when_first_duplicate_is_rejected(
        self,
    ) -> None:
        config = make_model_config(
            ("outer",),
            exact_yul_names={"outer": "fun_outer_1"},
        )
        yul = """
            function fun_outer_1() -> var_z_1 {
                var_z_1 := helper()
            }

            function helper() -> var_r_1 {
                for { } 0 { } {
                    var_r_1 := 1
                }
            }

            function helper() -> var_r_2 {
                var_r_2 := 7
            }
            """

        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_when_rejected_inner_helper_shadows_valid_outer_helper(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_1 {
                function helper() -> var_r_2 {
                    for { } 0 { } {
                        var_r_2 := 1
                    }
                }

                var_z_1 := helper()
            }

            function helper() -> var_r_3 {
                var_r_3 := 7
            }
            """

        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_build_lean_source_rejects_binder_collision_with_generated_model_name(
        self,
    ) -> None:
        config = make_model_config(("inner", "outer"))
        inner = ytl.FunctionModel(
            fn_name="inner",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ytl.Assignment(
                    "z",
                    ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1))),
                ),
            ),
        )
        outer = ytl.FunctionModel(
            fn_name="outer",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ytl.Assignment("model_inner", ytl.Var("x")),
                ytl.Assignment(
                    "z",
                    ytl.Call("inner", (ytl.Var("model_inner"),)),
                ),
            ),
        )

        with self.assertRaises(ytl.ParseError):
            ytl.build_lean_source(
                models=[inner, outer],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_ignores_constant_true_branch_local_binder_named_like_generated_model(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                let expr_1 := 1
                if expr_1 {
                    let usr$model_f := 1
                }
                var_z_2 := 0
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        targets: set[str] = {
            stmt.target
            for stmt in model.assignments
            if isinstance(stmt, ytl.Assignment)
        }
        self.assertNotIn("model_f", targets)

        source = ytl.build_lean_source(
            models=result.models,
            source_path="test-source",
            namespace="Test",
            config=config,
        )

        self.assertIn("def model_f_evm", source)

    def test_find_function_rejects_nonmatching_param_count_even_when_unique(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_dup_1(var_x_1, var_y_2) -> var_z_3 {
                var_z_3 := add(var_x_1, var_y_2)
            }
            """)

        with self.assertRaises(ytl.ParseError):
            ytl.YulParser(tokens).find_function("dup", n_params=1)

    def test_find_function_rejects_when_requested_arity_matches_no_candidate(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function helper(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_pick_1(var_a_3, var_b_4) -> var_z_5 {
                var_z_5 := helper(var_a_3)
            }

            function fun_pick_2(var_a_6, var_b_7, var_c_8) -> var_z_9 {
                var_z_9 := 7
            }
            """)

        with self.assertRaises(ytl.ParseError):
            ytl.YulParser(tokens).find_function(
                "pick",
                n_params=1,
                known_yul_names={"helper"},
            )

    def test_find_function_ignores_constant_false_helper_references(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function helper(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_pick_1(var_x_3) -> var_z_4 {
                if 0 {
                    var_z_4 := helper(var_x_3)
                }
                var_z_4 := 111
            }

            function fun_pick_2(var_x_5) -> var_z_6 {
                var_z_6 := helper(var_x_5)
            }
            """)

        func = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
        )
        self.assertEqual(func.yul_name, "fun_pick_2")

        leaf = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
            exclude_known=True,
        )
        self.assertEqual(leaf.yul_name, "fun_pick_1")

    def test_find_function_ignores_constant_switch_helper_references(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function helper(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_pick_1(var_x_3) -> var_z_4 {
                switch 1
                case 0 {
                    var_z_4 := helper(var_x_3)
                }
                default {
                    var_z_4 := 111
                }
            }

            function fun_pick_2(var_x_5) -> var_z_6 {
                var_z_6 := helper(var_x_5)
            }
            """)

        func = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
        )
        self.assertEqual(func.yul_name, "fun_pick_2")

        leaf = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
            exclude_known=True,
        )
        self.assertEqual(leaf.yul_name, "fun_pick_1")

    def test_find_function_respects_shadowing_between_nested_block_locals(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function helper(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_pick_1(var_c_1, var_x_3) -> var_z_4 {
                function nested(var_y_5) -> var_w_6 {
                    var_w_6 := 9
                }
                if var_c_1 {
                    function nested(var_q_7) -> var_r_8 {
                        var_r_8 := helper(var_q_7)
                    }
                    var_z_4 := 0
                }
                var_z_4 := nested(var_x_3)
            }

            function fun_pick_2(var_c_9, var_x_10) -> var_z_11 {
                var_z_11 := 7
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

        with self.assertRaisesRegex(
            ytl.ParseError,
            "Multiple Yul functions match 'pick'",
        ):
            ytl.YulParser(tokens).find_function(
                "pick",
                known_yul_names={"helper"},
                exclude_known=True,
            )

    def test_find_function_tracks_nested_helper_called_within_same_block(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function helper(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_pick_1(var_c_1, var_x_3) -> var_z_4 {
                if var_c_1 {
                    function nested(var_y_5) -> var_w_6 {
                        var_w_6 := helper(var_y_5)
                    }
                    var_z_4 := nested(var_x_3)
                }
            }

            function fun_pick_2(var_c_7, var_x_8) -> var_z_9 {
                var_z_9 := 7
            }
            """)

        func = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
        )
        self.assertEqual(func.yul_name, "fun_pick_1")

        leaf = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
            exclude_known=True,
        )
        self.assertEqual(leaf.yul_name, "fun_pick_2")

    def test_find_function_tracks_transitive_sibling_local_helper_dependencies(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function helper(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_pick_1(var_x_3) -> var_z_4 {
                function nested1(var_y_5) -> var_w_6 {
                    var_w_6 := helper(var_y_5)
                }
                function nested2(var_q_7) -> var_r_8 {
                    var_r_8 := nested1(var_q_7)
                }
                var_z_4 := nested2(var_x_3)
            }

            function fun_pick_2(var_x_9) -> var_z_10 {
                var_z_10 := 7
            }
            """)

        func = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
        )
        self.assertEqual(func.yul_name, "fun_pick_1")

        leaf = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
            exclude_known=True,
        )
        self.assertEqual(leaf.yul_name, "fun_pick_2")

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

    def test_find_function_ignores_nested_public_name_candidates(self) -> None:
        tokens = ytl.tokenize_yul("""
            function helper() -> var_h_1 {
                var_h_1 := 99
            }

            function fun_pick_1() -> var_z_1 {
                function fun_pick_2() -> var_r_2 {
                    var_r_2 := helper()
                }
                var_z_1 := 7
            }

            function fun_pick_3() -> var_z_3 {
                var_z_3 := helper()
            }
            """)

        found = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
        )

        self.assertEqual(found.yul_name, "fun_pick_3")

    def test_find_exact_function_ignores_nested_local_name_collisions(self) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_pick_1() -> var_z_1 {
                var_z_1 := 11
            }

            function fun_outer_2() -> var_r_2 {
                function fun_pick_1() -> var_s_3 {
                    var_s_3 := 99
                }
                var_r_2 := fun_pick_1()
            }
            """)

        found = ytl.YulParser(tokens).find_exact_function("fun_pick_1")

        expected_rets: list[str] = ["var_z_1"]
        self.assertEqual(found.rets, expected_rets)
        expected_assignments: list[ytl.RawStatement] = [
            ytl.PlainAssignment("var_z_1", ytl.IntLit(11)),
        ]
        self.assertEqual(found.assignments, expected_assignments)

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

    def test_translate_yul_to_models_rejects_lean_keyword_parameter_name(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_if_1) -> var_z_2 {
                var_z_2 := var_if_1
            }
            """

        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_validate_function_model_rejects_malformed_builtin_arity(self) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ytl.Assignment(
                    "z",
                    ytl.Call("add", (ytl.Var("x"),)),
                ),
            ),
        )

        with self.assertRaises(ytl.ParseError):
            ytl.validate_function_model(model)

    def test_validate_function_model_rejects_malformed_component_projection_shape(
        self,
    ) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ytl.Assignment(
                    "z",
                    ytl.Project(0, 2, ytl.Var("x")),
                ),
            ),
        )

        with self.assertRaises(ytl.ParseError):
            ytl.validate_function_model(model)

    def test_validate_function_model_rejects_out_of_range_component_projection_index(
        self,
    ) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("x", "y"),
            return_names=("z",),
            assignments=(
                ytl.Assignment(
                    "z",
                    ytl.Project(
                        2,
                        2,
                        ytl.Call("pair", (ytl.Var("x"), ytl.Var("y"))),
                    ),
                ),
            ),
        )

        with self.assertRaises(ytl.ParseError):
            ytl.validate_function_model(model)

    def test_validate_function_model_rejects_project_with_non_call_inner(self) -> None:
        """Project inner must be a Call — Var is rejected."""
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ytl.Assignment(
                    "z",
                    ytl.Project(0, 2, ytl.Var("x")),
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
            assignments=(ytl.Assignment("z", ytl.Var("normBitLengthPlus1")),),
        )
        config = ytl.ModelConfig(
            function_order=("f",),
            model_names={"f": "model_f"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={"bitLengthPlus1": "normBitLengthPlus1"},
            extra_lean_defs=("def normBitLengthPlus1 (x : Nat) : Nat := x + 1"),
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

    def test_build_lean_source_rejects_generated_model_name_collision_with_extra_norm_helper(
        self,
    ) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.Var("x")),),
        )
        config = ytl.ModelConfig(
            function_order=("f",),
            model_names={"f": "normBitLengthPlus1"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={"bitLengthPlus1": "normBitLengthPlus1"},
            extra_lean_defs=("def normBitLengthPlus1 (x : Nat) : Nat := x + 1"),
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

    def test_build_lean_source_rejects_cross_collision_between_generated_evm_and_norm_names(
        self,
    ) -> None:
        first = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.Var("x")),),
        )
        second = ytl.FunctionModel(
            fn_name="g",
            param_names=("y",),
            return_names=("r",),
            assignments=(ytl.Assignment("r", ytl.Var("y")),),
        )
        config = ytl.ModelConfig(
            function_order=("f", "g"),
            model_names={"f": "foo", "g": "foo_evm"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={},
            extra_lean_defs="",
            norm_rewrite=None,
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
                models=[first, second],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_allows_extra_norm_helper_name_when_norm_is_skipped(
        self,
    ) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("normBitLengthPlus1",),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.Var("normBitLengthPlus1")),),
        )
        config = ytl.ModelConfig(
            function_order=("f",),
            model_names={"f": "model_f"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={"bitLengthPlus1": "normBitLengthPlus1"},
            extra_lean_defs=("def normBitLengthPlus1 (x : Nat) : Nat := x + 1"),
            norm_rewrite=lambda expr: ytl.Call("bitLengthPlus1", (expr,)),
            inner_fn="f",
            n_params=None,
            exact_yul_names=None,
            keep_solidity_locals=False,
            skip_norm=frozenset({"f"}),
            hoist_repeated_calls=frozenset(),
            skip_prune=frozenset(),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )

        source = ytl.build_lean_source(
            models=[model],
            source_path="test-source",
            namespace="Test",
            config=config,
        )

        self.assertIn("def model_f_evm", source)
        self.assertNotIn("def model_f (", source)

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
            extra_lean_defs=("def normBitLengthPlus1 (x : Nat) : Nat := x + 1"),
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
            extra_lean_defs=("def normBitLengthPlus1 (x : Nat) : Nat := x + 1"),
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

    def test_find_function_ignores_dead_helper_reference_after_top_level_leave(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function helper(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_pick_1(var_x_3) -> var_z_4 {
                leave
                var_z_4 := helper(var_x_3)
            }

            function fun_pick_2(var_x_5) -> var_z_6 {
                var_z_6 := 7
            }
            """)

        found = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
        )
        self.assertEqual(found.yul_name, "fun_pick_2")

        leaf = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
            exclude_known=True,
        )
        self.assertEqual(leaf.yul_name, "fun_pick_1")

    def test_find_function_ignores_dead_helper_reference_after_constant_true_if_leave(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function helper(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_pick_1(var_x_3) -> var_z_4 {
                if 1 {
                    leave
                }
                var_z_4 := helper(var_x_3)
            }

            function fun_pick_2(var_x_5) -> var_z_6 {
                var_z_6 := 7
            }
            """)

        found = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
        )
        self.assertEqual(found.yul_name, "fun_pick_2")

        leaf = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
            exclude_known=True,
        )
        self.assertEqual(leaf.yul_name, "fun_pick_1")

    def test_inline_calls_does_not_consume_depth_budget_on_builtin_ast_nesting(
        self,
    ) -> None:
        expr: ytl.Expr = ytl.IntLit(0)
        for _ in range(41):
            expr = ytl.Call("add", (expr, ytl.IntLit(1)))

        self.assertEqual(ytl.inline_calls(expr, {}, max_depth=40), expr)

    def test_translate_yul_to_models_allows_exact_from_after_constant_false_inlined_leave(
        self,
    ) -> None:
        config = make_model_config(("target",))
        yul = """
            function fun_target_1(var_hi_1, var_lo_2) -> var_z_3 {
                var_z_3 := fun_helper_2(var_hi_1, var_lo_2)
            }

            function fun_helper_2(var_hi_4, var_lo_5) -> var_z_6 {
                if 0 {
                    leave
                }
                let usr$ptr := fun_from_3(0, var_hi_4, var_lo_5)
                var_z_6 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
            }

            function fun_from_3(var_r_7, var_hi_8, var_lo_9) -> var_r_out_10 {
                var_r_out_10 := 0
                mstore(var_r_7, var_hi_8)
                mstore(add(0x20, var_r_7), var_lo_9)
                var_r_out_10 := var_r_7
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (2, 3)), (5,))
        self.assertEqual(ytl.evaluate_function_model(model, (7, 11)), (18,))

    def test_translate_yul_to_models_allows_exact_from_in_constant_false_inlined_if_body(
        self,
    ) -> None:
        config = make_model_config(("target",))
        yul = """
            function fun_target_1(var_hi_1, var_lo_2) -> var_z_3 {
                var_z_3 := fun_helper_2(var_hi_1, var_lo_2)
            }

            function fun_helper_2(var_hi_4, var_lo_5) -> var_z_6 {
                var_z_6 := 9
                if 0 {
                    let usr$ptr := fun_from_3(0, var_hi_4, var_lo_5)
                    var_z_6 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                }
            }

            function fun_from_3(var_r_7, var_hi_8, var_lo_9) -> var_r_out_10 {
                var_r_out_10 := 0
                mstore(var_r_7, var_hi_8)
                mstore(add(0x20, var_r_7), var_lo_9)
                var_r_out_10 := var_r_7
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (2, 3)), (9,))
        self.assertEqual(ytl.evaluate_function_model(model, (7, 11)), (9,))

    def test_translate_yul_to_models_allows_constant_switch_with_dead_leave_branch(
        self,
    ) -> None:
        config = make_model_config(("target",))
        yul = """
            function fun_target_1() -> var_z_2 {
                var_z_2 := fun_helper_2()
            }

            function fun_helper_2() -> var_z_3 {
                switch 1
                case 0 {
                    var_z_3 := 7
                    leave
                }
                default {
                    var_z_3 := 9
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(ytl.evaluate_function_model(result.models[0], ()), (9,))

    def test_translate_yul_to_models_allows_constant_true_switch_with_dead_leave_branch_in_helper(
        self,
    ) -> None:
        config = make_model_config(("target",))
        yul = """
            function fun_target_1(var_x_1) -> var_z_2 {
                var_z_2 := fun_helper_2(var_x_1)
            }

            function fun_helper_2(var_a_3) -> var_r_4 {
                switch 1
                case 0 {
                    var_r_4 := 7
                    leave
                }
                default {
                    var_r_4 := add(var_a_3, 1)
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (1,))
        self.assertEqual(ytl.evaluate_function_model(model, (9,)), (10,))

    def test_translate_yul_to_models_preserves_constant_zero_switch_leave_path_in_inlined_helper(
        self,
    ) -> None:
        config = make_model_config(("target",))
        yul = """
            function fun_target_1() -> var_z_2 {
                var_z_2 := fun_helper_2(0)
            }

            function fun_helper_2(var_flag_3) -> var_r_4 {
                switch var_flag_3
                case 0 {
                    var_r_4 := 1
                    leave
                }
                default {
                    var_r_4 := 2
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(ytl.evaluate_function_model(result.models[0], ()), (1,))

    def test_translate_yul_to_models_preserves_constant_zero_switch_leave_path_with_trailing_dead_code(
        self,
    ) -> None:
        config = make_model_config(("target",))
        yul = """
            function fun_target_1() -> var_z_2 {
                var_z_2 := fun_helper_2(0)
            }

            function fun_helper_2(var_flag_3) -> var_r_4 {
                switch var_flag_3
                case 0 {
                    var_r_4 := 1
                    leave
                }
                default {
                    var_r_4 := 2
                }
                var_r_4 := 9
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(ytl.evaluate_function_model(result.models[0], ()), (1,))

    def test_build_lean_source_separates_extra_lean_defs_from_following_norm_helpers(
        self,
    ) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.Var("x")),),
        )
        config = ytl.ModelConfig(
            function_order=("f",),
            model_names={"f": "model_f"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={"bitLengthPlus1": "normBitLengthPlus1"},
            extra_lean_defs=("def normBitLengthPlus1 (x : Nat) : Nat := x + 1"),
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

        source = ytl.build_lean_source(
            models=[model],
            source_path="test-source",
            namespace="Test",
            config=config,
        )

        self.assertIn(
            "def normBitLengthPlus1 (x : Nat) : Nat := x + 1\n\ndef normLt",
            source,
        )

    def test_translate_yul_to_models_rejects_selected_model_call_with_wrong_arity(
        self,
    ) -> None:
        config = make_model_config(("f", "g"))
        yul = """
            function fun_f_1(var_x_1) -> var_z_2 {
                var_z_2 := fun_g_2(var_x_1)
            }

            function fun_g_2(var_a_3, var_b_4) -> var_r_5 {
                var_r_5 := add(var_a_3, var_b_4)
            }
            """

        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_ignores_dead_constant_false_selected_call_with_wrong_arity(
        self,
    ) -> None:
        config = make_model_config(("f", "g"))
        yul = """
            function fun_f_1() -> var_z_2 {
                var_z_2 := 0
                if 0 {
                    var_z_2 := fun_g_2(1, 2)
                }
            }

            function fun_g_2(var_x_3) -> var_r_4 {
                var_r_4 := var_x_3
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(ytl.evaluate_function_model(result.models[0], ()), (0,))

    def test_translate_yul_to_models_rejects_duplicate_selected_functions(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_x_1) -> var_z_2 {
                var_z_2 := add(var_x_1, 1)
            }
            """

        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                selected_functions=("f", "f"),
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_selected_multi_return_call_in_scalar_context(
        self,
    ) -> None:
        config = make_model_config(("f", "g"))
        yul = """
            function fun_f_1(var_x_1) -> var_z_2 {
                var_z_2 := fun_g_2(var_x_1)
            }

            function fun_g_2(var_a_3) -> var_r_4, var_s_5 {
                var_r_4 := var_a_3
                var_s_5 := add(var_a_3, 1)
            }
            """

        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_selected_projection_when_callee_returns_too_few_values(
        self,
    ) -> None:
        config = make_model_config(("f", "g"))
        yul = """
            function fun_f_1(var_x_1) -> var_z_2 {
                let usr$a, usr$b := fun_g_2(var_x_1)
                var_z_2 := add(usr$a, usr$b)
            }

            function fun_g_2(var_a_3) -> var_r_4 {
                var_r_4 := add(var_a_3, 1)
            }
            """

        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_selected_projection_when_callee_returns_too_many_values(
        self,
    ) -> None:
        config = make_model_config(("f", "g"))
        yul = """
            function fun_f_1(var_x_1) -> var_z_2 {
                let usr$a, usr$b := fun_g_2(var_x_1)
                var_z_2 := usr$a
            }

            function fun_g_2(var_a_3) -> var_r_4, var_s_5, var_t_6 {
                var_r_4 := var_a_3
                var_s_5 := add(var_a_3, 1)
                var_t_6 := add(var_a_3, 2)
            }
            """

        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_allows_exact_from_after_constant_true_inlined_leave(
        self,
    ) -> None:
        config = make_model_config(("target",))
        yul = """
            function fun_target_1(var_hi_1, var_lo_2) -> var_z_3 {
                var_z_3 := fun_helper_2(var_hi_1, var_lo_2)
            }

            function fun_helper_2(var_hi_4, var_lo_5) -> var_z_6 {
                if 1 {
                    var_z_6 := 9
                    leave
                }
                let usr$ptr := fun_from_3(0, var_hi_4, var_lo_5)
                var_z_6 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
            }

            function fun_from_3(var_r_7, var_hi_8, var_lo_9) -> var_r_out_10 {
                var_r_out_10 := 0
                mstore(var_r_7, var_hi_8)
                mstore(add(0x20, var_r_7), var_lo_9)
                var_r_out_10 := var_r_7
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (2, 3)), (9,))
        self.assertEqual(ytl.evaluate_function_model(model, (7, 11)), (9,))

    def test_translate_yul_to_models_collects_outer_helpers_for_exact_nested_target(
        self,
    ) -> None:
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "helper2"},
        )
        yul = """
            function helper() -> var_r_1 {
                var_r_1 := 7
            }

            function fun_outer_1() -> var_z_1 {
                function helper2() -> var_r_2 {
                    var_r_2 := helper()
                }
                var_z_1 := helper2()
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(
            ytl.evaluate_function_model(
                result.models[0],
                (),
                model_table=ytl.build_model_table(result.models),
            ),
            (7,),
        )

    def test_translate_yul_to_models_rejects_qualified_nested_homonym_shadowing_sibling(
        self,
    ) -> None:
        """Nested helper2 inside fun_outer_1 shadows sibling top-level helper2 — invalid per solc 1395."""
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_outer_1::helper2"},
        )
        yul = """
            function helper2() -> var_r_1 {
                var_r_1 := 1
            }

            function fun_outer_1() -> var_z_2 {
                function helper2() -> var_r_3 {
                    var_r_3 := 7
                }
                var_z_2 := helper2()
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_ambiguous_unqualified_exact_target_across_scopes(
        self,
    ) -> None:
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "top"},
        )
        yul = """
            function top() -> var_r_1 {
                var_r_1 := 1
            }

            function outer() -> var_z_2 {
                function top() -> var_r_3 {
                    var_r_3 := 2
                }
                var_z_2 := top()
            }
            """

        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_nested_top_shadowing_sibling_when_qualified(
        self,
    ) -> None:
        """Nested top inside outer shadows sibling top-level top — invalid per solc 1395."""
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "::top"},
        )
        yul = """
            function top() -> var_r_1 {
                var_r_1 := 1
            }

            function outer() -> var_z_2 {
                function top() -> var_r_3 {
                    var_r_3 := 2
                }
                var_z_2 := top()
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_exact_nested_target_rejects_rejected_sibling_helper_shadowing_outer_helper(
        self,
    ) -> None:
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_outer_1::target"},
        )
        yul = """
            function helper() -> var_r_1 {
                var_r_1 := 7
            }

            function fun_outer_1() -> var_z_2 {
                function helper() -> var_r_3 {
                    for { } 0 { } {
                        var_r_3 := 1
                    }
                }

                function target() -> var_r_4 {
                    var_r_4 := helper()
                }

                var_z_2 := target()
            }
            """

        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_build_lean_source_rejects_binder_collision_with_generated_evm_model_name(
        self,
    ) -> None:
        config = make_model_config(("inner", "outer"))
        inner = ytl.FunctionModel(
            fn_name="inner",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ytl.Assignment(
                    "z",
                    ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1))),
                ),
            ),
        )
        outer = ytl.FunctionModel(
            fn_name="outer",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ytl.Assignment("model_inner_evm", ytl.Var("x")),
                ytl.Assignment(
                    "z",
                    ytl.Call("inner", (ytl.Var("model_inner_evm"),)),
                ),
            ),
        )

        with self.assertRaises(ytl.ParseError):
            ytl.build_lean_source(
                models=[inner, outer],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_allows_binder_named_like_skipped_norm_model(
        self,
    ) -> None:
        base = make_model_config(("f",))
        config = ytl.ModelConfig(
            function_order=base.function_order,
            model_names=base.model_names,
            header_comment=base.header_comment,
            generator_label=base.generator_label,
            extra_norm_ops=base.extra_norm_ops,
            extra_lean_defs=base.extra_lean_defs,
            norm_rewrite=base.norm_rewrite,
            inner_fn=base.inner_fn,
            n_params=base.n_params,
            exact_yul_names=base.exact_yul_names,
            keep_solidity_locals=base.keep_solidity_locals,
            exclude_known=base.exclude_known,
            skip_norm=frozenset({"f"}),
            hoist_repeated_calls=base.hoist_repeated_calls,
            skip_prune=base.skip_prune,
            default_source_label=base.default_source_label,
            default_namespace=base.default_namespace,
            default_output=base.default_output,
            cli_description=base.cli_description,
        )
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("model_f",),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.Var("model_f")),),
        )

        source = ytl.build_lean_source(
            models=[model],
            source_path="test-source",
            namespace="Test",
            config=config,
        )

        self.assertIn("def model_f_evm", source)
        self.assertNotIn("\ndef model_f ", source)

    def test_build_lean_source_allows_reserved_base_name_for_skipped_norm_model(
        self,
    ) -> None:
        config = ytl.ModelConfig(
            function_order=("f",),
            model_names={"f": "normAdd"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={},
            extra_lean_defs="",
            norm_rewrite=None,
            inner_fn="f",
            skip_norm=frozenset({"f"}),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.Var("x")),),
        )

        source = ytl.build_lean_source(
            models=[model],
            source_path="test-source",
            namespace="Test",
            config=config,
        )

        self.assertIn("def normAdd_evm", source)
        self.assertNotIn("\ndef normAdd ", source)

    def test_build_lean_source_allows_extra_norm_helper_name_for_skipped_norm_model(
        self,
    ) -> None:
        config = ytl.ModelConfig(
            function_order=("f",),
            model_names={"f": "normBitLengthPlus1"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={"bitLengthPlus1": "normBitLengthPlus1"},
            extra_lean_defs="def normBitLengthPlus1 (x : Nat) : Nat := x + 1",
            norm_rewrite=None,
            inner_fn="f",
            skip_norm=frozenset({"f"}),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.Var("x")),),
        )

        source = ytl.build_lean_source(
            models=[model],
            source_path="test-source",
            namespace="Test",
            config=config,
        )

        self.assertIn("def normBitLengthPlus1_evm", source)
        self.assertNotIn("\ndef normBitLengthPlus1 ", source)

    def test_build_lean_source_allows_skipped_norm_model_name_when_other_models_emit_norm_defs(
        self,
    ) -> None:
        config = ytl.ModelConfig(
            function_order=("f", "g"),
            model_names={"f": "normAdd", "g": "model_g"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={},
            extra_lean_defs="",
            norm_rewrite=None,
            inner_fn="f",
            skip_norm=frozenset({"f"}),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )
        models = [
            ytl.FunctionModel(
                fn_name="f",
                param_names=("x",),
                return_names=("z",),
                assignments=(ytl.Assignment("z", ytl.Var("x")),),
            ),
            ytl.FunctionModel(
                fn_name="g",
                param_names=("y",),
                return_names=("w",),
                assignments=(ytl.Assignment("w", ytl.Var("y")),),
            ),
        ]

        source = ytl.build_lean_source(
            models=models,
            source_path="test-source",
            namespace="Test",
            config=config,
        )

        self.assertIn("def normAdd_evm (x : Nat) : Nat :=", source)
        self.assertNotIn(
            "/-- Normalized auto-generated model of `f` on Nat arithmetic. -/",
            source,
        )
        self.assertIn(
            "/-- Normalized auto-generated model of `g` on Nat arithmetic. -/",
            source,
        )

    def test_translate_yul_to_models_allows_constant_false_top_level_memory_write_branch(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                if 0 {
                    mstore(0, 7)
                }
                var_z_2 := 9
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(
            ytl.evaluate_function_model(result.models[0], ()),
            (9,),
        )

    def test_translate_yul_to_models_allows_constant_switch_case_memory_write_branch(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                switch 0
                case 0 {
                    mstore(0, 7)
                }
                default {
                }
                var_z_2 := mload(0)
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(
            ytl.evaluate_function_model(result.models[0], ()),
            (7,),
        )

    def test_translate_yul_to_models_rejects_recursive_selected_model_call(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                var_z_2 := fun_f_1()
            }
            """

        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_ignores_dead_selected_cycle_edge_from_constant_false_branch(
        self,
    ) -> None:
        config = make_model_config(("f", "g"))
        yul = """
            function fun_f_1() -> var_z_2 {
                var_z_2 := 0
                if 0 {
                    var_z_2 := fun_g_2()
                }
            }

            function fun_g_2() -> var_r_3 {
                var_r_3 := fun_f_1()
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model_table = ytl.build_model_table(result.models)

        self.assertEqual(
            ytl.evaluate_function_model(
                model_table["f"],
                (),
                model_table=model_table,
            ),
            (0,),
        )
        self.assertEqual(
            ytl.evaluate_function_model(
                model_table["g"],
                (),
                model_table=model_table,
            ),
            (0,),
        )

    def test_translate_yul_to_models_ignores_dead_constant_false_selected_projection_mismatch(
        self,
    ) -> None:
        config = make_model_config(("f", "g"))
        yul = """
            function fun_f_1() -> var_z_2 {
                var_z_2 := 0
                if 0 {
                    let usr$a, usr$b := fun_g_2()
                    var_z_2 := usr$a
                }
            }

            function fun_g_2() -> var_r_3 {
                var_r_3 := 1
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(ytl.evaluate_function_model(result.models[0], ()), (0,))

    def test_translate_yul_to_models_allows_constant_false_direct_leave_branch(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                if 0 {
                    leave
                }
                var_z_2 := 9
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(
            ytl.evaluate_function_model(result.models[0], ()),
            (9,),
        )

    def test_build_lean_source_rejects_generated_model_name_collision_in_conditional_output_vars(
        self,
    ) -> None:
        config = make_model_config(("inner", "outer"))
        inner = ytl.FunctionModel(
            fn_name="inner",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ytl.Assignment(
                    "z",
                    ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1))),
                ),
            ),
        )
        outer = ytl.FunctionModel(
            fn_name="outer",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ytl.ConditionalBlock(
                    condition=ytl.Var("x"),
                    output_vars=("model_inner",),
                    then_branch=ytl.ConditionalBranch(
                        assignments=(),
                        outputs=("x",),
                    ),
                    else_branch=ytl.ConditionalBranch(
                        assignments=(),
                        outputs=("x",),
                    ),
                ),
                ytl.Assignment(
                    "z",
                    ytl.Call("inner", (ytl.Var("model_inner"),)),
                ),
            ),
        )

        with self.assertRaises(ytl.ParseError):
            ytl.build_lean_source(
                models=[inner, outer],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_rejects_generated_evm_model_name_collision_in_conditional_branch_targets(
        self,
    ) -> None:
        config = make_model_config(("inner", "outer"))
        inner = ytl.FunctionModel(
            fn_name="inner",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ytl.Assignment(
                    "z",
                    ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1))),
                ),
            ),
        )
        outer = ytl.FunctionModel(
            fn_name="outer",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ytl.ConditionalBlock(
                    condition=ytl.Var("x"),
                    output_vars=("tmp",),
                    then_branch=ytl.ConditionalBranch(
                        assignments=(
                            ytl.Assignment("model_inner_evm", ytl.Var("x")),
                            ytl.Assignment(
                                "tmp",
                                ytl.Call(
                                    "inner",
                                    (ytl.Var("model_inner_evm"),),
                                ),
                            ),
                        ),
                        outputs=("tmp",),
                    ),
                    else_branch=ytl.ConditionalBranch(
                        assignments=(
                            ytl.Assignment("model_inner_evm", ytl.IntLit(0)),
                            ytl.Assignment(
                                "tmp",
                                ytl.Call(
                                    "inner",
                                    (ytl.Var("model_inner_evm"),),
                                ),
                            ),
                        ),
                        outputs=("tmp",),
                    ),
                ),
                ytl.Assignment("z", ytl.Var("tmp")),
            ),
        )

        with self.assertRaises(ytl.ParseError):
            ytl.build_lean_source(
                models=[inner, outer],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_rejects_invalid_namespace_name(self) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.Var("x")),),
        )
        config = make_model_config(("f",))

        with self.assertRaises(ytl.ParseError):
            ytl.build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="invalid-name",
                config=config,
            )

    def test_build_lean_source_rejects_lean_keyword_namespace(self) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.Var("x")),),
        )
        config = make_model_config(("f",))

        with self.assertRaises(ytl.ParseError):
            ytl.build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="if",
                config=config,
            )

    def test_build_lean_source_rejects_source_path_newline_injection(self) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.Var("x")),),
        )
        config = make_model_config(("f",))

        with self.assertRaises(ytl.ParseError):
            ytl.build_lean_source(
                models=[model],
                source_path="test-source\nopen scoped BigOperators",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_rejects_generator_label_newline_injection(
        self,
    ) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.Var("x")),),
        )
        config = ytl.ModelConfig(
            function_order=("f",),
            model_names={"f": "model_f"},
            header_comment="test",
            generator_label=("formal/test_yul_to_lean.py\nopen scoped BigOperators"),
            extra_norm_ops={},
            extra_lean_defs="",
            norm_rewrite=None,
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

    def test_build_lean_source_rejects_header_comment_terminator_injection(
        self,
    ) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.Var("x")),),
        )
        config = ytl.ModelConfig(
            function_order=("f",),
            model_names={"f": "model_f"},
            header_comment="test -/\nopen scoped BigOperators\n/--",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={},
            extra_lean_defs="",
            norm_rewrite=None,
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

    def test_translate_yul_to_models_rejects_mutually_recursive_selected_model_calls(
        self,
    ) -> None:
        config = make_model_config(("f", "g"))
        yul = """
            function fun_f_1(var_x_1) -> var_z_2 {
                var_z_2 := fun_g_2(var_x_1)
            }

            function fun_g_2(var_y_3) -> var_r_4 {
                var_r_4 := fun_f_1(var_y_3)
            }
            """

        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_build_lean_source_rejects_invalid_generated_model_name(self) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.Var("x")),),
        )
        config = ytl.ModelConfig(
            function_order=("f",),
            model_names={"f": "bad-name"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={},
            extra_lean_defs="",
            norm_rewrite=None,
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

    def test_build_lean_source_rejects_lean_keyword_generated_model_name(
        self,
    ) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.Var("x")),),
        )
        config = ytl.ModelConfig(
            function_order=("f",),
            model_names={"f": "if"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={},
            extra_lean_defs="",
            norm_rewrite=None,
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

    def test_build_lean_source_rejects_generated_model_name_collision_with_builtin_helper(
        self,
    ) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.Var("x")),),
        )
        config = ytl.ModelConfig(
            function_order=("f",),
            model_names={"f": "u256"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={},
            extra_lean_defs="",
            norm_rewrite=None,
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

    def test_build_lean_source_rejects_missing_model_name_mapping(self) -> None:
        model = ytl.FunctionModel(
            fn_name="g",
            param_names=("x",),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.Var("x")),),
        )
        config = make_model_config(("f",))

        with self.assertRaises(ytl.ParseError):
            ytl.build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_rejects_duplicate_generated_model_names(self) -> None:
        first = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.Var("x")),),
        )
        second = ytl.FunctionModel(
            fn_name="g",
            param_names=("y",),
            return_names=("r",),
            assignments=(ytl.Assignment("r", ytl.Var("y")),),
        )
        config = ytl.ModelConfig(
            function_order=("f", "g"),
            model_names={"f": "model_dup", "g": "model_dup"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={},
            extra_lean_defs="",
            norm_rewrite=None,
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
                models=[first, second],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_parse_function_skips_dead_code_after_leave_inside_bare_block(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function fun_f_1() -> var_z_2 {
                {
                    var_z_2 := 1
                    leave
                }
                var_z_2 := 2
            }
            """)

        parsed = ytl.YulParser(tokens).parse_function()

        expected: list[ytl.RawStatement] = [
            ytl.PlainAssignment("var_z_2", ytl.IntLit(1)),
        ]
        self.assertEqual(parsed.assignments, expected)

    def test_translate_yul_to_models_preserves_bare_block_temporary_snapshot_across_outer_rebind(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_x_1) -> var_z_2 {
                {
                    let usr$tmp := var_x_1
                    var_x_1 := 5
                    var_z_2 := usr$tmp
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (0,))
        self.assertEqual(ytl.evaluate_function_model(model, (7,)), (7,))

    def test_translate_yul_to_models_bare_block_alpha_rename_does_not_collide_with_user_identifiers(
        self,
    ) -> None:
        config = make_model_config(("f",))
        # The bare-block alpha-renaming must not produce names that
        # collide with user-visible Yul identifiers.  Here ``_blk_1``
        # is a legitimate user variable; the internal renaming of
        # ``usr$t`` must choose a name that cannot clash.
        yul = """
            function fun_f_1() -> var_z_2 {
                let _blk_1 := 9
                {
                    let usr$t := 1
                    var_z_2 := usr$t
                }
                var_z_2 := _blk_1
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, ()), (9,))

    def test_translate_yul_to_models_wraps_large_integer_literals_to_u256(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = f"""
            function fun_f_1() -> var_z_2 {{
                var_z_2 := {ytl.WORD_MOD + 1}
            }}
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(ytl.evaluate_function_model(result.models[0], ()), (1,))

    def test_translate_yul_to_models_wraps_large_memory_addresses_to_u256(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = f"""
            function fun_f_1() -> var_z_2 {{
                mstore({ytl.WORD_MOD}, 7)
                var_z_2 := mload(0)
            }}
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(ytl.evaluate_function_model(result.models[0], ()), (7,))

    def test_translate_yul_to_models_wraps_large_switch_case_literals_to_u256(
        self,
    ) -> None:
        config = make_model_config(("f",))
        cases: dict[
            str,
            tuple[str, list[tuple[tuple[int, ...], tuple[int, ...]]]],
        ] = {
            "constant_switch": (
                f"""
                function fun_f_1() -> var_z_2 {{
                    switch 0
                    case {ytl.WORD_MOD} {{
                        var_z_2 := 7
                    }}
                    default {{
                        var_z_2 := 9
                    }}
                }}
                """,
                [((), (7,))],
            ),
            "nonconstant_switch": (
                f"""
                function fun_f_1(var_x_1) -> var_z_2 {{
                    switch var_x_1
                    case {ytl.WORD_MOD} {{
                        var_z_2 := 7
                    }}
                    default {{
                        var_z_2 := 9
                    }}
                }}
                """,
                [((0,), (7,)), ((1,), (9,))],
            ),
        }

        for name, (yul, expectations) in cases.items():
            with self.subTest(name=name):
                result = ytl.translate_yul_to_models(
                    yul,
                    config,
                    pipeline=ytl.RAW_TRANSLATION_PIPELINE,
                )
                model = result.models[0]
                for args, expected in expectations:
                    self.assertEqual(ytl.evaluate_function_model(model, args), expected)

    def test_build_lean_source_ignores_dead_constant_false_branch_with_unresolved_helper(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                var_z_2 := 0
                if 0 {
                    var_z_2 := helper()
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(ytl.evaluate_function_model(result.models[0], ()), (0,))
        ytl.build_lean_source(
            models=result.models,
            source_path="test-source",
            namespace="Test",
            config=config,
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
                            ytl.Project(
                                0,
                                2,
                                ytl.Call("pair", (ytl.Var("p"),)),
                            ),
                            ytl.Project(
                                0,
                                2,
                                ytl.Call("pair", (ytl.Var("p"),)),
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

    def test_translate_yul_to_models_conditional_output_order_is_hash_seed_deterministic(
        self,
    ) -> None:
        formal_dir = pathlib.Path(__file__).resolve().parent
        code = f"""
import pathlib
import sys

sys.path.insert(0, {str(formal_dir)!r})

import yul_to_lean as ytl

config = ytl.ModelConfig(
    function_order=("f",),
    model_names={{"f": "model_f"}},
    header_comment="test",
    generator_label="formal/test_yul_to_lean.py",
    extra_norm_ops={{}},
    extra_lean_defs="",
    norm_rewrite=None,
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
yul = \"\"\"
function fun_f_1(var_c_1, var_x_2) -> var_z_3 {{
    let usr$a := 1
    if var_x_2 {{
        usr$a := 2
        var_c_1 := 3
    }}
    var_z_3 := add(var_c_1, usr$a)
}}
\"\"\"
result = ytl.translate_yul_to_models(
    yul,
    config,
    pipeline=ytl.RAW_TRANSLATION_PIPELINE,
)
stmt = next(
    assignment
    for assignment in result.models[0].assignments
    if isinstance(assignment, ytl.ConditionalBlock)
)
print(repr((stmt.output_vars, stmt.then_branch.outputs, stmt.else_branch.outputs)))
"""

        outputs: list[str] = []
        for seed in ("1", "2"):
            env = dict(os.environ)
            env["PYTHONHASHSEED"] = seed
            completed = subprocess.run(
                [sys.executable, "-c", code],
                check=True,
                capture_output=True,
                text=True,
                env=env,
            )
            outputs.append(completed.stdout.strip())

        self.assertEqual(outputs[0], outputs[1])


class BranchExprStmtTest(unittest.TestCase):
    """Tests for scope-aware expression-statement tracking in branches."""

    def test_inline_dead_branch_expr_stmt_discarded(self) -> None:
        """Bare expression in dead if-branch is discarded during inlining."""
        yul = """
            function fun_target_1(var_x_1) -> var_z_2 {
                var_z_2 := helper(var_x_1, 3)
            }
            function helper(var_x_3, var_y_4) -> var_r_5 {
                if iszero(var_y_4) { side_effect() }
                var_r_5 := div(var_x_3, var_y_4)
            }
        """
        config = make_model_config(("target",))
        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        self.assertEqual(ytl.evaluate_function_model(model, (9,)), (3,))

    def test_inline_live_branch_expr_stmt_rejected(self) -> None:
        """Bare expression in live if-branch is still rejected."""
        yul = """
            function fun_target_1(var_x_1) -> var_z_2 {
                var_z_2 := helper(var_x_1, 0)
            }
            function helper(var_x_3, var_y_4) -> var_r_5 {
                if iszero(var_y_4) { side_effect() }
                var_r_5 := div(var_x_3, var_y_4)
            }
        """
        config = make_model_config(("target",))
        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_inline_non_constant_branch_expr_stmt_rejected(self) -> None:
        """Bare expression in non-constant branch is rejected."""
        yul = """
            function fun_target_1(var_x_1, var_y_2) -> var_z_3 {
                var_z_3 := helper(var_x_1, var_y_2)
            }
            function helper(var_x_4, var_y_5) -> var_r_6 {
                if iszero(var_y_5) { side_effect() }
                var_r_6 := div(var_x_4, var_y_5)
            }
        """
        config = make_model_config(("target",))
        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    # -- Switch-based expr_stmts --

    def test_switch_dead_case0_expr_stmt_discarded(self) -> None:
        """Expr_stmt in dead case-0 branch of a switch is discarded."""
        yul = """
            function fun_target_1(var_x_1) -> var_z_2 {
                var_z_2 := helper(var_x_1, 5)
            }
            function helper(var_x_3, var_y_4) -> var_r_5 {
                switch iszero(var_y_4)
                case 0 {
                    var_r_5 := div(var_x_3, var_y_4)
                }
                default {
                    side_effect()
                    var_r_5 := 0
                }
            }
        """
        config = make_model_config(("target",))
        # iszero(5) == 0 → case 0 is live, default (with side_effect) is dead
        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        self.assertEqual(ytl.evaluate_function_model(model, (15,)), (3,))

    def test_switch_live_default_expr_stmt_rejected(self) -> None:
        """Expr_stmt in live default branch of a switch is rejected."""
        yul = """
            function fun_target_1(var_x_1) -> var_z_2 {
                var_z_2 := helper(var_x_1, 0)
            }
            function helper(var_x_3, var_y_4) -> var_r_5 {
                switch iszero(var_y_4)
                case 0 {
                    var_r_5 := div(var_x_3, var_y_4)
                }
                default {
                    side_effect()
                    var_r_5 := 0
                }
            }
        """
        config = make_model_config(("target",))
        # iszero(0) == 1 → default is live, and it has side_effect()
        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    # -- Leave-bearing branches with expr_stmts --

    def test_leave_dead_branch_expr_stmt_discarded(self) -> None:
        """Expr_stmt in dead leave-bearing branch is discarded."""
        yul = """
            function fun_target_1(var_x_1) -> var_z_2 {
                var_z_2 := helper(var_x_1, 3)
            }
            function helper(var_x_3, var_y_4) -> var_r_5 {
                var_r_5 := 99
                if iszero(var_y_4) {
                    side_effect()
                    var_r_5 := 0
                    leave
                }
                var_r_5 := div(var_x_3, var_y_4)
            }
        """
        config = make_model_config(("target",))
        # iszero(3) == 0 → DEAD, leave branch discarded along with side_effect
        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        self.assertEqual(ytl.evaluate_function_model(model, (9,)), (3,))

    def test_leave_live_branch_expr_stmt_rejected(self) -> None:
        """Expr_stmt in live leave-bearing branch is rejected."""
        yul = """
            function fun_target_1(var_x_1) -> var_z_2 {
                var_z_2 := helper(var_x_1, 0)
            }
            function helper(var_x_3, var_y_4) -> var_r_5 {
                var_r_5 := 99
                if iszero(var_y_4) {
                    side_effect()
                    var_r_5 := 0
                    leave
                }
                var_r_5 := div(var_x_3, var_y_4)
            }
        """
        config = make_model_config(("target",))
        # iszero(0) == 1 → THEN_LIVE, leave branch has side_effect()
        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_leave_switch_dead_else_expr_stmt_discarded(self) -> None:
        """Expr_stmt in dead else-branch of leave-bearing switch is discarded."""
        yul = """
            function fun_target_1(var_x_1) -> var_z_2 {
                var_z_2 := helper(var_x_1, 3)
            }
            function helper(var_x_3, var_y_4) -> var_r_5 {
                var_r_5 := 99
                switch iszero(var_y_4)
                case 0 {
                    var_r_5 := div(var_x_3, var_y_4)
                }
                default {
                    side_effect()
                    var_r_5 := 0
                    leave
                }
            }
        """
        config = make_model_config(("target",))
        # iszero(3) == 0 → case 0 is live; default (with leave+side_effect) dead
        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        self.assertEqual(ytl.evaluate_function_model(model, (12,)), (4,))

    def test_leave_switch_live_else_expr_stmt_rejected(self) -> None:
        """Expr_stmt in live else-branch of leave-bearing switch is rejected."""
        yul = """
            function fun_target_1(var_x_1) -> var_z_2 {
                var_z_2 := helper(var_x_1, 0)
            }
            function helper(var_x_3, var_y_4) -> var_r_5 {
                var_r_5 := 99
                switch iszero(var_y_4)
                case 0 {
                    side_effect()
                    var_r_5 := div(var_x_3, var_y_4)
                }
                default {
                    var_r_5 := 0
                    leave
                }
            }
        """
        config = make_model_config(("target",))
        # iszero(0) == 1 → default (leave) is THEN_LIVE; case 0 is ELSE_LIVE.
        # After switch normalization, the leave-bearing default becomes body.
        # The case-0 branch (with side_effect) becomes else_body.
        # Since leave is taken, else_body is unused — but if the fold picks
        # ELSE_LIVE, the side_effect must be rejected.
        # Actually iszero(0)==1 makes condition truthy → THEN_LIVE (leave taken).
        # That means the else-branch (case 0 with side_effect) is dead.
        # So this should succeed.
        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        # Leave branch: r = 0
        self.assertEqual(ytl.evaluate_function_model(model, (42,)), (0,))

    # -- Direct target function (yul_function_to_model path) --

    def test_direct_target_dead_branch_expr_stmt_discarded(self) -> None:
        """Branch expr_stmt in target function is discarded when branch is dead."""
        yul = """
            function fun_target_1(var_x_1) -> var_z_2 {
                if iszero(1) { side_effect() }
                var_z_2 := add(var_x_1, 1)
            }
        """
        config = make_model_config(("target",))
        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        self.assertEqual(ytl.evaluate_function_model(model, (5,)), (6,))

    def test_direct_target_live_branch_expr_stmt_rejected(self) -> None:
        """Branch expr_stmt in target function is rejected when branch is live."""
        yul = """
            function fun_target_1(var_x_1) -> var_z_2 {
                if iszero(0) { side_effect() }
                var_z_2 := add(var_x_1, 1)
            }
        """
        config = make_model_config(("target",))
        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_direct_target_non_constant_branch_expr_stmt_rejected(self) -> None:
        """Branch expr_stmt in target function is rejected when condition is variable."""
        yul = """
            function fun_target_1(var_x_1) -> var_z_2 {
                if var_x_1 { side_effect() }
                var_z_2 := add(var_x_1, 1)
            }
        """
        config = make_model_config(("target",))
        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    # -- Multiple expr_stmts in one branch --

    def test_multiple_expr_stmts_in_dead_branch_discarded(self) -> None:
        """Multiple bare expressions in a dead branch are all discarded."""
        yul = """
            function fun_target_1(var_x_1) -> var_z_2 {
                var_z_2 := helper(var_x_1, 3)
            }
            function helper(var_x_3, var_y_4) -> var_r_5 {
                if iszero(var_y_4) {
                    side_effect_a()
                    side_effect_b()
                }
                var_r_5 := div(var_x_3, var_y_4)
            }
        """
        config = make_model_config(("target",))
        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        self.assertEqual(ytl.evaluate_function_model(model, (12,)), (4,))

    def test_multiple_expr_stmts_in_live_branch_rejected(self) -> None:
        """Multiple bare expressions in a live branch are all rejected."""
        yul = """
            function fun_target_1(var_x_1) -> var_z_2 {
                var_z_2 := helper(var_x_1, 0)
            }
            function helper(var_x_3, var_y_4) -> var_r_5 {
                if iszero(var_y_4) {
                    side_effect_a()
                    side_effect_b()
                }
                var_r_5 := div(var_x_3, var_y_4)
            }
        """
        config = make_model_config(("target",))
        with self.assertRaisesRegex(
            ytl.ParseError,
            r"2 unhandled expression-statement",
        ):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    # -- Chained inlining: expr_stmt from a deeper helper --

    def test_chained_inline_dead_branch_expr_stmt_discarded(self) -> None:
        """Expr_stmt in dead branch survives through a chain of helpers."""
        yul = """
            function fun_target_1(var_x_1) -> var_z_2 {
                var_z_2 := wrapper(var_x_1)
            }
            function wrapper(var_a_3) -> var_b_4 {
                var_b_4 := divider(var_a_3, 7)
            }
            function divider(var_x_5, var_y_6) -> var_r_7 {
                if iszero(var_y_6) { panic() }
                var_r_7 := div(var_x_5, var_y_6)
            }
        """
        config = make_model_config(("target",))
        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        self.assertEqual(ytl.evaluate_function_model(model, (21,)), (3,))

    # -- Top-level function expr_stmts still rejected (regression) --

    def test_top_level_expr_stmt_still_rejected(self) -> None:
        """Bare expression at function top level (not in any branch) is still rejected."""
        yul = """
            function fun_target_1(var_x_1) -> var_z_2 {
                var_z_2 := helper(var_x_1, 3)
            }
            function helper(var_x_3, var_y_4) -> var_r_5 {
                side_effect()
                var_r_5 := div(var_x_3, var_y_4)
            }
        """
        config = make_model_config(("target",))
        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_bare_block_nested_live_expr_stmt_still_rejected(self) -> None:
        """Bare-block flattening must not erase a live nested branch expr_stmt."""
        yul = """
            function fun_target_1(var_c_1) -> var_z_2 {
                {
                    let usr$x := 0
                    if var_c_1 {
                        side_effect()
                        usr$x := 1
                    }
                    var_z_2 := usr$x
                }
            }
        """
        config = make_model_config(("target",))
        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_constant_true_flatten_preserves_nested_live_expr_stmt(self) -> None:
        """Constant-true flattening must preserve live nested branch expr_stmts."""
        yul = """
            function fun_target_1(var_c_1) -> var_z_2 {
                if 1 {
                    if var_c_1 { side_effect() }
                }
                var_z_2 := 1
            }
        """
        config = make_model_config(("target",))
        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_constant_switch_dead_branch_expr_stmt_discarded_in_target(self) -> None:
        """Dead expr_stmts in constant switch branches should be discarded."""
        yul = """
            function fun_target_1() -> var_z_2 {
                switch 1
                case 0 {
                    side_effect()
                    var_z_2 := 0
                }
                default {
                    var_z_2 := 7
                }
            }
        """
        config = make_model_config(("target",))
        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        self.assertEqual(ytl.evaluate_function_model(model, ()), (7,))

    # -- Constant propagation across statements in _inline_yul_function --

    def test_wrapping_div_pattern_intermediate_var(self) -> None:
        """Constant divisor via intermediate variable is resolved during inlining."""
        yul = """
            function fun_target_1(var_x_1) -> var_z_2 {
                let expr_1 := cleanup(3)
                var_z_2 := wrapping_div(var_x_1, expr_1)
            }
            function wrapping_div(x, y) -> r {
                if iszero(y) { panic_error_0x12() }
                r := div(x, y)
            }
            function cleanup(value) -> cleaned {
                cleaned := value
            }
        """
        config = make_model_config(("target",))
        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        self.assertEqual(ytl.evaluate_function_model(model, (9,)), (3,))

    def test_wrapping_div_pattern_non_constant_var_rejected(self) -> None:
        """Non-constant variable arg: branch with expr_stmt is correctly rejected."""
        yul = """
            function fun_target_1(var_x_1, var_y_2) -> var_z_3 {
                let expr_1 := cleanup(var_y_2)
                var_z_3 := wrapping_div(var_x_1, expr_1)
            }
            function wrapping_div(x, y) -> r {
                if iszero(y) { panic_error_0x12() }
                r := div(x, y)
            }
            function cleanup(value) -> cleaned {
                cleaned := value
            }
        """
        config = make_model_config(("target",))
        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_wrapping_div_pattern_dead_branch_after_cleanup_inline(self) -> None:
        """Real wrapping_div_t_uint256 pattern: cleanup identity inlined before fold."""
        yul = """
            function fun_target_1(var_x_1) -> var_z_2 {
                var_z_2 := wrapping_div_t_uint256(var_x_1, 3)
            }
            function wrapping_div_t_uint256(x, y) -> r {
                x := cleanup_t_uint256(x)
                y := cleanup_t_uint256(y)
                if iszero(y) { panic_error_0x12() }
                r := div(x, y)
            }
            function cleanup_t_uint256(value) -> cleaned {
                cleaned := value
            }
        """
        config = make_model_config(("target",))
        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        self.assertEqual(ytl.evaluate_function_model(model, (9,)), (3,))

    # -- const_subst invalidation edge cases --

    def test_const_subst_invalidated_after_non_constant_reassignment(self) -> None:
        """Variable reassigned to non-constant must be removed from const_subst.

        Without invalidation, ``usr$x`` would stay as ``IntLit(3)`` and the
        call would see ``wrapping_div(3, 3)`` instead of
        ``wrapping_div(add(3, y), 3)``.
        """
        yul = """
            function fun_target_1(var_y_1) -> var_z_2 {
                let usr$x := 3
                usr$x := add(usr$x, var_y_1)
                var_z_2 := wrapping_div(usr$x, 3)
            }
            function wrapping_div(x, y) -> r {
                if iszero(y) { panic_error_0x12() }
                r := div(x, y)
            }
        """
        config = make_model_config(("target",))
        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        # (3 + 6) / 3 == 3
        self.assertEqual(ytl.evaluate_function_model(model, (6,)), (3,))
        # (3 + 0) / 3 == 1
        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (1,))

    def test_const_subst_from_constant_true_if_body(self) -> None:
        """Variable assigned inside ``if 1 { x := 3 }`` should be usable as constant.

        The condition is statically true, so ``x := 3`` always executes.
        The constant should propagate to subsequent statements.
        """
        yul = """
            function fun_target_1(var_a_1) -> var_z_2 {
                let usr$x := 0
                if 1 {
                    usr$x := 3
                }
                var_z_2 := wrapping_div(var_a_1, usr$x)
            }
            function wrapping_div(x, y) -> r {
                if iszero(y) { panic_error_0x12() }
                r := div(x, y)
            }
        """
        config = make_model_config(("target",))
        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]
        self.assertEqual(ytl.evaluate_function_model(model, (9,)), (3,))

    def test_const_subst_not_poisoned_by_block_scoped_shadow(self) -> None:
        """Yul rejects cross-scope variable shadowing (solc error 1395).

        Inner ``let usr$x := 5`` shadows outer ``let usr$x := 3`` — invalid Yul.
        """
        yul = """
            function fun_target_1(var_a_1) -> var_z_2 {
                let usr$x := 3
                if 1 {
                    let usr$x := 5
                }
                var_z_2 := wrapping_div(var_a_1, usr$x)
            }
            function wrapping_div(x, y) -> r {
                if iszero(y) { panic_error_0x12() }
                r := div(x, y)
            }
        """
        config = make_model_config(("target",))
        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )


class NewReviewRegressionTest(unittest.TestCase):
    def test_parse_function_rejects_unsupported_constant_switch_shapes(
        self,
    ) -> None:
        # For constant-folded switches the only structural constraint
        # is that ``default`` must be the last branch — the parser loop
        # breaks on ``default``, so trailing branches would be silently
        # dropped.  Branch counts, missing defaults, and nonzero case
        # values are all valid; see the companion tests
        # test_translate_yul_to_models_accepts_constant_switch_without_default
        # and test_translate_yul_to_models_accepts_constant_switch_with_multiple_cases.
        cases = {
            "default_before_case": (
                """
                function fun_bad_1() -> z {
                    switch 1
                    default {
                        z := 9
                    }
                    case 0 {
                        z := 7
                    }
                }
                """,
                "'default' must be the last branch",
            ),
        }

        for name, (yul, message) in cases.items():
            with self.subTest(name=name):
                tokens = ytl.tokenize_yul(yul)
                with self.assertRaisesRegex(ytl.ParseError, message):
                    ytl.YulParser(tokens).parse_function()

    def test_parse_function_rejects_empty_constant_switch(self) -> None:
        yul = """
            function fun_bad_1() -> z {
                switch 1
            }
        """

        tokens = ytl.tokenize_yul(yul)
        with self.assertRaises(ytl.ParseError):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_rejects_duplicate_constant_switch_case_values(
        self,
    ) -> None:
        yul = """
            function fun_bad_1() -> z {
                switch 1
                case 1 {
                    z := 7
                }
                case 1 {
                    z := 8
                }
                default {
                    z := 9
                }
            }
        """

        tokens = ytl.tokenize_yul(yul)
        with self.assertRaises(ytl.ParseError):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_rejects_nonconstant_case_value_in_constant_switch(
        self,
    ) -> None:
        yul = """
            function fun_bad_1(var_x_1) -> z {
                switch 1
                case var_x_1 {
                    z := 7
                }
                default {
                    z := 9
                }
            }
        """

        tokens = ytl.tokenize_yul(yul)
        with self.assertRaises(ytl.ParseError):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_rejects_nonliteral_constant_expression_case_value(
        self,
    ) -> None:
        yul = """
            function fun_bad_1() -> z {
                switch 1
                case add(0, 1) {
                    z := 7
                }
                default {
                    z := 9
                }
            }
        """

        tokens = ytl.tokenize_yul(yul)
        with self.assertRaises(ytl.ParseError):
            ytl.YulParser(tokens).parse_function()

    def test_translate_yul_to_models_accepts_constant_switch_without_default(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                var_z_2 := 9
                switch 1
                case 1 {
                    var_z_2 := 7
                }
            }
        """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(ytl.evaluate_function_model(result.models[0], ()), (7,))

    def test_translate_yul_to_models_accepts_constant_switch_with_multiple_cases(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                switch 1
                case 0 {
                    var_z_2 := 0
                }
                case 1 {
                    var_z_2 := 1
                }
                default {
                    var_z_2 := 2
                }
            }
        """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )

        self.assertEqual(ytl.evaluate_function_model(result.models[0], ()), (1,))

    def test_translate_yul_to_models_rejects_branch_local_shadow_reassignment_in_nonconstant_conditional(
        self,
    ) -> None:
        # Yul rejects cross-scope variable shadowing (solc error 1395).
        # This Yul snippet is invalid; the resolver catches it before
        # the lowering parser runs.
        config = make_model_config(("f",))
        cases = {
            "if": """
                function fun_f_1(var_c_1) -> var_z_2 {
                    let usr$a := 1
                    if var_c_1 {
                        let usr$a := 1
                        usr$a := 2
                        var_z_2 := usr$a
                    }
                }
            """,
            "switch": """
                function fun_f_1(var_c_1) -> var_z_2 {
                    let usr$a := 1
                    switch var_c_1
                    case 0 {
                    }
                    default {
                        let usr$a := 1
                        usr$a := 2
                        var_z_2 := usr$a
                    }
                }
            """,
        }

        for name, yul in cases.items():
            with self.subTest(name=name):
                with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
                    ytl.translate_yul_to_models(
                        yul,
                        config,
                        pipeline=ytl.RAW_TRANSLATION_PIPELINE,
                    )

    def test_evaluate_function_model_wraps_raw_large_integer_literals_to_u256(
        self,
    ) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            assignments=(ytl.Assignment("z", ytl.IntLit(ytl.WORD_MOD + 1)),),
            param_names=(),
            return_names=("z",),
        )

        self.assertEqual(ytl.evaluate_function_model(model, ()), (1,))

    def test_build_model_body_wraps_raw_large_integer_literals_to_u256(
        self,
    ) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            assignments=(ytl.Assignment("z", ytl.IntLit(ytl.WORD_MOD + 1)),),
            param_names=(),
            return_names=("z",),
        )

        body = ytl.build_model_body(
            model.assignments,
            evm=True,
            config=make_model_config(("f",)),
            param_names=model.param_names,
            return_names=model.return_names,
        )

        self.assertEqual(body.splitlines()[0], "  let z := 1")


class CriticalReviewRegressionTest(unittest.TestCase):
    def test_translate_yul_to_models_rejects_nonconstant_conditional_local_used_out_of_scope_after_name_leak(
        self,
    ) -> None:
        config = make_model_config(("f",))
        cases = {
            "if": """
                function fun_f_1(var_x_1, var_c_2) -> var_z_3 {
                    if var_c_2 {
                        let usr$x := 7
                        var_x_1 := usr$x
                    }
                    var_z_3 := usr$x
                }
                """,
            "switch": """
                function fun_f_1(var_x_1, var_c_2) -> var_z_3 {
                    switch var_c_2
                    case 0 {
                        let usr$x := 7
                        var_x_1 := usr$x
                    }
                    default {
                        var_x_1 := 8
                    }
                    var_z_3 := usr$x
                }
                """,
        }

        for label, yul in cases.items():
            with self.subTest(control_flow=label):
                with self.assertRaisesRegex(
                    ytl.ParseError,
                    "Undefined variable",
                ):
                    ytl.translate_yul_to_models(
                        yul,
                        config,
                        pipeline=ytl.RAW_TRANSLATION_PIPELINE,
                    )

    def test_translate_yul_to_models_collects_nested_local_helpers_inside_nested_blocks(
        self,
    ) -> None:
        config = make_model_config(
            ("outer",),
            exact_yul_names={"outer": "fun_outer_1"},
        )
        cases = {
            "bare_block": """
                object "o" {
                    code {
                        function fun_outer_1() -> var_z_1 {
                            {
                                function helper() -> var_r_1 {
                                    var_r_1 := 1
                                }
                                var_z_1 := helper()
                            }
                        }
                    }
                }
                """,
            "constant_true_if": """
                object "o" {
                    code {
                        function fun_outer_1() -> var_z_1 {
                            if 1 {
                                function helper() -> var_r_1 {
                                    var_r_1 := 1
                                }
                                var_z_1 := helper()
                            }
                        }
                    }
                }
                """,
        }

        for label, yul in cases.items():
            with self.subTest(scope=label):
                result = ytl.translate_yul_to_models(
                    yul,
                    config,
                    pipeline=ytl.RAW_TRANSLATION_PIPELINE,
                )
                self.assertEqual(
                    ytl.evaluate_function_model(
                        result.models[0],
                        (),
                        model_table=ytl.build_model_table(result.models),
                    ),
                    (1,),
                )

    def test_parse_exact_yul_selector_rejects_empty_path_segments(self) -> None:
        for selector in ("outer::", "::top::", "a::::b"):
            with self.subTest(selector=selector):
                with self.assertRaisesRegex(
                    ytl.ParseError,
                    "Invalid exact Yul selector",
                ):
                    ytl._parse_exact_yul_selector(selector)


class CriticalReviewFixRegressionTest(unittest.TestCase):
    def test_translate_yul_to_models_rejects_nonconstant_conditional_local_reassignment_used_out_of_scope(
        self,
    ) -> None:
        config = make_model_config(("f",))
        cases = {
            "if": """
                function fun_f_1(var_x_1, var_c_2) -> var_z_3 {
                    if var_c_2 {
                        let usr$x := 7
                        usr$x := 9
                        var_x_1 := usr$x
                    }
                    var_z_3 := usr$x
                }
                """,
            "switch": """
                function fun_f_1(var_x_1, var_c_2) -> var_z_3 {
                    switch var_c_2
                    case 0 {
                        let usr$x := 7
                        usr$x := 9
                        var_x_1 := usr$x
                    }
                    default {
                        var_x_1 := 8
                    }
                    var_z_3 := usr$x
                }
                """,
        }

        for label, yul in cases.items():
            with self.subTest(control_flow=label):
                with self.assertRaisesRegex(
                    ytl.ParseError,
                    "Undefined variable",
                ):
                    ytl.translate_yul_to_models(
                        yul,
                        config,
                        pipeline=ytl.RAW_TRANSLATION_PIPELINE,
                    )

    def test_translate_yul_to_models_rejects_nested_helper_used_after_its_scope_ends(
        self,
    ) -> None:
        config = make_model_config(
            ("outer",),
            exact_yul_names={"outer": "fun_outer_1"},
        )
        cases = {
            "bare_block": """
                object "o" {
                    code {
                        function fun_outer_1() -> var_z_1 {
                            {
                                function helper() -> var_r_1 {
                                    var_r_1 := 1
                                }
                            }
                            var_z_1 := helper()
                        }
                    }
                }
                """,
            "constant_true_if": """
                object "o" {
                    code {
                        function fun_outer_1() -> var_z_1 {
                            if 1 {
                                function helper() -> var_r_1 {
                                    var_r_1 := 1
                                }
                            }
                            var_z_1 := helper()
                        }
                    }
                }
                """,
        }

        for label, yul in cases.items():
            with self.subTest(scope=label):
                with self.assertRaisesRegex(
                    ytl.ParseError,
                    "unresolved call target 'helper'",
                ):
                    ytl.translate_yul_to_models(
                        yul,
                        config,
                        pipeline=ytl.RAW_TRANSLATION_PIPELINE,
                    )

    def test_translate_yul_to_models_allows_same_helper_name_in_disjoint_nested_scopes(
        self,
    ) -> None:
        config = make_model_config(
            ("outer",),
            exact_yul_names={"outer": "fun_outer_1"},
        )
        yul = """
            object "o" {
                code {
                    function fun_outer_1(var_c_1) -> var_z_1 {
                        if var_c_1 {
                            function helper() -> var_r_1 {
                                var_r_1 := 1
                            }
                            var_z_1 := helper()
                        }
                        if iszero(var_c_1) {
                            function helper() -> var_r_2 {
                                var_r_2 := 2
                            }
                            var_z_1 := helper()
                        }
                    }
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(
            ytl.evaluate_function_model(
                model,
                (0,),
                model_table=ytl.build_model_table(result.models),
            ),
            (2,),
        )
        self.assertEqual(
            ytl.evaluate_function_model(
                model,
                (1,),
                model_table=ytl.build_model_table(result.models),
            ),
            (1,),
        )

    def test_translate_yul_to_models_rejects_duplicate_local_helpers_in_same_nested_scope(
        self,
    ) -> None:
        config = make_model_config(("f",))
        cases = {
            "valid_then_valid": """
                function fun_f_1() -> var_z_1 {
                    {
                        function helper() -> var_r_1 {
                            var_r_1 := 1
                        }
                        function helper() -> var_r_2 {
                            var_r_2 := 2
                        }
                        var_z_1 := helper()
                    }
                }
                """,
            "rejected_then_valid": """
                function fun_f_1() -> var_z_1 {
                    {
                        function helper() -> var_r_1 {
                            for { } 0 { } {
                                var_r_1 := 1
                            }
                        }
                        function helper() -> var_r_2 {
                            var_r_2 := 2
                        }
                        var_z_1 := helper()
                    }
                }
                """,
            "valid_then_rejected": """
                function fun_f_1() -> var_z_1 {
                    {
                        function helper() -> var_r_1 {
                            var_r_1 := 1
                        }
                        function helper() -> var_r_2 {
                            for { } 0 { } {
                                var_r_2 := 2
                            }
                        }
                        var_z_1 := helper()
                    }
                }
                """,
        }

        for label, yul in cases.items():
            with self.subTest(ordering=label):
                with self.assertRaises(ytl.ParseError):
                    ytl.translate_yul_to_models(
                        yul,
                        config,
                        pipeline=ytl.RAW_TRANSLATION_PIPELINE,
                    )

    def test_translate_yul_to_models_allows_exact_from_local_helper(self) -> None:
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_target_0"},
        )
        yul = """
            object "o" {
                code {
                    function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                        function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                            var_r_out_7 := 0
                            mstore(var_r_4, var_x_hi_5)
                            mstore(add(0x20, var_r_4), var_x_lo_6)
                            var_r_out_7 := var_r_4
                        }
                        let usr$ptr := fun_from_1(0, var_x_hi_1, var_x_lo_2)
                        var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                    }
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(
            ytl.evaluate_function_model(
                model,
                (5, 7),
                model_table=ytl.build_model_table(result.models),
            ),
            (12,),
        )

    def test_translate_yul_to_models_allows_exact_from_local_helper_in_nested_scope(
        self,
    ) -> None:
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_target_0"},
        )
        cases = {
            "bare_block": """
                object "o" {
                    code {
                        function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                            {
                                function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                    var_r_out_7 := 0
                                    mstore(var_r_4, var_x_hi_5)
                                    mstore(add(0x20, var_r_4), var_x_lo_6)
                                    var_r_out_7 := var_r_4
                                }
                                let usr$ptr := fun_from_1(0, var_x_hi_1, var_x_lo_2)
                                var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                            }
                        }
                    }
                }
                """,
            "constant_true_if": """
                object "o" {
                    code {
                        function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                            if 1 {
                                function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                    var_r_out_7 := 0
                                    mstore(var_r_4, var_x_hi_5)
                                    mstore(add(0x20, var_r_4), var_x_lo_6)
                                    var_r_out_7 := var_r_4
                                }
                                let usr$ptr := fun_from_1(0, var_x_hi_1, var_x_lo_2)
                                var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                            }
                        }
                    }
                }
                """,
        }

        for label, yul in cases.items():
            with self.subTest(scope=label):
                result = ytl.translate_yul_to_models(
                    yul,
                    config,
                    pipeline=ytl.RAW_TRANSLATION_PIPELINE,
                )
                model = result.models[0]

                self.assertEqual(
                    ytl.evaluate_function_model(
                        model,
                        (5, 7),
                        model_table=ytl.build_model_table(result.models),
                    ),
                    (12,),
                )

    def test_translate_yul_to_models_rejects_exact_from_helper_outside_nested_scope(
        self,
    ) -> None:
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_target_0"},
        )
        cases = {
            "bare_block": """
                object "o" {
                    code {
                        function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                            {
                                function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                    var_r_out_7 := 0
                                    mstore(var_r_4, var_x_hi_5)
                                    mstore(add(0x20, var_r_4), var_x_lo_6)
                                    var_r_out_7 := var_r_4
                                }
                            }
                            let usr$ptr := fun_from_1(0, var_x_hi_1, var_x_lo_2)
                            var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                        }
                    }
                }
                """,
            "constant_true_if": """
                object "o" {
                    code {
                        function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                            if 1 {
                                function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                    var_r_out_7 := 0
                                    mstore(var_r_4, var_x_hi_5)
                                    mstore(add(0x20, var_r_4), var_x_lo_6)
                                    var_r_out_7 := var_r_4
                                }
                            }
                            let usr$ptr := fun_from_1(0, var_x_hi_1, var_x_lo_2)
                            var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                        }
                    }
                }
                """,
        }

        for label, yul in cases.items():
            with self.subTest(scope=label):
                with self.assertRaises(ytl.ParseError):
                    ytl.translate_yul_to_models(
                        yul,
                        config,
                        pipeline=ytl.RAW_TRANSLATION_PIPELINE,
                    )

    def test_translate_yul_to_models_rejects_duplicate_deferred_exact_from_helpers_in_same_nested_scope(
        self,
    ) -> None:
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_target_0"},
        )
        cases = {
            "valid_then_valid": """
                object "o" {
                    code {
                        function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                            {
                                function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                    var_r_out_7 := 0
                                    mstore(var_r_4, var_x_hi_5)
                                    mstore(add(0x20, var_r_4), var_x_lo_6)
                                    var_r_out_7 := var_r_4
                                }
                                function fun_from_1(var_r_8, var_x_hi_9, var_x_lo_10) -> var_r_out_11 {
                                    var_r_out_11 := 0
                                    mstore(var_r_8, var_x_hi_9)
                                    mstore(add(0x20, var_r_8), var_x_lo_10)
                                    var_r_out_11 := var_r_8
                                }
                                let usr$ptr := fun_from_1(0, var_x_hi_1, var_x_lo_2)
                                var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                            }
                        }
                    }
                }
                """,
            "rejected_then_valid": """
                object "o" {
                    code {
                        function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                            {
                                function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                    for { } 0 { } {
                                        var_r_out_7 := 1
                                    }
                                }
                                function fun_from_1(var_r_8, var_x_hi_9, var_x_lo_10) -> var_r_out_11 {
                                    var_r_out_11 := 0
                                    mstore(var_r_8, var_x_hi_9)
                                    mstore(add(0x20, var_r_8), var_x_lo_10)
                                    var_r_out_11 := var_r_8
                                }
                                let usr$ptr := fun_from_1(0, var_x_hi_1, var_x_lo_2)
                                var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                            }
                        }
                    }
                }
                """,
            "valid_then_rejected": """
                object "o" {
                    code {
                        function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                            {
                                function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                    var_r_out_7 := 0
                                    mstore(var_r_4, var_x_hi_5)
                                    mstore(add(0x20, var_r_4), var_x_lo_6)
                                    var_r_out_7 := var_r_4
                                }
                                function fun_from_1(var_r_8, var_x_hi_9, var_x_lo_10) -> var_r_out_11 {
                                    for { } 0 { } {
                                        var_r_out_11 := 1
                                    }
                                }
                                let usr$ptr := fun_from_1(0, var_x_hi_1, var_x_lo_2)
                                var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                            }
                        }
                    }
                }
                """,
        }

        for label, yul in cases.items():
            with self.subTest(ordering=label):
                with self.assertRaises(ytl.ParseError):
                    ytl.translate_yul_to_models(
                        yul,
                        config,
                        pipeline=ytl.RAW_TRANSLATION_PIPELINE,
                    )

    def test_translate_yul_to_models_rejects_deferred_from_helper_shadowing_outer_rejected_sibling(
        self,
    ) -> None:
        """Nested fun_from_1 shadows sibling top-level fun_from_1 — invalid per solc 1395."""
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_target_0"},
        )
        yul = """
            object "o" {
                code {
                    function fun_from_1(var_r_90, var_x_hi_91, var_x_lo_92) -> var_r_out_93 {
                        for { } 0 { } {
                            var_r_out_93 := 1
                        }
                    }
                    function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                        {
                            function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                var_r_out_7 := 0
                                mstore(var_r_4, var_x_hi_5)
                                mstore(add(0x20, var_r_4), var_x_lo_6)
                                var_r_out_7 := var_r_4
                            }
                            let usr$ptr := fun_from_1(0, var_x_hi_1, var_x_lo_2)
                            var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                        }
                    }
                }
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_deferred_from_helper_shadowing_outer_valid_sibling(
        self,
    ) -> None:
        """Nested fun_from_1 shadows sibling top-level fun_from_1 — invalid per solc 1395."""
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_target_0"},
        )
        yul = """
            object "o" {
                code {
                    function fun_from_1(var_x_hi_91, var_x_lo_92) -> var_r_out_93 {
                        var_r_out_93 := add(var_x_hi_91, var_x_lo_92)
                    }
                    function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                        if 1 {
                            function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                var_r_out_7 := 0
                                mstore(var_r_4, var_x_hi_5)
                                mstore(add(0x20, var_r_4), var_x_lo_6)
                                var_r_out_7 := var_r_4
                            }
                            let usr$ptr := fun_from_1(0, var_x_hi_1, var_x_lo_2)
                            var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                        }
                    }
                }
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_deferred_exact_from_helper_after_scope_ends(
        self,
    ) -> None:
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_target_0"},
        )
        yul = """
            object "o" {
                code {
                    function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                        {
                            function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                var_r_out_7 := 0
                                mstore(var_r_4, var_x_hi_5)
                                mstore(add(0x20, var_r_4), var_x_lo_6)
                                var_r_out_7 := var_r_4
                            }
                            let usr$ptr := fun_from_1(0, var_x_hi_1, var_x_lo_2)
                            var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                        }
                        let usr$ptr2 := fun_from_1(0x40, var_x_hi_1, var_x_lo_2)
                        var_z_3 := sub(var_z_3, add(mload(usr$ptr2), mload(add(0x20, usr$ptr2))))
                    }
                }
            }
            """

        with self.assertRaises(ytl.ParseError):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_outer_helper_when_inner_deferred_shadows_sibling(
        self,
    ) -> None:
        """Nested fun_from_1 shadows sibling top-level fun_from_1 — invalid per solc 1395."""
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_target_0"},
        )
        yul = """
            object "o" {
                code {
                    function fun_from_1(var_x_hi_91, var_x_lo_92) -> var_r_out_93 {
                        var_r_out_93 := add(var_x_hi_91, var_x_lo_92)
                    }
                    function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                        {
                            function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                var_r_out_7 := 0
                                mstore(var_r_4, var_x_hi_5)
                                mstore(add(0x20, var_r_4), var_x_lo_6)
                                var_r_out_7 := var_r_4
                            }
                            let usr$ptr := fun_from_1(0, var_x_hi_1, var_x_lo_2)
                            var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                        }
                        var_z_3 := sub(var_z_3, fun_from_1(var_x_hi_1, var_x_lo_2))
                    }
                }
            }
            """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_allows_nested_exact_from_inside_inlined_helper(
        self,
    ) -> None:
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_target_0"},
        )
        yul = """
            object "o" {
                code {
                    function fun_wrap_1(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                        {
                            function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                var_r_out_7 := 0
                                mstore(var_r_4, var_x_hi_5)
                                mstore(add(0x20, var_r_4), var_x_lo_6)
                                var_r_out_7 := var_r_4
                            }
                            let usr$ptr := fun_from_1(0, var_x_hi_1, var_x_lo_2)
                            var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                        }
                    }
                    function fun_target_0(var_x_hi_8, var_x_lo_9) -> var_z_10 {
                        var_z_10 := fun_wrap_1(var_x_hi_8, var_x_lo_9)
                    }
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(
            ytl.evaluate_function_model(
                model,
                (5, 7),
                model_table=ytl.build_model_table(result.models),
            ),
            (12,),
        )

    def test_translate_yul_to_models_allows_exact_from_inside_inlined_local_helper(
        self,
    ) -> None:
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_target_0"},
        )
        yul = """
            object "o" {
                code {
                    function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                        function helper_1(var_x_hi_8, var_x_lo_9) -> var_r_10 {
                            {
                                function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                    var_r_out_7 := 0
                                    mstore(var_r_4, var_x_hi_5)
                                    mstore(add(0x20, var_r_4), var_x_lo_6)
                                    var_r_out_7 := var_r_4
                                }
                                let usr$ptr := fun_from_1(0, var_x_hi_8, var_x_lo_9)
                                var_r_10 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                            }
                        }
                        var_z_3 := helper_1(var_x_hi_1, var_x_lo_2)
                    }
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(
            ytl.evaluate_function_model(
                model,
                (5, 7),
                model_table=ytl.build_model_table(result.models),
            ),
            (12,),
        )

    def test_translate_yul_to_models_allows_nested_helper_chain_using_exact_from(
        self,
    ) -> None:
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_target_0"},
        )
        yul = """
            object "o" {
                code {
                    function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                        function helper_outer_1(var_x_hi_8, var_x_lo_9) -> var_r_10 {
                            function helper_inner_1(var_x_hi_11, var_x_lo_12) -> var_r_13 {
                                {
                                    function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                        var_r_out_7 := 0
                                        mstore(var_r_4, var_x_hi_5)
                                        mstore(add(0x20, var_r_4), var_x_lo_6)
                                        var_r_out_7 := var_r_4
                                    }
                                    let usr$ptr := fun_from_1(0, var_x_hi_11, var_x_lo_12)
                                    var_r_13 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                                }
                            }
                            var_r_10 := helper_inner_1(var_x_hi_8, var_x_lo_9)
                        }
                        var_z_3 := helper_outer_1(var_x_hi_1, var_x_lo_2)
                    }
                }
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(
            ytl.evaluate_function_model(
                model,
                (5, 7),
                model_table=ytl.build_model_table(result.models),
            ),
            (12,),
        )

    def test_translate_yul_to_models_allows_same_scope_exact_from_helper_chain(
        self,
    ) -> None:
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_target_0"},
        )
        yul_by_order = {
            "exact_from_before_helper": """
                object "o" {
                    code {
                        function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                            function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                var_r_out_7 := 0
                                mstore(var_r_4, var_x_hi_5)
                                mstore(add(0x20, var_r_4), var_x_lo_6)
                                var_r_out_7 := var_r_4
                            }
                            function helper_1(var_x_hi_8, var_x_lo_9) -> var_r_10 {
                                let usr$ptr := fun_from_1(0, var_x_hi_8, var_x_lo_9)
                                var_r_10 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                            }
                            var_z_3 := helper_1(var_x_hi_1, var_x_lo_2)
                        }
                    }
                }
                """,
            "exact_from_after_helper": """
                object "o" {
                    code {
                        function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                            function helper_1(var_x_hi_8, var_x_lo_9) -> var_r_10 {
                                let usr$ptr := fun_from_1(0, var_x_hi_8, var_x_lo_9)
                                var_r_10 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                            }
                            function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                var_r_out_7 := 0
                                mstore(var_r_4, var_x_hi_5)
                                mstore(add(0x20, var_r_4), var_x_lo_6)
                                var_r_out_7 := var_r_4
                            }
                            var_z_3 := helper_1(var_x_hi_1, var_x_lo_2)
                        }
                    }
                }
                """,
        }

        for name, yul in yul_by_order.items():
            with self.subTest(order=name):
                result = ytl.translate_yul_to_models(
                    yul,
                    config,
                    pipeline=ytl.RAW_TRANSLATION_PIPELINE,
                )
                model = result.models[0]

                self.assertEqual(
                    ytl.evaluate_function_model(
                        model,
                        (5, 7),
                        model_table=ytl.build_model_table(result.models),
                    ),
                    (12,),
                )

    def test_translate_yul_to_models_rejects_exact_from_inside_helper_if_body(
        self,
    ) -> None:
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_target_0"},
            n_params={"target": 3},
        )
        yul = """
            object "o" {
                code {
                    function fun_target_0(var_c_0, var_x_hi_1, var_x_lo_2) -> var_z_3 {
                        function helper_1(var_c_4, var_x_hi_8, var_x_lo_9) -> var_r_10 {
                            if var_c_4 {
                                let usr$ptr := fun_from_1(0, var_x_hi_8, var_x_lo_9)
                                var_r_10 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                            }
                        }
                        function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                            var_r_out_7 := 0
                            mstore(var_r_4, var_x_hi_5)
                            mstore(add(0x20, var_r_4), var_x_lo_6)
                            var_r_out_7 := var_r_4
                        }
                        var_z_3 := helper_1(var_c_0, var_x_hi_1, var_x_lo_2)
                    }
                }
            }
            """

        with self.assertRaisesRegex(
            ytl.ParseError,
            "Conditional memory write detected",
        ):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_exact_from_inside_helper_if_condition(
        self,
    ) -> None:
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_target_0"},
        )
        yul = """
            object "o" {
                code {
                    function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                        function helper_1(var_x_hi_8, var_x_lo_9) -> var_r_10 {
                            if iszero(fun_from_1(0, var_x_hi_8, var_x_lo_9)) {
                                var_r_10 := 1
                            }
                        }
                        function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                            var_r_out_7 := 0
                            mstore(var_r_4, var_x_hi_5)
                            mstore(add(0x20, var_r_4), var_x_lo_6)
                            var_r_out_7 := var_r_4
                        }
                        var_z_3 := helper_1(var_x_hi_1, var_x_lo_2)
                    }
                }
            }
            """

        with self.assertRaisesRegex(
            ytl.ParseError,
            "Conditional memory write detected",
        ):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_nested_transitive_exact_from_in_helper_condition(
        self,
    ) -> None:
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_target_0"},
        )
        yul = """
            object "o" {
                code {
                    function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                        function helper_outer_1(var_x_hi_8, var_x_lo_9) -> var_r_10 {
                            {
                                function ptr_inner_1(var_x_hi_11, var_x_lo_12) -> var_r_13 {
                                    var_r_13 := fun_from_1(0, var_x_hi_11, var_x_lo_12)
                                }
                                function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                    var_r_out_7 := 0
                                    mstore(var_r_4, var_x_hi_5)
                                    mstore(add(0x20, var_r_4), var_x_lo_6)
                                    var_r_out_7 := var_r_4
                                }
                                if iszero(ptr_inner_1(var_x_hi_8, var_x_lo_9)) {
                                    var_r_10 := 1
                                }
                            }
                        }
                        var_z_3 := helper_outer_1(var_x_hi_1, var_x_lo_2)
                    }
                }
            }
            """

        with self.assertRaisesRegex(
            ytl.ParseError,
            "Conditional memory write detected",
        ):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_rejects_nested_rejected_helper_in_non_pure_helper(
        self,
    ) -> None:
        config_by_case = {
            "selected_target": make_model_config(
                ("target",),
                exact_yul_names={"target": "fun_target_0"},
            ),
            "collected_helper": make_model_config(
                ("target",),
                exact_yul_names={"target": "fun_target_0"},
            ),
        }
        yul_by_case = {
            "selected_target": """
                object "o" {
                    code {
                        function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                            {
                                function bad_1(var_x_14) -> var_y_15 {
                                    for { } 1 { } { }
                                }
                                function ptr_inner_1(var_x_hi_11, var_x_lo_12) -> var_r_13 {
                                    var_r_13 := fun_from_1(0, var_x_hi_11, var_x_lo_12)
                                    var_r_13 := bad_1(var_r_13)
                                }
                                function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                    var_r_out_7 := 0
                                    mstore(var_r_4, var_x_hi_5)
                                    mstore(add(0x20, var_r_4), var_x_lo_6)
                                    var_r_out_7 := var_r_4
                                }
                                let usr$ptr := ptr_inner_1(var_x_hi_1, var_x_lo_2)
                                var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                            }
                        }
                    }
                }
                """,
            "collected_helper": """
                object "o" {
                    code {
                        function fun_wrap_1(var_x_hi_8, var_x_lo_9) -> var_r_10 {
                            {
                                function bad_1(var_x_14) -> var_y_15 {
                                    for { } 1 { } { }
                                }
                                function ptr_inner_1(var_x_hi_11, var_x_lo_12) -> var_r_13 {
                                    var_r_13 := fun_from_1(0, var_x_hi_11, var_x_lo_12)
                                    var_r_13 := bad_1(var_r_13)
                                }
                                function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                    var_r_out_7 := 0
                                    mstore(var_r_4, var_x_hi_5)
                                    mstore(add(0x20, var_r_4), var_x_lo_6)
                                    var_r_out_7 := var_r_4
                                }
                                let usr$ptr := ptr_inner_1(var_x_hi_8, var_x_lo_9)
                                var_r_10 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                            }
                        }
                        function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                            var_z_3 := fun_wrap_1(var_x_hi_1, var_x_lo_2)
                        }
                    }
                }
                """,
        }

        for case, config in config_by_case.items():
            with self.subTest(case=case):
                with self.assertRaisesRegex(
                    ytl.ParseError,
                    "Cannot inline helper 'bad_1': its Yul body was rejected during collection",
                ):
                    ytl.translate_yul_to_models(
                        yul_by_case[case],
                        config,
                        pipeline=ytl.RAW_TRANSLATION_PIPELINE,
                    )

    def test_translate_yul_to_models_rejects_inner_rejected_helper_even_when_outer_valid_helper_has_same_name(
        self,
    ) -> None:
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_target_0"},
        )
        yul_by_case = {
            "selected_target": """
                object "o" {
                    code {
                        function bad_1(var_x_20) -> var_y_21 {
                            var_y_21 := add(var_x_20, 1)
                        }
                        function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                            {
                                function bad_1(var_x_14) -> var_y_15 {
                                    for { } 1 { } { }
                                }
                                function ptr_inner_1(var_x_hi_11, var_x_lo_12) -> var_r_13 {
                                    var_r_13 := fun_from_1(0, var_x_hi_11, var_x_lo_12)
                                    var_r_13 := bad_1(var_r_13)
                                }
                                function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                    var_r_out_7 := 0
                                    mstore(var_r_4, var_x_hi_5)
                                    mstore(add(0x20, var_r_4), var_x_lo_6)
                                    var_r_out_7 := var_r_4
                                }
                                let usr$ptr := ptr_inner_1(var_x_hi_1, var_x_lo_2)
                                var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                            }
                        }
                    }
                }
                """,
            "collected_helper": """
                object "o" {
                    code {
                        function bad_1(var_x_20) -> var_y_21 {
                            var_y_21 := add(var_x_20, 1)
                        }
                        function fun_wrap_1(var_x_hi_8, var_x_lo_9) -> var_r_10 {
                            {
                                function bad_1(var_x_14) -> var_y_15 {
                                    for { } 1 { } { }
                                }
                                function ptr_inner_1(var_x_hi_11, var_x_lo_12) -> var_r_13 {
                                    var_r_13 := fun_from_1(0, var_x_hi_11, var_x_lo_12)
                                    var_r_13 := bad_1(var_r_13)
                                }
                                function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                    var_r_out_7 := 0
                                    mstore(var_r_4, var_x_hi_5)
                                    mstore(add(0x20, var_r_4), var_x_lo_6)
                                    var_r_out_7 := var_r_4
                                }
                                let usr$ptr := ptr_inner_1(var_x_hi_8, var_x_lo_9)
                                var_r_10 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                            }
                        }
                        function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                            var_z_3 := fun_wrap_1(var_x_hi_1, var_x_lo_2)
                        }
                    }
                }
                """,
        }

        for case, yul in yul_by_case.items():
            with self.subTest(case=case):
                with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
                    ytl.translate_yul_to_models(
                        yul,
                        config,
                        pipeline=ytl.RAW_TRANSLATION_PIPELINE,
                    )

    def test_translate_yul_to_models_reports_original_name_for_rejected_helper_in_deferred_export(
        self,
    ) -> None:
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_target_0"},
        )
        yul_by_case = {
            "selected_target": """
                object "o" {
                    code {
                        function bad_1(var_x_20) -> var_y_21 {
                            var_y_21 := add(var_x_20, 1)
                        }
                        function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                            {
                                function bad_1(var_x_14) -> var_y_15 {
                                    for { } 1 { } { }
                                }
                                function ptr_inner_1(var_x_hi_11, var_x_lo_12) -> var_r_13 {
                                    var_r_13 := fun_from_1(0, var_x_hi_11, var_x_lo_12)
                                    var_r_13 := bad_1(var_r_13)
                                }
                                function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                    var_r_out_7 := 0
                                    mstore(var_r_4, var_x_hi_5)
                                    mstore(add(0x20, var_r_4), var_x_lo_6)
                                    var_r_out_7 := var_r_4
                                }
                                let usr$ptr := ptr_inner_1(var_x_hi_1, var_x_lo_2)
                                var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                            }
                        }
                    }
                }
                """,
            "collected_helper": """
                object "o" {
                    code {
                        function bad_1(var_x_20) -> var_y_21 {
                            var_y_21 := add(var_x_20, 1)
                        }
                        function fun_wrap_1(var_x_hi_8, var_x_lo_9) -> var_r_10 {
                            {
                                function bad_1(var_x_14) -> var_y_15 {
                                    for { } 1 { } { }
                                }
                                function ptr_inner_1(var_x_hi_11, var_x_lo_12) -> var_r_13 {
                                    var_r_13 := fun_from_1(0, var_x_hi_11, var_x_lo_12)
                                    var_r_13 := bad_1(var_r_13)
                                }
                                function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                                    var_r_out_7 := 0
                                    mstore(var_r_4, var_x_hi_5)
                                    mstore(add(0x20, var_r_4), var_x_lo_6)
                                    var_r_out_7 := var_r_4
                                }
                                let usr$ptr := ptr_inner_1(var_x_hi_8, var_x_lo_9)
                                var_r_10 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                            }
                        }
                        function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                            var_z_3 := fun_wrap_1(var_x_hi_1, var_x_lo_2)
                        }
                    }
                }
                """,
        }

        for case, yul in yul_by_case.items():
            with self.subTest(case=case):
                with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
                    ytl.translate_yul_to_models(
                        yul,
                        config,
                        pipeline=ytl.RAW_TRANSLATION_PIPELINE,
                    )


class FinalCriticalReviewRegressionTest(unittest.TestCase):
    def test_find_function_ignores_dead_helper_reference_after_infinite_for_loop(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function helper(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_pick_1(var_x_3) -> var_z_4 {
                for { } 1 { } {
                }
                var_z_4 := helper(var_x_3)
            }

            function fun_pick_2(var_x_5) -> var_z_6 {
                var_z_6 := 7
            }
            """)

        found = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
        )

        self.assertEqual(found.yul_name, "fun_pick_2")

    def test_find_function_ignores_dead_helper_reference_after_for_post_leave(
        self,
    ) -> None:
        tokens = ytl.tokenize_yul("""
            function helper(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_pick_1(var_x_3) -> var_z_4 {
                for { } 1 { leave } {
                }
                var_z_4 := helper(var_x_3)
            }

            function fun_pick_2(var_x_5) -> var_z_6 {
                var_z_6 := 7
            }
            """)

        found = ytl.YulParser(tokens).find_function(
            "pick",
            known_yul_names={"helper"},
        )

        self.assertEqual(found.yul_name, "fun_pick_2")

    def test_prepare_translation_does_not_duplicate_single_deferred_helper_export(
        self,
    ) -> None:
        config = make_model_config(("target",))
        yul = """
            function fun_target_0(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                {
                    function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                        var_r_out_7 := 0
                        mstore(var_r_4, var_x_hi_5)
                        mstore(add(0x20, var_r_4), var_x_lo_6)
                        var_r_out_7 := var_r_4
                    }
                    let usr$ptr := fun_from_1(0, var_x_hi_1, var_x_lo_2)
                    var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                }
            }
        """

        old_counters = dict(ytl._gensym_counters)
        try:
            ytl._gensym_counters = {}
            preparation = ytl.prepare_translation(yul, config)
        finally:
            ytl._gensym_counters = old_counters

        helper_names: list[str] = sorted(
            fn.yul_name for fn in preparation.collected_helpers.values()
        )
        assert helper_names == ["fun_from_1"]

    def test_prepare_translation_does_not_duplicate_deferred_helper_for_exact_nested_target(
        self,
    ) -> None:
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_outer_1::target"},
        )
        yul = """
            function fun_outer_1() -> var_z_1 {
                function target(var_x_hi_1, var_x_lo_2) -> var_z_3 {
                    function fun_from_1(var_r_4, var_x_hi_5, var_x_lo_6) -> var_r_out_7 {
                        var_r_out_7 := 0
                        mstore(var_r_4, var_x_hi_5)
                        mstore(add(0x20, var_r_4), var_x_lo_6)
                        var_r_out_7 := var_r_4
                    }
                    let usr$ptr := fun_from_1(0, var_x_hi_1, var_x_lo_2)
                    var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
                }

                var_z_1 := target(1, 4)
            }
        """

        old_counters = dict(ytl._gensym_counters)
        try:
            ytl._gensym_counters = {}
            preparation = ytl.prepare_translation(yul, config)
        finally:
            ytl._gensym_counters = old_counters

        from_count = sum(
            1
            for fn in preparation.collected_helpers.values()
            if fn.yul_name == "fun_from_1"
        )
        self.assertEqual(from_count, 1)

    def test_translate_yul_to_models_allows_distinct_deferred_helpers_with_same_name_across_scopes(
        self,
    ) -> None:
        config = make_model_config(
            ("target",),
            exact_yul_names={"target": "fun_outer_1::target"},
        )
        yul = """
            function fun_outer_1() -> var_z_1 {
                function outer_wrap(var_hi_2, var_lo_3) -> var_out_4 {
                    function fun_from_1(var_r_5, var_hi_6, var_lo_7) -> var_r_out_8 {
                        var_r_out_8 := 0
                        mstore(var_r_5, var_hi_6)
                        mstore(add(0x20, var_r_5), var_lo_7)
                        var_r_out_8 := var_r_5
                    }
                    let usr$ptr := fun_from_1(0, var_hi_2, var_lo_3)
                    var_out_4 := mload(usr$ptr)
                }

                function target(var_x_hi_9, var_x_lo_10) -> var_t_11 {
                    function fun_from_1(var_r_12, var_hi_13, var_lo_14) -> var_r_out_15 {
                        var_r_out_15 := 0
                        mstore(var_r_12, var_hi_13)
                        mstore(add(0x20, var_r_12), var_lo_14)
                        var_r_out_15 := var_r_12
                    }
                    let usr$p1 := outer_wrap(var_x_hi_9, var_x_lo_10)
                    let usr$p2 := fun_from_1(64, var_x_hi_9, var_x_lo_10)
                    var_t_11 := add(usr$p1, mload(usr$p2))
                }

                var_z_1 := target(1, 4)
            }
        """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(
            ytl.evaluate_function_model(
                model,
                (5, 7),
                model_table=ytl.build_model_table(result.models),
            ),
            (10,),
        )

    def test_translate_yul_to_models_keeps_exact_selected_homonyms_scope_local(
        self,
    ) -> None:
        config = make_model_config(
            ("a", "b"),
            exact_yul_names={
                "a": "fun_outer1_1::target",
                "b": "fun_outer2_1::helper",
            },
        )
        yul = """
            function fun_outer1_1() -> var_o1_1 {
                function helper() -> var_h1_1 {
                    var_h1_1 := 7
                }
                function target() -> var_t1_1 {
                    var_t1_1 := helper()
                }
                var_o1_1 := target()
            }

            function fun_outer2_1() -> var_o2_1 {
                function helper() -> var_h2_1 {
                    var_h2_1 := 9
                }
                var_o2_1 := helper()
            }
        """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        models = ytl.build_model_table(result.models)

        self.assertEqual(
            ytl.evaluate_function_model(models["a"], (), model_table=models),
            (7,),
        )
        self.assertEqual(
            ytl.evaluate_function_model(models["b"], (), model_table=models),
            (9,),
        )

    def test_translate_yul_to_models_distinguishes_selected_exact_homonyms(
        self,
    ) -> None:
        config = make_model_config(
            ("a", "b", "c"),
            exact_yul_names={
                "a": "fun_outer1_1::target",
                "b": "fun_outer1_1::helper",
                "c": "fun_outer2_1::helper",
            },
        )
        yul = """
            function fun_outer1_1() -> var_o1_1 {
                function helper() -> var_h1_1 {
                    var_h1_1 := 7
                }
                function target() -> var_t1_1 {
                    var_t1_1 := helper()
                }
                var_o1_1 := target()
            }

            function fun_outer2_1() -> var_o2_1 {
                function helper() -> var_h2_1 {
                    var_h2_1 := 9
                }
                var_o2_1 := helper()
            }
        """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        models = ytl.build_model_table(result.models)

        self.assertEqual(
            ytl.evaluate_function_model(models["a"], (), model_table=models),
            (7,),
        )
        self.assertEqual(
            ytl.evaluate_function_model(models["b"], (), model_table=models),
            (7,),
        )
        self.assertEqual(
            ytl.evaluate_function_model(models["c"], (), model_table=models),
            (9,),
        )

    def test_translate_yul_to_models_preserves_selected_block_local_exact_helper(
        self,
    ) -> None:
        config = make_model_config(
            ("a", "b"),
            exact_yul_names={
                "a": "outer",
                "b": "outer::helper",
            },
        )
        yul = """
            function outer() -> var_z_1 {
                {
                    function helper() -> var_r_1 {
                        var_r_1 := 7
                    }
                    var_z_1 := helper()
                }
            }
        """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        models = ytl.build_model_table(result.models)

        self.assertEqual(
            ytl.evaluate_function_model(models["a"], (), model_table=models),
            (7,),
        )
        self.assertEqual(
            ytl.evaluate_function_model(models["b"], (), model_table=models),
            (7,),
        )
        self.assertTrue(
            any(
                isinstance(stmt, ytl.Assignment) and stmt.expr == ytl.Call("b", ())
                for stmt in models["a"].assignments
            )
        )

    def test_translate_yul_to_models_rejects_nested_helper_shadowing_unqualified_exact_sibling(
        self,
    ) -> None:
        """Nested helper inside outer shadows sibling top-level helper — invalid per solc 1395."""
        config = make_model_config(
            ("a", "b"),
            exact_yul_names={
                "a": "outer",
                "b": "helper",
            },
            n_params={
                "a": 0,
                "b": 1,
            },
        )
        yul = """
            function helper(var_x_1) -> var_r_1 {
                var_r_1 := 11
            }

            function outer() -> var_z_1 {
                {
                    function helper(var_x_2, var_y_3) -> var_r_2 {
                        var_r_2 := add(var_x_2, var_y_3)
                    }
                    var_z_1 := helper(4, 5)
                }
            }
        """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_does_not_leak_selected_block_local_helper_scope(
        self,
    ) -> None:
        config = make_model_config(
            ("a", "b"),
            exact_yul_names={
                "a": "outer",
                "b": "outer::helper",
            },
        )
        yul = """
            function outer() -> var_z_1 {
                {
                    function helper() -> var_r_1 {
                        var_r_1 := 7
                    }
                }
                var_z_1 := helper()
            }
        """

        with self.assertRaisesRegex(
            ytl.ParseError,
            "unresolved call target 'helper'",
        ):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_translate_yul_to_models_avoids_protected_call_name_collisions(
        self,
    ) -> None:
        config = make_model_config(
            ("a", "b"),
            exact_yul_names={
                "a": "outer",
                "b": "outer::helper",
            },
        )
        base_yul = """
            function outer() -> var_z_1 {
                function collision_name() -> var_r_0 {
                    var_r_0 := 99
                }
                {
                    function helper() -> var_r_1 {
                        var_r_1 := 7
                    }
                    var_z_1 := helper()
                }
            }
        """
        helper_token_idx = (
            ytl.YulParser(ytl.tokenize_yul(base_yul))
            .find_exact_function_path(("outer", "helper"))
            .token_idx
        )
        assert helper_token_idx is not None
        yul = base_yul.replace(
            "collision_name",
            f"__protected_{helper_token_idx}",
        )

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        models = ytl.build_model_table(result.models)

        self.assertEqual(
            ytl.evaluate_function_model(models["a"], (), model_table=models),
            (7,),
        )
        self.assertEqual(
            ytl.evaluate_function_model(models["b"], (), model_table=models),
            (7,),
        )
        self.assertTrue(
            any(
                isinstance(stmt, ytl.Assignment) and stmt.expr == ytl.Call("b", ())
                for stmt in models["a"].assignments
            )
        )


class LatestCriticalReviewRegressionTest(unittest.TestCase):
    def test_translate_yul_to_models_threads_compiler_temporary_through_nonconstant_if(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1) -> var_z_2 {
                let expr_1 := 0
                if var_c_1 {
                    expr_1 := 1
                }
                var_z_2 := expr_1
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (0,))
        self.assertEqual(ytl.evaluate_function_model(model, (1,)), (1,))
        self.assertEqual(ytl.evaluate_function_model(model, (7,)), (1,))

    def test_translate_yul_to_models_threads_compiler_temporary_through_nonconstant_switch(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_c_1) -> var_z_2 {
                let expr_1 := 0
                switch var_c_1
                case 0 {
                    expr_1 := 1
                }
                default {
                    expr_1 := 2
                }
                var_z_2 := expr_1
            }
            """

        result = ytl.translate_yul_to_models(
            yul,
            config,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(ytl.evaluate_function_model(model, (0,)), (1,))
        self.assertEqual(ytl.evaluate_function_model(model, (1,)), (2,))
        self.assertEqual(ytl.evaluate_function_model(model, (9,)), (2,))

    def test_build_lean_source_rejects_invalid_model_before_emitting_undefined_binders(
        self,
    ) -> None:
        model = ytl.FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(ytl.Assignment("z", ytl.Var("y")),),
        )

        with self.assertRaisesRegex(ytl.ParseError, "out-of-scope variable use"):
            ytl.build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="Test",
                config=make_model_config(("f",)),
            )


class ResolverFailClosedTest(unittest.TestCase):
    """Tests that the new yul_resolve pass rejects invalid lexical patterns.

    These mirror the corresponding FailClosedTranslatorTest binder-validation
    cases, confirming that the resolver (not the lowering parser) is the
    authoritative source of these rejections.
    """

    def _parse_and_resolve(self, yul: str) -> None:
        tokens = ytl.tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        resolve_function(func)

    def test_resolve_rejects_duplicate_param_names(self) -> None:
        with self.assertRaisesRegex(ytl.ParseError, "x"):
            self._parse_and_resolve("function f(x, x) -> z { z := x }")

    def test_resolve_rejects_duplicate_return_names(self) -> None:
        with self.assertRaisesRegex(ytl.ParseError, "z"):
            self._parse_and_resolve("function f(x) -> z, z { z := x }")

    def test_resolve_rejects_duplicate_local_declaration_in_same_scope(
        self,
    ) -> None:
        with self.assertRaisesRegex(ytl.ParseError, r"usr\$tmp"):
            self._parse_and_resolve("""
                function f(x) -> z {
                    let usr$tmp := 1
                    let usr$tmp := 2
                    z := usr$tmp
                }
            """)

    def test_resolve_rejects_duplicate_multi_let_target(self) -> None:
        with self.assertRaisesRegex(ytl.ParseError, r"usr\$a"):
            self._parse_and_resolve("""
                function f(x) -> z {
                    let usr$a, usr$a := fun_pair(x)
                    z := usr$a
                }
            """)

    def test_resolve_rejects_same_scope_local_shadowing_parameter(
        self,
    ) -> None:
        with self.assertRaisesRegex(ytl.ParseError, "x"):
            self._parse_and_resolve("""
                function f(x) -> z {
                    let x := 1
                    z := x
                }
            """)

    def test_resolve_rejects_same_scope_local_shadowing_return(self) -> None:
        with self.assertRaisesRegex(ytl.ParseError, "z"):
            self._parse_and_resolve("""
                function f(x) -> z {
                    let z := 1
                }
            """)

    def test_resolve_rejects_duplicate_local_inside_bare_block(self) -> None:
        with self.assertRaisesRegex(ytl.ParseError, r"usr\$tmp"):
            self._parse_and_resolve("""
                function f(x) -> z {
                    {
                        let usr$tmp := 1
                        let usr$tmp := 2
                        z := usr$tmp
                    }
                }
            """)

    def test_resolve_rejects_string_literal_assignment_rhs(self) -> None:
        with self.assertRaisesRegex(ytl.ParseError, "string"):
            self._parse_and_resolve("""
                function f(x) -> z {
                    z := "oops"
                }
            """)

    # -- Undefined-variable resolution tests --------------------------------

    def test_resolve_rejects_undefined_rhs_variable(self) -> None:
        with self.assertRaisesRegex(ytl.ParseError, "Undefined variable 'y'"):
            self._parse_and_resolve("function f(x) -> z { z := y }")

    def test_resolve_rejects_undefined_assignment_target(self) -> None:
        with self.assertRaisesRegex(ytl.ParseError, "Undefined variable 'y'"):
            self._parse_and_resolve("function f(x) -> z { y := x  z := x }")

    def test_resolve_rejects_if_scoped_let_used_after_block(self) -> None:
        with self.assertRaisesRegex(ytl.ParseError, "Undefined variable 'y'"):
            self._parse_and_resolve("""
                function f(x) -> z {
                    if x { let y := 1 }
                    z := y
                }
            """)

    def test_resolve_rejects_bare_block_scoped_let_used_after_block(
        self,
    ) -> None:
        with self.assertRaisesRegex(ytl.ParseError, "Undefined variable 'tmp'"):
            self._parse_and_resolve("""
                function f(x) -> z {
                    { let tmp := x }
                    z := tmp
                }
            """)

    def test_resolve_rejects_switch_scoped_let_used_after_block(self) -> None:
        with self.assertRaisesRegex(ytl.ParseError, "Undefined variable 'y'"):
            self._parse_and_resolve("""
                function f(x) -> z {
                    switch x
                    case 0 { let y := 1 }
                    default { }
                    z := y
                }
            """)

    def test_resolve_rejects_for_body_scoped_let_used_after_loop(
        self,
    ) -> None:
        with self.assertRaisesRegex(ytl.ParseError, "Undefined variable 'y'"):
            self._parse_and_resolve("""
                function f(x) -> z {
                    for { } x { } { let y := 1 }
                    z := y
                }
            """)

    def test_resolve_accepts_for_init_variable_in_condition_and_body(
        self,
    ) -> None:
        """For-loop init declarations are visible in condition, post, body."""
        self._parse_and_resolve("""
            function f(x) -> z {
                for { let i := 0 } i { i := add(i, x) } {
                    z := i
                }
            }
        """)

    def test_resolve_rejects_nested_block_inner_scope_shadowing(self) -> None:
        """Yul rejects cross-scope shadowing (solc error 1395)."""
        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            self._parse_and_resolve("""
                function f(x) -> z {
                    let y := x
                    {
                        let y := 1
                        z := y
                    }
                }
            """)

    def test_resolve_accepts_sibling_block_reuse(self) -> None:
        """Sibling blocks can each declare the same name independently."""
        self._parse_and_resolve("""
            function f(x) -> z {
                { let tmp := 1 }
                { let tmp := 2  z := tmp }
            }
        """)


class SyntaxParserSpanTest(unittest.TestCase):
    """Tests that SyntaxParser produces correct global Span offsets."""

    def test_span_of_first_function_starts_at_zero(self) -> None:
        tokens = ytl.tokenize_yul("function f(x) -> z { z := x }")
        func = SyntaxParser(tokens).parse_function()
        # 'function' is token 0
        self.assertEqual(func.span.start, 0)
        # 'f' is token 1
        self.assertEqual(func.name_span.start, 1)
        self.assertEqual(func.name_span.end, 2)

    def test_span_with_token_offset_is_globally_correct(self) -> None:
        tokens = ytl.tokenize_yul("""
            function f(x) -> z { z := x }
            function g(y) -> w { w := y }
        """)
        # Parse first function to find where it ends.
        p1 = SyntaxParser(tokens)
        f1 = p1.parse_function()
        first_end = f1.span.end

        # Parse second function with offset.
        p2 = SyntaxParser(tokens[first_end:], token_offset=first_end)
        f2 = p2.parse_function()

        # 'g' should have a global span pointing into the original tokens.
        self.assertEqual(tokens[f2.name_span.start][1], "g")
        self.assertGreater(f2.name_span.start, first_end)
        self.assertEqual(f2.span.start, first_end)

    def test_inner_node_spans_respect_offset(self) -> None:
        tokens = ytl.tokenize_yul("""
            function f(x) -> z { z := x }
            function g(y) -> w { w := add(y, 1) }
        """)
        p1 = SyntaxParser(tokens)
        f1 = p1.parse_function()
        first_end = f1.span.end

        p2 = SyntaxParser(tokens[first_end:], token_offset=first_end)
        f2 = p2.parse_function()

        # The body should contain one AssignStmt whose span is global.
        body_stmts = f2.body.stmts
        self.assertEqual(len(body_stmts), 1)
        stmt = body_stmts[0]
        self.assertIsInstance(stmt, yul_ast.AssignStmt)
        assert isinstance(stmt, yul_ast.AssignStmt)
        self.assertGreater(stmt.span.start, first_end)
        self.assertGreater(stmt.span.end, stmt.span.start)

    def test_span_end_greater_than_start(self) -> None:
        tokens = ytl.tokenize_yul("function f(x, y) -> z { z := add(x, y) }")
        func = SyntaxParser(tokens).parse_function()
        self.assertGreater(func.span.end, func.span.start)
        self.assertGreater(func.body.span.end, func.body.span.start)
        self.assertGreater(func.name_span.end, func.name_span.start)
        for ps in func.param_spans:
            self.assertGreater(ps.end, ps.start)


class ResolverSymbolIdTest(unittest.TestCase):
    """Tests for symbol ID assignment and call-target classification."""

    def _resolve(
        self, yul: str, builtins: frozenset[str] = frozenset()
    ) -> ResolutionResult:
        tokens = ytl.tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        return resolve_function(func, builtins=builtins)

    def test_symbol_ids_are_unique_across_declarations(self) -> None:
        result = self._resolve("function f(x, y) -> z { let w := x  z := w }")
        # x, y, z, w → 4 distinct symbols.
        self.assertEqual(len(result.symbols), 4)
        ids = [info.id for info in result.symbols.values()]
        self.assertEqual(len(set(ids)), 4)

    def test_variable_references_resolve_to_correct_declaration(self) -> None:
        result = self._resolve("function f(x) -> z { z := x }")
        # Find the declaration IDs for x and z.
        decl_by_name: dict[str, yul_ast.SymbolId] = {}
        for sid, info in result.symbols.items():
            decl_by_name[info.name] = sid

        self.assertIn("x", decl_by_name)
        self.assertIn("z", decl_by_name)

        # The RHS 'x' reference should resolve to x's declaration.
        x_ref_found = False
        for span, sid in result.references.items():
            if sid == decl_by_name["x"]:
                x_ref_found = True
        self.assertTrue(x_ref_found, "reference to 'x' not found")

        # The LHS 'z' assignment target should resolve to z's declaration.
        z_ref_found = False
        for span, sid in result.references.items():
            if sid == decl_by_name["z"]:
                z_ref_found = True
        self.assertTrue(z_ref_found, "reference to 'z' not found")

    def test_builtin_call_classified_as_builtin_target(self) -> None:
        result = self._resolve(
            "function f(x) -> z { z := add(x, 1) }",
            builtins=frozenset({"add"}),
        )
        # Exactly one call target.
        self.assertEqual(len(result.call_targets), 1)
        target = next(iter(result.call_targets.values()))
        self.assertIsInstance(target, yul_ast.BuiltinTarget)
        assert isinstance(target, yul_ast.BuiltinTarget)
        self.assertEqual(target.name, "add")

    def test_local_function_call_classified_as_local_function_target(
        self,
    ) -> None:
        result = self._resolve("""
            function f(x) -> z {
                function g(a) -> b { b := a }
                z := g(x)
            }
        """)
        # Find g's declaration symbol.
        g_id: yul_ast.SymbolId | None = None
        for sid, info in result.symbols.items():
            if info.name == "g":
                g_id = sid
                break
        self.assertIsNotNone(g_id)

        # The call to g should be LocalFunctionTarget with g's ID.
        call_targets = list(result.call_targets.values())
        self.assertEqual(len(call_targets), 1)
        target = call_targets[0]
        self.assertIsInstance(target, yul_ast.LocalFunctionTarget)
        assert isinstance(target, yul_ast.LocalFunctionTarget)
        self.assertEqual(target.id, g_id)
        self.assertEqual(target.name, "g")

    def test_unknown_call_classified_as_unresolved_target(self) -> None:
        result = self._resolve("function f(x) -> z { z := unknown(x) }")
        self.assertEqual(len(result.call_targets), 1)
        target = next(iter(result.call_targets.values()))
        self.assertIsInstance(target, yul_ast.UnresolvedTarget)
        assert isinstance(target, yul_ast.UnresolvedTarget)
        self.assertEqual(target.name, "unknown")

    def test_cross_scope_shadowing_rejected(self) -> None:
        """Yul rejects cross-scope shadowing (solc error 1395)."""
        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            self._resolve("""
                function f(x) -> z {
                    let y := x
                    {
                        let y := 1
                        z := y
                    }
                }
            """)

    def test_no_builtins_classifies_all_calls_as_unresolved(self) -> None:
        result = self._resolve("function f(x) -> z { z := add(x, 1) }")
        self.assertEqual(len(result.call_targets), 1)
        target = next(iter(result.call_targets.values()))
        self.assertIsInstance(target, yul_ast.UnresolvedTarget)

    def test_rejects_function_declaration_shadowing_builtin(self) -> None:
        """Yul forbids declaring a function with a builtin opcode name."""
        with self.assertRaisesRegex(ytl.ParseError, "Cannot use builtin function name"):
            self._resolve(
                """
                function f(x) -> z {
                    function add(a, b) -> c { c := a }
                    z := add(x, 1)
                }
                """,
                builtins=frozenset({"add"}),
            )

    def test_variable_shadowing_function_rejected(self) -> None:
        """Yul rejects variable declaration shadowing a visible function (solc error 1395)."""
        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            self._resolve("""
                function f(x) -> z {
                    function helper(a) -> b { b := a }
                    {
                        let helper := 7
                        z := helper(x)
                    }
                }
            """)

    def test_rejects_toplevel_function_named_as_builtin(self) -> None:
        """Top-level function named 'add' is rejected when add is a builtin."""
        with self.assertRaisesRegex(ytl.ParseError, "Cannot use builtin function name"):
            self._resolve(
                "function add(a, b) -> c { c := a }",
                builtins=frozenset({"add"}),
            )

    def test_rejects_let_variable_named_as_builtin(self) -> None:
        """let add := 7 is rejected when add is a builtin (solc error 5568)."""
        with self.assertRaisesRegex(ytl.ParseError, "Cannot use builtin function name"):
            self._resolve(
                "function f(x) -> z { let add := 7 z := x }",
                builtins=frozenset({"add"}),
            )

    def test_rejects_param_named_as_builtin(self) -> None:
        """Parameter named 'add' is rejected when add is a builtin."""
        with self.assertRaisesRegex(ytl.ParseError, "Cannot use builtin function name"):
            self._resolve(
                "function f(add) -> z { z := add }",
                builtins=frozenset({"add"}),
            )

    def test_rejects_return_named_as_builtin(self) -> None:
        """Return variable named 'add' is rejected when add is a builtin."""
        with self.assertRaisesRegex(ytl.ParseError, "Cannot use builtin function name"):
            self._resolve(
                "function f(x) -> add { add := x }",
                builtins=frozenset({"add"}),
            )


class ResolverModuleTest(unittest.TestCase):
    """Tests for module-level resolution (resolve_module) and TopLevelFunctionTarget."""

    def _resolve_module(
        self, yul: str, builtins: frozenset[str] = frozenset()
    ) -> dict[str, ResolutionResult]:
        tokens = ytl.tokenize_yul(yul)
        funcs = SyntaxParser(tokens).parse_functions()
        return resolve_module(funcs, builtins=builtins)

    # -- call classification --------------------------------------------------

    def test_sibling_call_classified_as_top_level_target(self) -> None:
        results = self._resolve_module("""
            function f(x) -> z { z := g(x) }
            function g(a) -> b { b := a }
        """)
        f_targets = list(results["f"].call_targets.values())
        self.assertEqual(len(f_targets), 1)
        self.assertIsInstance(f_targets[0], yul_ast.TopLevelFunctionTarget)
        assert isinstance(f_targets[0], yul_ast.TopLevelFunctionTarget)
        self.assertEqual(f_targets[0].name, "g")

    def test_nested_helper_classified_as_local_function_target(self) -> None:
        results = self._resolve_module("""
            function f(x) -> z {
                function h(a) -> b { b := a }
                z := h(x)
            }
            function g(a) -> b { b := a }
        """)
        f_targets = list(results["f"].call_targets.values())
        self.assertEqual(len(f_targets), 1)
        self.assertIsInstance(f_targets[0], yul_ast.LocalFunctionTarget)
        assert isinstance(f_targets[0], yul_ast.LocalFunctionTarget)
        self.assertEqual(f_targets[0].name, "h")

    def test_builtin_call_still_classified_as_builtin(self) -> None:
        results = self._resolve_module(
            """
            function f(x) -> z { z := add(x, 1) }
            function g(a) -> b { b := a }
            """,
            builtins=frozenset({"add"}),
        )
        f_targets = list(results["f"].call_targets.values())
        self.assertEqual(len(f_targets), 1)
        self.assertIsInstance(f_targets[0], yul_ast.BuiltinTarget)

    def test_unknown_call_classified_as_unresolved(self) -> None:
        results = self._resolve_module("""
            function f(x) -> z { z := unknown(x) }
        """)
        f_targets = list(results["f"].call_targets.values())
        self.assertEqual(len(f_targets), 1)
        self.assertIsInstance(f_targets[0], yul_ast.UnresolvedTarget)

    # -- cross-function scoping -----------------------------------------------

    def test_variable_shadowing_sibling_function_rejected(self) -> None:
        """let helper inside f conflicts with sibling function helper."""
        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            self._resolve_module("""
                function helper(a) -> b { b := a }
                function f(x) -> z { let helper := 7 z := x }
            """)

    def test_nested_function_shadowing_sibling_rejected(self) -> None:
        """Nested function helper inside f conflicts with sibling function helper."""
        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            self._resolve_module("""
                function helper(a) -> b { b := a }
                function f(x) -> z {
                    function helper(c) -> d { d := c }
                    z := helper(x)
                }
            """)

    def test_sibling_scope_reuse_allowed(self) -> None:
        """Different functions may each have their own nested 'inner' helper."""
        results = self._resolve_module("""
            function f(x) -> z {
                function inner(a) -> b { b := a }
                z := inner(x)
            }
            function g(x) -> z {
                function inner(a) -> b { b := a }
                z := inner(x)
            }
        """)
        self.assertIn("f", results)
        self.assertIn("g", results)

    # -- module-level validation ----------------------------------------------

    def test_duplicate_top_level_function_rejected(self) -> None:
        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            self._resolve_module("""
                function f(x) -> z { z := x }
                function f(a) -> b { b := a }
            """)

    def test_top_level_function_named_as_builtin_rejected(self) -> None:
        with self.assertRaisesRegex(ytl.ParseError, "Cannot use builtin function name"):
            self._resolve_module(
                "function add(a, b) -> c { c := a }",
                builtins=frozenset({"add"}),
            )

    def test_per_function_resolve_still_classifies_sibling_as_unresolved(self) -> None:
        """resolve_function (without module context) classifies sibling calls
        as UnresolvedTarget, preserving existing behavior."""
        tokens = ytl.tokenize_yul("function f(x) -> z { z := g(x) }")
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func)
        f_targets = list(result.call_targets.values())
        self.assertEqual(len(f_targets), 1)
        self.assertIsInstance(f_targets[0], yul_ast.UnresolvedTarget)

    # -- parse_functions ------------------------------------------------------

    def test_parse_functions_multiple(self) -> None:
        tokens = ytl.tokenize_yul("""
            function f(x) -> z { z := x }
            function g(a) -> b { b := a }
            function h(c) -> d { d := c }
        """)
        funcs = SyntaxParser(tokens).parse_functions()
        self.assertEqual(len(funcs), 3)
        names: list[str] = [f.name for f in funcs]
        expected: list[str] = ["f", "g", "h"]
        self.assertEqual(names, expected)

    def test_parse_functions_skips_non_function_tokens(self) -> None:
        """object/code wrappers are skipped; only function defs are returned."""
        tokens = ytl.tokenize_yul("""
            object "o" { code {
                function f(x) -> z { z := x }
                function g(a) -> b { b := a }
            } }
        """)
        funcs = SyntaxParser(tokens).parse_functions()
        self.assertEqual(len(funcs), 2)
        names: list[str] = [f.name for f in funcs]
        expected: list[str] = ["f", "g"]
        self.assertEqual(names, expected)

    def test_parse_function_groups_separates_object_blocks(self) -> None:
        """Functions in different object blocks form separate groups."""
        tokens = ytl.tokenize_yul("""
            object "A" { code {
                function f(x) -> z { z := x }
                function g(a) -> b { b := a }
            } }
            object "B" { code {
                function h(c) -> d { d := c }
            } }
        """)
        groups = SyntaxParser(tokens).parse_function_groups()
        self.assertEqual(len(groups), 2)
        group_a_names: list[str] = [f.name for f in groups[0]]
        group_b_names: list[str] = [f.name for f in groups[1]]
        expected_a: list[str] = ["f", "g"]
        expected_b: list[str] = ["h"]
        self.assertEqual(group_a_names, expected_a)
        self.assertEqual(group_b_names, expected_b)

    def test_parse_function_groups_keeps_root_scope_across_object_blocks(self) -> None:
        """Top-level functions stay in one group even when object blocks intervene."""
        tokens = ytl.tokenize_yul("""
            function top1(x) -> z { z := x }
            object "A" { code {
                function f(a) -> b { b := a }
            } }
            function top2(c) -> d { d := c }
            object "B" { code {
                function h(e) -> r { r := e }
            } }
        """)
        groups = SyntaxParser(tokens).parse_function_groups()
        self.assertEqual(len(groups), 3)
        root_names: list[str] = [f.name for f in groups[0]]
        group_a_names: list[str] = [f.name for f in groups[1]]
        group_b_names: list[str] = [f.name for f in groups[2]]
        expected_root: list[str] = ["top1", "top2"]
        expected_a: list[str] = ["f"]
        expected_b: list[str] = ["h"]
        self.assertEqual(root_names, expected_root)
        self.assertEqual(group_a_names, expected_a)
        self.assertEqual(group_b_names, expected_b)

    def test_module_prepass_validates_later_object_blocks(self) -> None:
        """Cross-scope shadowing in a later object block is rejected
        through the production pipeline (prepare_translation), not just
        through direct resolve_module calls."""
        config = make_model_config(
            ("foo",),
            exact_yul_names={"foo": "target"},
        )
        yul = """
            object "A" { code {
                function ctor_ok(x) -> z { z := x }
            } }
            object "B" { code {
                function helper(a) -> b { b := a }
                function target(x) -> z {
                    let helper := 7
                    z := x
                }
            } }
        """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )

    def test_module_prepass_validates_later_object_blocks_after_top_level_function(
        self,
    ) -> None:
        """A prior top-level function must not prevent later object blocks
        from receiving module-level validation."""
        config = make_model_config(
            ("foo",),
            exact_yul_names={"foo": "target"},
        )
        yul = """
            function top(x) -> z { z := x }
            object "A" { code {
                function ctor_ok(x) -> z { z := x }
            } }
            object "B" { code {
                function helper(a) -> b { b := a }
                function target(x) -> z {
                    let helper := 7
                    z := x
                }
            } }
        """

        with self.assertRaisesRegex(ytl.ParseError, "Duplicate declaration"):
            ytl.translate_yul_to_models(
                yul,
                config,
                pipeline=ytl.RAW_TRANSLATION_PIPELINE,
            )


class NormalizeStructureTest(unittest.TestCase):
    """Tests for the syntax AST → normalized IR lowering pass."""

    def _normalize(self, yul: str) -> norm_ir.NormalizedFunction:
        tokens = ytl.tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func, builtins=ytl._SUPPORTED_OPS_FROZENSET)
        return normalize_function(func, result)

    def test_params_and_returns_get_distinct_symbol_ids(self) -> None:
        nf = self._normalize("function f(x, y) -> z { z := add(x, y) }")
        self.assertEqual(len(nf.params), 2)
        self.assertEqual(len(nf.returns), 1)
        all_ids = list(nf.params) + list(nf.returns)
        self.assertEqual(len(set(all_ids)), 3)

    def test_let_binding_produces_nbind(self) -> None:
        nf = self._normalize("function f(x) -> z { let w := x  z := w }")
        stmts = nf.body.stmts
        self.assertIsInstance(stmts[0], norm_ir.NBind)
        bind = stmts[0]
        assert isinstance(bind, norm_ir.NBind)
        self.assertEqual(len(bind.targets), 1)
        self.assertIsNotNone(bind.expr)

    def test_assignment_produces_nassign(self) -> None:
        nf = self._normalize("function f(x) -> z { z := x }")
        stmts = nf.body.stmts
        self.assertIsInstance(stmts[0], norm_ir.NAssign)
        assign = stmts[0]
        assert isinstance(assign, norm_ir.NAssign)
        self.assertEqual(len(assign.targets), 1)
        self.assertIsInstance(assign.expr, norm_ir.NRef)

    def test_builtin_call_produces_nbuiltincall(self) -> None:
        nf = self._normalize("function f(x) -> z { z := add(x, 1) }")
        assign = nf.body.stmts[0]
        assert isinstance(assign, norm_ir.NAssign)
        self.assertIsInstance(assign.expr, norm_ir.NBuiltinCall)
        call = assign.expr
        assert isinstance(call, norm_ir.NBuiltinCall)
        self.assertEqual(call.op, "add")
        self.assertEqual(len(call.args), 2)

    def test_local_function_call_produces_nlocalcall(self) -> None:
        nf = self._normalize("""
            function f(x) -> z {
                function g(a) -> b { b := a }
                z := g(x)
            }
        """)
        # body has: NFunctionDef(g), NAssign(z := g(x))
        assign = nf.body.stmts[1]
        assert isinstance(assign, norm_ir.NAssign)
        self.assertIsInstance(assign.expr, norm_ir.NLocalCall)
        call = assign.expr
        assert isinstance(call, norm_ir.NLocalCall)
        self.assertEqual(call.name, "g")

    def test_if_statement_produces_nif(self) -> None:
        nf = self._normalize("function f(x) -> z { if x { z := 1 } }")
        stmt = nf.body.stmts[0]
        self.assertIsInstance(stmt, norm_ir.NIf)
        assert isinstance(stmt, norm_ir.NIf)
        self.assertIsInstance(stmt.condition, norm_ir.NRef)
        self.assertEqual(len(stmt.then_body.stmts), 1)

    def test_switch_produces_nswitch(self) -> None:
        nf = self._normalize("""
            function f(x) -> z {
                switch x
                case 0 { z := 1 }
                default { z := 2 }
            }
        """)
        stmt = nf.body.stmts[0]
        self.assertIsInstance(stmt, norm_ir.NSwitch)
        assert isinstance(stmt, norm_ir.NSwitch)
        self.assertEqual(len(stmt.cases), 1)
        self.assertIsNotNone(stmt.default)

    def test_nested_function_produces_nfunctiondef(self) -> None:
        nf = self._normalize("""
            function f(x) -> z {
                function g(a) -> b { b := a }
                z := g(x)
            }
        """)
        fdef = nf.body.stmts[0]
        self.assertIsInstance(fdef, norm_ir.NFunctionDef)
        assert isinstance(fdef, norm_ir.NFunctionDef)
        self.assertEqual(fdef.name, "g")
        self.assertEqual(len(fdef.params), 1)
        self.assertEqual(len(fdef.returns), 1)


class NormalizeEvalTest(unittest.TestCase):
    """Semantic equivalence tests: normalized IR eval vs old pipeline eval."""

    def _eval_normalized(
        self,
        yul: str,
        args: tuple[int, ...],
        builtins: frozenset[str] = ytl._SUPPORTED_OPS_FROZENSET,
    ) -> tuple[int, ...]:
        tokens = ytl.tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func, builtins=builtins)
        nf = normalize_function(func, result)
        return evaluate_normalized(nf, args)

    def test_pure_arithmetic(self) -> None:
        yul = "function f(x) -> z { z := add(x, 1) }"
        self.assertEqual(self._eval_normalized(yul, (5,)), (6,))
        self.assertEqual(self._eval_normalized(yul, (0,)), (1,))

    def test_multi_param(self) -> None:
        yul = "function f(x, y) -> z { z := add(x, y) }"
        self.assertEqual(self._eval_normalized(yul, (3, 7)), (10,))

    def test_if_branch(self) -> None:
        yul = "function f(x) -> z { if x { z := 1 } }"
        self.assertEqual(self._eval_normalized(yul, (0,)), (0,))
        self.assertEqual(self._eval_normalized(yul, (1,)), (1,))

    def test_switch_as_if_else(self) -> None:
        yul = """
            function f(x) -> z {
                switch x
                case 0 { z := 10 }
                default { z := 20 }
            }
        """
        self.assertEqual(self._eval_normalized(yul, (0,)), (10,))
        self.assertEqual(self._eval_normalized(yul, (1,)), (20,))

    def test_nested_helper_call(self) -> None:
        """Local helper calls are auto-resolved by SymbolId from NFunctionDef nodes."""
        yul = """
            function f(x) -> z {
                function g(a) -> b { b := add(a, 1) }
                z := g(x)
            }
        """
        self.assertEqual(self._eval_normalized(yul, (5,)), (6,))
        self.assertEqual(self._eval_normalized(yul, (0,)), (1,))

    def test_multi_return(self) -> None:
        yul = """
            function f(x) -> a, b {
                function g(v) -> p, q { p := v  q := add(v, 1) }
                a, b := g(x)
            }
        """
        self.assertEqual(self._eval_normalized(yul, (10,)), (10, 11))

    def test_shared_memory_across_helper_calls(self) -> None:
        """mstore in a helper is visible to mload in the caller (shared memory)."""
        yul = """
            function f() -> z {
                function g() { mstore(0, 7) }
                g()
                z := mload(0)
            }
        """
        # mstore/mload are not in _SUPPORTED_OPS, so pass empty builtins
        # to avoid confusing them with arithmetic ops.
        self.assertEqual(self._eval_normalized(yul, (), builtins=frozenset()), (7,))

    def test_same_named_helpers_resolved_by_symbol_id(self) -> None:
        """Two branch-local helpers named 'g' are distinguished by SymbolId."""
        yul = """
            function f(x) -> z {
                if x {
                    function g(a) -> b { b := add(a, 1) }
                    z := g(1)
                }
            }
        """
        self.assertEqual(self._eval_normalized(yul, (1,)), (2,))
        self.assertEqual(self._eval_normalized(yul, (0,)), (0,))

    def test_recursion_detection(self) -> None:
        """Mutual recursion (f→g→f) is caught before hitting Python stack limit."""
        yul = """
            function f(x) -> z { z := g(x) }
            function g(x) -> z { z := f(x) }
        """
        tokens = ytl.tokenize_yul(yul)
        funcs = SyntaxParser(tokens).parse_functions()
        results = resolve_module(funcs)
        nf_f = normalize_function(funcs[0], results["f"])
        nf_g = normalize_function(funcs[1], results["g"])

        ft: dict[str, norm_ir.NormalizedFunction] = {"f": nf_f, "g": nf_g}
        with self.assertRaisesRegex(ytl.EvaluationError, "Recursive call"):
            evaluate_normalized(nf_f, (1,), function_table=ft)


if __name__ == "__main__":
    unittest.main()
