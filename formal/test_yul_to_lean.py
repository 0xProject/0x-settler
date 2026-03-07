import pathlib
import sys
import unittest


sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

import yul_to_lean as ytl


class HoistRepeatedModelCallsTest(unittest.TestCase):
    MODEL_CALLS = frozenset({"inner"})

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
            model, model_call_names=self.MODEL_CALLS,
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
                    modified_vars=("y", "a"),
                    assignments=(
                        ytl.Assignment("y", ytl.Call("add", (ytl.Var("p"), ytl.Var("p")))),
                        ytl.Assignment("a", ytl.Call("inner", (ytl.Var("y"),))),
                    ),
                    else_vars=("y", "a"),
                    else_assignments=(
                        ytl.Assignment("y", ytl.Call("add", (ytl.Var("p"), ytl.Var("p")))),
                        ytl.Assignment("a", ytl.Call("inner", (ytl.Var("y"),))),
                    ),
                ),
                ytl.Assignment("out", ytl.Var("a")),
            ),
        )

        transformed = ytl.hoist_repeated_model_calls(
            model, model_call_names=self.MODEL_CALLS,
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
                stmt.assignments,
                available=scope,
            )
            for var in stmt.modified_vars:
                self.assertIn(var, then_scope, f"then-branch does not define {var}")

            if stmt.else_assignments is None:
                if stmt.else_vars is not None:
                    for var in stmt.else_vars:
                        self.assertIn(var, scope, f"else passthrough var {var} missing")
            else:
                else_scope = self._assert_block_well_scoped(
                    stmt.else_assignments,
                    available=scope,
                )
                mapped_else_vars = (
                    stmt.else_vars if stmt.else_vars is not None else stmt.modified_vars
                )
                for var in mapped_else_vars:
                    self.assertIn(var, else_scope, f"else-branch does not define {var}")

            scope.update(stmt.modified_vars)

        return scope

    def _eval_model(self, model: ytl.FunctionModel, *, p: int) -> int:
        env = self._eval_block(model.assignments, {"p": p})
        if len(model.return_names) != 1:
            raise AssertionError("test helper expects single-return models")
        return env[model.return_names[0]]

    def _eval_block(
        self,
        statements: tuple[ytl.ModelStatement, ...],
        env: dict[str, int],
    ) -> dict[str, int]:
        env = dict(env)
        for stmt in statements:
            if isinstance(stmt, ytl.Assignment):
                env[stmt.target] = self._eval_expr(stmt.expr, env)
                continue

            if not isinstance(stmt, ytl.ConditionalBlock):
                raise TypeError(f"Unsupported statement: {type(stmt)}")

            branch_env = dict(env)
            if self._eval_expr(stmt.condition, env) != 0:
                branch_env = self._eval_block(stmt.assignments, branch_env)
                for var in stmt.modified_vars:
                    env[var] = branch_env[var]
                continue

            if stmt.else_assignments is not None:
                branch_env = self._eval_block(stmt.else_assignments, branch_env)
                else_vars = (
                    stmt.else_vars if stmt.else_vars is not None else stmt.modified_vars
                )
                for target, source in zip(stmt.modified_vars, else_vars, strict=True):
                    env[target] = branch_env[source]
                continue

            if stmt.else_vars is not None:
                for target, source in zip(stmt.modified_vars, stmt.else_vars, strict=True):
                    env[target] = env[source]

        return env

    def _eval_expr(self, expr: ytl.Expr, env: dict[str, int]) -> int:
        if isinstance(expr, ytl.IntLit):
            return expr.value
        if isinstance(expr, ytl.Var):
            return env[expr.name]
        if not isinstance(expr, ytl.Call):
            raise TypeError(f"Unsupported expr: {type(expr)}")

        args = tuple(self._eval_expr(arg, env) for arg in expr.args)
        if expr.name == "add":
            return args[0] + args[1]
        if expr.name == "sub":
            return args[0] - args[1]
        if expr.name == "inner":
            return args[0] * args[0] + 1
        raise ValueError(f"Unsupported call in test evaluator: {expr.name}")


class FailClosedTranslatorTest(unittest.TestCase):
    def test_parse_function_rejects_non_function_keyword(self) -> None:
        parser = ytl.YulParser([("ident", "not_function")])

        with self.assertRaisesRegex(ytl.ParseError, "Expected 'function'"):
            parser.parse_function()

    def test_parse_function_rejects_unrecognized_statement_start(self) -> None:
        tokens = ytl.tokenize_yul(
            """
            function fun_bad_1() -> z {
                "oops"
                z := 1
            }
            """
        )

        with self.assertRaisesRegex(ytl.ParseError, "Unsupported statement start"):
            ytl.YulParser(tokens).parse_function()

    def test_parse_function_rejects_conditional_memory_write(self) -> None:
        tokens = ytl.tokenize_yul(
            """
            function fun_bad_1(x) -> z {
                if x {
                    mstore(0, x)
                }
                z := x
            }
            """
        )

        with self.assertRaisesRegex(ytl.ParseError, "Conditional memory write"):
            ytl.YulParser(tokens).parse_function()

    def test_collect_all_functions_records_rejected_helper_and_inlining_fails(self) -> None:
        tokens = ytl.tokenize_yul(
            """
            function fun_target_1(x) -> z {
                z := bad_helper(x)
            }

            function bad_helper(a) -> b {
                for { } 1 { } { }
            }
            """
        )
        collection = ytl.YulParser(tokens).collect_all_functions()
        target = collection.functions["fun_target_1"]

        self.assertIn("bad_helper", collection.rejected)
        with self.assertRaisesRegex(ytl.ParseError, "Cannot inline helper 'bad_helper'"):
            ytl._inline_yul_function(
                target,
                collection.functions,
                unsupported_function_errors=collection.rejected,
            )

    def test_inline_calls_rejects_depth_overflow(self) -> None:
        fn_table = {
            "f": ytl.YulFunction(
                yul_name="f",
                params=["x"],
                rets=["r"],
                assignments=[("r", ytl.Call("g", (ytl.Var("x"),)))],
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
                ("tmp", ytl.IntLit(1)),
                ("tmp", ytl.IntLit(2)),
                ("ret", ytl.Var("tmp")),
            ],
        )

        with self.assertRaisesRegex(ytl.ParseError, "classified as a compiler temporary"):
            ytl.yul_function_to_model(yf, "f", {})

    def test_inline_yul_function_rejects_helper_memory_write_inside_conditional(self) -> None:
        helper = ytl.YulFunction(
            yul_name="store_helper",
            params=["arg"],
            rets=["ret"],
            assignments=[
                ytl.MemoryWrite(ytl.IntLit(0), ytl.Var("arg")),
                ("ret", ytl.Var("arg")),
            ],
        )
        target = ytl.YulFunction(
            yul_name="target",
            params=["flag", "x"],
            rets=["ret"],
            assignments=[
                ytl.ParsedIfBlock(
                    condition=ytl.Var("flag"),
                    body=(("ret", ytl.Call("store_helper", (ytl.Var("x"),))),),
                ),
            ],
        )

        with self.assertRaisesRegex(ytl.ParseError, "Conditional memory write"):
            ytl._inline_yul_function(target, {"store_helper": helper})

    def test_inline_yul_function_preserves_else_body(self) -> None:
        helper = ytl.YulFunction(
            yul_name="inc",
            params=["arg"],
            rets=["ret"],
            assignments=[("ret", ytl.Call("add", (ytl.Var("arg"), ytl.IntLit(1))))],
        )
        target = ytl.YulFunction(
            yul_name="target",
            params=["flag", "x"],
            rets=["ret"],
            assignments=[
                ytl.ParsedIfBlock(
                    condition=ytl.Var("flag"),
                    body=(("ret", ytl.Call("inc", (ytl.Var("x"),))),),
                    else_body=(("ret", ytl.Var("x")),),
                ),
            ],
        )

        inlined = ytl._inline_yul_function(target, {"inc": helper})

        self.assertEqual(
            inlined.assignments,
            [
                ytl.ParsedIfBlock(
                    condition=ytl.Var("flag"),
                    body=(("ret", ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1)))),),
                    else_body=(("ret", ytl.Var("x")),),
                ),
            ],
        )


def make_model_config(
    function_order: tuple[str, ...],
    *,
    hoist_repeated_calls: frozenset[str] = frozenset(),
    skip_prune: frozenset[str] = frozenset(),
    keep_solidity_locals: bool = False,
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
        keep_solidity_locals=keep_solidity_locals,
        hoist_repeated_calls=hoist_repeated_calls,
        skip_prune=skip_prune,
        default_source_label="test",
        default_namespace="Test",
        default_output="",
        cli_description="test",
    )


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

    def test_translate_yul_to_models_raw_preserves_zero_and_dead_assignments(self) -> None:
        result = ytl.translate_yul_to_models(
            self.SIMPLE_YUL,
            self.SIMPLE_CONFIG,
            pipeline=ytl.RAW_TRANSLATION_PIPELINE,
        )
        model = result.models[0]

        self.assertEqual(result.pipeline, ytl.RAW_TRANSLATION_PIPELINE)
        self.assertEqual(
            [stmt.target for stmt in model.assignments if isinstance(stmt, ytl.Assignment)],
            ["tmp", "dead", "z", "z_1"],
        )
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
        self.assertEqual(model.assignments, (
            ytl.Assignment("z_1", ytl.Call("add", (ytl.Var("x"), ytl.IntLit(1)))),
        ))

    def test_apply_optional_model_transforms_skips_hoisting_in_raw_pipeline(self) -> None:
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

        self.assertEqual(raw_models, [model])
        self.assertNotEqual(optimized_models, [model])
        self.assertIsInstance(optimized_models[0].assignments[0], ytl.Assignment)
        self.assertRegex(optimized_models[0].assignments[0].target, r"^_cse_\d+$")


class ExplicitMemoryModelTest(unittest.TestCase):
    def test_yul_function_to_model_resolves_sequential_memory_slots(self) -> None:
        yf = ytl.YulFunction(
            yul_name="f",
            params=["var_x_1"],
            rets=["var_z_2"],
            assignments=[
                ("usr$base", ytl.IntLit(0)),
                ("usr$offset", ytl.IntLit(32)),
                ytl.MemoryWrite(ytl.Var("usr$base"), ytl.Var("var_x_1")),
                ytl.MemoryWrite(
                    ytl.Call("add", (ytl.Var("usr$base"), ytl.Var("usr$offset"))),
                    ytl.Call("mload", (ytl.Var("usr$base"),)),
                ),
                (
                    "var_z_2",
                    ytl.Call(
                        "mload",
                        (ytl.Call("add", (ytl.Var("usr$base"), ytl.Var("usr$offset"))),),
                    ),
                ),
            ],
        )

        model = ytl.yul_function_to_model(yf, "f", {})

        self.assertEqual(
            model.assignments,
            (
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
                ("usr$base", ytl.IntLit(0)),
                ytl.MemoryWrite(ytl.Var("usr$base"), ytl.Var("var_x_1")),
                ytl.MemoryWrite(ytl.Var("usr$base"), ytl.Var("var_x_1")),
                ("var_z_2", ytl.Var("var_x_1")),
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
                ("usr$base", ytl.IntLit(0)),
                ("var_z_2", ytl.Call("mload", (ytl.Var("usr$base"),))),
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
                ("var_z_2", ytl.IntLit(0)),
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
                ("var_z_2", ytl.IntLit(0)),
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
                ("var_z_2", ytl.Call("mload", (ytl.IntLit(1),))),
            ],
        )

        with self.assertRaisesRegex(ytl.ParseError, "unaligned address 1"):
            ytl.yul_function_to_model(yf, "f", {})


if __name__ == "__main__":
    unittest.main()
