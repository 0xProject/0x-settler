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


if __name__ == "__main__":
    unittest.main()
