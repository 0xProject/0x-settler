import os
import pathlib
import random
import subprocess
import sys
import unittest
from dataclasses import dataclass
from typing import Callable, cast

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

import model_config as modelcfg
from evm_builtins import (
    BASE_NORM_HELPERS,
    EVM_BUILTINS,
    OP_TO_LEAN_HELPER,
    OP_TO_OPCODE,
    WORD_MOD,
    eval_pure_builtin,
)
from lean_emit import (
    build_lean_source,
    build_model_body,
    emit_expr,
    render_function_defs,
)
from lean_names import validate_ident
from model_eval import build_model_table, evaluate_function_model
from model_helpers import _expr_vars, collect_model_opcodes, collect_ops_from_statement
from model_ir import (
    Assignment,
    Call,
    ConditionalBlock,
    ConditionalBranch,
    Expr,
    FunctionModel,
    IntLit,
    Ite,
    ModelStatement,
    Project,
    Var,
)
from model_transforms import (
    _prune_dead_assignments,
    apply_optional_model_transforms,
    hoist_repeated_model_calls,
)
from model_validate import validate_function_model, validate_model_set
from staged_selection import build_selection_plan
from yul_lexer import tokenize_yul

import norm_ir
import yul_ast
from norm_classify import (
    InlineClassification,
    classify_function_scope,
    summarize_function,
)
from norm_constprop import fold_expr, propagate_constants
from norm_eval import evaluate_normalized
from norm_inline import inline_pure_helpers
from norm_memory import lower_memory
from norm_to_restricted import lower_to_restricted
from restricted_eval import evaluate_restricted
from restricted_ir import RestrictedFunction
from restricted_to_model import to_function_models
from yul_ast import EvaluationError, ParseError
from yul_normalize import normalize_function
from yul_parser import SyntaxParser
from yul_resolve import ResolutionResult, resolve_function, resolve_module
from yul_to_lean import translate_yul_to_models


def branch(
    assignments: tuple[ModelStatement, ...] | list[ModelStatement],
    outputs: tuple[str | Expr, ...] | list[str | Expr],
) -> ConditionalBranch:
    wrapped: tuple[Expr, ...] = tuple(
        Var(o) if isinstance(o, str) else o for o in outputs
    )
    return ConditionalBranch(
        assignments=tuple(assignments),
        outputs=wrapped,
    )


@dataclass(frozen=True)
class _SelectedMatch:
    yul_name: str
    lexical_path: tuple[str, ...]
    token_idx: int


def _tokens_to_yul(tokens: list[tuple[str, str]]) -> str:
    return " ".join(text for _, text in tokens)


def _find_function(
    tokens: list[tuple[str, str]],
    sol_fn_name: str,
    *,
    n_params: int | None = None,
    known_yul_names: set[str] | None = None,
    avoid_known: bool = False,
) -> _SelectedMatch:
    known_names = tuple(sorted(known_yul_names or ()))
    known_aliases = tuple(f"known_{idx}" for idx, _ in enumerate(known_names))
    selected = known_aliases + (sol_fn_name,)
    config = make_model_config(
        selected,
        exact_yul_names={
            **{alias: name for alias, name in zip(known_aliases, known_names)},
        }
        or None,
        n_params={sol_fn_name: n_params} if n_params is not None else None,
        require_reaching_selected=(
            {sol_fn_name: frozenset(known_aliases)}
            if known_aliases and not avoid_known
            else None
        ),
        avoid_reaching_selected=(
            {sol_fn_name: frozenset(known_aliases)} if avoid_known else None
        ),
    )
    plan = build_selection_plan(_tokens_to_yul(tokens), config.selection)
    info = plan.target_infos[sol_fn_name]
    return _SelectedMatch(
        yul_name=info.raw_name,
        lexical_path=info.lexical_path,
        token_idx=info.key.token_idx,
    )


def _find_exact_function(
    tokens: list[tuple[str, str]],
    yul_name: str,
    *,
    n_params: int | None = None,
    search_nested: bool = False,
) -> _SelectedMatch:
    selector = yul_name if search_nested else f"::{yul_name}"
    config = make_model_config(
        ("target",),
        exact_yul_names={"target": selector},
        n_params={"target": n_params} if n_params is not None else None,
    )
    try:
        plan = build_selection_plan(_tokens_to_yul(tokens), config.selection)
    except ParseError as exc:
        if not search_nested:
            message = str(exc)
            path_prefix = "Exact Yul function path "
            if message.startswith(path_prefix):
                raise ParseError(
                    f"Exact Yul function {yul_name!r}{message[len(path_prefix) + len(repr(yul_name)):]}"
                ) from exc
        raise
    info = plan.target_infos["target"]
    return _SelectedMatch(
        yul_name=info.raw_name,
        lexical_path=info.lexical_path,
        token_idx=info.key.token_idx,
    )


def _find_exact_function_path(
    tokens: list[tuple[str, str]],
    yul_path: tuple[str, ...],
    *,
    n_params: int | None = None,
) -> _SelectedMatch:
    if not yul_path:
        raise ParseError("Exact Yul function path cannot be empty")
    selector = f"::{yul_path[0]}" if len(yul_path) == 1 else "::".join(yul_path)
    config = make_model_config(
        ("target",),
        exact_yul_names={"target": selector},
        n_params={"target": n_params} if n_params is not None else None,
    )
    plan = build_selection_plan(_tokens_to_yul(tokens), config.selection)
    info = plan.target_infos["target"]
    return _SelectedMatch(
        yul_name=info.raw_name,
        lexical_path=info.lexical_path,
        token_idx=info.key.token_idx,
    )


def _nref(name: str, sid: int = 0) -> norm_ir.NRef:
    return norm_ir.NRef(symbol_id=yul_ast.SymbolId(sid), name=name)


class HoistRepeatedModelCallsTest(unittest.TestCase):
    MODEL_CALLS = frozenset({"inner"})

    # Define ``inner`` as a proper FunctionModel: inner(x) = x*x + 1
    INNER_MODEL = FunctionModel(
        fn_name="inner",
        param_names=("x",),
        return_names=("ret",),
        assignments=(
            Assignment(
                "ret",
                Call(
                    "add",
                    (Call("mul", (Var("x"), Var("x"))), IntLit(1)),
                ),
            ),
        ),
    )

    def test_redefinition_blocks_cross_statement_hoist(self) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("p",),
            return_names=("out",),
            assignments=(
                Assignment("y", Var("p")),
                Assignment("a", Call("inner", (Var("y"),))),
                Assignment("y", Call("add", (Var("y"), Var("p")))),
                Assignment("b", Call("inner", (Var("y"),))),
                Assignment("out", Call("sub", (Var("b"), Var("a")))),
            ),
        )

        transformed = hoist_repeated_model_calls(
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
        model = FunctionModel(
            fn_name="g",
            param_names=("p",),
            return_names=("out",),
            assignments=(
                ConditionalBlock(
                    condition=Var("p"),
                    output_vars=("y", "a"),
                    then_branch=branch(
                        (
                            Assignment("y", Call("add", (Var("p"), Var("p")))),
                            Assignment("a", Call("inner", (Var("y"),))),
                        ),
                        ("y", "a"),
                    ),
                    else_branch=branch(
                        (
                            Assignment("y", Call("add", (Var("p"), Var("p")))),
                            Assignment("a", Call("inner", (Var("y"),))),
                        ),
                        ("y", "a"),
                    ),
                ),
                Assignment("out", Var("a")),
            ),
        )

        transformed = hoist_repeated_model_calls(
            model,
            model_call_names=self.MODEL_CALLS,
        )

        self._assert_well_scoped(transformed)
        for p in (0, 1, 9):
            self.assertEqual(
                self._eval_model(model, p=p),
                self._eval_model(transformed, p=p),
            )

    def _assert_well_scoped(self, model: FunctionModel) -> None:
        self._assert_block_well_scoped(
            model.assignments,
            available=set(model.param_names),
        )

    def _assert_block_well_scoped(
        self,
        statements: tuple[ModelStatement, ...],
        *,
        available: set[str],
    ) -> set[str]:
        scope = set(available)

        for stmt in statements:
            if isinstance(stmt, Assignment):
                missing = _expr_vars(stmt.expr) - scope
                self.assertFalse(
                    missing,
                    f"{stmt.target} uses undefined vars: {sorted(missing)}",
                )
                scope.add(stmt.target)
                continue

            if not isinstance(stmt, ConditionalBlock):
                raise TypeError(f"Unsupported statement: {type(stmt)}")

            missing = _expr_vars(stmt.condition) - scope
            self.assertFalse(
                missing,
                f"conditional uses undefined vars: {sorted(missing)}",
            )

            then_scope = self._assert_block_well_scoped(
                stmt.then_branch.assignments,
                available=scope,
            )
            for out_expr in stmt.then_branch.outputs:
                missing = _expr_vars(out_expr) - then_scope
                self.assertFalse(
                    missing, f"then-branch output {out_expr} uses {sorted(missing)}"
                )

            else_scope = self._assert_block_well_scoped(
                stmt.else_branch.assignments,
                available=scope,
            )
            for out_expr in stmt.else_branch.outputs:
                missing = _expr_vars(out_expr) - else_scope
                self.assertFalse(
                    missing, f"else-branch output {out_expr} uses {sorted(missing)}"
                )

            scope.update(stmt.output_vars)

        return scope

    def _eval_model(self, model: FunctionModel, *, p: int) -> int:
        table = build_model_table([self.INNER_MODEL, model])
        result = evaluate_function_model(model, (p,), model_table=table)
        if len(result) != 1:
            raise AssertionError("test helper expects single-return models")
        return result[0]


class StagedPipelineSmokeTest(unittest.TestCase):
    def test_tokenize_yul_rejects_malformed_input(self) -> None:
        with self.assertRaisesRegex(ParseError, "tokenizer stuck"):
            tokenize_yul("function fun_bad_1() { let x := 1 @ }")

    def test_syntax_parser_rejects_non_function_keyword(self) -> None:
        parser = SyntaxParser([("ident", "not_function")])

        with self.assertRaisesRegex(ParseError, "Expected 'function'"):
            parser.parse_function()

    def test_syntax_parser_rejects_unrecognized_statement_start(self) -> None:
        tokens = tokenize_yul("""
            function fun_bad_1() -> z {
                ->
                z := 1
            }
            """)

        with self.assertRaisesRegex(ParseError, "Unexpected statement start"):
            SyntaxParser(tokens).parse_function()

    def test_translate_yul_to_models_zero_initializes_multi_var_declaration(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_1 {
                let usr$a, usr$b
                var_z_1 := add(usr$a, usr$b)
            }
            """

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(
            model.assignments[:2],
            (
                Assignment("a", IntLit(0)),
                Assignment("b", IntLit(0)),
            ),
        )
        self.assertEqual(evaluate_function_model(model, ()), (0,))

    def test_translate_yul_to_models_rejects_multi_var_initializer_from_scalar_expr(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_1 {
                let usr$a, usr$b := 1
                var_z_1 := usr$a
            }
            """

        with self.assertRaisesRegex(
            ParseError,
            "Multi-target assignment in restricted IR lowering requires",
        ):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
            )

    def test_translate_yul_to_models_lowers_multi_target_assignment_without_let(
        self,
    ) -> None:
        config = make_model_config(("f", "pair"))
        yul = """
            function fun_f_1() -> var_z_1 {
                let usr$a
                let usr$b
                usr$a, usr$b := fun_pair_2()
                var_z_1 := usr$a
            }

            function fun_pair_2() -> var_a_1, var_b_1 {
                var_a_1 := 7
                var_b_1 := 9
            }
            """

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        models = build_model_table(result)
        model = models["f"]

        self.assertEqual(evaluate_function_model(model, (), model_table=models), (7,))
        self.assertIn(
            Assignment(
                "a_1",
                Project(0, 2, Call("pair", ())),
            ),
            model.assignments,
        )
        self.assertIn(
            Assignment(
                "b_1",
                Project(1, 2, Call("pair", ())),
            ),
            model.assignments,
        )

    def test_translate_yul_to_models_merges_bare_block_switch_temporary_updates(
        self,
    ) -> None:
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
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (10, 0)), (11,))
        self.assertEqual(evaluate_function_model(model, (10, 1)), (12,))


def make_model_config(
    function_order: tuple[str, ...],
    *,
    model_names: dict[str, str] | None = None,
    header_comment: str = "test",
    generator_label: str = "formal/test_yul_to_lean.py",
    norm_extensions: tuple[modelcfg.NormExtension, ...] = (),
    norm_rewrite: Callable[[Expr], Expr] | None = None,
    inner_fn: str | None = None,
    hoist_repeated_calls: frozenset[str] = frozenset(),
    skip_norm: frozenset[str] = frozenset(),
    skip_prune: frozenset[str] = frozenset(),
    exact_yul_names: dict[str, str] | None = None,
    n_params: dict[str, int] | None = None,
    require_reaching_selected: dict[str, frozenset[str]] | None = None,
    avoid_reaching_selected: dict[str, frozenset[str]] | None = None,
    source_label: str = "test",
    namespace: str = "Test",
    output: str = "",
    description: str = "test",
) -> modelcfg.ModelConfig:
    return modelcfg.ModelConfig(
        selection=modelcfg.SelectionConfig(
            function_order=function_order,
            inner_fn=inner_fn or function_order[0],
            n_params=n_params or {},
            exact_yul_names=exact_yul_names or {},
            require_reaching_selected=require_reaching_selected or {},
            avoid_reaching_selected=avoid_reaching_selected or {},
        ),
        emission=modelcfg.EmissionConfig(
            model_names=model_names or {fn: f"model_{fn}" for fn in function_order},
            header_comment=header_comment,
            generator_label=generator_label,
            norm_rewrite=norm_rewrite,
            norm_extensions=norm_extensions,
        ),
        transforms=modelcfg.TransformConfig(
            skip_norm=skip_norm,
            hoist_repeated_calls=hoist_repeated_calls,
            skip_prune=skip_prune,
        ),
        cli=modelcfg.CliConfig(
            source_label=source_label,
            namespace=namespace,
            output=output,
            description=description,
        ),
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
        WORD_MOD - 1,
        WORD_MOD,
        WORD_MOD + 1,
        WORD_MOD + 255,
    )

    def assertModelsEquivalent(
        self,
        before: FunctionModel,
        after: FunctionModel,
        *,
        before_table: dict[str, FunctionModel] | None = None,
        after_table: dict[str, FunctionModel] | None = None,
        random_cases: int = 64,
        seed: int = 0,
    ) -> None:
        self.assertEqual(
            len(before.param_names),
            len(after.param_names),
            "equivalence fuzzer requires matching arity",
        )

        if before_table is None:
            before_table = build_model_table([before])
        if after_table is None:
            after_table = build_model_table([after])

        validate_function_model(before)
        validate_function_model(after)

        for args in self._equivalence_cases(
            len(before.param_names), seed=seed, random_cases=random_cases
        ):
            before_result = evaluate_function_model(
                before,
                args,
                model_table=before_table,
            )
            after_result = evaluate_function_model(
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


class TranslationFlowTest(unittest.TestCase):
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
        bad_model = FunctionModel(
            fn_name="bad",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                Assignment(
                    "z",
                    Call("add", (Var("x"), Var("missing"))),
                ),
            ),
        )

        with self.assertRaisesRegex(ParseError, "out-of-scope"):
            validate_function_model(bad_model)

    def test_translate_yul_to_models_raw_preserves_zero_and_dead_assignments(
        self,
    ) -> None:
        result = translate_yul_to_models(
            self.SIMPLE_YUL,
            self.SIMPLE_CONFIG,
            optimize=False,
        )
        model = result[0]

        assignment_targets: list[str] = [
            stmt.target for stmt in model.assignments if isinstance(stmt, Assignment)
        ]
        expected_targets: list[str] = ["tmp", "dead", "z", "z_1"]
        self.assertEqual(assignment_targets, expected_targets)
        self.assertEqual(model.return_names, ("z_1",))

    def test_translate_yul_to_models_defaults_to_optimized_pipeline(self) -> None:
        default_result = translate_yul_to_models(
            self.SIMPLE_YUL,
            self.SIMPLE_CONFIG,
        )
        explicit_result = translate_yul_to_models(
            self.SIMPLE_YUL,
            self.SIMPLE_CONFIG,
            optimize=True,
        )

        self.assertEqual(default_result, explicit_result)
        model = default_result[0]
        self.assertEqual(len(model.assignments), 1)
        only = model.assignments[0]
        self.assertIsInstance(only, Assignment)
        only = cast(Assignment, only)
        self.assertTrue(only.target.startswith("z_"))
        self.assertEqual(
            only.expr,
            Call("add", (Var("x"), IntLit(1))),
        )

    def test_render_function_defs_uses_demangled_ssa_names(self) -> None:
        result = translate_yul_to_models(
            self.SIMPLE_YUL,
            self.SIMPLE_CONFIG,
            optimize=False,
        )
        model = result[0]
        rendered = render_function_defs([model], self.SIMPLE_CONFIG)

        self.assertIn("def model_f_evm (x : Nat) : Nat :=", rendered)
        self.assertIn("let x := u256 x", rendered)
        self.assertIn("let dead := 7", rendered)
        self.assertIn("let z := 0", rendered)
        self.assertIn("let z_1 := evmAdd (x) (1)", rendered)
        self.assertNotIn("usr$tmp", rendered)
        self.assertNotIn("var_z_2", rendered)

    def test_render_function_defs_supports_zero_argument_models(self) -> None:
        model = FunctionModel(
            fn_name="f",
            assignments=(Assignment("z", IntLit(1)),),
            param_names=(),
            return_names=("z",),
        )

        rendered = render_function_defs([model], self.SIMPLE_CONFIG)

        self.assertIn("def model_f_evm : Nat :=", rendered)
        self.assertIn("def model_f : Nat :=", rendered)
        self.assertNotIn("( : Nat)", rendered)

    def test_apply_optional_model_transforms_skips_hoisting_in_raw_pipeline(
        self,
    ) -> None:
        model = FunctionModel(
            fn_name="outer",
            param_names=("p",),
            return_names=("out",),
            assignments=(
                Assignment("a", Call("inner", (Var("p"),))),
                Assignment("b", Call("inner", (Var("p"),))),
                Assignment("out", Call("sub", (Var("a"), Var("b")))),
            ),
        )
        config = make_model_config(
            ("inner", "outer"),
            hoist_repeated_calls=frozenset({"outer"}),
        )

        raw_models = apply_optional_model_transforms(
            [model],
            config,
            optimize=False,
        )
        optimized_models = apply_optional_model_transforms(
            [model],
            config,
            optimize=True,
        )

        expected_models: list[FunctionModel] = [model]
        self.assertEqual(raw_models, expected_models)
        self.assertNotEqual(optimized_models, expected_models)
        first_stmt = optimized_models[0].assignments[0]
        self.assertIsInstance(first_stmt, Assignment)
        first_stmt = cast(Assignment, first_stmt)
        self.assertRegex(first_stmt.target, r"^_cse_\d+$")

    def test_multi_return_rebinding_keeps_old_argument_binding_for_later_components(
        self,
    ) -> None:
        result = translate_yul_to_models(
            self.MULTI_RETURN_REBIND_YUL,
            self.MULTI_RETURN_REBIND_CONFIG,
            optimize=False,
        )
        model = result[0]

        # Find the multi-return Project assignments.
        project_assigns = [
            stmt
            for stmt in model.assignments
            if isinstance(stmt, Assignment) and isinstance(stmt.expr, Project)
        ]
        if len(project_assigns) >= 2:
            x_lo_update, x_hi_update = project_assigns[0], project_assigns[1]
            self.assertNotIn(
                x_lo_update.target,
                _expr_vars(x_hi_update.expr),
                "later rebound component unexpectedly captured the already-updated "
                "argument value instead of the pre-call binding",
            )

    def test_multi_return_rebinding_matches_simultaneous_assignment_semantics(
        self,
    ) -> None:
        result = translate_yul_to_models(
            self.MULTI_RETURN_REBIND_YUL,
            self.MULTI_RETURN_REBIND_CONFIG,
            optimize=False,
        )
        model = result[0]

        for x_hi, x_lo in ((7, 11), (0, 3), (123, 0), (WORD_MOD - 1, 9)):
            with self.subTest(x_hi=x_hi, x_lo=x_lo):
                actual = evaluate_function_model(model, (x_hi, x_lo))
                expected = ((x_hi - 1) % WORD_MOD,)
                self.assertEqual(actual, expected)

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
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        # Check no duplicate targets in straight-line assignments.
        targets: list[str] = []
        for stmt in model.assignments:
            if isinstance(stmt, Assignment):
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
        self.assertEqual(evaluate_function_model(model, (10, 0)), (52,))
        self.assertEqual(evaluate_function_model(model, (10, 1)), (75,))

    def test_translate_yul_to_models_allows_nested_helper_memory_write_through_local(
        self,
    ) -> None:
        result = translate_yul_to_models(
            self.NESTED_MEMORY_ALIAS_LOCAL_YUL,
            self.NESTED_MEMORY_ALIAS_CONFIG,
            optimize=False,
        )
        model = result[0]
        self.assertEqual(
            evaluate_function_model(
                model,
                (13,),
                model_table=build_model_table(result),
            ),
            (13,),
        )

    def test_translate_yul_to_models_allows_nested_helper_memory_write_through_temp(
        self,
    ) -> None:
        result = translate_yul_to_models(
            self.NESTED_MEMORY_ALIAS_TEMP_YUL,
            self.NESTED_MEMORY_ALIAS_CONFIG,
            optimize=False,
        )
        model = result[0]
        self.assertEqual(
            evaluate_function_model(
                model,
                (13,),
                model_table=build_model_table(result),
            ),
            (13,),
        )

    def test_translate_yul_to_models_allows_top_level_memory_write_with_helper_mload(
        self,
    ) -> None:
        result = translate_yul_to_models(
            self.TOP_LEVEL_MEMORY_READ_HELPER_YUL,
            self.TOP_LEVEL_MEMORY_READ_HELPER_CONFIG,
            optimize=False,
        )
        model = result[0]

        for x in (0, 1, 7, 32, WORD_MOD - 1):
            with self.subTest(x=x):
                self.assertEqual(
                    evaluate_function_model(model, (x,)),
                    (x,),
                )

    def test_translate_yul_to_models_allows_exact_from_helper(
        self,
    ) -> None:
        result = translate_yul_to_models(
            self.FROM_HELPER_YUL,
            self.FROM_HELPER_CONFIG,
            optimize=False,
        )
        model = result[0]

        cases = {
            (0, 0): (0,),
            (1, 0): (1,),
            (0, 7): (7,),
            (5, 11): (16,),
            (WORD_MOD - 1, 3): (2,),
        }
        for args, expected in cases.items():
            with self.subTest(args=args):
                self.assertEqual(
                    evaluate_function_model(model, args),
                    expected,
                )

    def test_translate_yul_to_models_lowers_inlined_leave(self) -> None:
        result = translate_yul_to_models(
            self.LEAVE_HELPER_YUL,
            self.LEAVE_HELPER_CONFIG,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (0,)), (9,))
        self.assertEqual(evaluate_function_model(model, (1,)), (7,))
        self.assertEqual(evaluate_function_model(model, (WORD_MOD - 1,)), (7,))

    def test_translate_yul_to_models_ignores_dead_code_after_inlined_leave(
        self,
    ) -> None:
        result = translate_yul_to_models(
            self.LEAVE_HELPER_DEAD_CODE_YUL,
            self.LEAVE_HELPER_CONFIG,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (0,)), (9,))
        self.assertEqual(evaluate_function_model(model, (1,)), (7,))

    def test_translate_yul_to_models_lowers_plain_inlined_if(self) -> None:
        result = translate_yul_to_models(
            self.PLAIN_IF_HELPER_YUL,
            self.PLAIN_IF_HELPER_CONFIG,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (0, 5)), (5,))
        self.assertEqual(evaluate_function_model(model, (1, 5)), (6,))
        self.assertEqual(
            evaluate_function_model(model, (WORD_MOD - 1, 5)),
            (6,),
        )

    def test_translate_yul_to_models_handles_top_level_leave(self) -> None:
        """Top-level leave is lowered to did_leave flag semantics."""
        result = translate_yul_to_models(
            self.TOP_LEVEL_LEAVE_YUL,
            self.TOP_LEVEL_LEAVE_CONFIG,
            optimize=False,
        )
        model = result[0]
        # x=0: condition false → z=9
        self.assertEqual(evaluate_function_model(model, (0,)), (9,))
        # x=1: condition true, leave → z=7
        self.assertEqual(evaluate_function_model(model, (1,)), (7,))

    def test_translate_yul_to_models_handles_multiple_inlined_leave_sites(
        self,
    ) -> None:
        """New pipeline handles multiple leave sites via did_leave flag."""
        result = translate_yul_to_models(
            self.MULTI_LEAVE_HELPER_YUL,
            self.MULTI_LEAVE_HELPER_CONFIG,
            optimize=False,
        )
        model = result[0]
        # a=0,b=0: both conditions false → z=9
        self.assertEqual(evaluate_function_model(model, (0, 0)), (9,))
        # a=1,b=0: first condition true, leave → z=7
        self.assertEqual(evaluate_function_model(model, (1, 0)), (7,))
        # a=0,b=1: first false, second true, leave → z=8
        self.assertEqual(evaluate_function_model(model, (0, 1)), (8,))

    def test_translate_yul_to_models_isolates_conditional_branch_state(
        self,
    ) -> None:
        result = translate_yul_to_models(
            self.CONDITIONAL_BRANCH_ISOLATION_YUL,
            self.CONDITIONAL_BRANCH_ISOLATION_CONFIG,
            optimize=False,
        )
        model = result[0]

        cases = {
            (0, 0): (4,),
            (5, 0): (14,),
            (0, 1): (7,),
            (5, 1): (7,),
        }
        for args, expected in cases.items():
            with self.subTest(args=args):
                self.assertEqual(
                    evaluate_function_model(model, args),
                    expected,
                )

    def test_translate_yul_to_models_handles_sequential_if_and_switch_scoping(
        self,
    ) -> None:
        result = translate_yul_to_models(
            self.SEQUENTIAL_CONTROL_FLOW_YUL,
            self.SEQUENTIAL_CONTROL_FLOW_CONFIG,
            optimize=False,
        )
        model = result[0]

        cases = {
            (0, 0): (11,),
            (1, 0): (15,),
            (0, 1): (21,),
            (1, 1): (25,),
        }
        for args, expected in cases.items():
            with self.subTest(args=args):
                self.assertEqual(
                    evaluate_function_model(model, args),
                    expected,
                )


class RestrictedIRInterpreterTest(ModelEquivalenceTestCase):
    def test_evaluate_function_model_preserves_passthrough_when_if_is_false(
        self,
    ) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("out",),
            assignments=(
                Assignment("out", Call("add", (Var("x"), IntLit(5)))),
                ConditionalBlock(
                    condition=IntLit(0),
                    output_vars=("out",),
                    then_branch=branch(
                        (Assignment("out", IntLit(99)),),
                        ("out",),
                    ),
                    else_branch=branch((), ("out",)),
                ),
            ),
        )

        result = evaluate_function_model(model, (7,))

        self.assertEqual(result, (12,))

    def test_validate_function_model_rejects_undefined_conditional_branch_output(
        self,
    ) -> None:
        bad_model = FunctionModel(
            fn_name="bad_cond",
            param_names=("x",),
            return_names=("out",),
            assignments=(
                ConditionalBlock(
                    condition=Var("x"),
                    output_vars=("tmp",),
                    then_branch=branch((), ("missing",)),
                    else_branch=branch((), ("x",)),
                ),
                Assignment("out", Var("tmp")),
            ),
        )

        with self.assertRaisesRegex(ParseError, "undefined then-branch outputs"):
            validate_function_model(bad_model)

    def test_evaluate_function_model_supports_multi_return_projection(self) -> None:
        pair = FunctionModel(
            fn_name="pair",
            param_names=("x", "y"),
            return_names=("a", "b"),
            assignments=(
                Assignment("a", Call("add", (Var("x"), IntLit(1)))),
                Assignment("b", Call("mul", (Var("y"), IntLit(2)))),
            ),
        )
        outer = FunctionModel(
            fn_name="outer",
            param_names=("x", "y"),
            return_names=("out",),
            assignments=(
                Assignment(
                    "lhs",
                    Project(
                        0,
                        2,
                        Call("pair", (Var("x"), Var("y"))),
                    ),
                ),
                Assignment(
                    "rhs",
                    Project(
                        1,
                        2,
                        Call("pair", (Var("x"), Var("y"))),
                    ),
                ),
                Assignment("out", Call("add", (Var("lhs"), Var("rhs")))),
            ),
        )
        table = build_model_table([pair, outer])

        result = evaluate_function_model(outer, (3, 5), model_table=table)

        self.assertEqual(result, (14,))

    def test_evaluate_function_model_rejects_recursive_model_call_cycle(self) -> None:
        model = FunctionModel(
            fn_name="loop",
            param_names=("x",),
            return_names=("out",),
            assignments=(Assignment("out", Call("loop", (Var("x"),))),),
        )

        with self.assertRaisesRegex(EvaluationError, "Recursive model call cycle"):
            evaluate_function_model(
                model,
                (1,),
                model_table=build_model_table([model]),
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
    ) -> Expr:
        if depth <= 0 or rng.random() < 0.3:
            if available and rng.random() < 0.6:
                return Var(rng.choice(available))
            return IntLit(self._random_scalar(rng))

        kind = rng.random()
        if kind < 0.2 and available:
            return Var(rng.choice(available))
        if kind < 0.35:
            return IntLit(self._random_scalar(rng))
        if kind < 0.55:
            op = rng.choice(self.UNARY_OPS)
            return Call(
                op,
                (self._random_expr(rng, available, depth=depth - 1),),
            )
        if kind < 0.9:
            op = rng.choice(self.BINARY_OPS)
            return Call(
                op,
                (
                    self._random_expr(rng, available, depth=depth - 1),
                    self._random_expr(rng, available, depth=depth - 1),
                ),
            )
        op = rng.choice(self.TERNARY_OPS)
        return Call(
            op,
            (
                self._random_expr(rng, available, depth=depth - 1),
                self._random_expr(rng, available, depth=depth - 1),
                self._random_expr(rng, available, depth=depth - 1),
            ),
        )

    def _build_random_dce_model(self, seed: int) -> FunctionModel:
        rng = random.Random(seed)
        params = ("p0", "p1", "p2")
        assignments: list[ModelStatement] = []
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
                Assignment(name, self._random_expr(rng, tuple(outer_scope), depth=2))
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
                then_assignments: list[Assignment] = []
                else_assignments: list[Assignment] | None = (
                    [] if rng.random() < 0.65 else None
                )

                if rng.random() < 0.35:
                    then_assignments.append(
                        Assignment(
                            new_name("then_dead"),
                            self._random_expr(rng, tuple(outer_scope), depth=2),
                        )
                    )

                for target in modified:
                    then_assignments.append(
                        Assignment(
                            target,
                            self._random_expr(rng, tuple(outer_scope), depth=3),
                        )
                    )

                if else_assignments is not None:
                    if rng.random() < 0.35:
                        else_assignments.append(
                            Assignment(
                                new_name("else_dead"),
                                self._random_expr(rng, tuple(outer_scope), depth=2),
                            )
                        )
                    assigned_else = False
                    for target in modified:
                        if rng.random() < 0.65:
                            else_assignments.append(
                                Assignment(
                                    target,
                                    self._random_expr(rng, tuple(outer_scope), depth=3),
                                )
                            )
                            assigned_else = True
                    if not assigned_else and rng.random() < 0.5:
                        else_assignments = None

                assignments.append(
                    ConditionalBlock(
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
                Assignment(
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
                    Assignment(
                        dead_name,
                        self._random_expr(rng, tuple(outer_scope), depth=2),
                    )
                )
                outer_scope.append(dead_name)
                mutable_scope.append(dead_name)

        return_pool = tuple(outer_scope)
        return_count = min(2 if rng.random() < 0.35 else 1, len(return_pool))
        return_names = tuple(rng.sample(return_pool, k=return_count))
        model = FunctionModel(
            fn_name=f"random_dce_{seed}",
            param_names=params,
            return_names=return_names,
            assignments=tuple(assignments),
        )
        validate_function_model(model)
        return model

    def _build_random_cse_suite(
        self,
        seed: int,
    ) -> tuple[dict[str, FunctionModel], FunctionModel]:
        rng = random.Random(seed)
        c1 = self._random_scalar(rng)
        c2 = self._random_scalar(rng)
        threshold = self._random_scalar(rng)

        inner_square = FunctionModel(
            fn_name="inner_square",
            param_names=("x",),
            return_names=("ret",),
            assignments=(
                Assignment(
                    "ret",
                    Call(
                        "add",
                        (
                            Call("mul", (Var("x"), Var("x"))),
                            IntLit(c1),
                        ),
                    ),
                ),
            ),
        )
        inner_mix = FunctionModel(
            fn_name="inner_mix",
            param_names=("x", "y"),
            return_names=("ret",),
            assignments=(
                Assignment(
                    "ret",
                    Call(
                        "add",
                        (
                            Call("or", (Var("x"), Var("y"))),
                            Call("and", (Var("x"), IntLit(c2))),
                        ),
                    ),
                ),
            ),
        )

        cond_threshold = IntLit(threshold)
        global_call = Call("inner_square", (Var("p"),))
        global_pair_call = Call("inner_mix", (Var("p"), Var("q")))
        local_call = Call("inner_mix", (Var("base"), Var("q")))
        outer = FunctionModel(
            fn_name=f"outer_{seed}",
            param_names=("p", "q"),
            return_names=("out",),
            assignments=(
                Assignment("base", self._random_expr(rng, ("p", "q"), depth=2)),
                Assignment(
                    "acc",
                    Call(
                        "add",
                        (
                            global_call,
                            global_call,
                        ),
                    ),
                ),
                ConditionalBlock(
                    condition=Call("gt", (Var("p"), cond_threshold)),
                    output_vars=("tmp", "acc"),
                    then_branch=branch(
                        (
                            Assignment(
                                "tmp",
                                Call("sub", (local_call, local_call)),
                            ),
                            Assignment(
                                "acc",
                                Call("add", (Var("acc"), global_pair_call)),
                            ),
                        ),
                        ("tmp", "acc"),
                    ),
                    else_branch=branch(
                        (
                            Assignment(
                                "tmp",
                                Call("add", (global_call, global_pair_call)),
                            ),
                        ),
                        ("tmp", "acc"),
                    ),
                ),
                Assignment(
                    "out",
                    Call("add", (Var("acc"), Var("tmp"))),
                ),
            ),
        )

        helpers = build_model_table([inner_square, inner_mix])
        validate_function_model(outer)
        return helpers, outer

    def test_prune_dead_assignments_is_semantics_preserving(self) -> None:
        before = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("out",),
            assignments=(
                Assignment("dead", Call("add", (Var("x"), IntLit(9)))),
                Assignment("live", Call("mul", (Var("x"), IntLit(3)))),
                Assignment("out", Call("sub", (Var("live"), IntLit(1)))),
            ),
        )

        after = _prune_dead_assignments(before)

        self.assertModelsEquivalent(before, after, seed=19)

    def test_prune_dead_assignments_preserves_if_passthrough_inputs(self) -> None:
        before = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("out",),
            assignments=(
                Assignment("tmp", IntLit(0)),
                ConditionalBlock(
                    condition=Call("gt", (Var("x"), IntLit(10))),
                    output_vars=("tmp",),
                    then_branch=branch(
                        (Assignment("tmp", Call("add", (Var("x"), IntLit(1)))),),
                        ("tmp",),
                    ),
                    else_branch=branch((), ("tmp",)),
                ),
                Assignment("out", Call("add", (Var("tmp"), IntLit(1)))),
            ),
        )

        after = _prune_dead_assignments(before)

        validate_function_model(after)
        self.assertModelsEquivalent(before, after, seed=21)

    def test_hoist_repeated_model_calls_is_semantics_preserving(self) -> None:
        inner = FunctionModel(
            fn_name="inner",
            param_names=("p",),
            return_names=("ret",),
            assignments=(
                Assignment(
                    "ret",
                    Call(
                        "add",
                        (Call("mul", (Var("p"), Var("p"))), IntLit(1)),
                    ),
                ),
            ),
        )
        outer = FunctionModel(
            fn_name="outer",
            param_names=("p",),
            return_names=("out",),
            assignments=(
                Assignment("a", Call("inner", (Var("p"),))),
                Assignment("b", Call("inner", (Var("p"),))),
                Assignment("out", Call("sub", (Var("b"), Var("a")))),
            ),
        )

        transformed = hoist_repeated_model_calls(
            outer,
            model_call_names=frozenset({"inner"}),
        )

        self.assertModelsEquivalent(
            outer,
            transformed,
            before_table=build_model_table([inner, outer]),
            after_table=build_model_table([inner, transformed]),
            seed=23,
        )

    def test_randomized_dead_assignment_pruning_family(self) -> None:
        for seed in range(16):
            before = self._build_random_dce_model(seed)
            after = _prune_dead_assignments(before)

            validate_function_model(after)
            self.assertModelsEquivalent(
                before,
                after,
                seed=1000 + seed,
                random_cases=96,
            )

    def test_randomized_hoist_repeated_model_calls_family(self) -> None:
        for seed in range(16):
            helper_table, before = self._build_random_cse_suite(seed)
            transformed = hoist_repeated_model_calls(
                before,
                model_call_names=frozenset(helper_table),
            )

            validate_function_model(transformed)
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

        raw_result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        optimized_result = translate_yul_to_models(
            yul,
            config,
            optimize=True,
        )

        raw_table = build_model_table(raw_result)
        optimized_table = build_model_table(optimized_result)
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

            raw_result = translate_yul_to_models(
                yul,
                config,
                optimize=False,
            )
            optimized_result = translate_yul_to_models(
                yul,
                config,
                optimize=True,
            )

            raw_table = build_model_table(raw_result)
            optimized_table = build_model_table(optimized_result)
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
# Step 1 tests: normalized constant folding used by the staged pipeline
# ---------------------------------------------------------------------------


class TryConstEvalTest(unittest.TestCase):
    def test_fold_expr_folds_all_builtin_ops(self) -> None:
        self.assertEqual(
            fold_expr(
                norm_ir.NBuiltinCall("mul", (norm_ir.NConst(3), norm_ir.NConst(7)))
            ),
            norm_ir.NConst(21),
        )
        self.assertEqual(
            fold_expr(
                norm_ir.NBuiltinCall("div", (norm_ir.NConst(20), norm_ir.NConst(3)))
            ),
            norm_ir.NConst(6),
        )
        self.assertEqual(
            fold_expr(
                norm_ir.NBuiltinCall("mod", (norm_ir.NConst(10), norm_ir.NConst(3)))
            ),
            norm_ir.NConst(1),
        )
        self.assertEqual(
            fold_expr(norm_ir.NBuiltinCall("not", (norm_ir.NConst(0),))),
            norm_ir.NConst(WORD_MOD - 1),
        )
        self.assertEqual(
            fold_expr(
                norm_ir.NBuiltinCall("shl", (norm_ir.NConst(8), norm_ir.NConst(1)))
            ),
            norm_ir.NConst(256),
        )
        self.assertEqual(
            fold_expr(
                norm_ir.NBuiltinCall("shr", (norm_ir.NConst(4), norm_ir.NConst(256)))
            ),
            norm_ir.NConst(16),
        )
        self.assertEqual(
            fold_expr(
                norm_ir.NBuiltinCall("eq", (norm_ir.NConst(5), norm_ir.NConst(5)))
            ),
            norm_ir.NConst(1),
        )
        self.assertEqual(
            fold_expr(
                norm_ir.NBuiltinCall("lt", (norm_ir.NConst(3), norm_ir.NConst(7)))
            ),
            norm_ir.NConst(1),
        )
        self.assertEqual(
            fold_expr(
                norm_ir.NBuiltinCall("gt", (norm_ir.NConst(7), norm_ir.NConst(3)))
            ),
            norm_ir.NConst(1),
        )
        self.assertEqual(
            fold_expr(
                norm_ir.NBuiltinCall(
                    "and", (norm_ir.NConst(0xFF), norm_ir.NConst(0x0F))
                )
            ),
            norm_ir.NConst(0x0F),
        )
        self.assertEqual(
            fold_expr(
                norm_ir.NBuiltinCall("or", (norm_ir.NConst(0xF0), norm_ir.NConst(0x0F)))
            ),
            norm_ir.NConst(0xFF),
        )
        self.assertEqual(
            fold_expr(norm_ir.NBuiltinCall("clz", (norm_ir.NConst(1),))),
            norm_ir.NConst(255),
        )
        self.assertEqual(
            fold_expr(
                norm_ir.NBuiltinCall(
                    "mulmod",
                    (norm_ir.NConst(3), norm_ir.NConst(5), norm_ir.NConst(7)),
                )
            ),
            norm_ir.NConst(1),
        )

    def test_fold_expr_keeps_nonconstant_expressions(self) -> None:
        x = _nref("x")
        y = _nref("y", sid=1)
        self.assertEqual(fold_expr(x), x)
        self.assertEqual(
            fold_expr(norm_ir.NBuiltinCall("add", (x, norm_ir.NConst(1)))),
            norm_ir.NBuiltinCall("add", (x, norm_ir.NConst(1))),
        )
        self.assertEqual(
            fold_expr(norm_ir.NBuiltinCall("mul", (norm_ir.NConst(2), y))),
            norm_ir.NBuiltinCall("mul", (norm_ir.NConst(2), y)),
        )

    def test_fold_expr_folds_constant_ite_conditions(self) -> None:
        self.assertEqual(
            fold_expr(
                norm_ir.NIte(
                    cond=norm_ir.NConst(1),
                    if_true=norm_ir.NConst(5),
                    if_false=norm_ir.NConst(3),
                )
            ),
            norm_ir.NConst(5),
        )
        self.assertEqual(
            fold_expr(
                norm_ir.NIte(
                    cond=norm_ir.NConst(0),
                    if_true=norm_ir.NConst(5),
                    if_false=norm_ir.NConst(3),
                )
            ),
            norm_ir.NConst(3),
        )

    def test_fold_expr_ignores_dead_nonconstant_ite_branch(self) -> None:
        x = _nref("x")
        y = _nref("y", sid=1)
        self.assertEqual(
            fold_expr(
                norm_ir.NIte(
                    cond=norm_ir.NConst(1),
                    if_true=norm_ir.NConst(5),
                    if_false=x,
                )
            ),
            norm_ir.NConst(5),
        )
        self.assertEqual(
            fold_expr(
                norm_ir.NIte(
                    cond=norm_ir.NConst(0),
                    if_true=x,
                    if_false=norm_ir.NConst(3),
                )
            ),
            norm_ir.NConst(3),
        )
        self.assertEqual(
            fold_expr(
                norm_ir.NIte(
                    cond=norm_ir.NConst(42),
                    if_true=norm_ir.NConst(10),
                    if_false=y,
                )
            ),
            norm_ir.NConst(10),
        )

    def test_op_to_lean_helper_keys_match_op_to_opcode(self) -> None:
        lean_helpers: dict[str, str] = OP_TO_LEAN_HELPER
        opcodes: dict[str, str] = OP_TO_OPCODE
        lean_helper_keys: list[str] = sorted(lean_helpers)
        opcode_keys: list[str] = sorted(opcodes)
        self.assertEqual(lean_helper_keys, opcode_keys)

    def test_op_to_lean_helper_keys_match_base_norm_helpers(self) -> None:
        lean_helper_keys: list[str] = sorted(OP_TO_LEAN_HELPER)
        norm_helper_keys: list[str] = sorted(BASE_NORM_HELPERS)
        self.assertEqual(lean_helper_keys, norm_helper_keys)


# ---------------------------------------------------------------------------
# NIte simplification tests
# ---------------------------------------------------------------------------


def _expr_contains_ite(expr: Expr) -> bool:
    """Return True if *expr* contains any ``Ite`` node."""
    if isinstance(expr, Ite):
        return True
    if isinstance(expr, Project):
        return _expr_contains_ite(expr.inner)
    if isinstance(expr, Call):
        return any(_expr_contains_ite(arg) for arg in expr.args)
    return False


def _model_stmts_contain_ite(stmts: tuple[ModelStatement, ...]) -> bool:
    for stmt in stmts:
        if isinstance(stmt, Assignment):
            if _expr_contains_ite(stmt.expr):
                return True
        elif isinstance(stmt, ConditionalBlock):
            if _expr_contains_ite(stmt.condition):
                return True
            if _model_stmts_contain_ite(stmt.then_branch.assignments):
                return True
            if _model_stmts_contain_ite(stmt.else_branch.assignments):
                return True
    return False


def _model_contains_ite(model: FunctionModel) -> bool:
    """Return True if any expression in *model* contains an ``Ite`` node."""
    return _model_stmts_contain_ite(model.assignments)


class SimplifyIteTest(unittest.TestCase):
    """Tests for staged NIte simplification and its effect on translation."""

    # -- Unit tests for fold_expr(NIte(...)) --

    def test_constant_true_returns_if_val(self) -> None:
        result = fold_expr(
            norm_ir.NIte(norm_ir.NConst(1), _nref("a"), _nref("b", sid=1))
        )
        self.assertEqual(result, _nref("a"))

    def test_constant_nonzero_returns_if_val(self) -> None:
        result = fold_expr(
            norm_ir.NIte(norm_ir.NConst(42), _nref("a"), _nref("b", sid=1))
        )
        self.assertEqual(result, _nref("a"))

    def test_constant_false_returns_else_val(self) -> None:
        result = fold_expr(
            norm_ir.NIte(norm_ir.NConst(0), _nref("a"), _nref("b", sid=1))
        )
        self.assertEqual(result, _nref("b", sid=1))

    def test_equal_branches_returns_value(self) -> None:
        result = fold_expr(
            norm_ir.NIte(_nref("c"), norm_ir.NConst(5), norm_ir.NConst(5))
        )
        self.assertEqual(result, norm_ir.NConst(5))

    def test_equal_branches_with_variable_condition(self) -> None:
        expr = norm_ir.NBuiltinCall("add", (_nref("x"), norm_ir.NConst(1)))
        result = fold_expr(norm_ir.NIte(_nref("c", sid=1), expr, expr))
        self.assertEqual(result, expr)

    def test_variable_condition_emits_ite(self) -> None:
        result = fold_expr(
            norm_ir.NIte(_nref("c"), _nref("a", sid=1), _nref("b", sid=2))
        )
        self.assertEqual(
            result,
            norm_ir.NIte(_nref("c"), _nref("a", sid=1), _nref("b", sid=2)),
        )

    def test_computed_constant_condition_folds(self) -> None:
        cond = norm_ir.NBuiltinCall("eq", (norm_ir.NConst(5), norm_ir.NConst(5)))
        result = fold_expr(norm_ir.NIte(cond, _nref("a"), _nref("b", sid=1)))
        self.assertEqual(result, _nref("a"))

    def test_computed_zero_condition_folds(self) -> None:
        cond = norm_ir.NBuiltinCall("eq", (norm_ir.NConst(3), norm_ir.NConst(5)))
        result = fold_expr(norm_ir.NIte(cond, _nref("a"), _nref("b", sid=1)))
        self.assertEqual(result, _nref("b", sid=1))

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
        result = translate_yul_to_models(
            self.CONST_IF_HELPER_YUL,
            self.CONST_IF_HELPER_CONFIG,
            optimize=False,
        )
        model = result[0]
        self.assertFalse(
            _model_contains_ite(model),
            "Expected no Ite nodes when if-condition is constant 1",
        )
        # Semantics: always takes the if-body (add x 10)
        self.assertEqual(evaluate_function_model(model, (5,)), (15,))
        self.assertEqual(evaluate_function_model(model, (0,)), (10,))

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
        result = translate_yul_to_models(
            self.CONST_FALSE_IF_HELPER_YUL,
            self.CONST_IF_HELPER_CONFIG,
            optimize=False,
        )
        model = result[0]
        self.assertFalse(
            _model_contains_ite(model),
            "Expected no Ite nodes when if-condition is constant 0",
        )
        # Semantics: never takes the if-body, z = x
        self.assertEqual(evaluate_function_model(model, (5,)), (5,))
        self.assertEqual(evaluate_function_model(model, (0,)), (0,))

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
        result = translate_yul_to_models(
            self.CONST_LEAVE_HELPER_YUL,
            self.CONST_LEAVE_HELPER_CONFIG,
            optimize=False,
        )
        model = result[0]
        self.assertFalse(
            _model_contains_ite(model),
            "Expected no Ite nodes when leave condition is constant 1",
        )
        # Always takes the leave path: z = 7
        self.assertEqual(evaluate_function_model(model, (0,)), (7,))
        self.assertEqual(evaluate_function_model(model, (1,)), (7,))

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
        result = translate_yul_to_models(
            self.CONST_FALSE_LEAVE_HELPER_YUL,
            self.CONST_LEAVE_HELPER_CONFIG,
            optimize=False,
        )
        model = result[0]
        self.assertFalse(
            _model_contains_ite(model),
            "Expected no Ite nodes when leave condition is constant 0",
        )
        # Never takes the leave path: z = 9
        self.assertEqual(evaluate_function_model(model, (0,)), (9,))
        self.assertEqual(evaluate_function_model(model, (1,)), (9,))

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
        result = translate_yul_to_models(
            self.CONST_SWITCH_HELPER_YUL,
            self.CONST_SWITCH_HELPER_CONFIG,
            optimize=False,
        )
        model = result[0]
        self.assertFalse(
            _model_contains_ite(model),
            "Expected no Ite nodes when switch condition is constant 1",
        )
        # switch 1 → default branch: z = x + 20
        self.assertEqual(evaluate_function_model(model, (5,)), (25,))
        self.assertEqual(evaluate_function_model(model, (0,)), (20,))

    # -- Variable condition still produces Ite --

    def test_variable_condition_preserves_branching(self) -> None:
        """Sanity check: non-constant conditions still produce branches."""
        result = translate_yul_to_models(
            TranslationFlowTest.LEAVE_HELPER_YUL,
            TranslationFlowTest.LEAVE_HELPER_CONFIG,
            optimize=False,
        )
        model = result[0]
        # New pipeline uses ConditionalBlock for branches.
        has_branch = any(isinstance(s, ConditionalBlock) for s in model.assignments)
        self.assertTrue(
            has_branch or _model_contains_ite(model),
            "Expected ConditionalBlock or Ite nodes when condition depends on input",
        )
        # Semantics still correct
        self.assertEqual(evaluate_function_model(model, (0,)), (9,))
        self.assertEqual(evaluate_function_model(model, (1,)), (7,))


# ---------------------------------------------------------------------------
# Step 2 tests: standalone _eval_builtin EVM correctness
# ---------------------------------------------------------------------------


class EvalBuiltinCorrectnessTest(unittest.TestCase):
    def test_add_wraps(self) -> None:
        self.assertEqual(eval_pure_builtin("add", (WORD_MOD - 1, 1)), 0)

    def test_sub_wraps(self) -> None:
        self.assertEqual(eval_pure_builtin("sub", (0, 1)), WORD_MOD - 1)

    def test_mul_wraps(self) -> None:
        self.assertEqual(eval_pure_builtin("mul", (WORD_MOD - 1, WORD_MOD - 1)), 1)

    def test_div_by_zero(self) -> None:
        self.assertEqual(eval_pure_builtin("div", (7, 0)), 0)

    def test_mod_by_zero(self) -> None:
        self.assertEqual(eval_pure_builtin("mod", (7, 0)), 0)

    def test_not_complement(self) -> None:
        self.assertEqual(eval_pure_builtin("not", (0,)), WORD_MOD - 1)

    def test_shl_boundary(self) -> None:
        self.assertEqual(eval_pure_builtin("shl", (255, 1)), 1 << 255)
        self.assertEqual(eval_pure_builtin("shl", (256, 1)), 0)

    def test_shr_boundary(self) -> None:
        self.assertEqual(eval_pure_builtin("shr", (255, 1 << 255)), 1)
        self.assertEqual(eval_pure_builtin("shr", (256, 1 << 255)), 0)

    def test_clz_edges(self) -> None:
        self.assertEqual(eval_pure_builtin("clz", (0,)), 256)
        self.assertEqual(eval_pure_builtin("clz", (1,)), 255)
        self.assertEqual(eval_pure_builtin("clz", (1 << 255,)), 0)

    def test_lt_gt_boolean(self) -> None:
        self.assertIn(eval_pure_builtin("lt", (3, 7)), (0, 1))
        self.assertEqual(eval_pure_builtin("lt", (3, 7)), 1)
        self.assertEqual(eval_pure_builtin("lt", (7, 3)), 0)
        self.assertEqual(eval_pure_builtin("gt", (7, 3)), 1)
        self.assertEqual(eval_pure_builtin("gt", (3, 7)), 0)

    def test_mulmod_by_zero(self) -> None:
        self.assertEqual(eval_pure_builtin("mulmod", (3, 5, 0)), 0)
        # (WORD_MOD-1)^2 mod (WORD_MOD-1) = 0
        self.assertEqual(
            eval_pure_builtin("mulmod", (WORD_MOD - 1, WORD_MOD - 1, WORD_MOD - 1)),
            0,
        )
        # Standard case: 3*5 mod 7 = 1
        self.assertEqual(eval_pure_builtin("mulmod", (3, 5, 7)), 1)

    def test_unsupported_op_raises(self) -> None:
        with self.assertRaises(EvaluationError):
            eval_pure_builtin("fake_op", (1, 2))

    def test_wrong_arity_raises(self) -> None:
        with self.assertRaises(EvaluationError):
            eval_pure_builtin("add", (1,))


# ---------------------------------------------------------------------------
# Step 3 tests: validate_function_model structural invariants
# ---------------------------------------------------------------------------


class ValidateFunctionModelTest(unittest.TestCase):
    def test_validate_rejects_duplicate_param_names(self) -> None:
        model = FunctionModel(
            fn_name="bad",
            param_names=("x", "x"),
            return_names=("z",),
            assignments=(Assignment("z", Var("x")),),
        )
        with self.assertRaisesRegex(ParseError, "duplicate param"):
            validate_function_model(model)

    def test_validate_rejects_duplicate_return_names(self) -> None:
        model = FunctionModel(
            fn_name="bad",
            param_names=("x",),
            return_names=("z", "z"),
            assignments=(Assignment("z", Var("x")),),
        )
        with self.assertRaisesRegex(ParseError, "duplicate return"):
            validate_function_model(model)

    def test_validate_allows_param_return_overlap_in_restricted_ir(self) -> None:
        model = FunctionModel(
            fn_name="identity",
            param_names=("x",),
            return_names=("x",),
            assignments=(),
        )
        validate_function_model(model)
        self.assertEqual(evaluate_function_model(model, (7,)), (7,))

    def test_validate_rejects_duplicate_conditional_output_vars(self) -> None:
        model = FunctionModel(
            fn_name="bad",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ConditionalBlock(
                    condition=Var("x"),
                    output_vars=("a", "a"),
                    then_branch=ConditionalBranch(
                        assignments=(Assignment("a", IntLit(1)),),
                        outputs=(Var("a"), Var("a")),
                    ),
                    else_branch=ConditionalBranch(
                        assignments=(Assignment("a", IntLit(2)),),
                        outputs=(Var("a"), Var("a")),
                    ),
                ),
                Assignment("z", Var("a")),
            ),
        )
        with self.assertRaisesRegex(ParseError, "duplicate conditional output_vars"):
            validate_function_model(model)

    def test_validate_rejects_invalid_ident_in_param(self) -> None:
        model = FunctionModel(
            fn_name="bad",
            param_names=("123bad",),
            return_names=("z",),
            assignments=(Assignment("z", IntLit(0)),),
        )
        with self.assertRaisesRegex(ParseError, "Invalid.*param"):
            validate_function_model(model)

    def test_validate_rejects_negative_project_index(self) -> None:
        model = FunctionModel(
            fn_name="bad",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                Assignment(
                    "z",
                    Project(-1, 2, Call("pair", (Var("x"),))),
                ),
            ),
        )

        with self.assertRaises(ParseError):
            validate_function_model(model)

    def test_validate_rejects_projection_of_builtin_call(self) -> None:
        model = FunctionModel(
            fn_name="bad",
            param_names=(),
            return_names=("z",),
            assignments=(
                Assignment(
                    "z",
                    Project(
                        0,
                        1,
                        Call("add", (IntLit(1), IntLit(2))),
                    ),
                ),
            ),
        )

        with self.assertRaises(ParseError):
            validate_function_model(model)

    def test_validate_rejects_negative_nat_literal(self) -> None:
        model = FunctionModel(
            fn_name="bad",
            param_names=(),
            return_names=("z",),
            assignments=(Assignment("z", IntLit(-1)),),
        )

        with self.assertRaises(ParseError):
            validate_function_model(model)

    def test_validate_selected_models_rejects_projection_of_single_return_model(
        self,
    ) -> None:
        inner = FunctionModel(
            fn_name="inner",
            param_names=("x",),
            return_names=("ret",),
            assignments=(Assignment("ret", Var("x")),),
        )
        outer = FunctionModel(
            fn_name="outer",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                Assignment(
                    "z",
                    Project(0, 1, Call("inner", (Var("x"),))),
                ),
            ),
        )

        with self.assertRaises(ParseError):
            validate_model_set([inner, outer])


# ---------------------------------------------------------------------------
# Step 6a tests: collect_ops_from_statement
# ---------------------------------------------------------------------------


class CollectOpsTest(unittest.TestCase):
    def test_collects_ops_from_else_branch(self) -> None:
        stmt = ConditionalBlock(
            condition=IntLit(1),
            output_vars=("out",),
            then_branch=branch(
                (Assignment("out", IntLit(0)),),
                ("out",),
            ),
            else_branch=branch(
                (Assignment("out", Call("mul", (IntLit(3), IntLit(7)))),),
                ("out",),
            ),
        )
        ops = collect_ops_from_statement(stmt)
        self.assertIn("mul", ops)

    def test_collects_ops_from_condition(self) -> None:
        stmt = ConditionalBlock(
            condition=Call("gt", (IntLit(5), IntLit(3))),
            output_vars=("out",),
            then_branch=branch(
                (Assignment("out", IntLit(1)),),
                ("out",),
            ),
            else_branch=branch(
                (Assignment("out", IntLit(0)),),
                ("out",),
            ),
        )
        ops = collect_ops_from_statement(stmt)
        self.assertIn("gt", ops)


# ---------------------------------------------------------------------------
# Step 6b tests: emit_expr
# ---------------------------------------------------------------------------


class EmitExprTest(unittest.TestCase):
    OP_MAP = OP_TO_LEAN_HELPER
    CALL_MAP: dict[str, str] = {}

    def _emit(self, expr: Expr) -> str:
        return emit_expr(expr, helper_map={**self.OP_MAP, **self.CALL_MAP})

    def test_emit_intlit(self) -> None:
        self.assertEqual(self._emit(IntLit(42)), "42")

    def test_emit_var(self) -> None:
        self.assertEqual(self._emit(Var("x")), "x")

    def test_emit_builtin_call(self) -> None:
        result = self._emit(Call("add", (Var("x"), IntLit(1))))
        self.assertEqual(result, "evmAdd (x) (1)")

    def test_emit_ite(self) -> None:
        result = self._emit(Ite(Var("c"), IntLit(1), IntLit(0)))
        self.assertIn("if", result)
        self.assertIn("then", result)
        self.assertIn("else", result)

    def test_emit_component_projection(self) -> None:
        inner = Call("add", (Var("x"), IntLit(1)))
        result = self._emit(Project(0, 2, inner))
        self.assertIn(".1", result)

    def test_emit_unknown_call_raises(self) -> None:
        with self.assertRaises(ParseError):
            self._emit(Call("totally_unknown_func", (IntLit(1),)))


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
    ) -> Expr:
        if depth <= 0 or rng.random() < 0.3:
            if available and rng.random() < 0.6:
                return Var(rng.choice(available))
            return IntLit(self._random_scalar(rng))

        kind = rng.random()
        if kind < 0.15 and available:
            return Var(rng.choice(available))
        if kind < 0.30:
            return IntLit(self._random_scalar(rng))
        # Ite generation (5% probability at depth > 0)
        if kind < 0.35:
            cond = self._random_expr(rng, available, depth=depth - 1)
            a = self._random_expr(rng, available, depth=depth - 1)
            b = self._random_expr(rng, available, depth=depth - 1)
            return Ite(cond, a, b)
        if kind < 0.50:
            op = rng.choice(self.UNARY_OPS)
            return Call(op, (self._random_expr(rng, available, depth=depth - 1),))
        if kind < 0.90:
            op = rng.choice(self.BINARY_OPS)
            return Call(
                op,
                (
                    self._random_expr(rng, available, depth=depth - 1),
                    self._random_expr(rng, available, depth=depth - 1),
                ),
            )
        op = rng.choice(self.TERNARY_OPS)
        return Call(
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
            assignments: list[ModelStatement] = []
            scope = list(params)
            for i in range(6):
                name = f"v_{seed}_{i}"
                assignments.append(
                    Assignment(name, self._random_expr(rng, tuple(scope), depth=3))
                )
                scope.append(name)

            before = FunctionModel(
                fn_name=f"ite_dce_{seed}",
                param_names=params,
                return_names=(scope[-1],),
                assignments=tuple(assignments),
            )
            validate_function_model(before)
            after = _prune_dead_assignments(before)
            self.assertModelsEquivalent(
                before, after, seed=7000 + seed, random_cases=64
            )

    def test_randomized_multi_return_projection_equivalence(self) -> None:
        """Build a 2-return helper + outer using Project projections, verify DCE."""
        for seed in range(8):
            rng = random.Random(seed + 8000)

            helper = FunctionModel(
                fn_name="helper",
                param_names=("a", "b"),
                return_names=("r0", "r1"),
                assignments=(
                    Assignment(
                        "r0",
                        self._random_expr(rng, ("a", "b"), depth=2),
                    ),
                    Assignment(
                        "r1",
                        self._random_expr(rng, ("a", "b"), depth=2),
                    ),
                ),
            )

            outer = FunctionModel(
                fn_name="outer",
                param_names=("x", "y"),
                return_names=("out",),
                assignments=(
                    Assignment(
                        "lhs",
                        Project(
                            0,
                            2,
                            Call("helper", (Var("x"), Var("y"))),
                        ),
                    ),
                    Assignment(
                        "rhs",
                        Project(
                            1,
                            2,
                            Call("helper", (Var("x"), Var("y"))),
                        ),
                    ),
                    Assignment(
                        "dead",
                        self._random_expr(rng, ("x", "y"), depth=2),
                    ),
                    Assignment(
                        "out",
                        Call("add", (Var("lhs"), Var("rhs"))),
                    ),
                ),
            )

            table = build_model_table([helper, outer])
            validate_function_model(outer)
            after = _prune_dead_assignments(outer)
            validate_function_model(after)

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
        tokens = tokenize_yul("""
            function fun_dup_1(var_x_1) -> var_z_2 {
                var_z_2 := add(var_x_1, 1)
            }

            function fun_dup_2(var_x_3) -> var_z_4 {
                var_z_4 := sub(var_x_3, 1)
            }
            """)

        with self.assertRaisesRegex(ParseError, "Multiple Yul functions match 'dup'"):
            _find_function(tokens, "dup")

    def test_find_function_uses_param_count_to_disambiguate(self) -> None:
        tokens = tokenize_yul("""
            function fun_dup_1(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }

            function fun_dup_2(var_x_3, var_y_4) -> var_z_5 {
                var_z_5 := add(var_x_3, var_y_4)
            }
            """)

        found = _find_function(tokens, "dup", n_params=2)

        self.assertEqual(found.yul_name, "fun_dup_2")

    def test_find_function_prefers_candidate_referencing_known_yul_name(self) -> None:
        tokens = tokenize_yul("""
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

        found = _find_function(
            tokens,
            "pick",
            known_yul_names={"helper"},
        )

        self.assertEqual(found.yul_name, "fun_pick_1")

    def test_find_function_avoids_selected_helper_reachability(self) -> None:
        tokens = tokenize_yul("""
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

        found = _find_function(
            tokens,
            "pick",
            known_yul_names={"helper"},
            avoid_known=True,
        )

        self.assertEqual(found.yul_name, "fun_pick_2")

    def test_find_exact_function_returns_named_definition(self) -> None:
        tokens = tokenize_yul(self.EXACT_SELECTION_YUL)

        found = _find_exact_function(tokens, "fun_pick_2")

        self.assertEqual(found.yul_name, "fun_pick_2")

    def test_find_exact_function_rejects_missing_name(self) -> None:
        tokens = tokenize_yul(self.EXACT_SELECTION_YUL)

        with self.assertRaisesRegex(
            ParseError, "Exact Yul function 'fun_missing_9' not found"
        ):
            _find_exact_function(tokens, "fun_missing_9")

    def test_prepare_translation_uses_exact_yul_name_selection(self) -> None:
        config = make_model_config(
            ("pick",),
            exact_yul_names={"pick": "fun_pick_2"},
        )

        result = translate_yul_to_models(
            self.EXACT_SELECTION_YUL,
            config,
            optimize=False,
        )

        model = result[0]
        self.assertEqual(model.fn_name, "pick")
        # fun_pick_2: sub(x, 1) → pick(7) = 6
        self.assertEqual(evaluate_function_model(model, (7,)), (6,))


class ResolvedTranslatorBehaviorTest(unittest.TestCase):
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
            ParseError,
            "expression-statement",
        ):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(
            evaluate_function_model(result[0], ()),
            (1,),
        )

    def test_translate_yul_to_models_threads_block_local_branch_updates(
        self,
    ) -> None:
        config = make_model_config(("f",))
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(
            evaluate_function_model(result[0], (0,)),
            (0,),
        )
        self.assertEqual(
            evaluate_function_model(result[0], (1,)),
            (2,),
        )

    def test_find_function_rejects_nested_definition_name_collision(self) -> None:
        # The nested ``helper`` collides with the top-level helper name.
        # Selection should fail during resolver validation instead of trying
        # to disambiguate malformed Yul.
        tokens = tokenize_yul("""
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

        with self.assertRaisesRegex(
            ParseError,
            "Duplicate declaration of 'helper' in the same scope",
        ):
            _find_function(
                tokens,
                "pick",
                known_yul_names={"helper"},
            )

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        models = {model.fn_name: model for model in result}

        self.assertEqual(evaluate_function_model(models["f"], ()), (11,))
        self.assertEqual(evaluate_function_model(models["g"], ()), (22,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(
            evaluate_function_model(result[0], ()),
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(
            evaluate_function_model(result[0], ()),
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(
            evaluate_function_model(result[0], ()),
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        model = result[0]
        self.assertTrue(model.assignments)
        self.assertIsInstance(model.assignments[0], ConditionalBlock)
        assign_stmts: tuple[Assignment, ...] = tuple(
            stmt for stmt in model.assignments if isinstance(stmt, Assignment)
        )
        self.assertNotIn(
            Assignment("z", IntLit(0)),
            assign_stmts,
        )
        self.assertEqual(evaluate_function_model(model, (0,)), (8,))
        self.assertEqual(evaluate_function_model(model, (1,)), (8,))

    def test_translate_yul_to_models_scopes_helpers_for_selected_later_duplicate_symbol(
        self,
    ) -> None:
        config = make_model_config(
            ("inner", "outer"),
            require_reaching_selected={"outer": frozenset({"inner"})},
        )
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        models = {model.fn_name: model for model in result}
        table = build_model_table(result)

        self.assertEqual(
            evaluate_function_model(models["inner"], (), model_table=table),
            (7,),
        )
        self.assertEqual(
            evaluate_function_model(models["outer"], (), model_table=table),
            (22,),
        )


class TranslatorBehaviorTest(unittest.TestCase):
    # These are known-bad translator behaviors found during review.
    # They should fail loudly until the implementation is fixed.

    def test_find_function_ignores_transitive_calls_to_shadowing_local_helper(
        self,
    ) -> None:
        tokens = tokenize_yul("""
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
            ParseError,
            "Duplicate declaration of 'helper' in the same scope",
        ):
            _find_function(
                tokens,
                "pick",
                known_yul_names={"helper"},
            )

        with self.assertRaisesRegex(
            ParseError,
            "Duplicate declaration of 'helper' in the same scope",
        ):
            _find_function(
                tokens,
                "pick",
                known_yul_names={"helper"},
                avoid_known=True,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (0,)), (2,))
        self.assertEqual(evaluate_function_model(model, (1,)), (2,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (0,)), (1,))
        self.assertEqual(evaluate_function_model(model, (5,)), (6,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (7, 0)), (0,))
        self.assertEqual(evaluate_function_model(model, (7, 1)), (7,))
        self.assertEqual(evaluate_function_model(model, (9, 2)), (9,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (0, 5)), (0,))
        self.assertEqual(evaluate_function_model(model, (1, 5)), (5,))
        self.assertEqual(evaluate_function_model(model, (2, 9)), (9,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (0, 0)), (0,))
        self.assertEqual(evaluate_function_model(model, (7, 0)), (7,))
        self.assertEqual(evaluate_function_model(model, (7, 1)), (0,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (0, 0)), (1,))
        self.assertEqual(evaluate_function_model(model, (0, 1)), (0,))
        self.assertEqual(evaluate_function_model(model, (2, 1)), (0,))
        self.assertEqual(evaluate_function_model(model, (3, 1)), (1,))

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

        with self.assertRaisesRegex(ParseError, "Undefined variable"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, ()), (2,))

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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (3,)), (5,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, ()), (2,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, ()), (7,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (3,)), (5,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (0,)), (0,))
        self.assertEqual(evaluate_function_model(model, (5,)), (5,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (0,)), (1,))
        self.assertEqual(evaluate_function_model(model, (1,)), (2,))

    def test_translate_yul_to_models_rejects_unresolved_call_target(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1() -> var_z_2 {
                var_z_2 := helper()
            }
            """

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
            )

    def test_build_selection_plan_exact_nested_target_collects_only_reachable_helpers(
        self,
    ) -> None:
        config = make_model_config(
            ("pick",),
            exact_yul_names={"pick": "fun_outer_0::target"},
        )
        yul = """
            function fun_outer_0() -> z {
                function helper() -> h {
                    h := 7
                }
                function target() -> t {
                    t := helper()
                }
                z := target()
            }
            """
        plan = build_selection_plan(
            yul,
            config,
            selected_functions=("pick",),
        )
        helper_names = {
            helper.raw_name for helper in plan.target_infos["pick"].helper_infos
        }
        expected_helper_names: set[str] = {"helper"}
        self.assertEqual(helper_names, expected_helper_names)

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (0,)), (7,))
        self.assertEqual(evaluate_function_model(model, (1,)), (7,))

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
            ParseError,
            "Undefined variable",
        ):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, ()), (7,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (0,)), (1,))
        self.assertEqual(evaluate_function_model(model, (1,)), (7,))

    def test_translate_yul_to_models_allows_branch_local_constant_mload_address_for_kept_solidity_local(
        self,
    ) -> None:
        config = make_model_config(("f",))
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (0,)), (1,))
        self.assertEqual(evaluate_function_model(model, (1,)), (7,))

    def test_translate_yul_to_models_accepts_conditionally_constant_memory_address_for_kept_solidity_local(
        self,
    ) -> None:
        config = make_model_config(("f",))
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (0,)), (7,))
        self.assertEqual(evaluate_function_model(model, (1,)), (7,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(
            evaluate_function_model(result[0], (0,)),
            (1,),
        )
        self.assertEqual(
            evaluate_function_model(result[0], (5,)),
            (6,),
        )

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

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(
            evaluate_function_model(
                result[0],
                (),
                model_table=build_model_table(result),
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
            )

    def test_build_lean_source_rejects_binder_collision_with_generated_model_name(
        self,
    ) -> None:
        config = make_model_config(("inner", "outer"))
        inner = FunctionModel(
            fn_name="inner",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                Assignment(
                    "z",
                    Call("add", (Var("x"), IntLit(1))),
                ),
            ),
        )
        outer = FunctionModel(
            fn_name="outer",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                Assignment("model_inner", Var("x")),
                Assignment(
                    "z",
                    Call("inner", (Var("model_inner"),)),
                ),
            ),
        )

        with self.assertRaises(ParseError):
            build_lean_source(
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        targets: set[str] = {
            stmt.target for stmt in model.assignments if isinstance(stmt, Assignment)
        }
        self.assertIn("model_f", targets)

        with self.assertRaisesRegex(ParseError, "collides with a generated model def"):
            build_lean_source(
                models=result,
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_find_function_rejects_nonmatching_param_count_even_when_unique(
        self,
    ) -> None:
        tokens = tokenize_yul("""
            function fun_dup_1(var_x_1, var_y_2) -> var_z_3 {
                var_z_3 := add(var_x_1, var_y_2)
            }
            """)

        with self.assertRaises(ParseError):
            _find_function(tokens, "dup", n_params=1)

    def test_find_function_rejects_when_requested_arity_matches_no_candidate(
        self,
    ) -> None:
        tokens = tokenize_yul("""
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

        with self.assertRaises(ParseError):
            _find_function(
                tokens,
                "pick",
                n_params=1,
                known_yul_names={"helper"},
            )

    def test_find_function_ignores_constant_false_helper_references(
        self,
    ) -> None:
        tokens = tokenize_yul("""
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

        with self.assertRaisesRegex(ParseError, "Multiple Yul functions match 'pick'"):
            _find_function(
                tokens,
                "pick",
                known_yul_names={"helper"},
            )

        with self.assertRaisesRegex(
            ParseError,
            "avoids selected helper reachability",
        ):
            _find_function(
                tokens,
                "pick",
                known_yul_names={"helper"},
                avoid_known=True,
            )

    def test_find_function_ignores_constant_switch_helper_references(
        self,
    ) -> None:
        tokens = tokenize_yul("""
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

        with self.assertRaisesRegex(ParseError, "Multiple Yul functions match 'pick'"):
            _find_function(
                tokens,
                "pick",
                known_yul_names={"helper"},
            )

        with self.assertRaisesRegex(
            ParseError,
            "avoids selected helper reachability",
        ):
            _find_function(
                tokens,
                "pick",
                known_yul_names={"helper"},
                avoid_known=True,
            )

    def test_find_function_respects_shadowing_between_nested_block_locals(
        self,
    ) -> None:
        tokens = tokenize_yul("""
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
            ParseError,
            "Duplicate declaration of 'nested' in the same scope",
        ):
            _find_function(
                tokens,
                "pick",
                known_yul_names={"helper"},
            )

        with self.assertRaisesRegex(
            ParseError,
            "Duplicate declaration of 'nested' in the same scope",
        ):
            _find_function(
                tokens,
                "pick",
                known_yul_names={"helper"},
                avoid_known=True,
            )

    def test_find_function_tracks_nested_helper_called_within_same_block(
        self,
    ) -> None:
        tokens = tokenize_yul("""
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

        func = _find_function(
            tokens,
            "pick",
            known_yul_names={"helper"},
        )
        self.assertEqual(func.yul_name, "fun_pick_1")

        leaf = _find_function(
            tokens,
            "pick",
            known_yul_names={"helper"},
            avoid_known=True,
        )
        self.assertEqual(leaf.yul_name, "fun_pick_2")

    def test_find_function_tracks_transitive_sibling_local_helper_dependencies(
        self,
    ) -> None:
        tokens = tokenize_yul("""
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

        func = _find_function(
            tokens,
            "pick",
            known_yul_names={"helper"},
        )
        self.assertEqual(func.yul_name, "fun_pick_1")

        leaf = _find_function(
            tokens,
            "pick",
            known_yul_names={"helper"},
            avoid_known=True,
        )
        self.assertEqual(leaf.yul_name, "fun_pick_2")

    def test_find_function_ignores_dead_deeper_nested_helper_dependencies(
        self,
    ) -> None:
        tokens = tokenize_yul("""
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

        func = _find_function(
            tokens,
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

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
            )

    def test_find_function_ignores_nested_local_function_references(self) -> None:
        tokens = tokenize_yul("""
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
            ParseError,
            "reaches selected helper dependencies",
        ):
            _find_function(
                tokens,
                "pick",
                known_yul_names={"helper"},
            )

    def test_find_function_ignores_nested_public_name_candidates(self) -> None:
        tokens = tokenize_yul("""
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

        found = _find_function(
            tokens,
            "pick",
            known_yul_names={"helper"},
        )

        self.assertEqual(found.yul_name, "fun_pick_3")

    def test_find_exact_function_rejects_nested_local_name_collision(self) -> None:
        tokens = tokenize_yul("""
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

        with self.assertRaisesRegex(
            ParseError,
            "Duplicate declaration of 'fun_pick_1' in the same scope",
        ):
            _find_exact_function(tokens, "fun_pick_1")

    def test_validate_function_model_rejects_reserved_lean_helper_binder_names(
        self,
    ) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("u256",),
            return_names=("z",),
            assignments=(
                Assignment(
                    "z",
                    Call("add", (Var("u256"), IntLit(1))),
                ),
            ),
        )

        validate_function_model(model)

        config = make_model_config(("f",))
        with self.assertRaises(ParseError):
            build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_translate_yul_to_models_rejects_lean_keyword_parameter_name(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_if_1) -> var_z_2 {
                var_z_2 := var_if_1
            }
            """

        models = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        with self.assertRaises(ParseError):
            build_lean_source(
                models=models,
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_validate_function_model_rejects_malformed_builtin_arity(self) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                Assignment(
                    "z",
                    Call("add", (Var("x"),)),
                ),
            ),
        )

        with self.assertRaises(ParseError):
            validate_function_model(model)

    def test_validate_function_model_rejects_malformed_component_projection_shape(
        self,
    ) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                Assignment(
                    "z",
                    Project(0, 2, Var("x")),
                ),
            ),
        )

        with self.assertRaises(ParseError):
            validate_function_model(model)

    def test_validate_function_model_rejects_out_of_range_component_projection_index(
        self,
    ) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("x", "y"),
            return_names=("z",),
            assignments=(
                Assignment(
                    "z",
                    Project(
                        2,
                        2,
                        Call("pair", (Var("x"), Var("y"))),
                    ),
                ),
            ),
        )

        with self.assertRaises(ParseError):
            validate_function_model(model)

    def test_validate_function_model_rejects_project_with_non_call_inner(self) -> None:
        """Project inner must be a Call — Var is rejected."""
        model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                Assignment(
                    "z",
                    Project(0, 2, Var("x")),
                ),
            ),
        )

        with self.assertRaises(ParseError):
            validate_function_model(model)

    def test_build_lean_source_rejects_extra_norm_helper_binder_collisions(
        self,
    ) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("normBitLengthPlus1",),
            return_names=("z",),
            assignments=(Assignment("z", Var("normBitLengthPlus1")),),
        )
        config = modelcfg.ModelConfig(
            function_order=("f",),
            model_names={"f": "model_f"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={"bitLengthPlus1": "normBitLengthPlus1"},
            extra_lean_defs=("def normBitLengthPlus1 (x : Nat) : Nat := x + 1"),
            norm_rewrite=lambda expr: Call("bitLengthPlus1", (expr,)),
            inner_fn="f",
            n_params=None,
            exact_yul_names=None,
            hoist_repeated_calls=frozenset(),
            skip_prune=frozenset(),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )

        with self.assertRaises(ParseError):
            build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_rejects_generated_model_name_collision_with_extra_norm_helper(
        self,
    ) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(Assignment("z", Var("x")),),
        )
        config = modelcfg.ModelConfig(
            function_order=("f",),
            model_names={"f": "normBitLengthPlus1"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={"bitLengthPlus1": "normBitLengthPlus1"},
            extra_lean_defs=("def normBitLengthPlus1 (x : Nat) : Nat := x + 1"),
            norm_rewrite=lambda expr: Call("bitLengthPlus1", (expr,)),
            inner_fn="f",
            n_params=None,
            exact_yul_names=None,
            hoist_repeated_calls=frozenset(),
            skip_prune=frozenset(),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )

        with self.assertRaises(ParseError):
            build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_rejects_cross_collision_between_generated_evm_and_norm_names(
        self,
    ) -> None:
        first = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(Assignment("z", Var("x")),),
        )
        second = FunctionModel(
            fn_name="g",
            param_names=("y",),
            return_names=("r",),
            assignments=(Assignment("r", Var("y")),),
        )
        config = modelcfg.ModelConfig(
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
            hoist_repeated_calls=frozenset(),
            skip_prune=frozenset(),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )

        with self.assertRaises(ParseError):
            build_lean_source(
                models=[first, second],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_allows_extra_norm_helper_name_when_norm_is_skipped(
        self,
    ) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("normBitLengthPlus1",),
            return_names=("z",),
            assignments=(Assignment("z", Var("normBitLengthPlus1")),),
        )
        config = modelcfg.ModelConfig(
            function_order=("f",),
            model_names={"f": "model_f"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={"bitLengthPlus1": "normBitLengthPlus1"},
            extra_lean_defs=("def normBitLengthPlus1 (x : Nat) : Nat := x + 1"),
            norm_rewrite=lambda expr: Call("bitLengthPlus1", (expr,)),
            inner_fn="f",
            n_params=None,
            exact_yul_names=None,
            skip_norm=frozenset({"f"}),
            hoist_repeated_calls=frozenset(),
            skip_prune=frozenset(),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )

        source = build_lean_source(
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
        model = FunctionModel(
            fn_name="f",
            param_names=("p",),
            return_names=("z",),
            assignments=(
                ConditionalBlock(
                    condition=Var("p"),
                    output_vars=("tmp",),
                    then_branch=ConditionalBranch(
                        assignments=(
                            Assignment(
                                "normBitLengthPlus1",
                                IntLit(1),
                            ),
                            Assignment("tmp", Var("p")),
                        ),
                        outputs=(Var("tmp"),),
                    ),
                    else_branch=ConditionalBranch(
                        assignments=(
                            Assignment(
                                "normBitLengthPlus1",
                                IntLit(2),
                            ),
                            Assignment("tmp", Var("p")),
                        ),
                        outputs=(Var("tmp"),),
                    ),
                ),
                Assignment("z", Var("tmp")),
            ),
        )
        config = modelcfg.ModelConfig(
            function_order=("f",),
            model_names={"f": "model_f"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={"bitLengthPlus1": "normBitLengthPlus1"},
            extra_lean_defs=("def normBitLengthPlus1 (x : Nat) : Nat := x + 1"),
            norm_rewrite=lambda expr: Call("bitLengthPlus1", (expr,)),
            inner_fn="f",
            n_params=None,
            exact_yul_names=None,
            hoist_repeated_calls=frozenset(),
            skip_prune=frozenset(),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )

        with self.assertRaises(ParseError):
            build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_rejects_extra_norm_helper_collisions_in_conditional_output_vars(
        self,
    ) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("p",),
            return_names=("z",),
            assignments=(
                ConditionalBlock(
                    condition=Var("p"),
                    output_vars=("normBitLengthPlus1",),
                    then_branch=ConditionalBranch(
                        assignments=(),
                        outputs=(Var("p"),),
                    ),
                    else_branch=ConditionalBranch(
                        assignments=(),
                        outputs=(Var("p"),),
                    ),
                ),
                Assignment("z", Var("normBitLengthPlus1")),
            ),
        )
        config = modelcfg.ModelConfig(
            function_order=("f",),
            model_names={"f": "model_f"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={"bitLengthPlus1": "normBitLengthPlus1"},
            extra_lean_defs=("def normBitLengthPlus1 (x : Nat) : Nat := x + 1"),
            norm_rewrite=lambda expr: Call("bitLengthPlus1", (expr,)),
            inner_fn="f",
            n_params=None,
            exact_yul_names=None,
            hoist_repeated_calls=frozenset(),
            skip_prune=frozenset(),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )

        with self.assertRaises(ParseError):
            build_lean_source(
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

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
            )

    def test_find_function_ignores_dead_helper_reference_after_top_level_leave(
        self,
    ) -> None:
        tokens = tokenize_yul("""
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

        found = _find_function(
            tokens,
            "pick",
            known_yul_names={"helper"},
        )
        self.assertEqual(found.yul_name, "fun_pick_1")

        leaf = _find_function(
            tokens,
            "pick",
            known_yul_names={"helper"},
            avoid_known=True,
        )
        self.assertEqual(leaf.yul_name, "fun_pick_2")

    def test_find_function_ignores_dead_helper_reference_after_constant_true_if_leave(
        self,
    ) -> None:
        tokens = tokenize_yul("""
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

        found = _find_function(
            tokens,
            "pick",
            known_yul_names={"helper"},
        )
        self.assertEqual(found.yul_name, "fun_pick_1")

        leaf = _find_function(
            tokens,
            "pick",
            known_yul_names={"helper"},
            avoid_known=True,
        )
        self.assertEqual(leaf.yul_name, "fun_pick_2")

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (2, 3)), (5,))
        self.assertEqual(evaluate_function_model(model, (7, 11)), (18,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (2, 3)), (9,))
        self.assertEqual(evaluate_function_model(model, (7, 11)), (9,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(evaluate_function_model(result[0], ()), (9,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (0,)), (1,))
        self.assertEqual(evaluate_function_model(model, (9,)), (10,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(evaluate_function_model(result[0], ()), (1,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(evaluate_function_model(result[0], ()), (1,))

    def test_build_lean_source_separates_extra_lean_defs_from_following_norm_helpers(
        self,
    ) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(Assignment("z", Var("x")),),
        )
        config = modelcfg.ModelConfig(
            function_order=("f",),
            model_names={"f": "model_f"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={"bitLengthPlus1": "normBitLengthPlus1"},
            extra_lean_defs=("def normBitLengthPlus1 (x : Nat) : Nat := x + 1"),
            norm_rewrite=lambda expr: Call("bitLengthPlus1", (expr,)),
            inner_fn="f",
            n_params=None,
            exact_yul_names=None,
            hoist_repeated_calls=frozenset(),
            skip_prune=frozenset(),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )

        source = build_lean_source(
            models=[model],
            source_path="test-source",
            namespace="Test",
            config=config,
        )

        self.assertLess(
            source.index("def normMulmod"),
            source.index("def normBitLengthPlus1"),
        )
        self.assertLess(
            source.index("def normBitLengthPlus1"),
            source.index("def model_f_evm"),
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

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(evaluate_function_model(result[0], ()), (0,))

    def test_translate_yul_to_models_rejects_duplicate_selected_functions(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = """
            function fun_f_1(var_x_1) -> var_z_2 {
                var_z_2 := add(var_x_1, 1)
            }
            """

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                selected_functions=("f", "f"),
                optimize=False,
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

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (2, 3)), (9,))
        self.assertEqual(evaluate_function_model(model, (7, 11)), (9,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(
            evaluate_function_model(
                result[0],
                (),
                model_table=build_model_table(result),
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
            )

    def test_build_lean_source_rejects_binder_collision_with_generated_evm_model_name(
        self,
    ) -> None:
        config = make_model_config(("inner", "outer"))
        inner = FunctionModel(
            fn_name="inner",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                Assignment(
                    "z",
                    Call("add", (Var("x"), IntLit(1))),
                ),
            ),
        )
        outer = FunctionModel(
            fn_name="outer",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                Assignment("model_inner_evm", Var("x")),
                Assignment(
                    "z",
                    Call("inner", (Var("model_inner_evm"),)),
                ),
            ),
        )

        with self.assertRaises(ParseError):
            build_lean_source(
                models=[inner, outer],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_allows_binder_named_like_skipped_norm_model(
        self,
    ) -> None:
        base = make_model_config(("f",))
        config = modelcfg.ModelConfig(
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
            avoid_reaching_selected=base.selection.avoid_reaching_selected,
            skip_norm=frozenset({"f"}),
            hoist_repeated_calls=base.hoist_repeated_calls,
            skip_prune=base.skip_prune,
            default_source_label=base.default_source_label,
            default_namespace=base.default_namespace,
            default_output=base.default_output,
            cli_description=base.cli_description,
        )
        model = FunctionModel(
            fn_name="f",
            param_names=("model_f",),
            return_names=("z",),
            assignments=(Assignment("z", Var("model_f")),),
        )

        source = build_lean_source(
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
        config = modelcfg.ModelConfig(
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
        model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(Assignment("z", Var("x")),),
        )

        source = build_lean_source(
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
        config = modelcfg.ModelConfig(
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
        model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(Assignment("z", Var("x")),),
        )

        source = build_lean_source(
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
        config = modelcfg.ModelConfig(
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
            FunctionModel(
                fn_name="f",
                param_names=("x",),
                return_names=("z",),
                assignments=(Assignment("z", Var("x")),),
            ),
            FunctionModel(
                fn_name="g",
                param_names=("y",),
                return_names=("w",),
                assignments=(Assignment("w", Var("y")),),
            ),
        ]

        source = build_lean_source(
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

    def test_build_lean_source_rejects_norm_call_to_skipped_norm_callee(self) -> None:
        config = modelcfg.ModelConfig(
            function_order=("f", "g"),
            model_names={"f": "model_f", "g": "model_g"},
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
            FunctionModel(
                fn_name="f",
                param_names=("x",),
                return_names=("z",),
                assignments=(Assignment("z", Var("x")),),
            ),
            FunctionModel(
                fn_name="g",
                param_names=("y",),
                return_names=("w",),
                assignments=(Assignment("w", Call("f", (Var("y"),))),),
            ),
        ]

        with self.assertRaisesRegex(
            ParseError,
            "norm model.*f.*not emitted|skipped norm",
        ):
            build_lean_source(
                models=models,
                source_path="test-source",
                namespace="Test",
                config=config,
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(
            evaluate_function_model(result[0], ()),
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(
            evaluate_function_model(result[0], ()),
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

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model_table = build_model_table(result)

        self.assertEqual(
            evaluate_function_model(
                model_table["f"],
                (),
                model_table=model_table,
            ),
            (0,),
        )
        self.assertEqual(
            evaluate_function_model(
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(evaluate_function_model(result[0], ()), (0,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(
            evaluate_function_model(result[0], ()),
            (9,),
        )

    def test_build_lean_source_rejects_generated_model_name_collision_in_conditional_output_vars(
        self,
    ) -> None:
        config = make_model_config(("inner", "outer"))
        inner = FunctionModel(
            fn_name="inner",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                Assignment(
                    "z",
                    Call("add", (Var("x"), IntLit(1))),
                ),
            ),
        )
        outer = FunctionModel(
            fn_name="outer",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ConditionalBlock(
                    condition=Var("x"),
                    output_vars=("model_inner",),
                    then_branch=ConditionalBranch(
                        assignments=(),
                        outputs=(Var("x"),),
                    ),
                    else_branch=ConditionalBranch(
                        assignments=(),
                        outputs=(Var("x"),),
                    ),
                ),
                Assignment(
                    "z",
                    Call("inner", (Var("model_inner"),)),
                ),
            ),
        )

        with self.assertRaises(ParseError):
            build_lean_source(
                models=[inner, outer],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_rejects_generated_evm_model_name_collision_in_conditional_branch_targets(
        self,
    ) -> None:
        config = make_model_config(("inner", "outer"))
        inner = FunctionModel(
            fn_name="inner",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                Assignment(
                    "z",
                    Call("add", (Var("x"), IntLit(1))),
                ),
            ),
        )
        outer = FunctionModel(
            fn_name="outer",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ConditionalBlock(
                    condition=Var("x"),
                    output_vars=("tmp",),
                    then_branch=ConditionalBranch(
                        assignments=(
                            Assignment("model_inner_evm", Var("x")),
                            Assignment(
                                "tmp",
                                Call(
                                    "inner",
                                    (Var("model_inner_evm"),),
                                ),
                            ),
                        ),
                        outputs=(Var("tmp"),),
                    ),
                    else_branch=ConditionalBranch(
                        assignments=(
                            Assignment("model_inner_evm", IntLit(0)),
                            Assignment(
                                "tmp",
                                Call(
                                    "inner",
                                    (Var("model_inner_evm"),),
                                ),
                            ),
                        ),
                        outputs=(Var("tmp"),),
                    ),
                ),
                Assignment("z", Var("tmp")),
            ),
        )

        with self.assertRaises(ParseError):
            build_lean_source(
                models=[inner, outer],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_rejects_invalid_namespace_name(self) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(Assignment("z", Var("x")),),
        )
        config = make_model_config(("f",))

        with self.assertRaises(ParseError):
            build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="invalid-name",
                config=config,
            )

    def test_build_lean_source_rejects_lean_keyword_namespace(self) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(Assignment("z", Var("x")),),
        )
        config = make_model_config(("f",))

        with self.assertRaises(ParseError):
            build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="if",
                config=config,
            )

    def test_build_lean_source_rejects_source_path_newline_injection(self) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(Assignment("z", Var("x")),),
        )
        config = make_model_config(("f",))

        with self.assertRaises(ParseError):
            build_lean_source(
                models=[model],
                source_path="test-source\nopen scoped BigOperators",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_rejects_generator_label_newline_injection(
        self,
    ) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(Assignment("z", Var("x")),),
        )
        config = modelcfg.ModelConfig(
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
            hoist_repeated_calls=frozenset(),
            skip_prune=frozenset(),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )

        with self.assertRaises(ParseError):
            build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_rejects_header_comment_terminator_injection(
        self,
    ) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(Assignment("z", Var("x")),),
        )
        config = modelcfg.ModelConfig(
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
            hoist_repeated_calls=frozenset(),
            skip_prune=frozenset(),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )

        with self.assertRaises(ParseError):
            build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_rejects_raw_function_name_injection(self) -> None:
        injected_name = "f_bad` -/\naxiom injected : False\n/--"
        model = FunctionModel(
            fn_name=injected_name,
            param_names=("x",),
            return_names=("z",),
            assignments=(Assignment("z", Var("x")),),
        )
        config = modelcfg.ModelConfig(
            function_order=(injected_name,),
            model_names={injected_name: "model_f"},
            header_comment="test",
            generator_label="formal/test_yul_to_lean.py",
            extra_norm_ops={},
            extra_lean_defs="",
            norm_rewrite=None,
            inner_fn=injected_name,
            n_params=None,
            exact_yul_names=None,
            hoist_repeated_calls=frozenset(),
            skip_prune=frozenset(),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )

        with self.assertRaises(ParseError):
            build_lean_source(
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

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
            )

    def test_build_lean_source_rejects_invalid_generated_model_name(self) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(Assignment("z", Var("x")),),
        )
        config = modelcfg.ModelConfig(
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
            hoist_repeated_calls=frozenset(),
            skip_prune=frozenset(),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )

        with self.assertRaises(ParseError):
            build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_rejects_lean_keyword_generated_model_name(
        self,
    ) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(Assignment("z", Var("x")),),
        )
        config = modelcfg.ModelConfig(
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
            hoist_repeated_calls=frozenset(),
            skip_prune=frozenset(),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )

        with self.assertRaises(ParseError):
            build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_rejects_generated_model_name_collision_with_builtin_helper(
        self,
    ) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(Assignment("z", Var("x")),),
        )
        config = modelcfg.ModelConfig(
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
            hoist_repeated_calls=frozenset(),
            skip_prune=frozenset(),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )

        with self.assertRaises(ParseError):
            build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_rejects_missing_model_name_mapping(self) -> None:
        model = FunctionModel(
            fn_name="g",
            param_names=("x",),
            return_names=("z",),
            assignments=(Assignment("z", Var("x")),),
        )
        config = make_model_config(("f",))

        with self.assertRaises(ParseError):
            build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_build_lean_source_rejects_duplicate_generated_model_names(self) -> None:
        first = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(Assignment("z", Var("x")),),
        )
        second = FunctionModel(
            fn_name="g",
            param_names=("y",),
            return_names=("r",),
            assignments=(Assignment("r", Var("y")),),
        )
        config = modelcfg.ModelConfig(
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
            hoist_repeated_calls=frozenset(),
            skip_prune=frozenset(),
            default_source_label="test",
            default_namespace="Test",
            default_output="",
            cli_description="test",
        )

        with self.assertRaises(ParseError):
            build_lean_source(
                models=[first, second],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (0,)), (0,))
        self.assertEqual(evaluate_function_model(model, (7,)), (7,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, ()), (9,))

    def test_translate_yul_to_models_wraps_large_integer_literals_to_u256(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = f"""
            function fun_f_1() -> var_z_2 {{
                var_z_2 := {WORD_MOD + 1}
            }}
            """

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(evaluate_function_model(result[0], ()), (1,))

    def test_translate_yul_to_models_wraps_large_memory_addresses_to_u256(
        self,
    ) -> None:
        config = make_model_config(("f",))
        yul = f"""
            function fun_f_1() -> var_z_2 {{
                mstore({WORD_MOD}, 7)
                var_z_2 := mload(0)
            }}
            """

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(evaluate_function_model(result[0], ()), (7,))

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
                    case {WORD_MOD} {{
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
                    case {WORD_MOD} {{
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
                result = translate_yul_to_models(
                    yul,
                    config,
                    optimize=False,
                )
                model = result[0]
                for args, expected in expectations:
                    self.assertEqual(evaluate_function_model(model, args), expected)

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(evaluate_function_model(result[0], ()), (0,))
        build_lean_source(
            models=result,
            source_path="test-source",
            namespace="Test",
            config=config,
        )


class OptimizerBehaviorTest(ModelEquivalenceTestCase):
    # These are known-bad optimizer behaviors found during review.
    # They should fail loudly until the implementation is fixed.

    def test_hoist_repeated_model_calls_avoids_conditional_output_name_collisions(
        self,
    ) -> None:
        inner = FunctionModel(
            fn_name="inner",
            param_names=("x",),
            return_names=("ret",),
            assignments=(
                Assignment(
                    "ret",
                    Call("add", (Var("x"), IntLit(1))),
                ),
            ),
        )
        before = FunctionModel(
            fn_name="f",
            param_names=("p",),
            return_names=("out",),
            assignments=(
                ConditionalBlock(
                    condition=Var("p"),
                    output_vars=("_cse_1",),
                    then_branch=ConditionalBranch(
                        assignments=(),
                        outputs=(Var("p"),),
                    ),
                    else_branch=ConditionalBranch(
                        assignments=(),
                        outputs=(Var("p"),),
                    ),
                ),
                Assignment("a", Call("inner", (Var("p"),))),
                Assignment(
                    "b",
                    Call(
                        "add",
                        (
                            Var("_cse_1"),
                            Call("inner", (Var("p"),)),
                        ),
                    ),
                ),
                Assignment("out", Var("b")),
            ),
        )

        after = hoist_repeated_model_calls(
            before,
            model_call_names=frozenset({"inner"}),
        )

        self.assertModelsEquivalent(
            before,
            after,
            before_table=build_model_table([inner, before]),
            after_table=build_model_table([inner, after]),
        )

    def test_hoist_repeated_model_calls_avoids_parameter_name_collisions(
        self,
    ) -> None:
        inner = FunctionModel(
            fn_name="inner",
            param_names=("x",),
            return_names=("ret",),
            assignments=(
                Assignment(
                    "ret",
                    Call("add", (Var("x"), IntLit(1))),
                ),
            ),
        )
        before = FunctionModel(
            fn_name="f",
            param_names=("_cse_1", "p"),
            return_names=("out",),
            assignments=(
                Assignment("a", Call("inner", (Var("p"),))),
                Assignment(
                    "b",
                    Call(
                        "add",
                        (
                            Var("_cse_1"),
                            Call("inner", (Var("p"),)),
                        ),
                    ),
                ),
                Assignment("out", Var("b")),
            ),
        )

        after = hoist_repeated_model_calls(
            before,
            model_call_names=frozenset({"inner"}),
        )

        self.assertModelsEquivalent(
            before,
            after,
            before_table=build_model_table([inner, before]),
            after_table=build_model_table([inner, after]),
        )

    def test_hoist_repeated_model_calls_preserves_multi_return_component_projections(
        self,
    ) -> None:
        pair = FunctionModel(
            fn_name="pair",
            param_names=("x",),
            return_names=("lhs", "rhs"),
            assignments=(
                Assignment("lhs", Var("x")),
                Assignment(
                    "rhs",
                    Call("add", (Var("x"), IntLit(1))),
                ),
            ),
        )
        before = FunctionModel(
            fn_name="f",
            param_names=("p",),
            return_names=("out",),
            assignments=(
                Assignment(
                    "out",
                    Call(
                        "add",
                        (
                            Project(
                                0,
                                2,
                                Call("pair", (Var("p"),)),
                            ),
                            Project(
                                0,
                                2,
                                Call("pair", (Var("p"),)),
                            ),
                        ),
                    ),
                ),
            ),
        )

        after = hoist_repeated_model_calls(
            before,
            model_call_names=frozenset({"pair"}),
        )

        self.assertModelsEquivalent(
            before,
            after,
            before_table=build_model_table([pair, before]),
            after_table=build_model_table([pair, after]),
        )

    def test_hoist_repeated_model_calls_avoids_generated_name_collisions(
        self,
    ) -> None:
        inner = FunctionModel(
            fn_name="inner",
            param_names=("x",),
            return_names=("ret",),
            assignments=(
                Assignment(
                    "ret",
                    Call("add", (Var("x"), IntLit(1))),
                ),
            ),
        )
        before = FunctionModel(
            fn_name="f",
            param_names=("p",),
            return_names=("out",),
            assignments=(
                Assignment("_cse_1", IntLit(99)),
                Assignment("a", Call("inner", (Var("p"),))),
                Assignment(
                    "b",
                    Call(
                        "add",
                        (
                            Var("_cse_1"),
                            Call("inner", (Var("p"),)),
                        ),
                    ),
                ),
                Assignment("out", Var("b")),
            ),
        )

        after = hoist_repeated_model_calls(
            before,
            model_call_names=frozenset({"inner"}),
        )

        self.assertModelsEquivalent(
            before,
            after,
            before_table=build_model_table([inner, before]),
            after_table=build_model_table([inner, after]),
        )


class LeanSourceDeterminismTest(unittest.TestCase):
    CONFIG = make_model_config(("f",))

    def test_build_lean_source_is_deterministic(self) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(Assignment("z", Call("add", (Var("x"), IntLit(1)))),),
        )

        src1 = build_lean_source(
            models=[model],
            source_path="test-source",
            namespace="Test",
            config=self.CONFIG,
        )
        src2 = build_lean_source(
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

import model_config as modelcfg
from model_ir import ConditionalBlock
from yul_to_lean import translate_yul_to_models

config = modelcfg.ModelConfig(
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
result = translate_yul_to_models(
    yul,
    config,
    optimize=False,
)
stmt = next(
    assignment
    for assignment in result[0].assignments
    if isinstance(assignment, ConditionalBlock)
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
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]
        self.assertEqual(evaluate_function_model(model, (9,)), (3,))

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
        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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
        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]
        self.assertEqual(evaluate_function_model(model, (15,)), (3,))

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
        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]
        self.assertEqual(evaluate_function_model(model, (9,)), (3,))

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
        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]
        self.assertEqual(evaluate_function_model(model, (12,)), (4,))

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
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]
        # Leave branch: r = 0
        self.assertEqual(evaluate_function_model(model, (42,)), (0,))

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
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]
        self.assertEqual(evaluate_function_model(model, (5,)), (6,))

    def test_direct_target_live_branch_expr_stmt_rejected(self) -> None:
        """Branch expr_stmt in target function is rejected when branch is live."""
        yul = """
            function fun_target_1(var_x_1) -> var_z_2 {
                if iszero(0) { side_effect() }
                var_z_2 := add(var_x_1, 1)
            }
        """
        config = make_model_config(("target",))
        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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
        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]
        self.assertEqual(evaluate_function_model(model, (12,)), (4,))

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
            ParseError,
            "expression-statement",
        ):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]
        self.assertEqual(evaluate_function_model(model, (21,)), (3,))

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
        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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
        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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
        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]
        self.assertEqual(evaluate_function_model(model, ()), (7,))

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
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]
        self.assertEqual(evaluate_function_model(model, (9,)), (3,))

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
        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]
        self.assertEqual(evaluate_function_model(model, (9,)), (3,))

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
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]
        # (3 + 6) / 3 == 3
        self.assertEqual(evaluate_function_model(model, (6,)), (3,))
        # (3 + 0) / 3 == 1
        self.assertEqual(evaluate_function_model(model, (0,)), (1,))

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
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]
        self.assertEqual(evaluate_function_model(model, (9,)), (3,))

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
        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
            )


class ReviewBehaviorTest(unittest.TestCase):
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(evaluate_function_model(result[0], ()), (7,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )

        self.assertEqual(evaluate_function_model(result[0], ()), (1,))

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
                with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
                    translate_yul_to_models(
                        yul,
                        config,
                        optimize=False,
                    )

    def test_evaluate_function_model_wraps_raw_large_integer_literals_to_u256(
        self,
    ) -> None:
        model = FunctionModel(
            fn_name="f",
            assignments=(Assignment("z", IntLit(WORD_MOD + 1)),),
            param_names=(),
            return_names=("z",),
        )

        self.assertEqual(evaluate_function_model(model, ()), (1,))

    def test_build_model_body_wraps_raw_large_integer_literals_to_u256(
        self,
    ) -> None:
        model = FunctionModel(
            fn_name="f",
            assignments=(Assignment("z", IntLit(WORD_MOD + 1)),),
            param_names=(),
            return_names=("z",),
        )

        body = build_model_body(
            model.assignments,
            evm=True,
            config=make_model_config(("f",)),
            param_names=model.param_names,
            return_names=model.return_names,
        )

        self.assertEqual(body.splitlines()[0], "  let z := 1")


class ScopeLeakRejectionTest(unittest.TestCase):
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
                    ParseError,
                    "Undefined variable",
                ):
                    translate_yul_to_models(
                        yul,
                        config,
                        optimize=False,
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
                result = translate_yul_to_models(
                    yul,
                    config,
                    optimize=False,
                )
                self.assertEqual(
                    evaluate_function_model(
                        result[0],
                        (),
                        model_table=build_model_table(result),
                    ),
                    (1,),
                )

    def test_parse_exact_yul_selector_rejects_empty_path_segments(self) -> None:
        yul = """
            function outer() -> var_z_1 {
                var_z_1 := 7
            }
        """
        for selector in ("outer::", "::top::", "a::::b"):
            with self.subTest(selector=selector):
                config = make_model_config(("f",), exact_yul_names={"f": selector})
                with self.assertRaisesRegex(
                    ParseError,
                    "Invalid exact Yul selector",
                ):
                    build_selection_plan(yul, config.selection)


class ConditionalScopeRejectionTest(unittest.TestCase):
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
                    ParseError,
                    "Undefined variable",
                ):
                    translate_yul_to_models(
                        yul,
                        config,
                        optimize=False,
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
                    ParseError,
                    "Unresolved call to 'helper'",
                ):
                    translate_yul_to_models(
                        yul,
                        config,
                        optimize=False,
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(
            evaluate_function_model(
                model,
                (0,),
                model_table=build_model_table(result),
            ),
            (2,),
        )
        self.assertEqual(
            evaluate_function_model(
                model,
                (1,),
                model_table=build_model_table(result),
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
                with self.assertRaises(ParseError):
                    translate_yul_to_models(
                        yul,
                        config,
                        optimize=False,
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(
            evaluate_function_model(
                model,
                (5, 7),
                model_table=build_model_table(result),
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
                result = translate_yul_to_models(
                    yul,
                    config,
                    optimize=False,
                )
                model = result[0]

                self.assertEqual(
                    evaluate_function_model(
                        model,
                        (5, 7),
                        model_table=build_model_table(result),
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
                with self.assertRaises(ParseError):
                    translate_yul_to_models(
                        yul,
                        config,
                        optimize=False,
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
                with self.assertRaises(ParseError):
                    translate_yul_to_models(
                        yul,
                        config,
                        optimize=False,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(
            evaluate_function_model(
                model,
                (5, 7),
                model_table=build_model_table(result),
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(
            evaluate_function_model(
                model,
                (5, 7),
                model_table=build_model_table(result),
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(
            evaluate_function_model(
                model,
                (5, 7),
                model_table=build_model_table(result),
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
                result = translate_yul_to_models(
                    yul,
                    config,
                    optimize=False,
                )
                model = result[0]

                self.assertEqual(
                    evaluate_function_model(
                        model,
                        (5, 7),
                        model_table=build_model_table(result),
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

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaises(ParseError):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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
                with self.assertRaises(ParseError):
                    translate_yul_to_models(
                        yul_by_case[case],
                        config,
                        optimize=False,
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
                with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
                    translate_yul_to_models(
                        yul,
                        config,
                        optimize=False,
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
                with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
                    translate_yul_to_models(
                        yul,
                        config,
                        optimize=False,
                    )


class DeadCodeHelperFilterTest(unittest.TestCase):
    def test_find_function_ignores_dead_helper_reference_after_infinite_for_loop(
        self,
    ) -> None:
        tokens = tokenize_yul("""
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

        found = _find_function(
            tokens,
            "pick",
            known_yul_names={"helper"},
        )

        self.assertEqual(found.yul_name, "fun_pick_1")

    def test_find_function_ignores_dead_helper_reference_after_for_post_leave(
        self,
    ) -> None:
        tokens = tokenize_yul("""
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

        found = _find_function(
            tokens,
            "pick",
            known_yul_names={"helper"},
        )

        self.assertEqual(found.yul_name, "fun_pick_1")

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(
            evaluate_function_model(
                model,
                (5, 7),
                model_table=build_model_table(result),
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        models = build_model_table(result)

        self.assertEqual(
            evaluate_function_model(models["a"], (), model_table=models),
            (7,),
        )
        self.assertEqual(
            evaluate_function_model(models["b"], (), model_table=models),
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        models = build_model_table(result)

        self.assertEqual(
            evaluate_function_model(models["a"], (), model_table=models),
            (7,),
        )
        self.assertEqual(
            evaluate_function_model(models["b"], (), model_table=models),
            (7,),
        )
        self.assertEqual(
            evaluate_function_model(models["c"], (), model_table=models),
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        models = build_model_table(result)

        self.assertEqual(
            evaluate_function_model(models["a"], (), model_table=models),
            (7,),
        )
        self.assertEqual(
            evaluate_function_model(models["b"], (), model_table=models),
            (7,),
        )
        self.assertTrue(
            any(
                isinstance(stmt, Assignment) and stmt.expr == Call("b", ())
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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
            ParseError,
            "Unresolved call to 'helper'",
        ):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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
        helper_token_idx = _find_exact_function_path(
            tokenize_yul(base_yul),
            ("outer", "helper"),
        ).token_idx
        self.assertIsNotNone(helper_token_idx)
        yul = base_yul.replace(
            "collision_name",
            f"__protected_{helper_token_idx}",
        )

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        models = build_model_table(result)

        self.assertEqual(
            evaluate_function_model(models["a"], (), model_table=models),
            (7,),
        )
        self.assertEqual(
            evaluate_function_model(models["b"], (), model_table=models),
            (7,),
        )
        self.assertTrue(
            any(
                isinstance(stmt, Assignment) and stmt.expr == Call("b", ())
                for stmt in models["a"].assignments
            )
        )


class CompilerTemporaryThreadingTest(unittest.TestCase):
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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (0,)), (0,))
        self.assertEqual(evaluate_function_model(model, (1,)), (1,))
        self.assertEqual(evaluate_function_model(model, (7,)), (1,))

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

        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]

        self.assertEqual(evaluate_function_model(model, (0,)), (1,))
        self.assertEqual(evaluate_function_model(model, (1,)), (2,))
        self.assertEqual(evaluate_function_model(model, (9,)), (2,))

    def test_build_lean_source_rejects_invalid_model_before_emitting_undefined_binders(
        self,
    ) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(Assignment("z", Var("y")),),
        )

        with self.assertRaisesRegex(ParseError, "out-of-scope variable use"):
            build_lean_source(
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
        tokens = tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        resolve_function(func)

    def test_resolve_rejects_duplicate_param_names(self) -> None:
        with self.assertRaisesRegex(ParseError, "x"):
            self._parse_and_resolve("function f(x, x) -> z { z := x }")

    def test_resolve_rejects_duplicate_return_names(self) -> None:
        with self.assertRaisesRegex(ParseError, "z"):
            self._parse_and_resolve("function f(x) -> z, z { z := x }")

    def test_resolve_rejects_duplicate_local_declaration_in_same_scope(
        self,
    ) -> None:
        with self.assertRaisesRegex(ParseError, r"usr\$tmp"):
            self._parse_and_resolve("""
                function f(x) -> z {
                    let usr$tmp := 1
                    let usr$tmp := 2
                    z := usr$tmp
                }
            """)

    def test_resolve_rejects_duplicate_multi_let_target(self) -> None:
        with self.assertRaisesRegex(ParseError, r"usr\$a"):
            self._parse_and_resolve("""
                function f(x) -> z {
                    let usr$a, usr$a := fun_pair(x)
                    z := usr$a
                }
            """)

    def test_resolve_rejects_same_scope_local_shadowing_parameter(
        self,
    ) -> None:
        with self.assertRaisesRegex(ParseError, "x"):
            self._parse_and_resolve("""
                function f(x) -> z {
                    let x := 1
                    z := x
                }
            """)

    def test_resolve_rejects_same_scope_local_shadowing_return(self) -> None:
        with self.assertRaisesRegex(ParseError, "z"):
            self._parse_and_resolve("""
                function f(x) -> z {
                    let z := 1
                }
            """)

    def test_resolve_rejects_duplicate_local_inside_bare_block(self) -> None:
        with self.assertRaisesRegex(ParseError, r"usr\$tmp"):
            self._parse_and_resolve("""
                function f(x) -> z {
                    {
                        let usr$tmp := 1
                        let usr$tmp := 2
                        z := usr$tmp
                    }
                }
            """)

    def test_resolve_accepts_string_literal_assignment_rhs(self) -> None:
        """String literals resolve without error (UTF-8 right-padded big-endian)."""
        # Should not raise — strings resolve to integer constants.
        self._parse_and_resolve("""
            function f(x) -> z {
                z := "oops"
            }
        """)

    # -- Undefined-variable resolution tests --------------------------------

    def test_resolve_rejects_undefined_rhs_variable(self) -> None:
        with self.assertRaisesRegex(ParseError, "Undefined variable 'y'"):
            self._parse_and_resolve("function f(x) -> z { z := y }")

    def test_resolve_rejects_undefined_assignment_target(self) -> None:
        with self.assertRaisesRegex(ParseError, "Undefined variable 'y'"):
            self._parse_and_resolve("function f(x) -> z { y := x  z := x }")

    def test_resolve_rejects_if_scoped_let_used_after_block(self) -> None:
        with self.assertRaisesRegex(ParseError, "Undefined variable 'y'"):
            self._parse_and_resolve("""
                function f(x) -> z {
                    if x { let y := 1 }
                    z := y
                }
            """)

    def test_resolve_rejects_bare_block_scoped_let_used_after_block(
        self,
    ) -> None:
        with self.assertRaisesRegex(ParseError, "Undefined variable 'tmp'"):
            self._parse_and_resolve("""
                function f(x) -> z {
                    { let tmp := x }
                    z := tmp
                }
            """)

    def test_resolve_rejects_switch_scoped_let_used_after_block(self) -> None:
        with self.assertRaisesRegex(ParseError, "Undefined variable 'y'"):
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
        with self.assertRaisesRegex(ParseError, "Undefined variable 'y'"):
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
        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
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
        tokens = tokenize_yul("function f(x) -> z { z := x }")
        func = SyntaxParser(tokens).parse_function()
        # 'function' is token 0
        self.assertEqual(func.span.start, 0)
        # 'f' is token 1
        self.assertEqual(func.name_span.start, 1)
        self.assertEqual(func.name_span.end, 2)

    def test_span_with_token_offset_is_globally_correct(self) -> None:
        tokens = tokenize_yul("""
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
        tokens = tokenize_yul("""
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
        stmt = cast(yul_ast.AssignStmt, stmt)
        self.assertGreater(stmt.span.start, first_end)
        self.assertGreater(stmt.span.end, stmt.span.start)

    def test_span_end_greater_than_start(self) -> None:
        tokens = tokenize_yul("function f(x, y) -> z { z := add(x, y) }")
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
        tokens = tokenize_yul(yul)
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
        target = cast(yul_ast.BuiltinTarget, target)
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
        target = cast(yul_ast.LocalFunctionTarget, target)
        self.assertEqual(target.id, g_id)
        self.assertEqual(target.name, "g")

    def test_unknown_call_classified_as_unresolved_target(self) -> None:
        result = self._resolve("function f(x) -> z { z := unknown(x) }")
        self.assertEqual(len(result.call_targets), 1)
        target = next(iter(result.call_targets.values()))
        self.assertIsInstance(target, yul_ast.UnresolvedTarget)
        target = cast(yul_ast.UnresolvedTarget, target)
        self.assertEqual(target.name, "unknown")

    def test_cross_scope_shadowing_rejected(self) -> None:
        """Yul rejects cross-scope shadowing (solc error 1395)."""
        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
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
        with self.assertRaisesRegex(ParseError, "Cannot use builtin function name"):
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
        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
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
        with self.assertRaisesRegex(ParseError, "Cannot use builtin function name"):
            self._resolve(
                "function add(a, b) -> c { c := a }",
                builtins=frozenset({"add"}),
            )

    def test_rejects_let_variable_named_as_builtin(self) -> None:
        """let add := 7 is rejected when add is a builtin (solc error 5568)."""
        with self.assertRaisesRegex(ParseError, "Cannot use builtin function name"):
            self._resolve(
                "function f(x) -> z { let add := 7 z := x }",
                builtins=frozenset({"add"}),
            )

    def test_rejects_param_named_as_builtin(self) -> None:
        """Parameter named 'add' is rejected when add is a builtin."""
        with self.assertRaisesRegex(ParseError, "Cannot use builtin function name"):
            self._resolve(
                "function f(add) -> z { z := add }",
                builtins=frozenset({"add"}),
            )

    def test_rejects_return_named_as_builtin(self) -> None:
        """Return variable named 'add' is rejected when add is a builtin."""
        with self.assertRaisesRegex(ParseError, "Cannot use builtin function name"):
            self._resolve(
                "function f(x) -> add { add := x }",
                builtins=frozenset({"add"}),
            )

    def test_rejects_function_named_mstore(self) -> None:
        """mstore is an EVM builtin — cannot be used as an identifier (solc 5568)."""
        with self.assertRaisesRegex(ParseError, "Cannot use builtin function name"):
            self._resolve(
                "function f(x) -> z { function mstore(a, b) -> c { c := a } z := x }",
                builtins=EVM_BUILTINS,
            )

    def test_rejects_let_named_mstore(self) -> None:
        """let mstore := 7 is rejected when using the full EVM builtins set."""
        with self.assertRaisesRegex(ParseError, "Cannot use builtin function name"):
            self._resolve(
                "function f(x) -> z { let mstore := 7 z := x }",
                builtins=EVM_BUILTINS,
            )


class ResolverModuleTest(unittest.TestCase):
    """Tests for module-level resolution (resolve_module) and TopLevelFunctionTarget."""

    def _resolve_module(
        self, yul: str, builtins: frozenset[str] = frozenset()
    ) -> dict[str, ResolutionResult]:
        tokens = tokenize_yul(yul)
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
        f_target_0 = cast(yul_ast.TopLevelFunctionTarget, f_targets[0])
        self.assertEqual(f_target_0.name, "g")

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
        f_target_0 = cast(yul_ast.LocalFunctionTarget, f_targets[0])
        self.assertEqual(f_target_0.name, "h")

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
        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            self._resolve_module("""
                function helper(a) -> b { b := a }
                function f(x) -> z { let helper := 7 z := x }
            """)

    def test_nested_function_shadowing_sibling_rejected(self) -> None:
        """Nested function helper inside f conflicts with sibling function helper."""
        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
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
        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            self._resolve_module("""
                function f(x) -> z { z := x }
                function f(a) -> b { b := a }
            """)

    def test_top_level_function_named_as_builtin_rejected(self) -> None:
        with self.assertRaisesRegex(ParseError, "Cannot use builtin function name"):
            self._resolve_module(
                "function add(a, b) -> c { c := a }",
                builtins=frozenset({"add"}),
            )

    def test_per_function_resolve_still_classifies_sibling_as_unresolved(self) -> None:
        """resolve_function (without module context) classifies sibling calls
        as UnresolvedTarget, preserving existing behavior."""
        tokens = tokenize_yul("function f(x) -> z { z := g(x) }")
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func)
        f_targets = list(result.call_targets.values())
        self.assertEqual(len(f_targets), 1)
        self.assertIsInstance(f_targets[0], yul_ast.UnresolvedTarget)

    # -- parse_functions ------------------------------------------------------

    def test_parse_functions_multiple(self) -> None:
        tokens = tokenize_yul("""
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
        tokens = tokenize_yul("""
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
        tokens = tokenize_yul("""
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
        tokens = tokenize_yul("""
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

    def test_parse_function_groups_rejects_unmatched_closing_brace(self) -> None:
        tokens = tokenize_yul("""
            function f(x) -> z { z := x }
            }
        """)

        with self.assertRaisesRegex(ParseError, "Unmatched closing brace"):
            SyntaxParser(tokens).parse_function_groups()

    def test_parse_function_groups_rejects_unclosed_scope(self) -> None:
        tokens = tokenize_yul("""
            object "A" { code {
                function f(x) -> z { z := x }
        """)

        with self.assertRaisesRegex(ParseError, "Unterminated brace scope"):
            SyntaxParser(tokens).parse_function_groups()

    def test_parse_string_literal_preserves_raw_bytes(self) -> None:
        tokens = tokenize_yul(r"""
            function f() {
                linkersymbol("\xff")
            }
        """)

        parsed = SyntaxParser(tokens).parse_function()
        stmt = parsed.body.stmts[0]
        self.assertIsInstance(stmt, yul_ast.ExprStmt)
        stmt = cast(yul_ast.ExprStmt, stmt)
        self.assertIsInstance(stmt.expr, yul_ast.CallExpr)
        stmt_expr = cast(yul_ast.CallExpr, stmt.expr)
        self.assertEqual(len(stmt_expr.args), 1)
        self.assertIsInstance(stmt_expr.args[0], yul_ast.StringExpr)
        arg = cast(yul_ast.StringExpr, stmt_expr.args[0])
        self.assertEqual(arg.decoded_bytes, b"\xff")

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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
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

        with self.assertRaisesRegex(ParseError, "Duplicate declaration"):
            translate_yul_to_models(
                yul,
                config,
                optimize=False,
            )


class NormalizeStructureTest(unittest.TestCase):
    """Tests for the syntax AST → normalized IR lowering pass."""

    def _normalize(self, yul: str) -> norm_ir.NormalizedFunction:
        tokens = tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func, builtins=EVM_BUILTINS)
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
        bind = cast(norm_ir.NBind, stmts[0])
        self.assertEqual(len(bind.targets), 1)
        self.assertIsNotNone(bind.expr)

    def test_assignment_produces_nassign(self) -> None:
        nf = self._normalize("function f(x) -> z { z := x }")
        stmts = nf.body.stmts
        self.assertIsInstance(stmts[0], norm_ir.NAssign)
        assign = cast(norm_ir.NAssign, stmts[0])
        self.assertEqual(len(assign.targets), 1)
        self.assertIsInstance(assign.expr, norm_ir.NRef)

    def test_builtin_call_produces_nbuiltincall(self) -> None:
        nf = self._normalize("function f(x) -> z { z := add(x, 1) }")
        self.assertIsInstance(nf.body.stmts[0], norm_ir.NAssign)
        assign = cast(norm_ir.NAssign, nf.body.stmts[0])
        self.assertIsInstance(assign.expr, norm_ir.NBuiltinCall)
        call = cast(norm_ir.NBuiltinCall, assign.expr)
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
        self.assertIsInstance(nf.body.stmts[1], norm_ir.NAssign)
        assign = cast(norm_ir.NAssign, nf.body.stmts[1])
        self.assertIsInstance(assign.expr, norm_ir.NLocalCall)
        call = cast(norm_ir.NLocalCall, assign.expr)
        self.assertEqual(call.name, "g")

    def test_if_statement_produces_nif(self) -> None:
        nf = self._normalize("function f(x) -> z { if x { z := 1 } }")
        stmt = nf.body.stmts[0]
        self.assertIsInstance(stmt, norm_ir.NIf)
        stmt = cast(norm_ir.NIf, stmt)
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
        stmt = cast(norm_ir.NSwitch, stmt)
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
        fdef = cast(norm_ir.NFunctionDef, fdef)
        self.assertEqual(fdef.name, "g")
        self.assertEqual(len(fdef.params), 1)
        self.assertEqual(len(fdef.returns), 1)


class NormalizeEvalTest(unittest.TestCase):
    """Semantic equivalence tests for normalized IR evaluation."""

    def _eval_normalized(
        self,
        yul: str,
        args: tuple[int, ...],
        builtins: frozenset[str] = EVM_BUILTINS,
    ) -> tuple[int, ...]:
        tokens = tokenize_yul(yul)
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
        self.assertEqual(self._eval_normalized(yul, ()), (7,))

    def test_same_named_helpers_resolved_by_symbol_id(self) -> None:
        """Two sibling helpers named 'g' with different bodies are
        distinguished by SymbolId — the correct one is called in each branch."""
        yul = """
            function f(x) -> z {
                switch x
                case 0 {
                    function g() -> b { b := 10 }
                    z := g()
                }
                default {
                    function g() -> b { b := 20 }
                    z := g()
                }
            }
        """
        self.assertEqual(self._eval_normalized(yul, (0,)), (10,))
        self.assertEqual(self._eval_normalized(yul, (1,)), (20,))

    def test_recursion_detection(self) -> None:
        """Mutual recursion (f→g→f) is caught before hitting Python stack limit."""
        yul = """
            function f(x) -> z { z := g(x) }
            function g(x) -> z { z := f(x) }
        """
        tokens = tokenize_yul(yul)
        funcs = SyntaxParser(tokens).parse_functions()
        results = resolve_module(funcs)
        nf_f = normalize_function(funcs[0], results["f"])
        nf_g = normalize_function(funcs[1], results["g"])

        ft: dict[str, norm_ir.NormalizedFunction] = {"f": nf_f, "g": nf_g}
        with self.assertRaisesRegex(EvaluationError, "Recursive call"):
            evaluate_normalized(nf_f, (1,), function_table=ft)

    def test_sibling_helper_calling_sibling_helper(self) -> None:
        """g() calls h() — both hoisted in the same block (valid per solc)."""
        yul = """
            function f() -> z {
                function g() -> b { b := h() }
                function h() -> c { c := 7 }
                z := g()
            }
        """
        self.assertEqual(self._eval_normalized(yul, ()), (7,))

    def test_nested_function_cannot_capture_outer_variable(self) -> None:
        """Yul functions are NOT closures — solc error 8198."""
        with self.assertRaisesRegex(ParseError, "Undefined variable"):
            tokens = tokenize_yul("""
                function f(x) -> z {
                    function g() -> b { b := x }
                    z := g()
                }
            """)
            func = SyntaxParser(tokens).parse_function()
            resolve_function(func, builtins=EVM_BUILTINS)

    def test_nested_function_cannot_capture_let_variable(self) -> None:
        """let-bound variables are also not capturable across function boundaries."""
        with self.assertRaisesRegex(ParseError, "Undefined variable"):
            tokens = tokenize_yul("""
                function f() -> z {
                    let w := 7
                    function g() -> b { b := w }
                    z := g()
                }
            """)
            func = SyntaxParser(tokens).parse_function()
            resolve_function(func, builtins=EVM_BUILTINS)


class ClassifySummaryTest(unittest.TestCase):
    """Tests for per-function effect summarization."""

    def _summarize_helper(self, yul: str) -> norm_ir.NFunctionDef:
        """Parse a function, normalize, and return the first NFunctionDef."""
        tokens = tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func, builtins=EVM_BUILTINS)
        nf = normalize_function(func, result)
        for stmt in nf.body.stmts:
            if isinstance(stmt, norm_ir.NFunctionDef):
                return stmt
        raise AssertionError("No NFunctionDef found in body")

    def test_pure_arithmetic_helper(self) -> None:
        fdef = self._summarize_helper("""
            function f(x) -> z {
                function g(a) -> b { b := add(a, 1) }
                z := g(x)
            }
        """)
        s = summarize_function(fdef.body)
        self.assertFalse(s.writes_memory)
        self.assertFalse(s.reads_memory)
        self.assertFalse(s.may_leave)
        self.assertFalse(s.has_for_loop)
        self.assertFalse(s.has_expr_effects)

    def test_helper_with_mstore(self) -> None:
        fdef = self._summarize_helper("""
            function f() -> z {
                function g() { mstore(0, 7) }
                g()
                z := mload(0)
            }
        """)
        s = summarize_function(fdef.body)
        self.assertTrue(s.writes_memory)
        self.assertFalse(s.reads_memory)

    def test_helper_with_mload(self) -> None:
        fdef = self._summarize_helper("""
            function f() -> z {
                function g() -> b { b := mload(0) }
                z := g()
            }
        """)
        s = summarize_function(fdef.body)
        self.assertFalse(s.writes_memory)
        self.assertTrue(s.reads_memory)

    def test_helper_with_leave(self) -> None:
        fdef = self._summarize_helper("""
            function f(x) -> z {
                function g(a) -> b {
                    if a { b := 1 leave }
                    b := 0
                }
                z := g(x)
            }
        """)
        s = summarize_function(fdef.body)
        self.assertTrue(s.may_leave)

    def test_helper_with_for_loop(self) -> None:
        fdef = self._summarize_helper("""
            function f(x) -> z {
                function g(a) -> b {
                    for { } a { } { b := 1 leave }
                }
                z := g(x)
            }
        """)
        s = summarize_function(fdef.body)
        self.assertTrue(s.has_for_loop)

    def test_helper_with_expr_effect(self) -> None:
        fdef = self._summarize_helper("""
            function f(x) -> z {
                function g(a) -> b { add(a, 1) b := a }
                z := g(x)
            }
        """)
        s = summarize_function(fdef.body)
        self.assertTrue(s.has_expr_effects)


class ClassifyInlineTest(unittest.TestCase):
    """Tests for transitive inlining classification."""

    def _classify(self, yul: str) -> dict[str, InlineClassification]:
        """Classify helpers and return results keyed by helper name."""
        tokens = tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func, builtins=EVM_BUILTINS)
        nf = normalize_function(func, result)
        classifications = classify_function_scope(nf)
        # Build name-keyed dict for test convenience by walking all
        # NFunctionDef nodes (including inside blocks).
        name_map: dict[str, InlineClassification] = {}
        self._collect_name_map(nf.body, classifications, name_map)
        return name_map

    def _collect_name_map(
        self,
        block: norm_ir.NBlock,
        classifications: dict[yul_ast.SymbolId, InlineClassification],
        out: dict[str, InlineClassification],
    ) -> None:
        for stmt in block.stmts:
            if isinstance(stmt, norm_ir.NFunctionDef):
                if stmt.symbol_id in classifications:
                    out[stmt.name] = classifications[stmt.symbol_id]
                self._collect_name_map(stmt.body, classifications, out)
            elif isinstance(stmt, norm_ir.NIf):
                self._collect_name_map(stmt.then_body, classifications, out)
            elif isinstance(stmt, norm_ir.NSwitch):
                for case in stmt.cases:
                    self._collect_name_map(case.body, classifications, out)
                if stmt.default is not None:
                    self._collect_name_map(stmt.default, classifications, out)
            elif isinstance(stmt, norm_ir.NFor):
                self._collect_name_map(stmt.init, classifications, out)
                self._collect_name_map(stmt.post, classifications, out)
                self._collect_name_map(stmt.body, classifications, out)
            elif isinstance(stmt, norm_ir.NBlock):
                self._collect_name_map(stmt, classifications, out)

    def test_pure_helper_classified_as_pure(self) -> None:
        c = self._classify("""
            function f(x) -> z {
                function g(a) -> b { b := add(a, 1) }
                z := g(x)
            }
        """)
        self.assertTrue(c["g"].is_pure)
        self.assertFalse(c["g"].is_deferred)
        self.assertIsNone(c["g"].unsupported_reason)

    def test_memory_helper_classified_as_deferred(self) -> None:
        c = self._classify("""
            function f() -> z {
                function g() { mstore(0, 7) }
                g()
                z := mload(0)
            }
        """)
        self.assertFalse(c["g"].is_pure)
        self.assertTrue(c["g"].is_deferred)

    def test_transitive_deferred_propagation(self) -> None:
        c = self._classify("""
            function f() -> z {
                function inner() { mstore(0, 7) }
                function wrapper() -> b { inner() b := mload(0) }
                wrapper()
                z := mload(0)
            }
        """)
        self.assertTrue(c["inner"].is_deferred)
        self.assertTrue(c["wrapper"].is_deferred)
        self.assertFalse(c["wrapper"].is_pure)

    def test_for_loop_helper_unsupported(self) -> None:
        c = self._classify("""
            function f(x) -> z {
                function g(a) -> b {
                    for { } a { } { b := 1 leave }
                }
                z := g(x)
            }
        """)
        self.assertFalse(c["g"].is_pure)
        self.assertIsNotNone(c["g"].unsupported_reason)

    def test_unresolved_call_not_pure(self) -> None:
        """Helper calling unresolved function must not be classified as pure."""
        c = self._classify("""
            function f(x) -> z {
                function g(a) -> b { b := ext(a) }
                z := g(x)
            }
        """)
        self.assertFalse(c["g"].is_pure)
        self.assertIsNotNone(c["g"].unsupported_reason)

    def test_top_level_call_not_pure(self) -> None:
        """Helper calling a top-level sibling must not be classified as pure."""
        yul = """
            function h(a) -> b { b := a }
            function f(x) -> z {
                function g(a) -> b { b := h(a) }
                z := g(x)
            }
        """
        tokens = tokenize_yul(yul)
        funcs = SyntaxParser(tokens).parse_functions()
        results = resolve_module(funcs, builtins=EVM_BUILTINS)
        nf_f = normalize_function(funcs[1], results["f"])
        classifications = classify_function_scope(nf_f)
        name_map: dict[str, InlineClassification] = {}
        for stmt in nf_f.body.stmts:
            if isinstance(stmt, norm_ir.NFunctionDef):
                if stmt.symbol_id in classifications:
                    name_map[stmt.name] = classifications[stmt.symbol_id]
        self.assertFalse(name_map["g"].is_pure)

    def test_mstore_as_expr_effect_not_flagged_as_unsupported(self) -> None:
        """mstore(...) as an expression-statement is a normal memory op, not unsupported."""
        c = self._classify("""
            function f() -> z {
                function g() { mstore(0, 7) }
                g()
                z := mload(0)
            }
        """)
        self.assertTrue(c["g"].is_deferred)
        self.assertIsNone(c["g"].unsupported_reason)

    def test_block_local_helper_classified(self) -> None:
        """Helper inside an if-block is still found and classified."""
        c = self._classify("""
            function f(x) -> z {
                if x {
                    function g() { mstore(0, 7) }
                    g()
                }
                z := mload(0)
            }
        """)
        self.assertIn("g", c)
        self.assertTrue(c["g"].is_deferred)

    def test_wrapper_around_unresolved_callee_not_pure(self) -> None:
        """wrapper -> inner -> ext(): wrapper must not be pure."""
        c = self._classify("""
            function f(x) -> z {
                function inner(a) -> b { b := ext(a) }
                function wrapper(a) -> b { b := inner(a) }
                z := wrapper(x)
            }
        """)
        self.assertFalse(c["inner"].is_pure)
        self.assertFalse(c["wrapper"].is_pure)

    def test_wrapper_around_for_loop_callee_not_pure(self) -> None:
        """wrapper -> inner (has for): wrapper must not be pure."""
        c = self._classify("""
            function f(x) -> z {
                function inner(a) -> b {
                    for { } a { } { b := 1 leave }
                }
                function wrapper(a) -> b { b := inner(a) }
                z := wrapper(x)
            }
        """)
        self.assertFalse(c["inner"].is_pure)
        self.assertFalse(c["wrapper"].is_pure)

    def test_wrapper_around_top_level_callee_not_pure(self) -> None:
        """wrapper -> inner -> top_level_sibling(): wrapper must not be pure."""
        yul = """
            function sibling(a) -> b { b := a }
            function f(x) -> z {
                function inner(a) -> b { b := sibling(a) }
                function wrapper(a) -> b { b := inner(a) }
                z := wrapper(x)
            }
        """
        tokens = tokenize_yul(yul)
        funcs = SyntaxParser(tokens).parse_functions()
        results = resolve_module(funcs, builtins=EVM_BUILTINS)
        nf_f = normalize_function(funcs[1], results["f"])
        classifications = classify_function_scope(nf_f)
        name_map: dict[str, InlineClassification] = {}
        self._collect_name_map(nf_f.body, classifications, name_map)
        self.assertFalse(name_map["inner"].is_pure)
        self.assertFalse(name_map["wrapper"].is_pure)

    def test_helper_nested_inside_helper_body_classified(self) -> None:
        """h nested inside g's body must be found and classified."""
        c = self._classify("""
            function f(x) -> z {
                function g(a) -> b {
                    function h() { mstore(0, 7) }
                    h()
                    b := mload(0)
                }
                z := g(x)
            }
        """)
        self.assertIn("h", c)
        self.assertTrue(c["h"].is_deferred)
        self.assertFalse(c["g"].is_pure)
        self.assertTrue(c["g"].is_deferred)


class InlinePureTest(unittest.TestCase):
    """Tests for pure helper inlining on normalized IR."""

    def _inline(self, yul: str) -> norm_ir.NormalizedFunction:
        tokens = tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func, builtins=EVM_BUILTINS)
        nf = normalize_function(func, result)
        return inline_pure_helpers(nf)

    def _eval_inlined(self, yul: str, args: tuple[int, ...]) -> tuple[int, ...]:
        nf = self._inline(yul)
        return evaluate_normalized(nf, args)

    def test_simple_pure_inline(self) -> None:
        """g(a) -> add(a,1) inlined into z := g(x)."""
        result = self._eval_inlined(
            """
            function f(x) -> z {
                function g(a) -> b { b := add(a, 1) }
                z := g(x)
            }
        """,
            (5,),
        )
        self.assertEqual(result, (6,))

    def test_multi_return_inline(self) -> None:
        """g returns two values — split into separate binds after inlining."""
        result = self._eval_inlined(
            """
            function f(x) -> p, q {
                function g(a) -> b, c { b := a  c := add(a, 1) }
                p, q := g(x)
            }
        """,
            (10,),
        )
        self.assertEqual(result, (10, 11))

    def test_nested_inline(self) -> None:
        """g calls h, both pure — h inlined into g, then g into f."""
        result = self._eval_inlined(
            """
            function f(x) -> z {
                function h(a) -> b { b := add(a, 1) }
                function g(a) -> b { b := h(a) }
                z := g(x)
            }
        """,
            (5,),
        )
        self.assertEqual(result, (6,))

    def test_if_branch_merge(self) -> None:
        """Pure helper with if-branch produces NIte after inlining."""
        nf = self._inline("""
            function f(x) -> z {
                function g(a) -> b { if a { b := 1 } }
                z := g(x)
            }
        """)
        # After inlining, z's expression should be an NIte.
        self.assertIsInstance(nf.body.stmts[-1], norm_ir.NAssign)
        assign = cast(norm_ir.NAssign, nf.body.stmts[-1])
        self.assertIsInstance(assign.expr, norm_ir.NIte)
        # Verify semantics.
        self.assertEqual(evaluate_normalized(nf, (0,)), (0,))
        self.assertEqual(evaluate_normalized(nf, (1,)), (1,))

    def test_constant_fold_branch(self) -> None:
        """if 1 { z := 7 } is constant-folded — no NIte produced."""
        nf = self._inline("""
            function f() -> z {
                function g() -> b { if 1 { b := 7 } }
                z := g()
            }
        """)
        self.assertIsInstance(nf.body.stmts[-1], norm_ir.NAssign)
        assign = cast(norm_ir.NAssign, nf.body.stmts[-1])
        # Should be NConst(7), not NIte.
        self.assertIsInstance(assign.expr, norm_ir.NConst)
        self.assertEqual(evaluate_normalized(nf, ()), (7,))

    def test_semantic_equivalence(self) -> None:
        """Inlined result matches pre-inline eval for multiple inputs."""
        yul = """
            function f(x, y) -> z {
                function g(a, b) -> c { c := add(mul(a, a), b) }
                z := g(x, y)
            }
        """
        for x, y in [(0, 0), (1, 2), (3, 4), (10, 7)]:
            pre = self._eval_inlined(yul, (x, y))
            expected: tuple[int, ...] = ((x * x + y) % (2**256),)
            self.assertEqual(pre, expected, f"Failed for x={x}, y={y}")

    def test_non_pure_left_alone(self) -> None:
        """Calls to deferred helpers remain as NLocalCall after inlining."""
        nf = self._inline("""
            function f() -> z {
                function g() { mstore(0, 7) }
                g()
                z := mload(0)
            }
        """)
        # g() is deferred (memory effect) — should remain as NExprEffect(NLocalCall).
        self.assertIsInstance(nf.body.stmts[1], norm_ir.NExprEffect)
        effect_stmt = cast(norm_ir.NExprEffect, nf.body.stmts[1])
        self.assertIsInstance(effect_stmt.expr, norm_ir.NLocalCall)

    def test_simultaneous_multi_assignment_preserved(self) -> None:
        """x, y := g(y, x) must swap — not clobber via sequential assignment."""
        result = self._eval_inlined(
            """
            function f(x, y) -> z {
                function g(a, b) -> c, d { c := a  d := b }
                x, y := g(y, x)
                z := sub(x, y)
            }
        """,
            (3, 1),
        )
        # g(1, 3) → c=1, d=3 → x=1, y=3 → sub(1,3) wraps to 2^256-2
        pre_inline = evaluate_normalized(
            normalize_function(
                SyntaxParser(tokenize_yul("""
                    function f(x, y) -> z {
                        function g(a, b) -> c, d { c := a  d := b }
                        x, y := g(y, x)
                        z := sub(x, y)
                    }
                """)).parse_function(),
                resolve_function(
                    SyntaxParser(tokenize_yul("""
                        function f(x, y) -> z {
                            function g(a, b) -> c, d { c := a  d := b }
                            x, y := g(y, x)
                            z := sub(x, y)
                        }
                    """)).parse_function(),
                    builtins=EVM_BUILTINS,
                ),
            ),
            (3, 1),
        )
        self.assertEqual(result, pre_inline)

    def test_pure_helper_with_switch_inlines(self) -> None:
        """Pure helper containing switch must inline correctly."""
        result = self._eval_inlined(
            """
            function f(x) -> z {
                function g(a) -> b {
                    switch a
                    case 0 { b := 10 }
                    default { b := 20 }
                }
                z := g(x)
            }
        """,
            (0,),
        )
        self.assertEqual(result, (10,))
        result2 = self._eval_inlined(
            """
            function f(x) -> z {
                function g(a) -> b {
                    switch a
                    case 0 { b := 10 }
                    default { b := 20 }
                }
                z := g(x)
            }
        """,
            (1,),
        )
        self.assertEqual(result2, (20,))

    def test_internal_multi_return_in_pure_helper(self) -> None:
        """Pure helper that internally calls another multi-return pure helper."""
        result = self._eval_inlined(
            """
            function f(x) -> z {
                function inner(a, b) -> c, d { c := a  d := b }
                function g(a, b) -> e {
                    let p, q := inner(b, a)
                    e := sub(p, q)
                }
                z := g(x, 1)
            }
        """,
            (5,),
        )
        # inner(1, 5) → c=1, d=5 → p=1, q=5 → sub(1,5) wraps
        pre_val = (1 - 5) % (2**256)
        self.assertEqual(result, (pre_val,))

    def test_call_site_inside_if_block_inlined(self) -> None:
        """Call site inside an if-block body must be inlined."""
        nf = self._inline("""
            function f(x) -> z {
                function g(a) -> b { b := add(a, 1) }
                if x { z := g(x) }
            }
        """)
        self.assertEqual(evaluate_normalized(nf, (0,)), (0,))
        self.assertEqual(evaluate_normalized(nf, (5,)), (6,))
        # Verify g is actually inlined (no NLocalCall remaining).
        self.assertIsInstance(nf.body.stmts[-1], norm_ir.NIf)
        if_stmt = cast(norm_ir.NIf, nf.body.stmts[-1])
        self.assertIsInstance(if_stmt.then_body.stmts[0], norm_ir.NAssign)
        assign = cast(norm_ir.NAssign, if_stmt.then_body.stmts[0])
        self.assertNotIsInstance(assign.expr, norm_ir.NLocalCall)

    def test_multi_case_switch_inlines_correctly(self) -> None:
        """Switch with multiple cases + default produces correct values."""
        yul = """
            function f(x) -> z {
                function g(a) -> b {
                    switch a
                    case 0 { b := 10 }
                    case 1 { b := 20 }
                    default { b := 30 }
                }
                z := g(x)
            }
        """
        self.assertEqual(self._eval_inlined(yul, (0,)), (10,))
        self.assertEqual(self._eval_inlined(yul, (1,)), (20,))
        self.assertEqual(self._eval_inlined(yul, (2,)), (30,))

    def test_zero_return_pure_helper_eliminated(self) -> None:
        """Pure void helper call in statement position is eliminated."""
        nf = self._inline("""
            function f() -> z {
                function g() { }
                g()
                z := 1
            }
        """)
        self.assertEqual(evaluate_normalized(nf, ()), (1,))

    def test_switch_with_effectful_discriminant_not_duplicated(self) -> None:
        """Switch in the outer function body must not have its discriminant
        duplicated — pre-normalization only applies to pure helper bodies."""
        yul = """
            function f() -> z {
                mstore(0, 0)
                switch mstore(0, add(mload(0), 1))
                case 0 { }
                default { }
                z := mload(0)
            }
        """
        tokens = tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func, builtins=EVM_BUILTINS)
        nf = normalize_function(func, result)
        pre = evaluate_normalized(nf, ())
        post = evaluate_normalized(inline_pure_helpers(nf), ())
        self.assertEqual(pre, post)

    def test_leave_bearing_helper_inlined(self) -> None:
        """Helper with if cond { ... leave } is inlined via NIte merge."""
        yul = """
            function f(x) -> z {
                function g(a) -> b {
                    if a { b := 1  leave }
                    b := 2
                }
                z := g(x)
            }
        """
        self.assertEqual(self._eval_inlined(yul, (0,)), (2,))
        self.assertEqual(self._eval_inlined(yul, (1,)), (1,))

    def test_leave_bearing_helper_constant_fold(self) -> None:
        """Leave branch with constant-true condition folds away."""
        yul = """
            function f() -> z {
                function g() -> b {
                    if 1 { b := 7  leave }
                    b := 99
                }
                z := g()
            }
        """
        self.assertEqual(self._eval_inlined(yul, ()), (7,))

    def test_leave_bearing_helper_dead_branch(self) -> None:
        """Leave branch with constant-false condition is eliminated."""
        yul = """
            function f() -> z {
                function g() -> b {
                    if 0 { b := 7  leave }
                    b := 42
                }
                z := g()
            }
        """
        self.assertEqual(self._eval_inlined(yul, ()), (42,))

    def test_leave_helper_classified_pure(self) -> None:
        """A leave-bearing helper with no other effects is classified pure."""
        tokens = tokenize_yul("""
            function f(x) -> z {
                function g(a) -> b {
                    if a { b := 1  leave }
                    b := 2
                }
                z := g(x)
            }
        """)
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func, builtins=EVM_BUILTINS)
        nf = normalize_function(func, result)
        classifications = classify_function_scope(nf)
        for sid, cls in classifications.items():
            self.assertTrue(cls.is_pure, f"Helper should be pure: {cls}")

    def test_uint512_from_inlined_as_explicit_mstores(self) -> None:
        """uint512.from helper is inlined by emitting explicit mstore statements."""
        nf = self._inline("""
            function f(hi, lo) -> z {
                function from_helper(ptr, x_hi, x_lo) -> r {
                    r := 0
                    mstore(ptr, x_hi)
                    mstore(add(0x20, ptr), x_lo)
                    r := ptr
                }
                let p := from_helper(64, hi, lo)
                z := add(mload(p), mload(add(0x20, p)))
            }
        """)
        # After inlining, the from_helper call should be replaced by
        # explicit mstore statements + ptr assignment.
        # Evaluate: hi=5, lo=7 → mstore(64, 5), mstore(96, 7) → z = 5+7 = 12
        self.assertEqual(evaluate_normalized(nf, (5, 7), memory={}), (12,))


class ConstPropTest(unittest.TestCase):
    """Tests for constant propagation and dead branch elimination."""

    def _prop(self, yul: str) -> norm_ir.NormalizedFunction:
        tokens = tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func, builtins=EVM_BUILTINS)
        nf = normalize_function(func, result)
        return propagate_constants(nf)

    def test_fold_constant_arithmetic(self) -> None:
        """add(3, 4) folds to NConst(7)."""
        nf = self._prop("function f() -> z { z := add(3, 4) }")
        self.assertIsInstance(nf.body.stmts[0], norm_ir.NAssign)
        assign = cast(norm_ir.NAssign, nf.body.stmts[0])
        self.assertEqual(assign.expr, norm_ir.NConst(7))

    def test_propagate_through_variable(self) -> None:
        """let x := 3; z := add(x, 1) → z := NConst(4)."""
        nf = self._prop("function f() -> z { let x := 3  z := add(x, 1) }")
        self.assertIsInstance(nf.body.stmts[1], norm_ir.NAssign)
        assign = cast(norm_ir.NAssign, nf.body.stmts[1])
        self.assertEqual(assign.expr, norm_ir.NConst(4))

    def test_dead_branch_eliminated(self) -> None:
        """if 0 { z := 1 } is removed entirely."""
        nf = self._prop("function f() -> z { if 0 { z := 1 } }")
        # Body should have no statements (the if was dead).
        self.assertEqual(len(nf.body.stmts), 0)

    def test_live_branch_flattened(self) -> None:
        """if 1 { z := 7 } flattened to z := 7."""
        nf = self._prop("function f() -> z { if 1 { z := 7 } }")
        self.assertEqual(len(nf.body.stmts), 1)
        self.assertIsInstance(nf.body.stmts[0], norm_ir.NAssign)
        assign = cast(norm_ir.NAssign, nf.body.stmts[0])
        self.assertEqual(assign.expr, norm_ir.NConst(7))

    def test_switch_constant_fold(self) -> None:
        """switch 1 case 0 { ... } case 1 { z := 20 } default { ... } → z := 20."""
        nf = self._prop("""
            function f() -> z {
                switch 1
                case 0 { z := 10 }
                case 1 { z := 20 }
                default { z := 30 }
            }
        """)
        # Only the matching case body should remain.
        self.assertEqual(len(nf.body.stmts), 1)
        self.assertIsInstance(nf.body.stmts[0], norm_ir.NAssign)
        assign = cast(norm_ir.NAssign, nf.body.stmts[0])
        self.assertEqual(assign.expr, norm_ir.NConst(20))

    def test_invalidation_at_conditional_join(self) -> None:
        """Variable modified in if-body is not propagated after the if."""
        nf = self._prop("""
            function f(x) -> z {
                let y := 5
                if x { y := 10 }
                z := y
            }
        """)
        # z := y should NOT be folded to a constant (y is path-dependent).
        self.assertIsInstance(nf.body.stmts[2], norm_ir.NAssign)
        assign = cast(norm_ir.NAssign, nf.body.stmts[2])
        self.assertIsInstance(assign.expr, norm_ir.NRef)

    def test_nite_constant_fold(self) -> None:
        """NIte(NConst(1), a, b) folds to a."""
        result = fold_expr(
            norm_ir.NIte(
                cond=norm_ir.NConst(1),
                if_true=norm_ir.NConst(10),
                if_false=norm_ir.NConst(20),
            )
        )
        self.assertEqual(result, norm_ir.NConst(10))

    def test_semantic_equivalence(self) -> None:
        """Propagated result matches original for multiple inputs."""
        yul = """
            function f(x) -> z {
                let a := 3
                let b := add(a, 4)
                z := add(x, b)
            }
        """
        tokens = tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func, builtins=EVM_BUILTINS)
        nf = normalize_function(func, result)
        prop = propagate_constants(nf)
        for x in [0, 1, 5, 100]:
            pre = evaluate_normalized(nf, (x,))
            post = evaluate_normalized(prop, (x,))
            self.assertEqual(pre, post, f"Failed for x={x}")

    def test_expr_effect_folded(self) -> None:
        """Expression inside NExprEffect is constant-folded."""
        nf = self._prop("""
            function f() -> z {
                mstore(0, add(3, 4))
                z := mload(0)
            }
        """)
        # The mstore arg should be folded to NConst(7).
        self.assertIsInstance(nf.body.stmts[0], norm_ir.NExprEffect)
        effect = cast(norm_ir.NExprEffect, nf.body.stmts[0])
        self.assertIsInstance(effect.expr, norm_ir.NBuiltinCall)
        effect_call = cast(norm_ir.NBuiltinCall, effect.expr)
        self.assertEqual(effect_call.args[1], norm_ir.NConst(7))
        self.assertEqual(evaluate_normalized(nf, (), memory={}), (7,))

    def test_for_loop_invalidates_modified_vars(self) -> None:
        """Variables modified in a for-loop body are not propagated after."""
        nf = self._prop("""
            function f(n) -> z {
                let i := 0
                for { } lt(i, n) { i := add(i, 1) } {
                    z := add(z, 1)
                }
            }
        """)
        # z and i are modified in the loop — should not be constant after.
        # The for-loop should still be present (not eliminated).
        has_for = any(isinstance(s, norm_ir.NFor) for s in nf.body.stmts)
        self.assertTrue(has_for)
        # Semantic check: f(3) should give z=3.
        self.assertEqual(evaluate_normalized(nf, (3,)), (3,))

    def test_leave_preserved(self) -> None:
        """NLeave passes through constant propagation unchanged."""
        nf = self._prop("""
            function f(x) -> z {
                if x { z := 1  leave }
                z := 2
            }
        """)
        # With x=1: z=1 (leave before z:=2). With x=0: z=2.
        self.assertEqual(evaluate_normalized(nf, (1,)), (1,))
        self.assertEqual(evaluate_normalized(nf, (0,)), (2,))

    def test_nested_block_propagation(self) -> None:
        """Constants propagate through nested bare blocks."""
        nf = self._prop("""
            function f() -> z {
                let a := 10
                {
                    let b := add(a, 5)
                    z := b
                }
            }
        """)
        # a=10 propagates into the block; b=15 propagates to z.
        self.assertEqual(evaluate_normalized(nf, ()), (15,))

        # Check that z's final assignment is folded.
        def find_last_assign(block: norm_ir.NBlock) -> norm_ir.NAssign | None:
            for s in reversed(block.stmts):
                if isinstance(s, norm_ir.NAssign):
                    return s
                if isinstance(s, norm_ir.NBlock):
                    r = find_last_assign(s)
                    if r is not None:
                        return r
            return None

        assign = find_last_assign(nf.body)
        self.assertIsNotNone(assign)
        assign = cast(norm_ir.NAssign, assign)
        self.assertEqual(assign.expr, norm_ir.NConst(15))

    def test_function_def_preserved(self) -> None:
        """NFunctionDef passes through without being removed or modified."""
        nf = self._prop("""
            function f(x) -> z {
                function g(a) -> b { b := add(a, 1) }
                z := g(x)
            }
        """)
        has_fdef = any(isinstance(s, norm_ir.NFunctionDef) for s in nf.body.stmts)
        self.assertTrue(has_fdef)

    def test_for_loop_body_expressions_folded(self) -> None:
        """Expressions inside for-loop bodies are still constant-folded."""
        nf = self._prop("""
            function f(n) -> z {
                for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                    z := add(z, add(2, 3))
                }
            }
        """)
        # add(2, 3) should be folded to NConst(5) inside the loop body.
        self.assertIsInstance(nf.body.stmts[0], norm_ir.NFor)
        for_stmt = cast(norm_ir.NFor, nf.body.stmts[0])
        self.assertIsInstance(for_stmt.body.stmts[0], norm_ir.NAssign)
        assign = cast(norm_ir.NAssign, for_stmt.body.stmts[0])
        self.assertIsInstance(assign.expr, norm_ir.NBuiltinCall)
        assign_call = cast(norm_ir.NBuiltinCall, assign.expr)
        self.assertEqual(assign_call.args[1], norm_ir.NConst(5))


class InlineArchitectureTest(unittest.TestCase):
    """Coverage for the block-based inliner architecture."""

    def _inline(self, yul: str) -> norm_ir.NormalizedFunction:
        tokens = tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func, builtins=EVM_BUILTINS)
        nf = normalize_function(func, result)
        return inline_pure_helpers(nf)

    def _has_local_call(self, block: norm_ir.NBlock, name: str) -> bool:
        """Check if any NLocalCall to *name* remains anywhere in the IR tree."""
        from norm_walk import for_each_expr

        found: list[bool] = [False]

        def check_expr(e: norm_ir.NExpr) -> None:
            if isinstance(e, norm_ir.NLocalCall) and e.name == name:
                found[0] = True

        def walk_block(b: norm_ir.NBlock) -> None:
            for stmt in b.stmts:
                walk_stmt(stmt)

        def walk_stmt(stmt: norm_ir.NStmt) -> None:
            if isinstance(stmt, (norm_ir.NBind, norm_ir.NAssign)):
                if stmt.expr is not None:
                    for_each_expr(stmt.expr, check_expr)
            elif isinstance(stmt, norm_ir.NExprEffect):
                for_each_expr(stmt.expr, check_expr)
            elif isinstance(stmt, norm_ir.NStore):
                for_each_expr(stmt.addr, check_expr)
                for_each_expr(stmt.value, check_expr)
            elif isinstance(stmt, norm_ir.NIf):
                for_each_expr(stmt.condition, check_expr)
                walk_block(stmt.then_body)
            elif isinstance(stmt, norm_ir.NSwitch):
                for_each_expr(stmt.discriminant, check_expr)
                for case in stmt.cases:
                    walk_block(case.body)
                if stmt.default is not None:
                    walk_block(stmt.default)
            elif isinstance(stmt, norm_ir.NFor):
                walk_block(stmt.init)
                if stmt.condition_setup is not None:
                    walk_block(stmt.condition_setup)
                for_each_expr(stmt.condition, check_expr)
                walk_block(stmt.post)
                walk_block(stmt.body)
            elif isinstance(stmt, norm_ir.NBlock):
                walk_block(stmt)
            elif isinstance(stmt, norm_ir.NFunctionDef):
                pass  # Structural — not executed, don't check

        walk_block(block)
        return found[0]

    def test_nested_block_inline_call(self) -> None:
        """BLOCK_INLINE call nested inside add() must be inlined."""
        nf = self._inline("""
            function f(x) -> z {
                function g(a) -> b {
                    if a { b := 1  leave }
                    b := 2
                }
                z := add(g(x), 10)
            }
        """)
        self.assertFalse(
            self._has_local_call(nf.body, "g"),
            "g should be inlined, not left as NLocalCall",
        )
        self.assertEqual(evaluate_normalized(nf, (0,)), (12,))
        self.assertEqual(evaluate_normalized(nf, (1,)), (11,))

    def test_nested_effect_lower_call(self) -> None:
        """EFFECT_LOWER call nested inside add() must be inlined."""
        nf = self._inline("""
            function f(hi, lo) -> z {
                function from_helper(ptr, x_hi, x_lo) -> r {
                    r := 0
                    mstore(ptr, x_hi)
                    mstore(add(0x20, ptr), x_lo)
                    r := ptr
                }
                z := add(from_helper(64, hi, lo), 1)
            }
        """)
        self.assertFalse(
            self._has_local_call(nf.body, "from_helper"),
            "from_helper should be inlined, not left as NLocalCall",
        )
        self.assertEqual(evaluate_normalized(nf, (5, 7), memory={}), (65,))

    def test_effect_lower_as_expression_statement(self) -> None:
        """Bare from_helper(64, hi, lo) as expression-statement must emit NStores."""
        nf = self._inline("""
            function f(hi, lo) -> z {
                function from_helper(ptr, x_hi, x_lo) -> r {
                    r := 0
                    mstore(ptr, x_hi)
                    mstore(add(0x20, ptr), x_lo)
                    r := ptr
                }
                from_helper(64, hi, lo)
                z := add(mload(64), mload(add(0x20, 64)))
            }
        """)
        self.assertFalse(
            self._has_local_call(nf.body, "from_helper"),
            "from_helper should be inlined, not left as NLocalCall",
        )
        self.assertEqual(evaluate_normalized(nf, (5, 7), memory={}), (12,))

    def test_block_inline_binder_hygiene(self) -> None:
        """Two inlines of the same BLOCK_INLINE helper must use distinct SymbolIds."""
        nf = self._inline("""
            function f(x, y) -> p, q {
                function g(a) -> b {
                    let t := a
                    if t { b := 1  leave }
                    b := 2
                }
                p := g(x)
                q := g(y)
            }
        """)
        # Verify correctness.
        self.assertEqual(evaluate_normalized(nf, (0, 0)), (2, 2))
        self.assertEqual(evaluate_normalized(nf, (1, 0)), (1, 2))
        self.assertEqual(evaluate_normalized(nf, (0, 1)), (2, 1))
        self.assertEqual(evaluate_normalized(nf, (1, 1)), (1, 1))
        # Verify no duplicate SymbolIds across ALL declarations (recursive).
        all_decl_ids: list[yul_ast.SymbolId] = []
        self._collect_all_decl_ids(nf.body, all_decl_ids)
        self.assertEqual(
            len(all_decl_ids),
            len(set(all_decl_ids)),
            f"Duplicate declaration SymbolIds: {all_decl_ids}",
        )

    def _collect_all_decl_ids(
        self, block: norm_ir.NBlock, out: list[yul_ast.SymbolId]
    ) -> None:
        """Recursively collect ALL declaration SymbolIds from the IR tree."""
        for stmt in block.stmts:
            if isinstance(stmt, norm_ir.NBind):
                out.extend(stmt.targets)
            elif isinstance(stmt, norm_ir.NFunctionDef):
                out.append(stmt.symbol_id)
                out.extend(stmt.params)
                out.extend(stmt.returns)
                self._collect_all_decl_ids(stmt.body, out)
            elif isinstance(stmt, norm_ir.NIf):
                self._collect_all_decl_ids(stmt.then_body, out)
            elif isinstance(stmt, norm_ir.NSwitch):
                for case in stmt.cases:
                    self._collect_all_decl_ids(case.body, out)
                if stmt.default is not None:
                    self._collect_all_decl_ids(stmt.default, out)
            elif isinstance(stmt, norm_ir.NFor):
                self._collect_all_decl_ids(stmt.init, out)
                if stmt.condition_setup is not None:
                    self._collect_all_decl_ids(stmt.condition_setup, out)
                self._collect_all_decl_ids(stmt.post, out)
                self._collect_all_decl_ids(stmt.body, out)
            elif isinstance(stmt, norm_ir.NBlock):
                self._collect_all_decl_ids(stmt, out)

    def test_block_inline_prelude_has_no_inlineable_local_calls(self) -> None:
        """Nested EXPR_INLINE helper inside BLOCK_INLINE helper must be
        inlined in the generated prelude — no NLocalCall to h should remain."""
        nf = self._inline("""
            function f(x) -> z {
                function g(a) -> b {
                    function h(v) -> c { c := add(v, 1) }
                    if a { b := h(1)  leave }
                    b := h(2)
                }
                z := g(x)
            }
        """)
        self.assertFalse(
            self._has_local_call(nf.body, "h"),
            "h should be inlined inside g's block-inline prelude",
        )
        self.assertEqual(evaluate_normalized(nf, (0,)), (3,))
        self.assertEqual(evaluate_normalized(nf, (1,)), (2,))


class MemoryLowerTest(unittest.TestCase):
    """Tests for memory model lowering."""

    def _pipeline(self, yul: str) -> norm_ir.NormalizedFunction:
        """Run full pipeline: parse → resolve → normalize → inline → constprop → memory."""
        tokens = tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func, builtins=EVM_BUILTINS)
        nf = normalize_function(func, result)
        nf = inline_pure_helpers(nf)
        nf = propagate_constants(nf)
        return lower_memory(nf)

    def test_basic_mstore_mload_resolution(self) -> None:
        """mstore(0, 7); z := mload(0) → z := 7, NStore removed."""
        nf = self._pipeline("""
            function f() -> z {
                mstore(0, 7)
                z := mload(0)
            }
        """)
        # NStore should be removed, z should be NConst(7).
        has_store = any(isinstance(s, norm_ir.NStore) for s in nf.body.stmts)
        self.assertFalse(has_store, "NStore should be removed after lowering")
        self.assertEqual(evaluate_normalized(nf, ()), (7,))

    def test_uint512_from_pattern(self) -> None:
        """Two NStore + two mload from uint512.from → direct value references."""
        nf = self._pipeline("""
            function f(hi, lo) -> z {
                function from_helper(ptr, x_hi, x_lo) -> r {
                    r := 0
                    mstore(ptr, x_hi)
                    mstore(add(0x20, ptr), x_lo)
                    r := ptr
                }
                let p := from_helper(64, hi, lo)
                z := add(mload(p), mload(add(0x20, p)))
            }
        """)
        self.assertEqual(evaluate_normalized(nf, (5, 7)), (12,))

    def test_chained_resolution(self) -> None:
        """mload in mstore value resolves recursively."""
        nf = self._pipeline("""
            function f() -> z {
                mstore(0, 7)
                mstore(32, mload(0))
                z := mload(32)
            }
        """)
        self.assertEqual(evaluate_normalized(nf, ()), (7,))

    def test_non_constant_address_rejected(self) -> None:
        """mstore with non-constant address raises ParseError."""
        with self.assertRaisesRegex(ParseError, "Non-constant"):
            self._pipeline("""
                function f(x) -> z {
                    mstore(x, 7)
                    z := mload(x)
                }
            """)

    def test_unaligned_address_rejected(self) -> None:
        """mstore to non-32-byte-aligned address raises ParseError."""
        with self.assertRaisesRegex(ParseError, "Unaligned"):
            self._pipeline("""
                function f() -> z {
                    mstore(1, 7)
                    z := mload(1)
                }
            """)

    def test_duplicate_write_rejected(self) -> None:
        """Two mstore to same address raises ParseError."""
        with self.assertRaisesRegex(ParseError, "Duplicate mstore"):
            self._pipeline("""
                function f() -> z {
                    mstore(0, 7)
                    mstore(0, 8)
                    z := mload(0)
                }
            """)

    def test_uninitialized_read_rejected(self) -> None:
        """mload from address with no prior mstore raises ParseError."""
        with self.assertRaisesRegex(ParseError, "no prior mstore"):
            self._pipeline("""
                function f() -> z {
                    z := mload(0)
                }
            """)

    def test_semantic_equivalence(self) -> None:
        """Lowered result matches pre-lower eval for uint512.from inputs."""
        yul = """
            function f(hi, lo) -> z {
                function from_helper(ptr, x_hi, x_lo) -> r {
                    r := 0
                    mstore(ptr, x_hi)
                    mstore(add(0x20, ptr), x_lo)
                    r := ptr
                }
                let p := from_helper(64, hi, lo)
                z := add(mload(p), mload(add(0x20, p)))
            }
        """
        tokens = tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func, builtins=EVM_BUILTINS)
        nf = normalize_function(func, result)
        nf = inline_pure_helpers(nf)
        nf = propagate_constants(nf)
        for hi, lo in [(0, 0), (5, 7), (100, 200)]:
            pre = evaluate_normalized(nf, (hi, lo), memory={})
            lowered = lower_memory(nf)
            post = evaluate_normalized(lowered, (hi, lo))
            self.assertEqual(pre, post, f"Failed for hi={hi}, lo={lo}")

    def test_mstore_inside_if_rejected(self) -> None:
        """mstore inside conditional is rejected (straight-line only)."""
        with self.assertRaisesRegex(ParseError, "inside control flow"):
            self._pipeline("""
                function f(x) -> z {
                    if x { mstore(0, 7) }
                    z := mload(0)
                }
            """)

    def test_mload_inside_if_resolved(self) -> None:
        """Read-only mload inside conditional resolves from straight-line writes."""
        nf = self._pipeline("""
            function f(x) -> z {
                mstore(0, 7)
                if x { z := mload(0) }
            }
        """)
        self.assertEqual(evaluate_normalized(nf, (0,)), (0,))
        self.assertEqual(evaluate_normalized(nf, (1,)), (7,))

    def test_store_value_snapshot_semantics(self) -> None:
        """mstore(0, x) then x := add(x, 1) then mload(0) must return original x."""
        nf = self._pipeline("""
            function f(x) -> z {
                mstore(0, x)
                z := mload(0)
            }
        """)
        self.assertEqual(evaluate_normalized(nf, (5,)), (5,))

    def test_mstore_inside_for_rejected(self) -> None:
        """mstore inside for-loop is rejected."""
        with self.assertRaisesRegex(ParseError, "inside control flow"):
            self._pipeline("""
                function f(n) -> z {
                    for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                        mstore(0, i)
                    }
                    z := mload(0)
                }
            """)

    def test_mstore_inside_nested_switch_under_if_rejected(self) -> None:
        with self.assertRaisesRegex(ParseError, "inside control flow"):
            self._pipeline("""
                function f(x) -> z {
                    if x {
                        switch x
                        case 1 { mstore(0, 7) }
                        default { }
                    }
                    z := 0
                }
            """)

    def test_bare_mload_expr_stmt_inside_if_resolved(self) -> None:
        nf = self._pipeline("""
            function f(x) -> z {
                mstore(0, 7)
                if x { mload(0) }
                z := mload(0)
            }
        """)
        self.assertEqual(evaluate_normalized(nf, (0,)), (7,))
        self.assertEqual(evaluate_normalized(nf, (1,)), (7,))

    def test_switch_condition_mload_resolved(self) -> None:
        """mload in top-level switch discriminant must be resolved."""
        nf = self._pipeline("""
            function f() -> z {
                mstore(0, 1)
                switch mload(0)
                case 0 { z := 10 }
                case 1 { z := 20 }
                default { z := 30 }
            }
        """)
        self.assertEqual(evaluate_normalized(nf, ()), (20,))

    def test_for_condition_mload_resolved(self) -> None:
        """mload in top-level for condition must be resolved."""
        nf = self._pipeline("""
            function f() -> z {
                mstore(0, 0)
                for { let i := 0 } lt(i, mload(0)) { i := add(i, 1) } {
                    z := add(z, 1)
                }
            }
        """)
        # mload(0) resolves to NConst(0), lt(i, 0) is always false, loop never runs.
        self.assertEqual(evaluate_normalized(nf, ()), (0,))

    def test_snapshot_with_reassignment(self) -> None:
        """mstore(0, x) then x := add(x, 1) then mload(0) must return original x=5, not 6."""
        nf = self._pipeline("""
            function f(x) -> z {
                mstore(0, x)
                x := add(x, 1)
                z := mload(0)
            }
        """)
        self.assertEqual(evaluate_normalized(nf, (5,)), (5,))

    def test_mload_in_nested_if_condition_resolved(self) -> None:
        """Nested control-flow conditions may read from straight-line memory."""
        nf = self._pipeline("""
            function f(x) -> z {
                mstore(0, 7)
                if x { if mload(0) { z := 1 } }
            }
        """)
        self.assertEqual(evaluate_normalized(nf, (0,)), (0,))
        self.assertEqual(evaluate_normalized(nf, (1,)), (1,))

    def test_mload_in_nested_switch_discriminant_resolved(self) -> None:
        """Nested switch discriminants may read from straight-line memory."""
        nf = self._pipeline("""
            function f(x) -> z {
                mstore(0, 1)
                if x {
                    switch mload(0)
                    case 1 { z := 10 }
                    default { z := 20 }
                }
            }
        """)
        self.assertEqual(evaluate_normalized(nf, (0,)), (0,))
        self.assertEqual(evaluate_normalized(nf, (1,)), (10,))

    def test_mload_in_nested_for_condition_resolved(self) -> None:
        """Nested for-conditions may read straight-line memory and preserve semantics."""
        nf = self._pipeline("""
            function f(x) -> z {
                mstore(0, 0)
                if x {
                    for { let i := 0 } iszero(mload(0)) { i := add(i, 1) } {
                        z := 1
                    }
                }
            }
        """)
        self.assertEqual(evaluate_normalized(nf, (0,)), (0,))
        with self.assertRaisesRegex(
            EvaluationError, "For-loop exceeded maximum iteration count"
        ):
            evaluate_normalized(nf, (1,))


class RestrictedIRTest(unittest.TestCase):
    """Tests for restricted IR construction after explicit memory lowering."""

    def _to_restricted(self, yul: str) -> RestrictedFunction:
        """Full pipeline: Yul → restricted IR."""
        tokens = tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func, builtins=EVM_BUILTINS)
        nf = normalize_function(func, result)
        nf = inline_pure_helpers(nf)
        nf = propagate_constants(nf)
        return lower_to_restricted(lower_memory(nf))

    def _eval_restricted(self, yul: str, args: tuple[int, ...]) -> tuple[int, ...]:
        return evaluate_restricted(self._to_restricted(yul), args)

    def _module_to_restricted(self, yul: str) -> dict[str, RestrictedFunction]:
        tokens = tokenize_yul(yul)
        funcs = SyntaxParser(tokens).parse_functions()
        resolved = resolve_module(funcs, builtins=EVM_BUILTINS)
        out: dict[str, RestrictedFunction] = {}

        for name, result in resolved.items():
            nf = normalize_function(result.func, result)
            nf = inline_pure_helpers(nf)
            nf = propagate_constants(nf)
            out[name] = lower_to_restricted(lower_memory(nf))
        return out

    def test_simple_assignment(self) -> None:
        result = self._eval_restricted("function f(x) -> z { z := add(x, 1) }", (5,))
        self.assertEqual(result, (6,))

    def test_if_else_produces_conditional_block(self) -> None:
        result = self._eval_restricted(
            """
            function f(x) -> z {
                if x { z := 1 }
            }
        """,
            (0,),
        )
        self.assertEqual(result, (0,))
        result2 = self._eval_restricted(
            """
            function f(x) -> z {
                if x { z := 1 }
            }
        """,
            (1,),
        )
        self.assertEqual(result2, (1,))

    def test_switch_nonconstant(self) -> None:
        self.assertEqual(
            self._eval_restricted(
                """
                function f(x) -> z {
                    switch x
                    case 1 { z := 7 }
                    default { z := 9 }
                }
            """,
                (0,),
            ),
            (9,),
        )
        self.assertEqual(
            self._eval_restricted(
                """
                function f(x) -> z {
                    switch x
                    case 1 { z := 7 }
                    default { z := 9 }
                }
            """,
                (1,),
            ),
            (7,),
        )
        self.assertEqual(
            self._eval_restricted(
                """
                function f(x) -> z {
                    switch x
                    case 1 { z := 7 }
                    default { z := 9 }
                }
            """,
                (2,),
            ),
            (9,),
        )

    def test_switch_default_only(self) -> None:
        self.assertEqual(
            self._eval_restricted(
                """
                function f(x) -> z {
                    switch x
                    case 1 { }
                    default { z := 9 }
                }
            """,
                (0,),
            ),
            (9,),
        )
        self.assertEqual(
            self._eval_restricted(
                """
                function f(x) -> z {
                    switch x
                    case 1 { }
                    default { z := 9 }
                }
            """,
                (1,),
            ),
            (0,),
        )

    def test_switch_case_only(self) -> None:
        self.assertEqual(
            self._eval_restricted(
                """
                function f(x) -> z {
                    switch x
                    case 1 { z := 7 }
                }
            """,
                (0,),
            ),
            (0,),
        )
        self.assertEqual(
            self._eval_restricted(
                """
                function f(x) -> z {
                    switch x
                    case 1 { z := 7 }
                }
            """,
                (1,),
            ),
            (7,),
        )

    def test_switch_multi_case(self) -> None:
        self.assertEqual(
            self._eval_restricted(
                """
                function f(x) -> z {
                    switch x
                    case 0 { z := 10 }
                    case 1 { z := 20 }
                    default { z := 30 }
                }
            """,
                (0,),
            ),
            (10,),
        )
        self.assertEqual(
            self._eval_restricted(
                """
                function f(x) -> z {
                    switch x
                    case 0 { z := 10 }
                    case 1 { z := 20 }
                    default { z := 30 }
                }
            """,
                (1,),
            ),
            (20,),
        )
        self.assertEqual(
            self._eval_restricted(
                """
                function f(x) -> z {
                    switch x
                    case 0 { z := 10 }
                    case 1 { z := 20 }
                    default { z := 30 }
                }
            """,
                (2,),
            ),
            (30,),
        )

    def test_nested_switch_under_if(self) -> None:
        self.assertEqual(
            self._eval_restricted(
                """
                function f(x, y) -> z {
                    if x {
                        switch y
                        case 1 { z := 7 }
                        default { z := 9 }
                    }
                }
            """,
                (0, 1),
            ),
            (0,),
        )
        self.assertEqual(
            self._eval_restricted(
                """
                function f(x, y) -> z {
                    if x {
                        switch y
                        case 1 { z := 7 }
                        default { z := 9 }
                    }
                }
            """,
                (1, 1),
            ),
            (7,),
        )
        self.assertEqual(
            self._eval_restricted(
                """
                function f(x, y) -> z {
                    if x {
                        switch y
                        case 1 { z := 7 }
                        default { z := 9 }
                    }
                }
            """,
                (1, 2),
            ),
            (9,),
        )

    def test_mstore_mload_resolved(self) -> None:
        """Memory ops eliminated: mstore consumed, mload resolved."""
        result = self._eval_restricted(
            """
            function f() -> z {
                mstore(0, 7)
                z := mload(0)
            }
        """,
            (),
        )
        self.assertEqual(result, (7,))

    def test_uint512_from_memory_pattern(self) -> None:
        result = self._eval_restricted(
            """
            function f(hi, lo) -> z {
                function from_helper(ptr, x_hi, x_lo) -> r {
                    r := 0
                    mstore(ptr, x_hi)
                    mstore(add(0x20, ptr), x_lo)
                    r := ptr
                }
                let p := from_helper(64, hi, lo)
                z := add(mload(p), mload(add(0x20, p)))
            }
        """,
            (5, 7),
        )
        self.assertEqual(result, (12,))

    def test_snapshot_semantics(self) -> None:
        """mstore(0, x) then x := add(x, 1) then mload(0) returns original x."""
        result = self._eval_restricted(
            """
            function f(x) -> z {
                mstore(0, x)
                x := add(x, 1)
                z := mload(0)
            }
        """,
            (5,),
        )
        self.assertEqual(result, (5,))

    def test_memory_in_branch_rejected(self) -> None:
        with self.assertRaisesRegex(ParseError, "inside control flow"):
            self._to_restricted("""
                function f(x) -> z {
                    if x { mstore(0, 7) }
                    z := 0
                }
            """)

    def test_non_constant_address_rejected(self) -> None:
        with self.assertRaisesRegex(ParseError, "Non-constant"):
            self._to_restricted("""
                function f(x) -> z {
                    mstore(x, 7)
                    z := mload(x)
                }
            """)

    def test_duplicate_write_rejected(self) -> None:
        with self.assertRaisesRegex(ParseError, "Duplicate mstore"):
            self._to_restricted("""
                function f() -> z {
                    mstore(0, 7)
                    mstore(0, 8)
                    z := mload(0)
                }
            """)

    def test_uninitialized_read_rejected(self) -> None:
        with self.assertRaisesRegex(ParseError, "no prior mstore"):
            self._to_restricted("""
                function f() -> z {
                    z := mload(0)
                }
            """)

    def test_semantic_equivalence_with_normalized(self) -> None:
        """Restricted IR eval matches normalized IR eval."""
        yul = """
            function f(x) -> z {
                let a := add(x, 3)
                if x { a := mul(a, 2) }
                z := a
            }
        """
        tokens = tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func, builtins=EVM_BUILTINS)
        nf = normalize_function(func, result)
        nf = inline_pure_helpers(nf)
        nf = propagate_constants(nf)
        rf = lower_to_restricted(lower_memory(nf))

        for x in [0, 1, 5, 100]:
            norm_result = evaluate_normalized(nf, (x,))
            rest_result = evaluate_restricted(rf, (x,))
            self.assertEqual(norm_result, rest_result, f"Mismatch at x={x}")

    def test_top_level_multi_return_call(self) -> None:
        models = self._module_to_restricted("""
            function g(x) -> a, b {
                a := x
                b := add(x, 1)
            }
            function f(x) -> z, w {
                z, w := g(x)
            }
        """)
        self.assertEqual(
            evaluate_restricted(models["f"], (0,), model_table=models),
            (0, 1),
        )
        self.assertEqual(
            evaluate_restricted(models["f"], (5,), model_table=models),
            (5, 6),
        )


class SSAModelTest(unittest.TestCase):
    """Tests for SSA renaming and FunctionModel conversion."""

    def _to_model(self, yul: str, fn_name: str = "f") -> FunctionModel:
        """Full pipeline: Yul → FunctionModel."""
        tokens = tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func, builtins=EVM_BUILTINS)
        nf = normalize_function(func, result)
        nf = inline_pure_helpers(nf)
        nf = propagate_constants(nf)
        rf = lower_to_restricted(lower_memory(nf))
        return to_function_models({rf.name: rf})[fn_name]

    def test_simple_function(self) -> None:
        """Params and returns get correct names, eval is correct."""
        model = self._to_model("function f(x) -> z { z := add(x, 1) }")
        self.assertEqual(model.fn_name, "f")
        self.assertIn("x", model.param_names)
        # Return name is the final SSA name for z (may have suffix).
        self.assertTrue(
            any(n.startswith("z") for n in model.return_names),
            f"Expected return name starting with 'z': {model.return_names}",
        )
        self.assertEqual(evaluate_function_model(model, (5,)), (6,))

    def test_ssa_numbering(self) -> None:
        """Multiple assignments to same variable get suffixed SSA names."""
        model = self._to_model("""
            function f(x) -> z {
                let a := x
                a := add(a, 1)
                z := a
            }
        """)
        # a should appear as a, a_1
        targets: list[str] = [
            s.target for s in model.assignments if isinstance(s, Assignment)
        ]
        a_targets: list[str] = [t for t in targets if t.startswith("a")]
        self.assertGreater(len(a_targets), 1, f"Expected SSA suffixes: {targets}")
        self.assertEqual(evaluate_function_model(model, (5,)), (6,))

    def test_conditional_block(self) -> None:
        """If-else produces ConditionalBlock with correct eval."""
        model = self._to_model("""
            function f(x) -> z {
                if x { z := 1 }
            }
        """)
        self.assertEqual(evaluate_function_model(model, (0,)), (0,))
        self.assertEqual(evaluate_function_model(model, (1,)), (1,))

    def test_eval_equivalence_with_restricted(self) -> None:
        """FunctionModel eval matches restricted IR eval."""
        yul = """
            function f(x) -> z {
                let a := add(x, 3)
                if x { a := mul(a, 2) }
                z := a
            }
        """
        tokens = tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func, builtins=EVM_BUILTINS)
        nf = normalize_function(func, result)
        nf = inline_pure_helpers(nf)
        nf = propagate_constants(nf)
        rf = lower_to_restricted(lower_memory(nf))
        model = to_function_models({rf.name: rf})["f"]

        for x in [0, 1, 5, 100]:
            rest_val = evaluate_restricted(rf, (x,))
            model_val = evaluate_function_model(model, (x,))
            self.assertEqual(rest_val, model_val, f"Mismatch at x={x}")

    def test_zero_init_return(self) -> None:
        """Return variable gets explicit zero-init."""
        model = self._to_model("""
            function f(x) -> z {
                if x { z := 1 }
            }
        """)
        # The first assignment to z should be zero-init.
        first_z = None
        for s in model.assignments:
            if isinstance(s, Assignment) and s.target.startswith("z"):
                first_z = s
                break
        self.assertIsNotNone(first_z)
        first_z = cast(Assignment, first_z)
        self.assertEqual(first_z.expr, IntLit(0))

    def test_memory_resolved_uint512(self) -> None:
        """Full pipeline with uint512.from produces valid FunctionModel."""
        model = self._to_model("""
            function f(hi, lo) -> z {
                function from_helper(ptr, x_hi, x_lo) -> r {
                    r := 0
                    mstore(ptr, x_hi)
                    mstore(add(0x20, ptr), x_lo)
                    r := ptr
                }
                let p := from_helper(64, hi, lo)
                z := add(mload(p), mload(add(0x20, p)))
            }
        """)
        self.assertEqual(evaluate_function_model(model, (5, 7)), (12,))

    # ------------------------------------------------------------------
    # Nested conditional, SSA collision, and name legalization coverage.
    # ------------------------------------------------------------------

    def test_nested_if_in_if(self) -> None:
        """Nested if inside if must flatten and eval correctly."""
        model = self._to_model("""
            function f(x) -> z {
                if x { if add(x, 1) { z := 7 } }
            }
        """)
        rf = self._to_restricted(
            "function f(x) -> z { if x { if add(x, 1) { z := 7 } } }"
        )
        for x in [0, 1, 5]:
            rest_val = evaluate_restricted(rf, (x,))
            model_val = evaluate_function_model(model, (x,))
            self.assertEqual(rest_val, model_val, f"Mismatch at x={x}")

    def test_nested_switch_in_if(self) -> None:
        """Nested switch inside if must flatten and eval correctly."""
        model = self._to_model("""
            function f(x, y) -> z {
                if x {
                    switch y
                    case 1 { z := 7 }
                    default { z := 9 }
                }
            }
        """)
        rf = self._to_restricted("""function f(x, y) -> z {
                if x { switch y case 1 { z := 7 } default { z := 9 } }
            }""")
        for x, y in [(0, 0), (0, 1), (1, 0), (1, 1), (3, 1)]:
            rest_val = evaluate_restricted(rf, (x, y))
            model_val = evaluate_function_model(model, (x, y))
            self.assertEqual(rest_val, model_val, f"Mismatch at x={x}, y={y}")

    def test_nested_conditional_both_branches(self) -> None:
        """Nested conditionals in BOTH then and else branches."""
        model = self._to_model("""
            function f(x, y) -> z {
                switch x
                case 0 {
                    if y { z := 10 }
                }
                default {
                    if y { z := 20 }
                }
            }
        """)
        rf = self._to_restricted("""
            function f(x, y) -> z {
                switch x
                case 0 { if y { z := 10 } }
                default { if y { z := 20 } }
            }
        """)
        for x, y in [(0, 0), (0, 1), (1, 0), (1, 1), (2, 1)]:
            rest_val = evaluate_restricted(rf, (x, y))
            model_val = evaluate_function_model(model, (x, y))
            self.assertEqual(rest_val, model_val, f"Mismatch at x={x}, y={y}")

    def test_ssa_collision(self) -> None:
        """SSA allocator must not alias x_1 (from SSA) with literal x_1."""
        model = self._to_model("""
            function f(x) -> z {
                x := add(x, 1)
                let x_1 := 7
                z := x
            }
        """)
        # z should be x+1, NOT 7.
        for x in [0, 5, 100]:
            self.assertEqual(
                evaluate_function_model(model, (x,)),
                ((x + 1) % (2**256),),
                f"SSA collision at x={x}: got {evaluate_function_model(model, (x,))}",
            )

    def test_invalid_name_sanitization(self) -> None:
        """Compiler-generated names like var_x_1 and usr$tmp must be legalized."""
        model = self._to_model(
            "function fun_f_1(var_x_1) -> var_z_2 "
            "{ let usr$tmp := add(var_x_1, 1) var_z_2 := usr$tmp }",
            fn_name="f",
        )
        # Must pass validation (no invalid binder names).
        validate_function_model(model)
        # Must evaluate correctly.
        self.assertEqual(evaluate_function_model(model, (5,)), (6,))

    def test_demangle_collision(self) -> None:
        """Two variables that demangle to the same base name stay distinct."""
        # var_a_1 and var_a_2 both demangle to "a" — should still eval correctly.
        model = self._to_model(
            "function fun_f_1(var_a_1) -> var_z_2 "
            "{ let var_a_2 := add(var_a_1, 10) var_z_2 := add(var_a_1, var_a_2) }",
            fn_name="f",
        )
        validate_function_model(model)
        # a=5: a_2=15, z=5+15=20
        self.assertEqual(evaluate_function_model(model, (5,)), (20,))

    def test_nested_conditional_preserved(self) -> None:
        """Nested ConditionalBlock must survive in model branches."""
        model = self._to_model("""
            function f(x) -> z {
                if x { if add(x, 1) { z := 7 } }
            }
        """)
        outer_conds = [s for s in model.assignments if isinstance(s, ConditionalBlock)]
        self.assertTrue(outer_conds, "Expected outer ConditionalBlock")
        outer = outer_conds[0]
        nested = [
            s for s in outer.then_branch.assignments if isinstance(s, ConditionalBlock)
        ]
        self.assertTrue(nested, "Expected nested ConditionalBlock in then-branch")

    def test_all_binders_valid(self) -> None:
        """Every produced binder must pass validate_ident."""
        for yul in [
            "function f(x) -> z { if x { if add(x, 1) { z := 7 } } }",
            "function fun_f_1(var_x_1) -> var_z_2 "
            "{ let usr$tmp := add(var_x_1, 1) var_z_2 := usr$tmp }",
        ]:
            model = self._to_model(yul, fn_name="f")
            # validate_function_model checks all binders via validate_ident.
            validate_function_model(model)

    def _to_restricted(self, yul: str) -> RestrictedFunction:
        """Full pipeline: Yul → RestrictedFunction."""
        tokens = tokenize_yul(yul)
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func, builtins=EVM_BUILTINS)
        nf = normalize_function(func, result)
        nf = inline_pure_helpers(nf)
        nf = propagate_constants(nf)
        return lower_to_restricted(lower_memory(nf))

    def _module_to_models(
        self,
        yul: str,
        selected: tuple[str, ...],
        *,
        exact_yul_names: dict[str, str] | None = None,
    ) -> dict[str, FunctionModel]:
        """Public staged path: multi-function Yul → model table."""
        result = translate_yul_to_models(
            yul,
            make_model_config(selected, exact_yul_names=exact_yul_names),
            optimize=False,
        )
        return build_model_table(result)

    # ------------------------------------------------------------------
    # Flattening, callee naming, and Lean-emission boundary coverage.
    # ------------------------------------------------------------------

    def test_nested_untaken_branch_model_call(self) -> None:
        """Untaken branch with model call must not be eagerly evaluated."""
        models = self._module_to_models(
            """
            function good() -> r { r := 7 }
            function f(x, y) -> z {
                if x {
                    if y { z := good() }
                    z := good()
                }
            }
        """,
            ("f", "good"),
            exact_yul_names={"f": "f", "good": "good"},
        )
        # f(1, 0): outer if taken, inner if NOT taken, z := good() = 7
        self.assertEqual(
            evaluate_function_model(models["f"], (1, 0), model_table=models),
            (7,),
        )
        # f(0, 1): outer if not taken, z = 0
        self.assertEqual(
            evaluate_function_model(models["f"], (0, 1), model_table=models),
            (0,),
        )

    def test_nested_model_call_both_branches(self) -> None:
        """Model calls in both nested branches must eval correctly."""
        models = self._module_to_models(
            """
            function g() -> r { r := 10 }
            function h() -> r { r := 20 }
            function f(x, y) -> z {
                if x {
                    switch y
                    case 0 { z := g() }
                    default { z := h() }
                }
            }
        """,
            ("f", "g", "h"),
            exact_yul_names={"f": "f", "g": "g", "h": "h"},
        )
        self.assertEqual(
            evaluate_function_model(models["f"], (1, 0), model_table=models),
            (10,),
        )
        self.assertEqual(
            evaluate_function_model(models["f"], (1, 1), model_table=models),
            (20,),
        )
        self.assertEqual(
            evaluate_function_model(models["f"], (0, 0), model_table=models),
            (0,),
        )

    def test_compiler_style_callee_names(self) -> None:
        """Compiler-generated function names are demangled for model calls."""
        models = self._module_to_models(
            """
            function fun_g_1(var_x_1) -> var_z_2 {
                var_z_2 := add(var_x_1, 1)
            }
            function fun_f_2(var_a_1) -> var_b_2 {
                var_b_2 := fun_g_1(var_a_1)
            }
        """,
            ("f", "g"),
        )
        self.assertIn("f", models)
        self.assertIn("g", models)
        # f calls g; g(5) = 6
        self.assertEqual(
            evaluate_function_model(models["f"], (5,), model_table=models),
            (6,),
        )
        # All models must pass validation.
        for m in models.values():
            validate_function_model(m)

    def test_reserved_lean_name_is_checked_at_emission(self) -> None:
        """Lean-reserved binders remain valid model names until emission."""
        model = self._to_model(
            "function fun_f_1(var_x_1) -> var_z_2 "
            "{ let usr$u256 := add(var_x_1, 1) var_z_2 := usr$u256 }",
            fn_name="f",
        )
        validate_function_model(model)
        self.assertEqual(evaluate_function_model(model, (5,)), (6,))
        binders: list[str] = []
        for s in model.assignments:
            if isinstance(s, Assignment):
                binders.append(s.target)
        self.assertIn("u256", binders)

        config = make_model_config(("f",))
        with self.assertRaises(ParseError):
            build_lean_source(
                models=[model],
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    # ------------------------------------------------------------------
    # Branch-local hoisting behavior
    # ------------------------------------------------------------------

    def test_hoist_does_not_pull_call_from_nested_branch(self) -> None:
        """Hoisting must not pull model calls out of untaken nested branches."""
        # bad() is recursive — evaluating it diverges. It appears twice
        # inside a nested branch (if b), but the test evaluates at b=0
        # so that branch is never taken.
        bad_model = FunctionModel(
            fn_name="bad",
            param_names=("a",),
            return_names=("r",),
            assignments=(Assignment("r", Call("bad", (Var("a"),))),),
        )
        good_model = FunctionModel(
            fn_name="good",
            param_names=(),
            return_names=("r",),
            assignments=(Assignment("r", IntLit(7)),),
        )
        # f(a, b) -> z: if a { if b { z := add(bad(a), bad(a)) } z := good() }
        f_model = FunctionModel(
            fn_name="f",
            param_names=("a", "b"),
            return_names=("z_2",),
            assignments=(
                Assignment("z", IntLit(0)),
                ConditionalBlock(
                    condition=Var("a"),
                    output_vars=("z_2",),
                    then_branch=ConditionalBranch(
                        assignments=(
                            ConditionalBlock(
                                condition=Var("b"),
                                output_vars=("z_1",),
                                then_branch=ConditionalBranch(
                                    assignments=(
                                        Assignment(
                                            "z_1",
                                            Call(
                                                "add",
                                                (
                                                    Call("bad", (Var("a"),)),
                                                    Call("bad", (Var("a"),)),
                                                ),
                                            ),
                                        ),
                                    ),
                                    outputs=(Var("z_1"),),
                                ),
                                else_branch=ConditionalBranch(
                                    assignments=(),
                                    outputs=(Var("z"),),
                                ),
                            ),
                            Assignment("z_2", Call("good", ())),
                        ),
                        outputs=(Var("z_2"),),
                    ),
                    else_branch=ConditionalBranch(
                        assignments=(),
                        outputs=(Var("z"),),
                    ),
                ),
            ),
        )
        table = build_model_table([bad_model, good_model, f_model])
        # Before hoisting: (1, 0) → (7,) because inner branch is skipped.
        self.assertEqual(
            evaluate_function_model(f_model, (1, 0), model_table=table),
            (7,),
        )
        # After hoisting: must still be (7,), not diverge.
        hoisted = hoist_repeated_model_calls(
            f_model, model_call_names=frozenset({"bad", "good"})
        )
        self.assertEqual(
            evaluate_function_model(hoisted, (1, 0), model_table=table),
            (7,),
        )

    def test_hoist_does_not_pull_call_across_conditional(self) -> None:
        """Model call appearing once in then and once in else must not hoist above if."""
        inner_model = FunctionModel(
            fn_name="inner",
            param_names=("x",),
            return_names=("r",),
            assignments=(Assignment("r", Call("add", (Var("x"), IntLit(1)))),),
        )
        # f(x) -> z: if x { z := inner(x) } else { z := inner(x) }
        # inner(x) depends only on params, appears in both branches.
        # Hoist must NOT move it above the if (would change semantics for
        # model calls that might fail/diverge).
        f_model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                ConditionalBlock(
                    condition=Var("x"),
                    output_vars=("z",),
                    then_branch=ConditionalBranch(
                        assignments=(Assignment("z", Call("inner", (Var("x"),))),),
                        outputs=(Var("z"),),
                    ),
                    else_branch=ConditionalBranch(
                        assignments=(Assignment("z", Call("inner", (Var("x"),))),),
                        outputs=(Var("z"),),
                    ),
                ),
            ),
        )
        hoisted = hoist_repeated_model_calls(
            f_model, model_call_names=frozenset({"inner"})
        )
        # The call must NOT be hoisted to a top-level _cse assignment.
        top_level_cse = [
            s
            for s in hoisted.assignments
            if isinstance(s, Assignment) and s.target.startswith("_cse")
        ]
        self.assertFalse(
            top_level_cse, "inner(x) was incorrectly hoisted above conditional"
        )
        # Eval equivalence must still hold.
        table = build_model_table([inner_model, f_model])
        for x in [0, 1, 5]:
            self.assertEqual(
                evaluate_function_model(f_model, (x,), model_table=table),
                evaluate_function_model(hoisted, (x,), model_table=table),
            )

    def test_hoist_still_works_for_top_level_repeated_calls(self) -> None:
        """Repeated model call at top level must still be hoisted."""
        inner_model = FunctionModel(
            fn_name="inner",
            param_names=("x",),
            return_names=("r",),
            assignments=(
                Assignment(
                    "r",
                    Call(
                        "add",
                        (Call("mul", (Var("x"), Var("x"))), IntLit(1)),
                    ),
                ),
            ),
        )
        # z := add(inner(x), inner(x)) — repeated at top level.
        f_model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                Assignment(
                    "z",
                    Call(
                        "add",
                        (
                            Call("inner", (Var("x"),)),
                            Call("inner", (Var("x"),)),
                        ),
                    ),
                ),
            ),
        )
        hoisted = hoist_repeated_model_calls(
            f_model, model_call_names=frozenset({"inner"})
        )
        # There should be a top-level _cse assignment.
        cse_assigns = [
            s
            for s in hoisted.assignments
            if isinstance(s, Assignment) and s.target.startswith("_cse")
        ]
        self.assertTrue(cse_assigns, "Top-level repeated call was not hoisted")
        # Eval equivalence.
        table = build_model_table([inner_model, f_model])
        for x in [0, 1, 5]:
            self.assertEqual(
                evaluate_function_model(f_model, (x,), model_table=table),
                evaluate_function_model(hoisted, (x,), model_table=table),
            )

    # ------------------------------------------------------------------
    # Module-level API (to_function_models)
    # ------------------------------------------------------------------

    def test_module_api_compiler_style_names(self) -> None:
        """to_function_models must handle compiler-style names without external map."""
        from restricted_to_model import to_function_models

        tokens = tokenize_yul("""
            function fun_g_1(var_x_1) -> var_z_2 {
                var_z_2 := add(var_x_1, 1)
            }
            function fun_f_2(var_a_1) -> var_b_2 {
                var_b_2 := fun_g_1(var_a_1)
            }
        """)
        funcs = SyntaxParser(tokens).parse_functions()
        resolved = resolve_module(funcs, builtins=EVM_BUILTINS)
        restricted: dict[str, RestrictedFunction] = {}
        for name, result in resolved.items():
            nf = normalize_function(result.func, result)
            nf = inline_pure_helpers(nf)
            nf = propagate_constants(nf)
            restricted[name] = lower_to_restricted(lower_memory(nf))
        models = to_function_models(restricted)
        self.assertIn("f", models)
        self.assertIn("g", models)
        # f calls g; g(5) = 6
        self.assertEqual(
            evaluate_function_model(models["f"], (5,), model_table=models),
            (6,),
        )
        for m in models.values():
            validate_function_model(m)

    def test_module_api_callee_invariant(self) -> None:
        """Every non-builtin call in a module's models must be a module function."""
        from restricted_to_model import to_function_models

        tokens = tokenize_yul("""
            function fun_g_1(var_x_1) -> var_z_2 {
                var_z_2 := add(var_x_1, 1)
            }
            function fun_f_2(var_a_1) -> var_b_2 {
                var_b_2 := fun_g_1(var_a_1)
            }
        """)
        funcs = SyntaxParser(tokens).parse_functions()
        resolved = resolve_module(funcs, builtins=EVM_BUILTINS)
        restricted: dict[str, RestrictedFunction] = {}
        for name, result in resolved.items():
            nf = normalize_function(result.func, result)
            nf = inline_pure_helpers(nf)
            nf = propagate_constants(nf)
            restricted[name] = lower_to_restricted(lower_memory(nf))
        models = to_function_models(restricted)
        model_names = set(models.keys())
        # Collect all non-builtin call names from all models.
        for model in models.values():
            for op in collect_model_opcodes([model]):
                # opcodes are builtins — skip
                pass
            for stmt in model.assignments:
                self._check_calls_in_stmt(stmt, model_names)

    def _check_calls_in_stmt(self, stmt: ModelStatement, model_names: set[str]) -> None:
        if isinstance(stmt, Assignment):
            self._check_calls_in_expr(stmt.expr, model_names)
        elif isinstance(stmt, ConditionalBlock):
            self._check_calls_in_expr(stmt.condition, model_names)
            for s in stmt.then_branch.assignments:
                self._check_calls_in_stmt(s, model_names)
            for s in stmt.else_branch.assignments:
                self._check_calls_in_stmt(s, model_names)
            for expr in stmt.then_branch.outputs:
                self._check_calls_in_expr(expr, model_names)
            for expr in stmt.else_branch.outputs:
                self._check_calls_in_expr(expr, model_names)

    def _check_calls_in_expr(self, expr: Expr, model_names: set[str]) -> None:
        if isinstance(expr, Call):
            if expr.name not in OP_TO_LEAN_HELPER:
                self.assertIn(
                    expr.name,
                    model_names,
                    f"Non-builtin call {expr.name!r} not in module function set",
                )
            for a in expr.args:
                self._check_calls_in_expr(a, model_names)
        elif isinstance(expr, Ite):
            self._check_calls_in_expr(expr.cond, model_names)
            self._check_calls_in_expr(expr.if_true, model_names)
            self._check_calls_in_expr(expr.if_false, model_names)
        elif isinstance(expr, Project):
            self._check_calls_in_expr(expr.inner, model_names)

    # ------------------------------------------------------------------
    # Expression-valued branch outputs
    # ------------------------------------------------------------------

    def test_branch_output_const(self) -> None:
        """Branch output_exprs can be RConst, not just RRef."""
        from restricted_ir import (
            RAssignment,
            RBranch,
            RConditionalBlock,
            RConst,
            RRef,
        )

        x_sid, z_sid = yul_ast.SymbolId(0), yul_ast.SymbolId(1)
        rf = RestrictedFunction(
            name="f",
            params=(x_sid,),
            param_names=("x",),
            returns=(z_sid,),
            return_names=("z",),
            body=(
                RConditionalBlock(
                    condition=RRef(symbol_id=x_sid, name="x"),
                    output_targets=(z_sid,),
                    output_names=("z",),
                    then_branch=RBranch(
                        assignments=(),
                        output_exprs=(RConst(7),),  # NOT RRef
                    ),
                    else_branch=RBranch(
                        assignments=(),
                        output_exprs=(RConst(0),),  # NOT RRef
                    ),
                ),
            ),
        )
        model = to_function_models({rf.name: rf})["f"]
        for x in [0, 1, 5]:
            self.assertEqual(
                evaluate_restricted(rf, (x,)),
                evaluate_function_model(model, (x,)),
                f"Mismatch at x={x}",
            )

    def test_branch_output_builtin_call(self) -> None:
        """Branch output_exprs can be RBuiltinCall."""
        from restricted_ir import (
            RBranch,
            RBuiltinCall,
            RConditionalBlock,
            RConst,
            RRef,
        )

        x_sid, z_sid = yul_ast.SymbolId(0), yul_ast.SymbolId(1)
        rf = RestrictedFunction(
            name="f",
            params=(x_sid,),
            param_names=("x",),
            returns=(z_sid,),
            return_names=("z",),
            body=(
                RConditionalBlock(
                    condition=RRef(symbol_id=x_sid, name="x"),
                    output_targets=(z_sid,),
                    output_names=("z",),
                    then_branch=RBranch(
                        assignments=(),
                        output_exprs=(
                            RBuiltinCall(
                                "add", (RRef(symbol_id=x_sid, name="x"), RConst(1))
                            ),
                        ),
                    ),
                    else_branch=RBranch(
                        assignments=(),
                        output_exprs=(RConst(0),),
                    ),
                ),
            ),
        )
        model = to_function_models({rf.name: rf})["f"]
        for x in [0, 1, 5]:
            self.assertEqual(
                evaluate_restricted(rf, (x,)),
                evaluate_function_model(model, (x,)),
                f"Mismatch at x={x}",
            )

    def test_nested_conditional_with_expr_output(self) -> None:
        """Inner branch with expression output, outer with ref output."""
        from restricted_ir import (
            RAssignment,
            RBranch,
            RBuiltinCall,
            RConditionalBlock,
            RConst,
            RRef,
        )

        x_sid = yul_ast.SymbolId(0)
        y_sid = yul_ast.SymbolId(1)
        z_sid = yul_ast.SymbolId(2)
        z2_sid = yul_ast.SymbolId(3)
        rf = RestrictedFunction(
            name="f",
            params=(x_sid, y_sid),
            param_names=("x", "y"),
            returns=(z_sid,),
            return_names=("z",),
            body=(
                RConditionalBlock(
                    condition=RRef(symbol_id=x_sid, name="x"),
                    output_targets=(z_sid,),
                    output_names=("z",),
                    then_branch=RBranch(
                        assignments=(
                            RConditionalBlock(
                                condition=RRef(symbol_id=y_sid, name="y"),
                                output_targets=(z2_sid,),
                                output_names=("z",),
                                then_branch=RBranch(
                                    assignments=(),
                                    output_exprs=(
                                        RBuiltinCall(
                                            "add",
                                            (
                                                RRef(symbol_id=x_sid, name="x"),
                                                RRef(symbol_id=y_sid, name="y"),
                                            ),
                                        ),
                                    ),
                                ),
                                else_branch=RBranch(
                                    assignments=(),
                                    output_exprs=(RConst(99),),
                                ),
                            ),
                        ),
                        output_exprs=(RRef(symbol_id=z2_sid, name="z"),),
                    ),
                    else_branch=RBranch(
                        assignments=(),
                        output_exprs=(RConst(0),),
                    ),
                ),
            ),
        )
        model = to_function_models({rf.name: rf})["f"]
        for x, y in [(0, 0), (0, 1), (1, 0), (1, 1), (3, 5)]:
            self.assertEqual(
                evaluate_restricted(rf, (x, y)),
                evaluate_function_model(model, (x, y)),
                f"Mismatch at x={x}, y={y}",
            )

    def test_validate_selected_models_rejects_branch_output_cycle(self) -> None:
        """Cross-model validation must inspect calls that appear only in branch outputs."""
        model = FunctionModel(
            fn_name="f",
            param_names=("p",),
            return_names=("out",),
            assignments=(
                Assignment("out", IntLit(0)),
                ConditionalBlock(
                    condition=Var("p"),
                    output_vars=("out",),
                    then_branch=ConditionalBranch(
                        assignments=(),
                        outputs=(Call("f", (Var("p"),)),),
                    ),
                    else_branch=ConditionalBranch(
                        assignments=(),
                        outputs=(IntLit(0),),
                    ),
                ),
            ),
        )
        with self.assertRaisesRegex(ParseError, "Cycle detected"):
            validate_model_set([model])

    def test_validate_selected_models_rejects_unresolved_branch_output_call(
        self,
    ) -> None:
        """Cross-model validation must reject unresolved calls in branch outputs."""
        model = FunctionModel(
            fn_name="f",
            param_names=("p",),
            return_names=("out",),
            assignments=(
                Assignment("out", IntLit(0)),
                ConditionalBlock(
                    condition=Var("p"),
                    output_vars=("out",),
                    then_branch=ConditionalBranch(
                        assignments=(),
                        outputs=(Call("missing", (Var("p"),)),),
                    ),
                    else_branch=ConditionalBranch(
                        assignments=(),
                        outputs=(IntLit(0),),
                    ),
                ),
            ),
        )
        with self.assertRaisesRegex(ParseError, "unresolved call target"):
            validate_model_set([model])

    def test_validate_selected_models_rejects_multi_return_branch_output_scalar_use(
        self,
    ) -> None:
        """Branch outputs in scalar context must not hide tuple-returning model calls."""
        callee = FunctionModel(
            fn_name="g",
            param_names=("x",),
            return_names=("a", "b"),
            assignments=(
                Assignment("a", Var("x")),
                Assignment("b", IntLit(1)),
            ),
        )
        model = FunctionModel(
            fn_name="f",
            param_names=("p",),
            return_names=("out",),
            assignments=(
                Assignment("out", IntLit(0)),
                ConditionalBlock(
                    condition=Var("p"),
                    output_vars=("out",),
                    then_branch=ConditionalBranch(
                        assignments=(),
                        outputs=(Call("g", (Var("p"),)),),
                    ),
                    else_branch=ConditionalBranch(
                        assignments=(),
                        outputs=(IntLit(0),),
                    ),
                ),
            ),
        )
        with self.assertRaisesRegex(ParseError, "multi-return function"):
            validate_model_set([model, callee])

    def test_collect_model_opcodes_includes_branch_output_exprs(self) -> None:
        """Builtin calls used only in branch outputs must still count as used opcodes."""
        model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("out",),
            assignments=(
                Assignment("out", IntLit(0)),
                ConditionalBlock(
                    condition=Var("x"),
                    output_vars=("out",),
                    then_branch=ConditionalBranch(
                        assignments=(),
                        outputs=(Call("clz", (Var("x"),)),),
                    ),
                    else_branch=ConditionalBranch(
                        assignments=(),
                        outputs=(IntLit(0),),
                    ),
                ),
            ),
        )
        expected_ops: list[str] = [OP_TO_OPCODE["clz"]]
        self.assertEqual(collect_model_opcodes([model]), expected_ops)

    # ------------------------------------------------------------------
    # Positive branch-local hoist
    # ------------------------------------------------------------------

    def test_branch_local_hoist_sibling_stmts(self) -> None:
        """Repeated model call across sibling stmts in same branch gets CSE'd."""
        inner = FunctionModel(
            fn_name="inner",
            param_names=("x",),
            return_names=("r",),
            assignments=(Assignment("r", Call("add", (Var("x"), IntLit(1)))),),
        )
        # f(p) -> out: if p { a := inner(p); b := inner(p); out := add(a,b) }
        f_model = FunctionModel(
            fn_name="f",
            param_names=("p",),
            return_names=("out",),
            assignments=(
                Assignment("out", IntLit(0)),
                ConditionalBlock(
                    condition=Var("p"),
                    output_vars=("out",),
                    then_branch=ConditionalBranch(
                        assignments=(
                            Assignment("a", Call("inner", (Var("p"),))),
                            Assignment("b", Call("inner", (Var("p"),))),
                            Assignment(
                                "out",
                                Call("add", (Var("a"), Var("b"))),
                            ),
                        ),
                        outputs=(Var("out"),),
                    ),
                    else_branch=ConditionalBranch(
                        assignments=(),
                        outputs=(Var("out"),),
                    ),
                ),
            ),
        )
        hoisted = hoist_repeated_model_calls(
            f_model, model_call_names=frozenset({"inner"})
        )
        # The _cse should be INSIDE the then-branch, not at top level.
        top_cse = [
            s
            for s in hoisted.assignments
            if isinstance(s, Assignment) and s.target.startswith("_cse")
        ]
        self.assertFalse(top_cse, "CSE incorrectly hoisted to top level")
        # Find CSE inside then-branch.
        cond_blocks = [
            s for s in hoisted.assignments if isinstance(s, ConditionalBlock)
        ]
        self.assertTrue(cond_blocks)
        then_cse = [
            s
            for s in cond_blocks[0].then_branch.assignments
            if isinstance(s, Assignment) and s.target.startswith("_cse")
        ]
        self.assertTrue(then_cse, "Expected branch-local CSE inside then-branch")
        # Eval equivalence.
        table = build_model_table([inner, f_model])
        for p in [0, 1, 5]:
            self.assertEqual(
                evaluate_function_model(f_model, (p,), model_table=table),
                evaluate_function_model(hoisted, (p,), model_table=table),
            )

    def test_hoist_projected_model_call_top_level(self) -> None:
        """Repeated projected model calls should still be hoisted."""
        f_model = FunctionModel(
            fn_name="f",
            param_names=("x",),
            return_names=("z",),
            assignments=(
                Assignment(
                    "z",
                    Call(
                        "add",
                        (
                            Project(
                                0,
                                2,
                                Call("g", (Var("x"),)),
                            ),
                            Project(
                                0,
                                2,
                                Call("g", (Var("x"),)),
                            ),
                        ),
                    ),
                ),
            ),
        )
        hoisted = hoist_repeated_model_calls(f_model, model_call_names=frozenset({"g"}))
        cse_assigns = [
            s
            for s in hoisted.assignments
            if isinstance(s, Assignment) and s.target.startswith("_cse")
        ]
        self.assertTrue(cse_assigns, "Projected model call was not hoisted")

    # ------------------------------------------------------------------
    # ModuleNamePlan
    # ------------------------------------------------------------------

    def test_name_plan_uniqueness(self) -> None:
        """ModuleNamePlan produces unique, valid names for colliding demangles."""
        from restricted_names import plan_module

        # Two functions that demangle to the same clean name.
        rf_dummy = RestrictedFunction(
            name="dummy",
            params=(),
            param_names=(),
            returns=(yul_ast.SymbolId(0),),
            return_names=("r",),
            body=(),
        )
        funcs = {"fun_f_1": rf_dummy, "fun_f_2": rf_dummy}
        plan = plan_module(funcs)
        names = list(plan.function_names.values())
        self.assertEqual(len(names), len(set(names)), f"Duplicate names: {names}")
        for n in names:
            validate_ident(n, what="planned function name")

    def test_name_plan_binder_uniqueness(self) -> None:
        """ModuleNamePlan must uniquify colliding binder base names too."""
        from restricted_ir import RAssignment, RConst
        from restricted_names import plan_module

        x_sid, z_sid, local_sid = (
            yul_ast.SymbolId(10),
            yul_ast.SymbolId(11),
            yul_ast.SymbolId(12),
        )
        rf = RestrictedFunction(
            name="f",
            params=(x_sid,),
            param_names=("var_x_1",),
            returns=(z_sid,),
            return_names=("var_z_2",),
            body=(
                RAssignment(
                    target=local_sid,
                    target_name="usr$x",
                    expr=RConst(1),
                ),
            ),
        )
        plan = plan_module({"fun_f_1": rf})
        names = list(plan.binder_names["fun_f_1"].values())
        self.assertEqual(
            len(names), len(set(names)), f"Duplicate binder names: {names}"
        )
        for n in names:
            validate_ident(n, what="planned binder name")

    def test_name_plan_binder_preserves_generic_base_name(self) -> None:
        """ModuleNamePlan stays generic and leaves Lean checks to emission."""
        from restricted_ir import RAssignment, RBuiltinCall, RConst, RRef
        from restricted_names import plan_module

        x_sid, z_sid, u_sid = (
            yul_ast.SymbolId(0),
            yul_ast.SymbolId(1),
            yul_ast.SymbolId(2),
        )
        rf = RestrictedFunction(
            name="f",
            params=(x_sid,),
            param_names=("x",),
            returns=(z_sid,),
            return_names=("z",),
            body=(
                RAssignment(
                    target=u_sid,
                    target_name="u256",
                    expr=RBuiltinCall(
                        "add", (RRef(symbol_id=x_sid, name="x"), RConst(1))
                    ),
                ),
                RAssignment(
                    target=z_sid,
                    target_name="z",
                    expr=RRef(symbol_id=u_sid, name="u256"),
                ),
            ),
        )
        plan = plan_module({"f": rf})
        self.assertIn("u256", plan.binder_names["f"].values())


class StagedPipelineWiringTest(unittest.TestCase):
    """Tests that translate_yul_to_models uses the staged pipeline."""

    NESTED_IF_YUL = """
        function fun_f_1(var_x_1) -> var_z_2 {
            if var_x_1 {
                if add(var_x_1, 1) { var_z_2 := 7 }
            }
        }
    """
    NESTED_IF_CONFIG = make_model_config(("f",))

    MULTI_FN_YUL = """
        function fun_g_1(var_x_1) -> var_z_2 {
            var_z_2 := add(var_x_1, 1)
        }
        function fun_f_2(var_a_1) -> var_b_2 {
            var_b_2 := fun_g_1(var_a_1)
        }
    """

    def test_production_path_produces_recursive_branches(self) -> None:
        """translate_yul_to_models preserves nested ConditionalBlock branches."""
        result = translate_yul_to_models(
            self.NESTED_IF_YUL,
            self.NESTED_IF_CONFIG,
        )
        model = result[0]
        # Find nested ConditionalBlock inside a branch.
        found_nested = False
        for stmt in model.assignments:
            if isinstance(stmt, ConditionalBlock):
                for s in stmt.then_branch.assignments:
                    if isinstance(s, ConditionalBlock):
                        found_nested = True
        self.assertTrue(
            found_nested,
            "Expected nested ConditionalBlock in branch",
        )

    def test_production_path_valid_and_evaluable(self) -> None:
        """Models from translate_yul_to_models must validate and evaluate."""
        result = translate_yul_to_models(
            self.NESTED_IF_YUL,
            self.NESTED_IF_CONFIG,
        )
        model = result[0]
        validate_function_model(model)
        self.assertEqual(evaluate_function_model(model, (0,)), (0,))
        self.assertEqual(evaluate_function_model(model, (1,)), (7,))

    def test_production_path_lean_emission(self) -> None:
        """translate_yul_to_models + build_lean_source must succeed."""
        result = translate_yul_to_models(
            self.NESTED_IF_YUL,
            self.NESTED_IF_CONFIG,
        )
        lean_src = build_lean_source(
            models=result,
            source_path="test",
            namespace="Test",
            config=self.NESTED_IF_CONFIG,
        )
        self.assertIn("model_f", lean_src)

    def test_production_path_function_selection(self) -> None:
        """translate_yul_to_models selects only config.function_order."""
        config = make_model_config(("f",))
        result = translate_yul_to_models(
            self.MULTI_FN_YUL,
            config,
        )
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0].fn_name, "f")

    def test_production_path_multi_function_with_calls(self) -> None:
        """translate_yul_to_models with multiple selected functions and calls."""
        config = make_model_config(("g", "f"))
        result = translate_yul_to_models(
            self.MULTI_FN_YUL,
            config,
        )
        self.assertEqual(len(result), 2)
        names: list[str] = [m.fn_name for m in result]
        expected_names: list[str] = ["g", "f"]
        self.assertEqual(names, expected_names)
        table = build_model_table(result)
        self.assertEqual(
            evaluate_function_model(result[1], (5,), model_table=table),
            (6,),
        )


class StagedPipelineEmbedTest(unittest.TestCase):
    """Tests that the staged pipeline internalizes non-selected helpers.

    These tests verify that when ``config.function_order`` selects only a
    subset of the module, the non-selected helpers are internal to the
    selected targets and are handled by the staged inline plan rather than
    by emitting extra standalone models.
    """

    # -- target calls a simple pure helper (not selected) --
    HELPER_INLINE_YUL = """
        function fun_target_1(var_x_1) -> var_z_2 {
            var_z_2 := helper(var_x_1)
        }
        function helper(var_a_3) -> var_r_4 {
            var_r_4 := add(var_a_3, 42)
        }
    """

    def test_non_selected_helper_inlined_into_target(self) -> None:
        """Helper not in function_order is inlined; model evaluates standalone."""
        config = make_model_config(("target",))
        result = translate_yul_to_models(
            self.HELPER_INLINE_YUL,
            config,
            optimize=False,
        )
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0].fn_name, "target")
        self.assertEqual(evaluate_function_model(result[0], (10,)), (52,))

    # -- target calls helper-with-leave (not selected) --
    LEAVE_HELPER_YUL = """
        function fun_target_1(var_x_1) -> var_z_2 {
            var_z_2 := helper(var_x_1)
        }
        function helper(var_x_3) -> var_z_4 {
            var_z_4 := 1
            if var_x_3 {
                var_z_4 := 7
                leave
            }
            var_z_4 := 9
        }
    """

    def test_leave_in_non_selected_helper_inlined(self) -> None:
        """Helper with ``leave`` is block-inlined via did_leave semantics."""
        config = make_model_config(("target",))
        result = translate_yul_to_models(
            self.LEAVE_HELPER_YUL,
            config,
            optimize=False,
        )
        model = result[0]
        # x=0: condition false → z=9 (fall through past leave)
        self.assertEqual(evaluate_function_model(model, (0,)), (9,))
        # x=1: condition true → z=7 (leave skips z=9)
        self.assertEqual(evaluate_function_model(model, (1,)), (7,))

    # -- transitive helper chain A→B (neither selected) --
    CHAIN_YUL = """
        function fun_target_1(var_x_1) -> var_z_2 {
            var_z_2 := helperA(var_x_1)
        }
        function helperA(var_a_3) -> var_r_4 {
            var_r_4 := helperB(add(var_a_3, 1))
        }
        function helperB(var_b_5) -> var_s_6 {
            var_s_6 := mul(var_b_5, 2)
        }
    """

    def test_transitive_helper_chain_inlined(self) -> None:
        """Transitive helper closure A→B both internalized and inlined."""
        config = make_model_config(("target",))
        result = translate_yul_to_models(
            self.CHAIN_YUL,
            config,
            optimize=False,
        )
        model = result[0]
        # target(3) = helperA(3) = helperB(4) = 4*2 = 8
        self.assertEqual(evaluate_function_model(model, (3,)), (8,))

    # -- helper with mstore/mload (memory resolved after inlining) --
    MEMORY_HELPER_YUL = """
        function fun_target_1(var_x_hi_1, var_x_lo_2) -> var_z_3 {
            let usr$ptr := fun_from_4(0, var_x_hi_1, var_x_lo_2)
            var_z_3 := add(mload(usr$ptr), mload(add(0x20, usr$ptr)))
        }
        function fun_from_4(var_r_5, var_hi_6, var_lo_7) -> var_r_out_8 {
            var_r_out_8 := 0
            mstore(var_r_5, var_hi_6)
            mstore(add(0x20, var_r_5), var_lo_7)
            var_r_out_8 := var_r_5
        }
    """

    def test_memory_helper_resolved_after_embed(self) -> None:
        """mstore/mload in helper resolved after embedding + inlining + constprop."""
        config = make_model_config(("target",))
        result = translate_yul_to_models(
            self.MEMORY_HELPER_YUL,
            config,
            optimize=False,
        )
        model = result[0]
        # target(5, 11) = mload(0)+mload(0x20) = 5+11 = 16
        self.assertEqual(evaluate_function_model(model, (5, 11)), (16,))

    def test_selected_sibling_remains_model_call_while_wrapper_inlines(self) -> None:
        """Selected helper stays a model call; non-selected wrapper does not."""
        yul = """
            function fun_target_0(var_x_1) -> var_z_2 {
                var_z_2 := wrapper(var_x_1)
            }
            function wrapper(var_a_3) -> var_r_4 {
                var_r_4 := helper(var_a_3)
            }
            function helper(var_b_5) -> var_s_6 {
                var_s_6 := add(var_b_5, 1)
            }
        """
        config = make_model_config(
            ("helper_model", "target"),
            exact_yul_names={
                "helper_model": "helper",
                "target": "fun_target_0",
            },
        )
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        table = build_model_table(result)
        target_model = table["target"]
        self.assertEqual(
            evaluate_function_model(target_model, (5,), model_table=table), (6,)
        )

        rendered = repr(target_model.assignments)
        self.assertIn("helper_model", rendered)
        self.assertNotIn("wrapper", rendered)

    def test_top_level_helper_dead_after_leave_cleanup_is_origin_independent(
        self,
    ) -> None:
        """Top-level helper cleanup matches the existing local-helper behavior."""
        yul = """
            function fun_target_0(var_x_1) -> var_z_2 {
                var_z_2 := helper(var_x_1)
            }
            function helper(var_x_3) -> var_z_4 {
                if var_x_3 {
                    var_z_4 := 7
                    leave
                    var_z_4 := 99
                }
                var_z_4 := 9
            }
        """
        config = make_model_config(("target",))
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        model = result[0]
        self.assertEqual(evaluate_function_model(model, (0,)), (9,))
        self.assertEqual(evaluate_function_model(model, (1,)), (7,))


class StagedPipelineSelectionTest(unittest.TestCase):
    """Tests for config-driven function selection in the staged pipeline."""

    # -- exact_yul_names selects among homonyms --
    HOMONYM_YUL = """
        function fun_pick_1(var_x_1) -> var_z_2 {
            var_z_2 := add(var_x_1, 100)
        }
        function fun_pick_2(var_x_3) -> var_z_4 {
            var_z_4 := sub(var_x_3, 1)
        }
    """

    def test_exact_yul_names_selects_correct_homonym(self) -> None:
        """exact_yul_names={'pick': 'fun_pick_2'} picks the second function."""
        config = make_model_config(("pick",), exact_yul_names={"pick": "fun_pick_2"})
        result = translate_yul_to_models(
            self.HOMONYM_YUL,
            config,
            optimize=False,
        )
        model = result[0]
        self.assertEqual(model.fn_name, "pick")
        # fun_pick_2: sub(x, 1) → pick(7) = 6
        self.assertEqual(evaluate_function_model(model, (7,)), (6,))

    # -- n_params disambiguates by arity --
    ARITY_YUL = """
        function fun_f_1(var_x_1) -> var_z_2 {
            var_z_2 := add(var_x_1, 1)
        }
        function fun_f_2(var_a_3, var_b_4) -> var_z_5 {
            var_z_5 := mul(var_a_3, var_b_4)
        }
    """

    def test_n_params_disambiguates_by_arity(self) -> None:
        """n_params={'f': 2} selects the two-parameter variant."""
        config = make_model_config(("f",), n_params={"f": 2})
        result = translate_yul_to_models(
            self.ARITY_YUL,
            config,
            optimize=False,
        )
        model = result[0]
        # fun_f_2: mul(a, b) → f(3, 4) = 12
        self.assertEqual(evaluate_function_model(model, (3, 4)), (12,))

    # -- multi-object: object-local helper scoping --
    MULTI_OBJECT_YUL = """
        object "A" {
            code {
                function fun_f_1() -> var_z_1 {
                    var_z_1 := helper()
                }
                function helper() -> var_r_2 {
                    var_r_2 := 1
                }
            }
        }
        object "B" {
            code {
                function helper() -> var_r_3 {
                    var_r_3 := 2
                }
            }
        }
    """

    def test_object_local_helper_scope(self) -> None:
        """Selecting f from object A resolves helper within A, not B."""
        config = make_model_config(("f",))
        result = translate_yul_to_models(
            self.MULTI_OBJECT_YUL,
            config,
            optimize=False,
        )
        model = result[0]
        # f calls object A's helper → 1, not object B's → 2
        self.assertEqual(evaluate_function_model(model, ()), (1,))

    def test_exact_selected_nested_target_inlines_disambiguating_helper(self) -> None:
        """A helper named only in the selected path is inlined, not emitted."""
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
                function target() -> var_t2_1 {
                    var_t2_1 := helper()
                }
                var_o2_1 := target()
            }
        """
        config = make_model_config(
            ("pick",),
            exact_yul_names={"pick": "fun_outer1_1::target"},
        )
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0].fn_name, "pick")
        self.assertEqual(evaluate_function_model(result[0], ()), (7,))
        self.assertNotIn("helper", repr(result[0].assignments))


class StagedPipelineValidationTest(unittest.TestCase):
    """Tests for pre-restricted validation in the staged pipeline."""

    def test_top_level_leave_handled(self) -> None:
        """leave in the selected target is lowered via did_leave semantics."""
        yul = """
            function fun_f_1(var_x_1) -> var_z_2 {
                var_z_2 := 1
                if var_x_1 { leave }
                var_z_2 := 2
            }
        """
        config = make_model_config(("f",))
        result = translate_yul_to_models(yul, config, optimize=False)
        model = result[0]
        # x=0: no leave → z=2
        self.assertEqual(evaluate_function_model(model, (0,)), (2,))
        # x=1: leave → z=1 (leave with current z value)
        self.assertEqual(evaluate_function_model(model, (1,)), (1,))

    def test_bare_expression_stmt_rejected(self) -> None:
        """Bare expression statement (non-memory side effect) is rejected."""
        yul = """
            function fun_f_1(var_x_1) -> var_z_2 {
                var_z_2 := helper(var_x_1, 3)
            }
            function helper(var_a_3, var_b_4) -> var_r_5 {
                side_effect()
                var_r_5 := div(var_a_3, var_b_4)
            }
        """
        config = make_model_config(("f",))
        with self.assertRaises(ParseError):
            translate_yul_to_models(yul, config, optimize=False)

    def test_dead_expression_stmt_eliminated_before_validation(self) -> None:
        """Dead bare expression statements are removed before the fail-closed boundary."""
        yul = """
            function fun_f_1(var_x_1) -> var_z_2 {
                if 0 {
                    side_effect()
                }
                var_z_2 := add(var_x_1, 1)
            }
        """
        config = make_model_config(("f",))
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        self.assertEqual(evaluate_function_model(result[0], (5,)), (6,))

    def test_reserved_lean_keyword_param_is_checked_at_emission(self) -> None:
        """Lean keywords stay valid until Lean emission runs."""
        yul = """
            function fun_f_1(var_if_1) -> var_z_2 {
                var_z_2 := var_if_1
            }
        """
        config = make_model_config(("f",))
        models = translate_yul_to_models(yul, config, optimize=False)
        with self.assertRaises(ParseError):
            build_lean_source(
                models=models,
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_zero_return_function_rejected(self) -> None:
        """Function with zero return values is rejected."""
        yul = """
            function fun_f_1(var_x_1) {
                mstore(0, var_x_1)
            }
        """
        config = make_model_config(("f",))
        with self.assertRaises(ParseError):
            translate_yul_to_models(yul, config, optimize=False)

    def test_dead_unresolved_call_eliminated_before_validation(self) -> None:
        """Dead unresolved calls are removed before the validation boundary."""
        yul = """
            function fun_f_1(var_x_1) -> var_z_2 {
                if 0 {
                    var_z_2 := missing(var_x_1)
                }
                var_z_2 := add(var_x_1, 1)
            }
        """
        config = make_model_config(("f",))
        result = translate_yul_to_models(yul, config, optimize=False)
        self.assertEqual(evaluate_function_model(result[0], (5,)), (6,))

    def test_live_unresolved_call_rejected_before_restricted_lowering(self) -> None:
        """Live unresolved calls fail at the explicit validation boundary."""
        yul = """
            function fun_f_1(var_x_1) -> var_z_2 {
                if var_x_1 {
                    var_z_2 := missing(var_x_1)
                }
                var_z_2 := 7
            }
        """
        config = make_model_config(("f",))
        with self.assertRaisesRegex(ParseError, "unresolved call"):
            translate_yul_to_models(yul, config, optimize=False)


class LeaveGuardGroupingTest(unittest.TestCase):
    """Tests that did_leave guards group trailing stmts into maximal blocks."""

    def test_block_inline_leave_temp_chain(self) -> None:
        """Block-inlined helper with leave + temp chain evaluates correctly."""
        yul = """
            function fun_target_1(var_x_1) -> var_r_2 {
                var_r_2 := helper(var_x_1)
            }
            function helper(var_x_3) -> var_r_4 {
                var_r_4 := 1
                if var_x_3 {
                    var_r_4 := 7
                    leave
                }
                let usr$t := var_r_4
                var_r_4 := add(usr$t, 1)
            }
        """
        config = make_model_config(("target",))
        result = translate_yul_to_models(yul, config, optimize=False)
        model = result[0]
        # x=0: no leave → r = 1, t = 1, r = 1+1 = 2
        self.assertEqual(evaluate_function_model(model, (0,)), (2,))
        # x=1: leave → r = 7 (leave skips the temp chain)
        self.assertEqual(evaluate_function_model(model, (1,)), (7,))

    def test_top_level_leave_temp_chain(self) -> None:
        """Selected target with leave + temp chain evaluates correctly."""
        yul = """
            function fun_f_1(var_x_1) -> var_r_2 {
                var_r_2 := 1
                if var_x_1 {
                    var_r_2 := 7
                    leave
                }
                let usr$t := var_r_2
                var_r_2 := add(usr$t, 1)
            }
        """
        config = make_model_config(("f",))
        result = translate_yul_to_models(yul, config, optimize=False)
        model = result[0]
        # x=0: no leave → r = 1, t = 1, r = 1+1 = 2
        self.assertEqual(evaluate_function_model(model, (0,)), (2,))
        # x=1: leave → r = 7
        self.assertEqual(evaluate_function_model(model, (1,)), (7,))

    def test_lower_leave_groups_trailing_stmts(self) -> None:
        """Trailing statements after leave share one guarded block, not N."""
        from norm_simplify import lower_leave

        from yul_normalize import normalize_function
        from yul_parser import SyntaxParser
        from yul_resolve import resolve_function

        tokens = tokenize_yul("""
            function fun_f_1(var_x_1) -> var_r_2 {
                var_r_2 := 1
                if var_x_1 { leave }
                let usr$a := 2
                let usr$b := 3
                var_r_2 := add(usr$a, usr$b)
            }
        """)
        func = SyntaxParser(tokens).parse_function()
        result = resolve_function(func)
        nf = normalize_function(func, result)
        lowered = lower_leave(nf)

        # Count top-level NIf nodes in the lowered body.
        from norm_ir import NIf

        top_ifs = [s for s in lowered.body.stmts if isinstance(s, NIf)]
        # Should have exactly 2 NIf: the original `if var_x_1 { ... }` and
        # ONE grouped guard `if iszero(did_leave) { a; b; r := add(a, b) }`.
        # NOT 3 separate guards (one per trailing statement).
        self.assertEqual(
            len(top_ifs),
            2,
            f"Expected 2 top-level NIf (original + 1 grouped guard), "
            f"got {len(top_ifs)}",
        )


class AdditionalBehaviorTest(unittest.TestCase):
    def test_translate_yul_to_models_string_literal_omits_quote_bytes(self) -> None:
        yul = """
            function fun_f_1() -> var_z_2 {
                var_z_2 := "AB"
            }
        """
        config = make_model_config(("f",))
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        expected = int.from_bytes(b"AB".ljust(32, b"\x00"), "big")
        self.assertEqual(
            evaluate_function_model(result[0], ()),
            (expected,),
        )

    def test_translate_yul_to_models_string_literal_decodes_escape_sequences(
        self,
    ) -> None:
        yul = r"""
            function fun_f_1() -> var_z_2 {
                var_z_2 := "A\n"
            }
        """
        config = make_model_config(("f",))
        result = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        expected = int.from_bytes(b"A\n".ljust(32, b"\x00"), "big")
        self.assertEqual(
            evaluate_function_model(result[0], ()),
            (expected,),
        )

    def test_missing_model_name_mapping_is_checked_at_emission(self) -> None:
        base = make_model_config(("f",))
        config = modelcfg.ModelConfig(
            function_order=base.function_order,
            model_names={},
            header_comment=base.header_comment,
            generator_label=base.generator_label,
            extra_norm_ops=base.extra_norm_ops,
            extra_lean_defs=base.extra_lean_defs,
            norm_rewrite=base.norm_rewrite,
            inner_fn=base.inner_fn,
            n_params=base.n_params,
            exact_yul_names=base.exact_yul_names,
            avoid_reaching_selected=base.selection.avoid_reaching_selected,
            skip_norm=base.skip_norm,
            hoist_repeated_calls=base.hoist_repeated_calls,
            skip_prune=base.skip_prune,
            default_source_label=base.default_source_label,
            default_namespace=base.default_namespace,
            default_output=base.default_output,
            cli_description=base.cli_description,
        )
        yul = """
            function fun_f_1(var_x_1) -> var_z_2 {
                var_z_2 := var_x_1
            }
        """

        models = translate_yul_to_models(
            yul,
            config,
            optimize=False,
        )
        with self.assertRaisesRegex(ParseError, "model_names"):
            build_lean_source(
                models=models,
                source_path="test-source",
                namespace="Test",
                config=config,
            )

    def test_hoist_repeated_model_calls_hoists_branch_output_exprs(self) -> None:
        model = FunctionModel(
            fn_name="f",
            param_names=("p",),
            return_names=("out_a", "out_b"),
            assignments=(
                ConditionalBlock(
                    condition=Var("p"),
                    output_vars=("out_a", "out_b"),
                    then_branch=ConditionalBranch(
                        assignments=(),
                        outputs=(
                            Call("inner", (Var("p"),)),
                            Call("inner", (Var("p"),)),
                        ),
                    ),
                    else_branch=ConditionalBranch(
                        assignments=(),
                        outputs=(IntLit(0), IntLit(0)),
                    ),
                ),
            ),
        )

        hoisted = hoist_repeated_model_calls(
            model,
            model_call_names=frozenset({"inner"}),
        )

        cond_block = next(
            stmt for stmt in hoisted.assignments if isinstance(stmt, ConditionalBlock)
        )
        then_cse = [
            stmt
            for stmt in cond_block.then_branch.assignments
            if isinstance(stmt, Assignment) and stmt.target.startswith("_cse")
        ]
        self.assertTrue(then_cse, "Expected branch-output CSE inside then-branch")
        hoisted_name = then_cse[0].target
        self.assertEqual(
            cond_block.then_branch.outputs,
            (Var(hoisted_name), Var(hoisted_name)),
        )


if __name__ == "__main__":
    unittest.main()
