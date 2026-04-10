# Pipeline Cutover: Test Failure Categorization

85 tests fail after wiring `translate_yul_to_models` to the new staged pipeline.
491 tests pass. Categorization below.

## Category 1: NLeave not lowered (10 tests)

The new pipeline's `norm_to_restricted.py` rejects `NLeave` statements — it expects all `leave` to be inlined before lowering. The old pipeline had special `leave` handling in its model builder (lowering leave to early-return semantics inline). The new pipeline's inliner handles `leave` via `did_leave` flag for block-inlined helpers, but top-level `leave` in the selected target function itself is not supported.

**Root cause**: `NLeave` in restricted IR lowering — new pipeline doesn't support `leave` in the top-level function body.

| Test | Error |
|------|-------|
| `TranslationPipelineTest::test_translate_yul_to_models_lowers_inlined_leave` | NLeave in restricted IR lowering |
| `TranslationPipelineTest::test_translate_yul_to_models_ignores_dead_code_after_inlined_leave` | NLeave in restricted IR lowering |
| `TranslationPipelineTest::test_translate_yul_to_models_rejects_top_level_leave` | error message mismatch |
| `TranslationPipelineTest::test_translate_yul_to_models_rejects_multiple_inlined_leave_sites` | error message mismatch |
| `KnownTranslatorBugRegressionTest::test_translate_yul_to_models_allows_constant_switch_with_dead_leave_branch` | NLeave |
| `KnownTranslatorBugRegressionTest::test_translate_yul_to_models_allows_constant_true_switch_with_dead_leave_branch_in_helper` | NLeave |
| `KnownTranslatorBugRegressionTest::test_translate_yul_to_models_preserves_constant_zero_switch_leave_path_in_inlined_helper` | NLeave |
| `KnownTranslatorBugRegressionTest::test_translate_yul_to_models_preserves_constant_zero_switch_leave_path_with_trailing_dead_code` | NLeave |
| `KnownTranslatorBugRegressionTest::test_translate_yul_to_models_allows_exact_from_after_constant_false_inlined_leave` | NLeave |
| `KnownTranslatorBugRegressionTest::test_translate_yul_to_models_allows_exact_from_after_constant_true_inlined_leave` | NLeave |

**Fix needed**: Support `NLeave` in `norm_to_restricted.py` or eliminate it during constprop (dead-branch elimination after constant-condition leave).

## Category 2: Unsupported/unresolved model calls (22 tests)

The new pipeline models ALL functions as top-level. When the test's `config.function_order` selects only a subset, other functions become sibling model calls. But the test's `model_table` doesn't include them, causing `EvaluationError: Unsupported model call`. The old pipeline inlined non-selected helpers before building models.

**Root cause**: New pipeline doesn't inline non-selected helpers — they become top-level model calls that the test's evaluator can't find.

| Test | Missing callee |
|------|---------------|
| `SimplifyIteTest::test_inline_constant_false_if_eliminates_ite` | helper |
| `SimplifyIteTest::test_inline_constant_true_if_eliminates_ite` | helper |
| `SimplifyIteTest::test_inline_constant_false_leave_eliminates_ite` | helper |
| `SimplifyIteTest::test_inline_constant_true_leave_eliminates_ite` | helper |
| `SimplifyIteTest::test_inline_constant_switch_eliminates_ite` | helper |
| `SimplifyIteTest::test_variable_condition_preserves_ite` | helper |
| `BranchExprStmtTest::test_inline_dead_branch_expr_stmt_discarded` | helper |
| `BranchExprStmtTest::test_inline_live_branch_expr_stmt_rejected` | helper |
| `BranchExprStmtTest::test_inline_non_constant_branch_expr_stmt_rejected` | helper |
| `BranchExprStmtTest::test_chained_inline_dead_branch_expr_stmt_discarded` | helper |
| `BranchExprStmtTest::test_leave_dead_branch_expr_stmt_discarded` | helper |
| `BranchExprStmtTest::test_leave_switch_dead_else_expr_stmt_discarded` | helper |
| `BranchExprStmtTest::test_leave_switch_live_else_expr_stmt_rejected` | helper |
| `BranchExprStmtTest::test_wrapping_div_pattern_dead_branch_after_cleanup_inline` | wrapping_div |
| `BranchExprStmtTest::test_wrapping_div_pattern_intermediate_var` | wrapping_div |
| `BranchExprStmtTest::test_wrapping_div_pattern_non_constant_var_rejected` | wrapping_div_t_uint256 |
| `TranslationPipelineTest::test_translate_yul_to_models_allows_exact_from_helper` | pair |
| `TranslationPipelineTest::test_multi_return_rebinding_keeps_old_argument_binding_for_later_components` | pair |
| `TranslationPipelineTest::test_multi_return_rebinding_matches_simultaneous_assignment_semantics` | pair (4 sub-failures) |
| `KnownTranslatorBugRegressionTest::test_translate_yul_to_models_allows_exact_from_in_constant_false_inlined_if_body` | helper |
| `KnownTranslatorBugRegressionTest::test_translate_yul_to_models_dispatches_modeled_function_named_like_builtin` | cleanup |
| `KnownTranslatorBugRegressionTest::test_translate_yul_to_models_collects_outer_helpers_for_exact_nested_target` | wrapper/helperA |

**Fix needed**: The new pipeline's inliner should inline non-top-level helpers (functions not in the selected set). Alternatively, `translate_yul_to_models` should build model_tables that include all sibling functions.

## Category 3: Unresolved local calls after inlining (8 tests)

The new pipeline's inliner doesn't inline all local helpers. Some remain as `NLocalCall` in the normalized IR, which `norm_to_restricted.py` rejects.

| Test | Unresolved call |
|------|----------------|
| `BranchExprStmtTest::test_const_subst_from_constant_true_if_body` | helper_1 |
| `BranchExprStmtTest::test_const_subst_invalidated_after_non_constant_reassignment` | helper_1 |
| `KnownTranslatorBugRegressionTest::test_translate_yul_to_models_rejects_nested_helper_memory_write_through_local` | helper_1 |
| `KnownTranslatorBugRegressionTest::test_translate_yul_to_models_rejects_nested_helper_memory_write_through_temp` | helper_1 |
| `KnownTranslatorBugRegressionTest::test_translate_yul_to_models_alpha_renames_callee_locals_during_inlining` | helper2 |
| `CriticalReviewFixRegressionTest::test_translate_yul_to_models_allows_nested_helper_chain_using_exact_from` | helper_outer_1 |
| `CriticalReviewFixRegressionTest::test_translate_yul_to_models_rejects_nested_rejected_helper_in_non_pure_helper` | ptr_inner_1 (2 subfailures) |
| `CriticalReviewFixRegressionTest::test_translate_yul_to_models_rejects_nested_helper_used_after_its_scope_ends` | (2 subfailures) |

**Root cause**: The new pipeline uses `norm_classify` + `norm_inline` which classifies helpers as EXPR_INLINE, BLOCK_INLINE, EFFECT_LOWER, or DO_NOT_INLINE. Helpers classified as DO_NOT_INLINE remain as local calls. The old pipeline had different inlining heuristics.

**Fix needed**: Ensure all local helpers are either inlined or promoted to top-level model calls before restricted IR lowering.

## Category 4: Memory model limitations (7 tests)

Non-constant memory addresses after the new pipeline — `norm_to_restricted.py` requires constant 32-byte-aligned mload/mstore addresses but the new pipeline doesn't always resolve them to constants.

| Test | Error |
|------|-------|
| `TranslationPipelineTest::test_translate_yul_to_models_allows_top_level_memory_write_with_helper_mload` | Non-constant mload |
| `KnownTranslatorBugRegressionTest::test_translate_yul_to_models_accepts_conditionally_constant_memory_address` | Non-constant mstore |
| `KnownTranslatorBugRegressionTest::test_translate_yul_to_models_accepts_conditionally_constant_memory_address_for_kept_solidity_local` | Non-constant mstore |
| `KnownTranslatorBugRegressionTest::test_translate_yul_to_models_allows_branch_local_constant_mload_address` | Non-constant mload |
| `KnownTranslatorBugRegressionTest::test_translate_yul_to_models_allows_branch_local_constant_mload_address_for_kept_solidity_local` | Non-constant mload |
| `BranchExprStmtTest::test_constant_true_flatten_preserves_nested_live_expr_stmt` | Memory in conditional |
| `ResolvedTranslatorRegressionTest::test_translate_yul_to_models_skips_unneeded_zero_init_after_branch_write` | Non-constant mstore |

**Root cause**: The old pipeline resolved memory addresses through constant propagation during model building. The new pipeline's constprop pass doesn't resolve some address patterns (especially conditionally-constant addresses via `mstore(ptr, ...)` where `ptr` is a function parameter that happens to be constant).

**Fix needed**: Improve constprop to resolve more memory address patterns, or make the restricted IR lowerer accept non-constant addresses when they can be proven constant through analysis.

## Category 5: Expected ParseError not raised (14 tests)

Tests expect `translate_yul_to_models` to raise `ParseError` for specific invalid patterns. The new pipeline either accepts the pattern (different error semantics) or raises a different error.

| Test | Expected rejection |
|------|-------------------|
| `BranchExprStmtTest::test_top_level_expr_stmt_still_rejected` | expression statements |
| `BranchExprStmtTest::test_direct_target_live_branch_expr_stmt_rejected` | expression statements |
| `BranchExprStmtTest::test_direct_target_non_constant_branch_expr_stmt_rejected` | expression statements |
| `BranchExprStmtTest::test_bare_block_nested_live_expr_stmt_still_rejected` | expression statements |
| `BranchExprStmtTest::test_multiple_expr_stmts_in_live_branch_rejected` | expression statements |
| `BranchExprStmtTest::test_switch_live_default_expr_stmt_rejected` | expression statements |
| `BranchExprStmtTest::test_multiple_expr_stmts_in_dead_branch_discarded` | expression statements |
| `BranchExprStmtTest::test_switch_dead_case0_expr_stmt_discarded` | expression statements |
| `ResolvedTranslatorRegressionTest::test_translate_yul_to_models_rejects_target_expression_statements` | expression statements |
| `CriticalReviewFixRegressionTest::test_translate_yul_to_models_rejects_exact_from_inside_helper_if_body` | scope violation |
| `CriticalReviewFixRegressionTest::test_translate_yul_to_models_rejects_exact_from_inside_helper_if_condition` | scope violation |
| `CriticalReviewFixRegressionTest::test_translate_yul_to_models_rejects_nested_transitive_exact_from_in_helper_condition` | scope violation |
| `KnownTranslatorBugRegressionTest::test_translate_yul_to_models_rejects_lean_keyword_parameter_name` | reserved name |
| `KnownTranslatorBugRegressionTest::test_translate_yul_to_models_rejects_zero_return_functions` | zero-return |

**Root cause**: The new pipeline has different error semantics. Expression statements are handled (normalized away or kept as NExprEffect), while the old pipeline rejected them. Some scope-violation checks from the old pipeline's `exact_from` handling don't exist in the new pipeline.

**Fix needed**: Some of these rejections are important for safety (reserved names, zero-return). Others are old-pipeline-specific (exact_from scope rules). Triage individually.

## Category 6: SSA name / model structure differences (5 tests)

The new pipeline produces different SSA names and model structure than the old pipeline.

| Test | Issue |
|------|-------|
| `TranslationPipelineTest::test_translate_yul_to_models_raw_preserves_zero_and_dead_assignments` | different target names (`z_2` vs `z_1`) |
| `TranslationPipelineTest::test_translate_yul_to_models_defaults_to_optimized_pipeline` | different assignment structure |
| `TranslationPipelineTest::test_render_function_defs_uses_demangled_ssa_names` | different Lean output |
| `TranslationPipelineTest::test_translate_yul_to_models_lowers_plain_inlined_if` | different model shape |
| `KnownTranslatorBugRegressionTest::test_translate_yul_to_models_wraps_large_switch_case_literals_to_u256` | different structure |

**Fix needed**: Update expected values to match new pipeline output. These are not bugs, just different (correct) SSA naming.

## Category 7: Function selection / scope issues (9 tests)

Tests use old pipeline's function selection features (`exact_yul_names`, scope-local helpers, object-scoped resolution) that the new pipeline handles differently.

| Test | Issue |
|------|-------|
| `FunctionSelectionTest::test_prepare_translation_uses_exact_yul_name_selection` | tests old `prepare_translation` directly |
| `ResolvedTranslatorRegressionTest::test_translate_yul_to_models_keeps_helper_resolution_object_local` | function not found |
| `ResolvedTranslatorRegressionTest::test_translate_yul_to_models_scopes_helpers_per_selected_target_object` | function not found |
| `CriticalReviewFixRegressionTest::test_translate_yul_to_models_allows_exact_from_inside_inlined_local_helper` | unresolved call |
| `CriticalReviewFixRegressionTest::test_translate_yul_to_models_allows_same_scope_exact_from_helper_chain` | unresolved call (2 sub) |
| `FinalCriticalReviewRegressionTest::test_translate_yul_to_models_allows_distinct_deferred_helpers_with_same_name_across_scopes` | model call error |
| `FinalCriticalReviewRegressionTest::test_translate_yul_to_models_avoids_protected_call_name_collisions` | KeyError |
| `FinalCriticalReviewRegressionTest::test_translate_yul_to_models_distinguishes_selected_exact_homonyms` | model call error |
| `FinalCriticalReviewRegressionTest::test_translate_yul_to_models_does_not_leak_selected_block_local_helper_scope` | function not found |
| `FinalCriticalReviewRegressionTest::test_translate_yul_to_models_keeps_exact_selected_homonyms_scope_local` | function not found |
| `FinalCriticalReviewRegressionTest::test_translate_yul_to_models_preserves_selected_block_local_exact_helper` | function not found |
| `StagedPipelineWiringTest::test_production_path_function_selection` | function not found |
| `KnownTranslatorBugRegressionTest::test_build_lean_source_ignores_constant_true_branch_local_binder_named_like_generated_model` | binder collision |

**Root cause**: The new pipeline uses `parse_function_groups` which handles multi-object Yul differently from the old pipeline. Functions inside `object "X" { code { ... } }` blocks may not match simple name lookup.

**Fix needed**: Ensure `translate_groups` handles scope-qualified function names and object-local helpers correctly.

## Summary

| Category | Count | Severity | Fix complexity |
|----------|-------|----------|---------------|
| NLeave not lowered | 10 | High | Medium — need to handle NLeave in lowerer or eliminate via constprop |
| Unsupported model calls | 22 | High | Medium — need to inline non-selected helpers or include them in model_table |
| Unresolved local calls | 8 | High | Medium — improve inliner coverage |
| Memory model limitations | 7 | Medium | Medium — improve constprop for memory addresses |
| Expected errors not raised | 14 | Low | Easy — triage, update error expectations |
| SSA name differences | 5 | Low | Easy — update expected values |
| Function selection/scope | 9 | Medium | Medium — fix parse_function_groups handling |
| **Total** | **85** | | |
