# Deleted test notes

- Deleted the earlier `KnownTranslatorBugRegressionTest.test_build_lean_source_rejects_generated_model_name_collision_with_builtin_helper` variant that used `model_names={"f": "evmAdd"}`.
  It was shadowed by a later test with the same Python method name, so it never ran.
  Remaining coverage: `KnownTranslatorBugRegressionTest.test_build_lean_source_rejects_generated_model_name_collision_with_builtin_helper` still covers the same `build_lean_source` defect class using `model_names={"f": "u256"}`.

- Deleted `KnownTranslatorBugRegressionTest.test_translate_yul_to_models_rejects_wrong_builtin_arity`.
  It only re-parsed `add(1)` before hitting the same missing malformed-builtin validation that is already covered more directly.
  Remaining coverage: `KnownTranslatorBugRegressionTest.test_validate_function_model_rejects_malformed_builtin_arity` still covers the same missing `validate_function_model` call-shape check.

- Deleted `KnownTranslatorBugRegressionTest.test_translate_yul_to_models_rejects_unsupported_builtin_name`.
  In `formal/yul_to_lean.py`, `xor(1, 2)` and `helper()` both flow through the same unknown-call path; there is no builtin-specific translator branch before emission.
  Remaining coverage: `KnownTranslatorBugRegressionTest.test_translate_yul_to_models_rejects_unresolved_call_target` still covers the same missing unknown-call rejection.

- Deleted `KnownTranslatorBugRegressionTest.test_find_function_rejects_when_requested_arity_matches_no_candidate`.
  It exercises the same missing `find_function(..., n_params=...)` enforcement as the simpler single-candidate mismatch case, just with an extra `known_yul_names` disambiguation layer.
  Remaining coverage: `KnownTranslatorBugRegressionTest.test_find_function_rejects_nonmatching_param_count_even_when_unique` still covers the same missing requested-arity rejection in `YulParser.find_function`.

- Deleted `KnownTranslatorBugRegressionTest.test_find_function_ignores_constant_switch_helper_references`.
  In `YulParser._scope_references_any`, both `if 0 { helper() }` and `switch 1 case 0 { helper() } default { ... }` fail for the same reason: the scanner recursively visits every sub-block without switch-specific handling or constant-condition pruning.
  Remaining coverage: `KnownTranslatorBugRegressionTest.test_find_function_ignores_constant_false_helper_references` still covers the same missing dead-branch reference pruning in `YulParser.find_function`.

- Deleted `KnownTranslatorBugRegressionTest.test_translate_yul_to_models_rejects_selected_projection_when_callee_returns_too_many_values`.
  It exercises the same missing exact return-arity validation for selected-model `__component_N_M(...)` projections as the simpler two-targets-vs-one-return mismatch case; `translate_yul_to_models` never checks that the selected callee's arity matches the wrapper total before handing the malformed projection downstream.
  Remaining coverage: `KnownTranslatorBugRegressionTest.test_translate_yul_to_models_rejects_selected_projection_when_callee_returns_too_few_values` still covers the same missing selected-model projection arity check.

- After this review, no other new tests in `569ef1ffa4f66fdaf205877d99997295429b5ac9..HEAD` were removed.
  Similar-looking regressions were kept because they exercise different parser, scope, control-flow, validation, or Lean-emission paths in `formal/yul_to_lean.py`.
