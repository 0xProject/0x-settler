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

- After this review, no other new tests in `569ef1ffa4f66fdaf205877d99997295429b5ac9..HEAD` were removed.
  Similar-looking regressions were kept because they exercise different parser, scope, control-flow, validation, or Lean-emission paths in `formal/yul_to_lean.py`.
