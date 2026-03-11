# Deleted test notes

- Deleted the earlier `KnownTranslatorBugRegressionTest.test_build_lean_source_rejects_generated_model_name_collision_with_builtin_helper` variant that used `model_names={"f": "evmAdd"}`.
  It was shadowed by a later test with the same Python method name, so it never ran.
  Remaining coverage: `KnownTranslatorBugRegressionTest.test_build_lean_source_rejects_generated_model_name_collision_with_builtin_helper` still covers the same `build_lean_source` defect class using `model_names={"f": "u256"}`.

- No other new tests in `569ef1ffa4f66fdaf205877d99997295429b5ac9..HEAD` were removed.
  Similar-looking regressions were kept because they exercise different parser, scope, control-flow, or Lean-emission paths in `formal/yul_to_lean.py`.
