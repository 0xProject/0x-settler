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

- Deleted `KnownTranslatorBugRegressionTest.test_find_function_tracks_transitive_nested_helper_called_before_definition`.
  In `YulParser._scope_references_any`, local function discovery and loose-call collection are order-insensitive within a block, so calling `nested(...)` before its definition exercises the same transitive dependency scan as the simpler after-definition case.
  Remaining coverage: `KnownTranslatorBugRegressionTest.test_find_function_tracks_transitive_sibling_local_helper_dependencies` still covers the same missing transitive nested-helper reference handling in `YulParser.find_function`, with an extra local-helper hop.

- Deleted `KnownTranslatorBugRegressionTest.test_find_function_ignores_dead_nested_helper_inside_deeper_block`.
  In `YulParser._scope_references_any`, the deeper `if { ... }` wrapper only adds one recursive sub-block hop before reaching the same "local function body references helper but no loose call to that local function exists" logic as the simpler top-level case.
  Remaining coverage: `KnownTranslatorBugRegressionTest.test_find_function_ignores_nested_local_function_references` still covers the same missing requirement that an uncalled nested local helper body must not count as a known-name reference in `YulParser.find_function`.

- Deleted `KnownTranslatorBugRegressionTest.test_find_function_tracks_transitive_nested_local_helper_dependencies`.
  It exercises the same local-function reference promotion in `YulParser._scope_references_any` as the stronger sibling-chain variant, just with one fewer hop. If the fixed-point promotion handles `nested2 -> nested1 -> helper`, it necessarily handles the simpler `nested -> helper` case too.
  Remaining coverage: `KnownTranslatorBugRegressionTest.test_find_function_tracks_transitive_sibling_local_helper_dependencies` still covers the same missing transitive nested-helper promotion in `YulParser.find_function`.
