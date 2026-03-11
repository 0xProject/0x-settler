# Yul -> Lean Refactor Plan

This plan focuses on places where recent bug fixes repaired behavior but left
behind duplicated or stringly logic that should be replaced with a cleaner
general mechanism.

Prioritization is by payoff-to-risk, not by raw ambition. The first item is
the best candidate to land immediately without destabilizing the translator.

## Priority 1: Centralize Lean emission planning

Status: Executed in this change

Problem:
- `build_lean_source()` recomputes emitted model names, reserved-name checks,
  `skip_norm` behavior, binder-collision rules, and helper-name collisions with
  several ad hoc sets.
- `render_function_defs()` independently re-derives which definitions will be
  emitted.
- The previous `skip_norm` bugs came from those two views drifting apart.

Refactor:
- Introduce a small `LeanEmissionPlan` that computes, once:
  - the emitted EVM/norm def names for each model
  - whether each model emits a norm def
  - the full set of generated def names
  - the builtin/helper names that generated defs may not collide with
- Make both validation and rendering consume that plan instead of rebuilding
  parallel logic from `config.model_names` and `config.skip_norm`.
- Factor binder iteration into a helper so target collection is shared rather
  than duplicated across collision checks.

Why first:
- It removes a real source of recent bugs.
- It is contained to Lean emission, so the risk is much lower than changing
  parsing or semantic lowering.
- The existing `build_lean_source` regression suite already gives good coverage.

## Priority 2: Replace token rescans with scope-aware helper analysis

Status: Executed in this change

Problem:
- `_scope_references_any()` is effectively a second parser over raw tokens.
- It has bespoke logic for constant `if`/`switch`, nested scopes, and helper
  promotion.
- That makes it brittle and guarantees drift from the actual parser.

Refactor:
- Build helper-reference analysis on a parsed scope tree rather than token
  positions.
- Give each lexical scope one representation containing:
  - parsed statements
  - local helper definitions
  - rejected helper definitions
- Resolve helper visibility by walking scope frames rather than rescanning
  slices of tokens.

Expected payoff:
- One source of truth for shadowing, rejected-helper shadowing, dead branches,
  and exact-path helper lookup.

## Priority 3: Normalize control flow once, then lower

Problem:
- Constant-folding and branch-selection semantics currently exist in multiple
  places: parser control-flow handling, helper inlining, and direct model
  lowering.
- That duplication is what kept producing inconsistent `if`/`switch` and
  `leave` behavior.

Refactor:
- Introduce a normalization pass over raw statements that:
  - folds constant `if`/`switch`
  - removes dead trailing code after guaranteed `leave`
  - preserves dynamic conditionals in one normalized shape
- Have helper inlining and direct model lowering consume normalized statements
  instead of re-implementing branch specialization independently.

Expected payoff:
- Fixes an entire class of “works in parser but not in inliner/lowerer”
  regressions.

## Priority 4: Preserve declaration semantics explicitly in the raw IR

Problem:
- The parser still compensates for lost `let` vs reassignment information with
  side structures like `block_let_vars`, `block_subst`, `pre_if_names`, and
  `inside_conditional`.

Refactor:
- Replace plain raw assignments with an explicit binding node that records
  whether it came from `let` or `:=`.
- Use that information in block lowering and conditional lowering instead of
  reconstructing scope semantics from target names.

Expected payoff:
- Cleaner and more correct handling of branch-local shadowing and block scope.

## Priority 5: Replace synthetic call-name encodings with explicit IR nodes

Problem:
- Multi-return projections and conditional expressions are still represented as
  fake call names like `__component_0_2(...)` and `__ite(...)`, then decoded by
  regex in multiple passes.

Refactor:
- Introduce explicit expression nodes for projection and conditional
  expressions.
- Lower to Lean syntax directly from those nodes instead of encoding semantics
  in string names.

Expected payoff:
- Removes repeated regex parsing and makes arity and shape validation local to
  the IR rather than scattered through the pipeline.

## Execution order after this change

1. Land the `LeanEmissionPlan` cleanup and keep the existing emission behavior.
2. Build a parsed scope-frame representation and migrate helper analysis to it.
3. Add a shared control-flow normalization pass and route inlining/lowering
   through it.
4. Upgrade the raw IR to preserve declaration semantics.
5. Replace synthetic projection/`__ite` encodings with explicit nodes.
