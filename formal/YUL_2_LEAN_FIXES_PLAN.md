# Yul -> Lean Fixes Plan

## Goals

The current failures are symptoms of a few missing semantics in the translator:

1. Function selection treats `n_params` as a soft hint instead of a hard contract.
2. Known-name reference analysis is token-based and not control-flow aware.
3. The raw Yul AST loses the difference between `let` and reassignment inside top-level conditionals.
4. Constant control flow is not normalized early enough, so dead/live branch memory writes are both mishandled.
5. Restricted-IR validation does not fully validate expression shape or inter-model call arity.
6. The parser and symbol-discovery logic only support a subset of straight-line Yul forms that the tests already rely on.
7. Helper collection/inlining does not model scope, shadowing, and duplication robustly enough.
8. Lean emission trusts configuration and generated names too much.
9. Word-sized Yul semantics are not normalized consistently for literals and constant addresses.

The implementation should fix those semantics generally, not by adding one-off checks for the restored tests.

## Guiding principles

- Preserve Yul meaning in the raw AST before lowering to restricted IR.
- Fold constant control flow early, but keep the translator fail-closed for dynamic semantics we still do not model.
- Treat user-supplied selection constraints (`n_params`, exact names, expected return arity) as hard requirements.
- Keep scope-sensitive behavior explicit instead of reconstructing it from token scans and naming heuristics.

## Workstream 1: Preserve declaration semantics in the raw AST

### Problem

`_parse_let()` currently emits `PlainAssignment` for both `let x := ...` and `x := ...`, and top-level conditional lowering later cannot tell whether a branch wrote to an outer variable or introduced a new shadowing local.

This is the root cause of:

- branch-local shadowing leaking into the outer scope
- `switch` branch shadowing behaving like reassignment

### Intended change

Replace `PlainAssignment` with a richer raw binding node that preserves whether the statement is a declaration.

```python
@dataclass(frozen=True)
class RawBinding:
    target: str
    expr: Expr
    is_declaration: bool


@dataclass(frozen=True)
class RawLeave:
    pass


RawStatement = RawBinding | MemoryWrite | ParsedIfBlock | RawLeave
```

`_parse_let()` should emit `RawBinding(..., is_declaration=True)`.
Plain `:=` assignment should emit `RawBinding(..., is_declaration=False)`.

### Why this is the right abstraction

The translator is already trying to recover declaration-vs-assignment with `_let_vars` in bare blocks. That side channel is too narrow; the same distinction is needed in top-level `if` and `switch` branches, and later in any control-flow-aware analysis.

### Follow-on changes

- `ParsedIfBlock.body` and `else_body` should become tuples of `RawBinding | MemoryWrite | RawLeave`, not just `PlainAssignment`.
- Bare-block lowering should stop relying on a separate `block_let_vars` set and instead use `is_declaration`.

## Workstream 2: Make function selection AST-based and harden arity handling

### Problem

`find_function()` currently filters by `n_params` only when there are multiple matches, and if the filter yields zero matches it silently falls back to the unfiltered set. That makes arity a heuristic instead of a requirement.

Separately, `_scope_references_any()` walks raw tokens. It does not understand:

- constant-dead `if` / `switch` branches
- guaranteed termination after `leave`
- executable-vs-non-executable subpaths

### Intended change

Treat `n_params` as a hard filter before any known-name disambiguation.

```python
if n_params is not None:
    matches = [m for m in matches if self._count_params_at(m) == n_params]
    if not matches:
        raise ParseError(
            f"No Yul function for {sol_fn_name!r} matches {n_params} parameter(s)"
        )
```

Then replace `_scope_references_any()` with analysis over parsed function bodies rather than token scans.

### Proposed shape

Introduce a parsed block/scope representation for analysis:

```python
@dataclass(frozen=True)
class ParsedBlock:
    statements: tuple[RawStatement, ...]
    local_functions: dict[str, "ParsedLocalFunction"]


def block_references_any(block: ParsedBlock, names: set[str]) -> bool:
    reachable = True
    promoted: set[str] = set()

    while True:
        changed = False
        for name, local_fn in block.local_functions.items():
            if name in promoted:
                continue
            if block_references_any(local_fn.body, (names - set(block.local_functions)) | promoted):
                promoted.add(name)
                changed = True
        if not changed:
            break

    visible = (names - set(block.local_functions)) | promoted
    return statements_reference_any(block.statements, visible, reachable=True)
```

The statement walker should:

- prune constant-false/constant-true branches using `_try_const_eval`
- stop after guaranteed `leave`
- only count local-function dependencies that are actually reachable

### Why this is the right abstraction

Function selection is trying to answer a semantic question: "does this candidate depend on any of these known Yul helpers?" Token rescans are the wrong level of abstraction for that question.

## Workstream 3: Normalize constant control flow before model lowering

### Problem

The parser rejects all branch-local `mstore` by parsing branch bodies with `allow_control_flow=False`. That is too coarse:

- a dead `if 0 { mstore(...) }` should be dropped
- a constant-selected `switch 0 case 0 { mstore(...) }` should lower as straight-line code
- dynamic conditional memory writes should still be rejected until memory-state merging is modeled

### Intended change

Split "parse the branch" from "decide whether the branch is semantically supported".

1. Parse branch bodies into raw statements, including `MemoryWrite`.
2. Run a normalization pass that folds constant `if` / `switch`.
3. Reject only the remaining dynamic conditional memory writes.

Implementation sketch:

```python
def normalize_block(statements: tuple[RawStatement, ...]) -> tuple[tuple[RawStatement, ...], bool]:
    out: list[RawStatement] = []
    terminated = False

    for stmt in statements:
        if terminated:
            break

        if isinstance(stmt, RawLeave):
            terminated = True
            continue

        if isinstance(stmt, ParsedIfBlock):
            cond = _try_const_eval(stmt.condition)
            if cond is not None:
                chosen = stmt.body if cond != 0 else (stmt.else_body or ())
                lowered, child_terminated = normalize_block(chosen)
                out.extend(lowered)
                terminated = child_terminated
                continue

            reject_dynamic_memory_writes(stmt)
            out.append(stmt)
            continue

        out.append(stmt)

    return tuple(out), terminated
```

### Why this is the right abstraction

The translator's memory model is intentionally limited, but constant control flow does not require branch-state merging. We should exploit that rather than rejecting all branch-local `mstore` uniformly.

## Workstream 4: Fix conditional lowering to respect branch-local shadowing

### Problem

`yul_function_to_model()` currently assumes any branch binding with the same demangled name as a pre-existing variable is an outer-scope modification. That is incorrect for `let` shadowing.

### Intended change

Process branch bindings with explicit declaration semantics:

- declarations create branch-local scope entries
- assignments update an existing outer variable only if they are not declarations
- conditional outputs should only include mutated outer variables

Implementation sketch:

```python
def _process_conditional_branch(
    raw_branch: tuple[RawStatement, ...],
    *,
    outer_var_map: dict[str, str],
    outer_scope_names: set[str],
) -> BranchLowering:
    branch_var_map = dict(outer_var_map)
    branch_assignments: list[Assignment] = []
    modified_outer: list[str] = []

    for stmt in raw_branch:
        if isinstance(stmt, RawBinding):
            assignment = _process_binding_into(..., binding=stmt, branch_var_map=branch_var_map)
            if assignment is not None:
                branch_assignments.append(assignment)
            if not stmt.is_declaration:
                clean = demangle_var(stmt.target, ...)
                if clean in outer_scope_names:
                    modified_outer.append(clean)
```

This should be used for both `if` and lowered `switch`, so the semantics are shared instead of being fixed in one branch shape only.

### Additional rule

If a branch-local declaration shadows an outer variable and is later read by another branch-local binding, the branch-local version must remain visible only inside that branch. The post-conditional environment should continue to point at the outer binding unless a non-declaration assignment mutated it.

## Workstream 5: Add full expression and call-shape validation

### Problem

`validate_function_model()` currently checks scope and binder names, but not enough expression semantics:

- builtin call arity is not validated structurally
- `__ite` and `__component_N_M` shape validation is incomplete
- selected-model call/projection arity is not checked exactly

### Intended change

Add a recursive expression validator.

```python
def _validate_expr(
    expr: Expr,
    *,
    available: set[str],
    known_model_arity: dict[str, int] | None,
) -> None:
    if isinstance(expr, Var):
        if expr.name not in available:
            raise ParseError(...)
        return

    if isinstance(expr, Call):
        if expr.name in OP_TO_LEAN_HELPER:
            expected = builtin_arity(expr.name)
            if len(expr.args) != expected:
                raise ParseError(...)
        elif expr.name == "__ite":
            if len(expr.args) != 3:
                raise ParseError(...)
        elif component := parse_component_projection(expr.name):
            validate_component_projection(expr, component, known_model_arity)
        elif known_model_arity is not None and expr.name in known_model_arity:
            expected = known_model_arity[expr.name]
            if len(expr.args) != expected:
                raise ParseError(...)
        for arg in expr.args:
            _validate_expr(arg, available=available, known_model_arity=known_model_arity)
```

### Exact selected-model arity check

For a projection `__component_i_n(g(...))`, the translator should reject both:

- `g` returning fewer than `n`
- `g` returning more than `n`

That is an exact contract, not a lower-bound check.

The cleanest place to enforce this is in a translation-time pass with access to the selected-function signatures:

```python
selected_return_arity = {
    sol_name: len(preparation.yul_functions[sol_name].rets)
    for sol_name in preparation.selected_functions
}
```

Then validate every generated model against that signature map before emission.

## Workstream 6: Expand parser support for the intended straight-line subset

### Problem

Several failures are not about later lowering at all; they come from the parser and symbol finder not recognizing forms that are still within the intended restricted subset:

- `let a, b` without an initializer
- `a, b := pair()`
- dead code after `leave` inside a bare block
- top-level exact-function lookup accidentally considering nested local functions

### Intended change

Factor the parser around a small set of reusable helpers for assignment targets and function discovery.

```python
def _parse_binding_targets(self) -> tuple[list[str], bool]:
    targets = [self._expect_ident()]
    saw_comma = False
    while self._peek_kind() == ",":
        saw_comma = True
        self._pop()
        targets.append(self._expect_ident())
    return targets, saw_comma
```

Use that in both `let` parsing and plain assignment parsing so multi-target forms share the same shape checks.

For symbol discovery, stop scanning the flat token stream for exact-name matches. Instead, build the same top-level parsed-function index used by normal function selection, and make exact-name lookup query that index only.

### Why this is the right abstraction

These are not special cases. They are all consequences of the parser currently being too statement-specific and of function discovery operating below the level where lexical scope is visible.

## Workstream 7: Rebuild helper collection and inlining around explicit scope frames

### Problem

The remaining helper-related failures cluster around the same issue: helper collection is too flat.

Symptoms include:

- nested local helpers not collected when they should be
- outer helpers not collected for exact nested targets
- nested helpers not preferred over shadowed siblings
- duplicate helper names in the same scope not rejected
- transitive calls to shadowing local helpers counted incorrectly
- helper inlining depth accounting conflating helper recursion with builtin AST nesting

### Intended change

Represent helper lookup with explicit scope frames instead of one merged `dict[str, YulFunction]`.

```python
@dataclass(frozen=True)
class ScopeFrame:
    functions: dict[str, YulFunction]
    parent: "ScopeFrame | None" = None

    def resolve(self, name: str) -> YulFunction | None:
        if name in self.functions:
            return self.functions[name]
        if self.parent is None:
            return None
        return self.parent.resolve(name)
```

Parsing/helper collection should:

- reject duplicate helper names within one `ScopeFrame`
- allow shadowing across nested frames
- carry the frame of each selected target into inlining

Inlining depth should only advance when following a helper edge, not when descending through builtin arguments.

```python
def inline_calls(expr: Expr, scope: ScopeFrame, helper_depth: int = 0) -> Expr:
    if isinstance(expr, Call):
        inlined_args = tuple(inline_calls(arg, scope, helper_depth) for arg in expr.args)
        callee = scope.resolve(expr.name)
        if callee is None:
            return Call(expr.name, inlined_args)
        return _inline_single_call(callee, inlined_args, scope, helper_depth + 1)
```

### Why this is the right abstraction

Yul helper visibility is lexical. Flattening helpers into one table loses exactly the information needed for shadowing, duplicate detection, and nested-target helper capture.

## Workstream 8: Validate the selected-model call graph explicitly

### Problem

The current translator lets several invalid selected-model programs through:

- duplicate selected functions
- unresolved selected-model calls
- wrong selected-model call arity
- selected multi-return call in scalar context
- recursive or mutually recursive selected-model calls

These are all graph/signature invariants on the selected model set, not just local expression-shape issues.

### Intended change

Build a selected-model signature table and call graph immediately after `prepare_translation()`, then validate it before restricted-IR emission.

```python
def validate_selected_models(models: dict[str, YulFunction]) -> None:
    signatures = {
        name: FunctionSig(n_params=len(fn.params), n_rets=len(fn.rets))
        for name, fn in models.items()
    }
    graph = {
        name: collect_direct_selected_calls(fn.assignments, selected=set(models))
        for name, fn in models.items()
    }
    reject_signature_mismatches(models, signatures)
    reject_selected_cycles(graph)
```

This validation should share the same projection/call rules as Workstream 5 so there is one source of truth for selected-function call semantics.

## Workstream 9: Harden Lean emission and config validation

### Problem

`build_lean_source()` currently does very little validation of the emitted Lean namespace and generated definition set.

The failing tests show missing checks for:

- invalid namespace and generated model names
- Lean keyword/reserved helper collisions
- missing model-name mappings
- duplicate norm names and cross collisions between `foo` and `foo_evm`
- binder collisions with generated model names in plain assignments and conditionals
- newline/comment injection through `source_path`, `generator_label`, and `header_comment`
- ensuring `extra_lean_defs` is separated cleanly from following helper definitions
- dead constant branches with unresolved helpers surviving all the way to emission

### Intended change

Add a dedicated pre-emission validation pass that constructs the exact set of emitted Lean names and validates all user-controlled text fields.

```python
def validate_lean_emission_inputs(
    models: list[FunctionModel],
    *,
    namespace: str,
    source_path: str,
    config: ModelConfig,
) -> None:
    validate_ident(namespace, what="Lean namespace")
    validate_header_field(source_path, what="source path")
    validate_header_field(config.generator_label, what="generator label")
    validate_header_comment(config.header_comment)

    emitted_defs = collect_emitted_def_names(models, config)
    ensure_unique(emitted_defs, context="generated Lean definitions")
    ensure_binder_names_do_not_collide(models, emitted_defs)
```

`collect_emitted_def_names()` should include:

- norm defs
- evm defs
- config extra norm helpers
- generated model names and generated `_evm` names

The same pass should also reject unsupported calls that remain only in dead code by requiring constant-folding/DCE to run before emission-visible validation.

### Why this is the right abstraction

Lean emission is a compilation boundary. All naming, injection, and source-shape checks should happen there in one place rather than being scattered across ad hoc identifier checks.

## Workstream 10: Normalize uint256 semantics for literals and constant addresses

### Problem

The current evaluator/lowering path treats some raw integer literals and constant memory addresses as unbounded integers instead of EVM words. That breaks:

- large integer literal wrapping
- large constant memory addresses that should wrap modulo `2^256`
- conditionally constant address reasoning when the constant is only visible after substitution/folding

### Intended change

Normalize constant words at the translator boundary instead of leaving this to selected builtin helpers only.

```python
def normalize_word_expr(expr: Expr) -> Expr:
    if isinstance(expr, IntLit):
        return IntLit(u256(expr.value))
    if isinstance(expr, Call):
        return Call(expr.name, tuple(normalize_word_expr(arg) for arg in expr.args))
    return expr
```

Use this in:

- parsed literal construction
- assignment lowering before storing expressions in the model
- `_resolve_memory_address()` before alignment and address-key checks

This should preserve the current restricted memory model while making it word-accurate.

## Workstream 11: Implementation order

Recommended order:

1. Introduce the richer raw AST (`RawBinding`, `RawLeave`, parsed blocks/scopes).
2. Migrate parsing code to produce that AST without changing external behavior yet.
3. Expand multi-target parsing and top-level symbol discovery onto that AST.
4. Move function-selection dependency analysis onto the parsed AST.
5. Rebuild helper collection/inlining around scope frames.
6. Add control-flow normalization and make branch-local memory-write support depend on that pass.
7. Update `yul_function_to_model()` to use declaration-aware branch lowering.
8. Add recursive expression validation and selected-model graph validation.
9. Add Lean emission/config validation and emitted-name collision checks.
10. Normalize word semantics for literals and constant addresses.
11. Re-run the full `KnownTranslatorBugRegressionTest` class, then broaden coverage around nearby semantics.

## Verification strategy

The restored tests should pass, but verification should go beyond them:

- `find_function`:
  - unique wrong-arity candidate
  - multi-candidate no-match arity
  - constant-dead `if`
  - constant-dead `switch`
  - top-level `leave`
  - nested reachable/unreachable local helpers
  - exact-name lookup ignoring nested local collisions
  - leaf-vs-wrapper selection when nested public-name candidates exist

- conditional lowering:
  - `if` shadowing with no outer write
  - `if` shadowing after an outer write
  - `switch` shadowing in both `case 0` and `default`
  - branch-local declaration followed by branch-local use
  - temporary snapshots across parameter and return rebinding
  - conditional writes later overwritten
  - branch-local constant `mload` and conditionally constant addresses

- memory model:
  - dead constant branch with `mstore`
  - live constant-selected branch with `mstore`
  - dynamic conditional `mstore` still rejected
  - exact-from helpers across constant false/true leave normalization
  - wrapped constant addresses modulo `2^256`

- call validation:
  - malformed builtin arity
  - malformed `__ite`
  - malformed `__component`
  - selected-model projection exact-match, underflow, and overflow
  - selected-model scalar-vs-multi-return mismatch
  - selected-model direct-call arity mismatch
  - unresolved call target rejection
  - recursive and mutually recursive selected-model call rejection

- parser/support:
  - multi-variable `let` declarations
  - multi-target assignment without `let`
  - scalar initializer rejected for multi-variable declaration
  - dead code after `leave` inside a bare block

- helper/inlining:
  - duplicate helper names in the same scope rejected
  - nested helper collection for selected and exact-name targets
  - nested helper shadowing preferred over sibling/outer helpers
  - builtin AST nesting does not spend helper inlining depth budget
  - callee locals alpha-renamed hygienically

- Lean emission:
  - namespace and generated model identifiers validated
  - generated norm/evm name collisions rejected, including cross-collisions
  - missing model-name mappings rejected
  - binder collisions against emitted def names rejected in plain and conditional scopes
  - header/source metadata injection rejected
  - `extra_lean_defs` separated cleanly from following generated defs
  - dead unresolved helper calls eliminated before emission

- word semantics:
  - large integer literals wrapped to `u256`
  - constant memory addresses wrapped to `u256`

## Non-goals for this pass

- Full support for dynamic conditional memory-state merging
- General Yul loop support
- Broadening the supported control-flow subset beyond what can be expressed faithfully in the current restricted IR

Those can be addressed later, but this plan should leave the code structured so that future extensions do not require another parser redesign.
