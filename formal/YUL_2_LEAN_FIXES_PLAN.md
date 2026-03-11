# Yul -> Lean Fixes Plan

## Goals

The current failures are symptoms of a few missing semantics in the translator:

1. Function selection treats `n_params` as a soft hint instead of a hard contract.
2. Known-name reference analysis is token-based and not control-flow aware.
3. The raw Yul AST loses the difference between `let` and reassignment inside top-level conditionals.
4. Constant control flow is not normalized early enough, so dead/live branch memory writes are both mishandled.
5. Restricted-IR validation does not fully validate expression shape or inter-model call arity.

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

## Workstream 6: Implementation order

Recommended order:

1. Introduce the richer raw AST (`RawBinding`, `RawLeave`, parsed blocks/scopes).
2. Migrate parsing code to produce that AST without changing external behavior yet.
3. Move function-selection dependency analysis onto the parsed AST.
4. Add control-flow normalization and make branch-local memory-write support depend on that pass.
5. Update `yul_function_to_model()` to use declaration-aware branch lowering.
6. Add recursive expression validation and exact selected-call arity validation.
7. Re-run the restored regression cases, then broaden coverage around nearby semantics.

## Verification strategy

The restored tests should pass, but verification should go beyond them:

- `find_function`:
  - unique wrong-arity candidate
  - multi-candidate no-match arity
  - constant-dead `if`
  - constant-dead `switch`
  - top-level `leave`
  - nested reachable/unreachable local helpers

- conditional lowering:
  - `if` shadowing with no outer write
  - `if` shadowing after an outer write
  - `switch` shadowing in both `case 0` and `default`
  - branch-local declaration followed by branch-local use

- memory model:
  - dead constant branch with `mstore`
  - live constant-selected branch with `mstore`
  - dynamic conditional `mstore` still rejected

- call validation:
  - malformed builtin arity
  - malformed `__ite`
  - malformed `__component`
  - selected-model projection exact-match, underflow, and overflow

## Non-goals for this pass

- Full support for dynamic conditional memory-state merging
- General Yul loop support
- Broadening the supported control-flow subset beyond what can be expressed faithfully in the current restricted IR

Those can be addressed later, but this plan should leave the code structured so that future extensions do not require another parser redesign.
