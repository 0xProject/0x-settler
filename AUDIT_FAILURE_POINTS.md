# 0x Settler — Possible Failure Points & Audit Scope Notes

> A structured, general-purpose map of where this codebase is most likely to
> fail or be mis-used. The emphasis is on **recurring themes and ideas** rather
> than one-off scenarios, so the same lens can be re-applied to future changes.
> Where a theme maps onto a concrete area of the code, that area is named so the
> idea can be made actionable during review.

---

## How to read this document

Most of the risks below reduce to a single underlying principle:

> **The system encodes a large fraction of its safety guarantees as *unenforced
> assumptions* — about inputs, environment, structure, and trust — rather than
> as runtime checks.**

The code can be correct as written while remaining fragile against future
change. So the recurring question for any review or edit is not only *"is this
correct today?"* but *"which silent assumption does this rely on, and what
happens the day that assumption stops holding?"*

The document has two halves:

1. **General failure-point themes** — the conceptual risk categories.
2. **Audit scope notes** — where to actually point attention, including the
   specific hints from 0x.

---

# Part 1 — General Failure-Point Themes

## 1. Trust placed in unchecked input decoding

The system deliberately favors gas efficiency over defensive decoding, so
malformed or adversarial inputs are not rejected up front. The general risk is
that safety depends on *every* downstream consumer failing gracefully — any
component that does not handle garbage, aliased, or zero-padded input becomes a
weak link.

- The action stream is decoded "laxly": offsets may be negative, may run off the
  end of calldata (and be implicitly zero-padded), and may alias other regions
  of calldata — including the action array itself.
- Nothing validates this at decode time. Correctness is delegated entirely to
  the action handlers reverting on nonsense.
- **The recurring failure mode:** a newly added action that does *not* revert on
  malformed or aliased input silently becomes an exploit primitive.

## 2. Duplicated logic that must stay in sync

Core dispatch logic is intentionally replicated across multiple locations
instead of being shared, for contract-size and inlining reasons. The general
hazard is **drift**: a fix or feature applied in one place but not its mirrors,
with nothing in the compiler forcing the copies to agree.

- The base dispatch routine is copy/pasted into chain-specific mixins (the
  Mainnet mixin is explicitly called out in code comments as a manual mirror).
- **The recurring failure mode:** an action behaves on one chain/flavor and is
  unreachable (or subtly different) on another, purely because one copy was
  updated and another was not.

## 3. Authorization that hinges on positional / structural conventions

Whether a signed request is valid depends on conventions rather than explicit,
localized checks — e.g. *"the first action authorizes the rest"* and *"the
signature commits to the entire action sequence."* The general risk is that any
new path which **decouples the authorization from what actually executes** quietly
breaks the security model.

- Meta-transaction / intent flows rely on the first action being a
  witness-aware action, and on the witness/signature binding the full action
  list.
- The guardrails (witness must be non-zero, witness must be spent exactly once,
  payer reentrancy guard) are present but are *conventions enforced at the
  edges*, not invariants the type system maintains.
- **The recurring failure mode:** a new privileged action that consumes the
  authorization token without re-binding it to the rest of the work.

## 4. Reliance on environmental and compiler assumptions

Several mechanisms assume specific compiler behavior, encoding widths, and chain
characteristics. The general failure mode is **portability**: an assumption that
holds on mainstream chains and toolchains may silently break on a new or exotic
target.

- Transient-storage packing assumes internal function pointers fit in a fixed,
  small width — true under the IR pipeline, not guaranteed everywhere.
- Various routines assume `block.chainid` cannot collide with hashable data,
  assume EIP-1153 transient storage exists, assume Cancun/Osaka semantics, etc.
- **The recurring failure mode:** a chain is added where one of these
  environmental assumptions does not hold, and a packed value is truncated or a
  hash domain collides.

## 5. Callback and confused-deputy exposure

The contract makes outbound calls and accepts callbacks, so correctness depends
on rigorously distinguishing **trusted counterparties from arbitrary ones**. The
general risk is that any gap in target-restriction or callback authentication
lets the contract be used as a deputy for someone else's intent.

- Callback targets must be derived from trusted initcode (a documented, *unchecked*
  precondition of the call helper).
- A set of "restricted targets" (Permit2, AllowanceHolder, etc.) must never be
  callable as arbitrary targets; some paths intentionally skip the restricted-target
  check based on the assumption that selectors do not clash.
- Callbacks authenticate by matching caller + selector against transient state.
- **The recurring failure mode:** a new restricted target, a selector collision,
  or a "trusted" target that can be coerced into relaying attacker calldata.

## 6. Sensitivity to inheritance and resolution order

Behavior depends heavily on how method resolution threads through a deep
inheritance graph — most importantly the resolution of caller/identity
(`_msgSender`, `_operator`, `_isForwarded`, `_isRestrictedTarget`). The general
hazard is that reordering or refactoring base contracts **quietly changes who is
treated as the payer versus the authorized party.**

- Multiple base lists carry explicit `DANGER: do not reorder` comments because
  the `super` chain is load-bearing.
- Identity is context-dependent: in some contexts `_msgSender()` returns the
  transient *payer*, while `_operator()` returns the actual caller.
- **The recurring failure mode:** a refactor that looks behavior-preserving but
  swaps payer/operator identity — i.e. an authentication bug disguised as a
  cleanup.

## 7. Integrity of hand-maintained data structures

Privileged state (e.g. authorization lists) is managed with bespoke, low-level
assembly rather than high-level Solidity, for size reasons. The general risk is
that subtle bugs in this logic can **corrupt the structure, orphan entries, or
leave stale entries authorized.**

- The intent solver set is a hand-rolled circular linked list manipulated in
  assembly, with deferred reverts and bit-twiddled "expected vs new" values.
- Read-only enumeration helpers can be denial-of-service-prone if mis-used
  on-chain.
- **The recurring failure mode:** an off-by-one or mis-set slot that either
  orphans the list or leaves a removed principal still authorized.

## 8. Balance-based accounting and custody assumptions

Settlement correctness relies on reasoning about **where token balances came
from** — specifically that the user's "bought" amount originates directly from
the settler, not from some other exchange of value. The general failure mode is
that stray, donated, or externally-sourced balances satisfy a check meant to
validate a genuine swap.

- The final slippage check intentionally forgoes custody optimization on the
  last hop precisely to enforce "the increase came from us."
- Positive-slippage and whole-balance arithmetic run in `unchecked` blocks.
- **The recurring failure mode:** a new action that lets value arrive by a path
  that the whole-balance accounting cannot distinguish from a legitimate swap
  output.

## 9. Tight coupling to deployment and registry state

Contracts assume a specific relationship with the deployment registry both at
construction (the instance asserts it already owns its feature token) and at
runtime (callers must discover the live instance through the registry, never by
hardcoding). The general risk is that **deployment ordering or registry
mismatches** render an instance invalid, unreachable, or impersonated.

- Constructors assert `registry.ownerOf(featureId) == address(this)`, coupling
  the deploy scripts tightly to registry state and to the `gitCommit` argument.
- Integrators are told to *always* resolve the address via `ownerOf` (with a
  `prev` fallback during the API "dwell" window) and never hardcode it.
- **The recurring failure mode:** a deploy-script change, a dwell-time edge, or a
  registry inconsistency that leaves callers pointed at a paused, stale, or
  counterfeit instance.

## 10. Divergent code paths with different trust profiles

Different execution modes delegate trust differently — sometimes relying on an
external component to enforce a constraint that is *not* re-checked locally. The
general hazard is that a new mode or path **inherits a weaker set of checks**
unless it explicitly re-establishes its own guarantees.

- The forwarded (AllowanceHolder) transfer path skips local amount checks
  because AllowanceHolder is trusted to enforce them; it must require empty
  signature / zero nonce / manual deadline check to be safe.
- Meta-transaction flavors deliberately *disable* the forwarded path; a new
  flavor that forgets to disable it would inherit an unauthenticated transfer.
- **The recurring failure mode:** a new flavor or mode that copies a path but
  not all of the assumptions that made the original safe.

---

# Part 2 — Audit Scope Notes (from 0x)

These are the areas 0x highlighted as worth disproportionate attention. They are
not separate from Part 1 — they are *where the themes above bite hardest.*

## A. The NFT registry, ERC-721 semantics, and "weird" tokens

Two distinct token-shaped trust surfaces converge here:

- **The registry is an ERC-721 NFT.** Deployment discovery, pausing, and the
  dwell-time fallback all run through `ownerOf` / `prev` on an upgradeable
  ERC721-compatible registry. Anything that depends on NFT semantics (a revert
  meaning "paused", `prev` meaning "in dwell") is a behavioral contract that
  off-chain and on-chain consumers must agree on. Mis-reading these signals →
  interacting with a paused or counterfeit instance.
- **ERC-20 "weird tokens" are a first-class hazard.** The settler must remain
  correct against fee-on-transfer, rebasing, missing-return-value,
  non-reverting-on-failure, double-entrypoint, and reentrant tokens. Because
  settlement relies on *balance deltas* (see Theme 8), fee-on-transfer and
  rebasing tokens are especially dangerous: the "amount received" measured by
  balance can diverge from any amount encoded in calldata.
- **Review lens:** for every token-touching action, ask which weird-token class
  could make the balance-delta accounting lie, and whether the slippage check
  still protects the user when it does.

## B. Chain proliferation — most chains can be skipped, but *keep Mainnet*

There are ~20+ chain directories, each with the same four flavor files plus a
`Common.sol` mixin. The vast majority are near-identical thin configurations
over the shared base.

- **Audit guidance from 0x:** you can largely *skip* the per-chain directories
  during deep review and concentrate effort on **Mainnet**, which carries the
  richest mixin (the most DEX integrations and therefore the most novel code).
- The risk that *does* live in the other chains is **Theme 2 (copy/paste drift)**
  and **Theme 4 (environmental assumptions)** — i.e. a chain that diverges from
  the base dispatch or that violates an environmental assumption.
- **Review lens:** diff each chain's `Common.sol` against the canonical base
  dispatch to confirm it is a faithful superset, and confirm the chain actually
  supports the EVM features the base assumes. Spend the rest of the budget on
  Mainnet's integrations.

## C. The fork integrations are interesting (and the Lido pattern reuses them)

`src/core/univ3forks/` holds 25+ Uniswap-V3-style fork configs, and
`UniswapV3Fork` plus the various `*V2`/`*V3`/slipstream integrations all share a
single parameterized shape (factory address, init-code hash, fee encoding,
callback shape).

- **Why interesting:** every fork is "the same code with different constants."
  A wrong init-code hash, factory, or fee-bit layout silently points the settler
  at the wrong pool or mis-authenticates a callback — and the shared shape means
  one subtle config error can be copied across many forks (Theme 2 again, in
  data form rather than code form).
- **The same pattern is being applied for Lido.** Reusing the fork shape for a
  Lido-style integration means the same class of constant/callback-authentication
  mistakes applies; it deserves the same scrutiny as a new fork entry, *plus*
  Lido-specific wrap/unwrap and rebasing-token considerations (tie back to
  Theme 8 and Scope A).
- **Review lens:** for each fork/Lido entry verify the deployment constants
  against on-chain reality and confirm the pool callback can only be entered by a
  genuinely derived pool address.

## D. Off-chain transaction encoding is part of the trust boundary

Because on-chain decoding is intentionally lax (Theme 1), the **off-chain encoder
that produces the action stream is effectively a security-relevant component.**

- A bug in the off-chain encoding (wrong offset, wrong selector, mis-bound
  recipient/amount, accidental aliasing) will not be caught by the contract's
  decoder; it will either revert opaquely or, worse, execute something the user
  did not intend.
- For signed flows, the off-chain side is also responsible for producing exactly
  the bytes that the on-chain witness hashing expects — any mismatch between the
  encoder and the on-chain typed-data layout breaks signature validation or, if
  the layouts drift, breaks the binding between signature and executed actions
  (Theme 3).
- **Review lens:** treat the encoder ↔ decoder pair as one unit. Confirm the
  off-chain encoding cannot emit calldata whose lax-decoded interpretation
  differs from the intended one, and that the signed-struct layout matches the
  on-chain hashing byte-for-byte.

## E. `src/core/` is the interesting scope

The action mixins in `src/core/` are where the real logic lives — RFQ,
Uniswap-family, Velodrome, Maverick, Balancer, Ekubo, Euler, Maker PSM, the
Permit2 payment layer, the bridge actions, and so on. This is the highest-value
review surface because:

- It is where new attack surface is most frequently introduced (every new DEX is
  a new mixin here).
- It is where Themes 1, 5, and 8 concentrate: novel calldata shapes, novel
  callbacks, and novel balance accounting.
- The `Permit2Payment` layer in particular is the crossroads of identity
  resolution (Theme 6), callback authentication (Theme 5), and the forwarded-path
  trust split (Theme 10).
- **Review lens:** prioritize `src/core/` over the chain glue. For each mixin
  ask the three standing questions — does it revert on malformed input, can its
  callback be spoofed, and can its balance accounting be fooled?

## F. Bridge: cross-chain logic is isolated from swap logic

The `BridgeSettler` (feature token 5) is deliberately **isolated from the swap
engine**. It does not embed DEX integrations; instead, when it needs a swap it
*delegates to the canonical taker-submitted Settler*, which it first validates
through the registry (the same `ownerOf` / `prev` genuineness check used by
integrators).

- **Why this isolation matters:** it keeps the (large, novel) cross-chain bridge
  surface from co-mingling with the (already audited) swap surface, and it means
  the bridge inherits the swap engine's guarantees only through a single,
  validated entry point.
- **Where the isolation can leak:**
  - The bridge funds the swap by approving AllowanceHolder and routing through
    it; its own comments note this makes the swap **MEV-susceptible** (an
    attacker can force the swap to its slippage limit). That is an accepted,
    documented property — but it is a property, and any change that widens it is
    a regression.
    - The delegated Settler call passes **arbitrary `settlerData`**; safety rests
    on (a) the settler having been validated as genuine and (b) the genuine
    settler's own restricted-target / VIP handling. If the validation or the
    isolation boundary weakens, the bridge becomes a confused deputy (Theme 5).
  - Native vs. ERC-20 paths differ (direct value call vs. AllowanceHolder pull);
    these are two trust profiles to keep in sync (Theme 10).
- **Review lens:** confirm the settler-genuineness check cannot be bypassed,
  confirm the bridge never treats a restricted target as a swap target, and
  treat the documented MEV exposure as a fixed boundary not to be widened.

## G. `CrossChainReceiverFactory` — flagged by 0x as containing an interesting bug

0x specifically flagged this contract as worth hunting for a bug. It is the most
assembly-dense and assumption-dense contract in the tree (counterfactual proxy
deployment, Merkle-proof *and* ERC-7739 signature validation, EIP-712 hashing of
a forwarded `MultiCall`, Permit2 unordered-nonce bookkeeping, native/wrapped
juggling, and `selfdestruct`-based cleanup). I have **not confirmed a definitive
exploit**; below are the concrete candidate areas I consider most worth
scrutinizing, framed honestly as *leads*, not conclusions.

### Candidate areas to scrutinize

1. **Dual signature decoding (Merkle proof vs. ERC-7739).**
   `isValidSignature` decides between a Merkle-proof signature and an ERC-7739
   nested signature based on whether the leading word decodes as a clean
   (upper-96-bits-zero) address. The security argument is a 96-bit
   computational-hardness claim that a signature cannot be valid under *both*
   interpretations. This is exactly the kind of "two decoders over one byte
   string" surface (Theme 1) where ambiguity bugs hide — worth checking that a
   single short or boundary-length signature cannot be steered down the wrong
   branch, and that the `signature.length >> 6 == 0` early-return for the
   ERC-7739 empty-signature sentinel cannot be abused.

2. **Merkle root / single-element proofs.**
   With an empty proof, the computed root equals the leaf. Verify that
   `_verifyDeploymentRootHash` (which re-derives the proxy address from the root
   and original owner) genuinely prevents a crafted `(leaf, owner)` pair from
   matching `address(this)` — i.e. that a proof of length zero or one cannot be
   used to assert membership of an attacker-chosen hash. Also check the leaf
   construction's stated assumption that `block.chainid` cannot alias a tree node
   (Theme 4).

3. **`metaTx` nonce/owner/relayer packing.**
   The upper 160 bits of `nonce` encode the owner and the upper bits of
   `deadline` optionally encode a permitted relayer. The two branches (owner
   supplied in nonce → Merkle path; owner zero → current-owner + simple ECDSA
   path) construct the signing hash differently and use different domain
   separators (real vs. sentinel). Worth confirming: that the relayer binding is
   actually covered by the signed hash, that `deadlineForHashing` vs. the masked
   `deadline` cannot be played against each other, and that the
   ownership-transferred-back comment ("confusion may occur") is not an
   exploitable nonce-replay window.

4. **Nonce invalidation ordering.**
   `_useUnorderedNonce` is invoked before the external `multicall`. Confirm there
   is no path where the multicall (or the native/wrapped withdraw before it) can
   re-enter `metaTx` with the same nonce before invalidation is observable, and
   that the Permit2 nonce bitmap read/write cannot be desynced.

5. **`call(..., ppm, patchOffset, ...)` amount patching.**
   The patched value is computed as `ppm * balance / 1e6` and `mstore`'d as a
   full word at `patchOffset` into copied calldata. The bounds check only
   guarantees `patchOffset + 31 < data.length`. Worth verifying the patch cannot
   clobber adjacent encoded fields in a way the target misinterprets, and that
   the native-vs-ERC20 branch selects `value` consistently with the patched
   amount.

6. **`cleanup` / `selfdestruct` semantics post-Cancun.**
   `deploy(setOwnerNotCleanup = false)` relies on `cleanup` self-destructing in
   the *same* transaction as the `create2` (the only case where post-Cancun
   `selfdestruct` actually removes code). Confirm the `_MISSING_WNATIVE`
   force-to-`setOwner` path and the same-tx assumption hold, and that a proxy
   left un-cleaned cannot be re-used adversarially.

7. **`receive()` auto-wrapping and `getFromMulticall` sentinel substitution.**
   The proxy forwards incoming native to the wrapped-native contract, and
   `getFromMulticall` substitutes `caller()` for the `address(this)` sentinel
   recipient. Worth checking these conveniences cannot be combined to redirect
   funds or to wrap/unwrap in a way that strands value in the `MultiCall`.

- **Review lens:** the unifying risk across all seven is Theme 1 + Theme 4 —
  multiple hand-written decoders and hash constructions over the same byte
  strings, each carrying an *unchecked* assumption (clean padding, length bounds,
  chainid non-aliasing, same-tx self-destruct). The bug, if present, most likely
  lives at one of these assumption boundaries rather than in the high-level
  control flow.

---

## Summary table

| # | Theme / Scope | Core risk in one line |
|---|---------------|------------------------|
| 1 | Unchecked input decoding | Safety delegated to every consumer reverting on garbage |
| 2 | Duplicated logic | Copy/paste dispatch drifts out of sync |
| 3 | Positional authorization | New path decouples signature from executed work |
| 4 | Environmental assumptions | Packing/hash assumptions break on a new chain/toolchain |
| 5 | Callback / confused deputy | Untrusted target or selector collision relays attacker intent |
| 6 | Inheritance order | Refactor swaps payer vs. operator identity |
| 7 | Hand-maintained structures | Assembly list bug orphans or leaves stale authorization |
| 8 | Balance accounting | Stray/donated balance satisfies a swap-output check |
| 9 | Registry coupling | Deploy/dwell mismatch points callers at a bad instance |
| 10 | Divergent trust profiles | New mode copies a path but not its safety preconditions |
| A | NFT + weird tokens | Balance-delta accounting lies for fee-on-transfer/rebasing tokens |
| B | Chain proliferation | Skip most chains, focus on Mainnet; watch for divergence |
| C | Fork (+ Lido) configs | One wrong constant/callback shape copied across many forks |
| D | Off-chain encoding | Encoder bugs are unguarded by the lax on-chain decoder |
| E | `src/core/` | Highest-value surface; every new DEX adds attack surface here |
| F | Bridge isolation | Confused-deputy / MEV boundary around the delegated swap |
| G | `CrossChainReceiverFactory` | Assumption-boundary bug among multiple hand-rolled decoders |
