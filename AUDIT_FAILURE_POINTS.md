# 0x Settler — Failure-Point Map & Audit Guide (for an AI audit agent)

> **Purpose.** This document is written to be consumed by an automated audit
> agent (and the humans supervising it). It does two things:
>
> 1. Builds an accurate **mental model** of how 0x Settler is wired, so the agent
>    can reason about consequences instead of pattern-matching surface syntax.
> 2. Enumerates the **failure-point themes** — the categories of bug this design
>    is structurally prone to — each one explained from first principles, mapped
>    to concrete code locations, and paired with **detection heuristics** the
>    agent can act on.
>
> **How to use it.** When reviewing any file or diff, (a) locate the change in
> the mental model below, (b) identify which failure-point theme(s) it touches,
> and (c) run the "What to check" probes for those themes. Treat every
> `file:line` reference as a navigation anchor; line numbers are approximate and
> may drift, so confirm by reading the surrounding function.

---

## 0. Orientation: the mental model

### 0.1 What the system does

0x Settler executes DEX swaps on behalf of users **without holding standing
token allowances**. Instead of pre-approving the settler, a user authorizes a
single transfer through one of:

- **Permit2** (`0x000000000022D473030F116dDEE9F6B43aC78BA3`) — a signed,
  one-time `permitTransferFrom` / `permitWitnessTransferFrom`.
- **AllowanceHolder** — a transient-approval forwarder for the taker-submitted
  flow (no signature; the approval lives only for the duration of the call).

The settler then runs a user-supplied **list of actions** (the "action stream"),
each action being an ABI-encoded call selected by a 4-byte selector. The actions
move the just-transferred tokens through pools and finally pay the user, subject
to a slippage check.

### 0.2 The four "flavors" (feature/token IDs)

Each flavor is a different *trust and authentication model* over the same action
engine. The flavor is identified by a feature/`tokenId` in the deployer registry:

| Flavor | tokenId | Auth model | Entry function | `_msgSender()` resolves to |
|--------|---------|------------|----------------|----------------------------|
| Taker-submitted | 2 | `msg.sender` is the user (or AllowanceHolder forwarder) | `execute` / `executeWithPermit` (`src/Settler.sol:118`, `:132`) | the transient *payer* |
| MetaTxn (gasless) | 3 | EIP-712 signature over `(slippage, actions)`; a relayer submits | `executeMetaTxn` (`src/SettlerMetaTxn.sol:145`) | the signer |
| Intent | 4 | EIP-712 signature over slippage only; an allow-listed **solver** submits & chooses the route | `executeMetaTxn` (`src/SettlerIntent.sol:250`) | the signer |
| Bridge | 5 | taker-submitted; delegates swaps to flavor-2 settler | `execute` (`src/bridge/BridgeSettler.sol:38`) | the transient payer |

The inheritance spine (see `CLAUDE.md` for the diagram):

```
SettlerAbstract  ──>  Permit2PaymentAbstract        (interfaces, constants, typehashes)
SettlerBase      ──>  Basic, RFQ, UniV3Fork, UniV2, Velodrome   (the shared action engine)
   ├─ Settler            (taker-submitted)
   └─ SettlerMetaTxn     (metatxn)
         └─ SettlerIntent (intent)  + MultiCallContext + Permit2PaymentIntent
BridgeSettlerBase ──> Basic, Relay, LayerZeroOFT, CCIP   (separate engine for tokenId 5)
```

Each **chain** (`src/chains/<Chain>/`) supplies a `Common.sol` mixin that extends
`SettlerBase` with that chain's extra DEX integrations, plus four thin flavor
files. **Mainnet's mixin is the richest** (MakerPSM, MaverickV2, DodoV1/V2,
UniswapV4, BalancerV3, Ekubo, EulerSwap, Bebop, …) — see `src/chains/Mainnet/Common.sol`.

### 0.3 The dispatch flow (read this before anything else)

The core loop lives in `Settler._execute` (`src/Settler.sol:164-189`) and its
siblings. Pseudocode:

```
for each encoded action in `actions`:
    (selector, args) = CalldataDecoder.decodeCall(...)   // LAX decode, no bounds checks
    if first action:
        if !_dispatchVIP(selector, args):                // VIP = pulls funds via Permit2/AH
            if !_dispatch(0, selector, args, slippage):
                revertActionInvalid(...)
    else:
        if !_dispatch(i, selector, args, slippage):
            revertActionInvalid(...)
_checkSlippageAndTransfer(slippage, false)               // final payout + slippage guard
```

Two dispatch tiers:

- **VIP dispatch** (`_dispatchVIP`, first action only): actions that pull the
  user's funds *into* the settler, e.g. `TRANSFER_FROM`, `UNISWAPV3_VIP`. These
  are where the Permit2/AllowanceHolder authentication happens.
- **Regular dispatch** (`_dispatch`, every action): actions that operate on funds
  the settler already custodies, e.g. `UNISWAPV3`, `BASIC`, `VELODROME`,
  `CHECK_SLIPPAGE`.

`_dispatch` is implemented in `SettlerBase._dispatch` (`src/SettlerBase.sol:117`)
and **copy/pasted** into chain mixins (e.g. `MainnetMixin._dispatch`) — see Theme 2.

### 0.4 Transient storage = the implicit state machine

`library TransientStorage` (`src/core/Permit2Payment.sol:41-181`) holds three
EIP-1153 slots that together form a one-call-deep state machine:

- `_PAYER_SLOT` — the current payer. Set on entry, cleared on exit. **Doubles as
  the reentrancy guard**: `setPayer` reverts `ReentrantPayer` if already set
  (`:154-159`). `_msgSender()` for the payment layer returns this value
  (`Permit2PaymentBase._msgSender`, `:195-197`).
- `_OPERATOR_SLOT` — packs `(selector | callbackPtr | operator)` for the
  *currently expected* callback. Set by `setOperatorAndCallback` before an
  external call; consumed by the `fallback` (`:235-249`). Guards against
  unexpected callbacks.
- `_WITNESS_SLOT` — the EIP-712 witness hash for a metatxn; set in the `metaTx`
  modifier, must be spent (cleared) by the first action's transfer.

The **callback discipline**: `_setOperatorAndCall` (`:208-220`) stores the
expected operator+selector+callback, makes the external call, then asserts the
callback was consumed (`checkSpentOperatorAndCallback`). The `fallback`
re-authenticates by requiring `caller() == operator` **and**
`calldataload(0) selector == stored selector` (`getAndClearCallback`, `:98-111`).
This is the backbone of callback security; understand it deeply.

### 0.5 Key constants & addresses

- `BASIS = 10_000` (BPS denominator), `ETH_ADDRESS = 0xEeee...EEeE` — `src/SettlerAbstract.sol:19-20`.
- Permit2 `0x000000000022D473030F116dDEE9F6B43aC78BA3` — `src/core/Permit2Payment.sol:31`.
- Deployer/registry `0x00000000000004533Fe15556B1E086BB1A72cEae`.
- AllowanceHolder (Cancun) `0x0000000000001fF3684f28c67538d4D072C22734`.
- CrossChainReceiverFactory `0x00000000000000304861c3aDfb80dd5ebeC96325`.

---

# Part 1 — General Failure-Point Themes

Each theme follows the same structure:
**Idea → How it works in this codebase → Why it is risky → Concrete failure modes → What to check (probes).**

---

## Theme 1 — Trust placed in unchecked input decoding

**Idea.** The system trades input validation for gas. Safety therefore depends on
*every* downstream consumer reverting on malformed input. Any consumer that does
not is an exploit primitive.

**How it works here.** `CalldataDecoder.decodeCall` (`src/SettlerBase.sol:31-54`)
is explicitly "more lax than the Solidity ABIDecoder." Its own header comment
(`:26-30`) enumerates the consequences:

- It omits index bounds / overflow checks when indexing the `actions` array.
- It omits checks against `calldatasize()`, so `args` may run off the end of
  calldata and be **implicitly zero-padded**.
- Offsets may be **negative** (no overflow check), so `args` may **alias** other
  calldata regions — including the `actions` array itself.

This laxness is intentional and is relied upon elsewhere (e.g.
`SettlerMetaTxn._hashArrayOfBytes` at `:29-52` deliberately does no bounds
checking; `UniswapV3Fork.uniswapV3SwapCallback` at `:334-343` skips
underflow checks because "the trusted inithash ensures `data` was passed
unmodified").

**Why it is risky.** The decoder will happily hand an action a `bytes calldata`
that is shorter than expected (zero-padded) or that points at attacker-chosen
bytes. A handler that reads fields without re-validating them inherits whatever
the attacker placed there.

**Concrete failure modes.**
- A new action `abi.decode`s a struct but then uses a raw field (address,
  amount, offset) in a privileged way without sanity-checking it.
- An action computes a memory/calldata offset from a decoded value and indexes
  with it (classic OOB → memory corruption or fund misrouting).
- An action assumes a dynamic array is non-empty; zero-padding makes it empty and
  a later step silently no-ops where it should have reverted.

**What to check (probes).**
- For each handler in `_dispatch` / `_dispatchVIP`: does it revert (not silently
  proceed) when `args` is truncated/empty/aliased? Especially handlers that read
  *raw* fields via assembly after `abi.decode`.
- Any new assembly that does `calldataload`/`calldatacopy` using a decoded
  length/offset without an explicit bound.
- Any action whose safety argument is "the inithash guarantees the data is
  well-formed" — verify that guarantee actually holds for *that* call path.

---

## Theme 2 — Duplicated logic that must stay in sync

**Idea.** Hot dispatch code is copy/pasted rather than shared (for size and
inlining). Nothing forces the copies to agree, so they **drift**.

**How it works here.** `SettlerBase._dispatch` carries the explicit notice
(`src/SettlerBase.sol:123-125`):
> *"This function has been largely copy/paste'd into
> `src/chains/Mainnet/Common.sol:MainnetMixin._dispatch`. If you make changes
> here, you need to make sure that corresponding changes are made to that
> function."*

The same notice appears in `Settler._dispatch` (`src/Settler.sol:40-42`).
`CLAUDE.md` reinforces: *"Do NOT modify the `_dispatch` copy/paste pattern without
updating all locations."* The fork-info table `_uniV3ForkInfo`
(`src/chains/Mainnet/Common.sol:203`) is a second instance of the same pattern in
*data* form — per-chain `(factory, initHash, callbackSelector)` triples.

**Why it is risky.** A fix in the base that is not mirrored into a chain mixin
means that chain behaves differently — an action may be unreachable, or worse,
behave inconsistently (e.g. a bounds fix applied on Mainnet but not elsewhere).

**Concrete failure modes.**
- A new action added to `SettlerBase._dispatch` but missing from
  `MainnetMixin._dispatch` → on Mainnet that action reverts `ActionInvalid`.
- A security fix added to one copy but not the other → the unpatched chain stays
  vulnerable.
- A fork constant (`initHash`/`factory`) copied with a typo → swaps route to a
  non-existent or wrong pool, or callback auth derives the wrong pool address.

**What to check (probes).**
- Diff every chain's `Common.sol _dispatch` against `SettlerBase._dispatch` and
  `Settler._dispatch`; confirm each chain is a faithful superset.
- When a diff touches any `_dispatch`/`_dispatchVIP`, grep for the same selector
  across `src/chains/*/Common.sol`, `src/chains/*/TakerSubmitted.sol`,
  `src/chains/*/MetaTxn.sol` and confirm parallel updates.
- Cross-check each fork `initHash`/`factory` constant against an authoritative
  on-chain source.

---

## Theme 3 — Authorization that hinges on positional / structural conventions

**Idea.** "Who authorized this work" is established by *convention* (position in
the action list, a witness bound to the whole list), not by a localized check on
each action. Decoupling the authorization from the executed work breaks the model.

**How it works here.** For metatxn/intent, the **first action must be a
witness-aware VIP action**. `SettlerMetaTxn._executeMetaTxn`
(`src/SettlerMetaTxn.sol:114-143`) dispatches action 0 only through
`_dispatchVIP(action, data, sig)`; if that returns false it reverts
(`:129-131`). The comment (`:126-128`) states the intent: *"By forcing the first
action to be one of the witness-aware actions, we ensure that the entire sequence
of actions is authorized."*

The binding mechanism:
- **MetaTxn:** the signature is over `(slippage, actions)` via
  `_hashActionsAndSlippage` → `_hashArrayOfBytes` (`src/SettlerMetaTxn.sol:29-67`),
  passed to the `metaTx` modifier which `setWitness` (`Permit2Payment.sol:618`).
  The first transfer consumes the witness in
  `Permit2PaymentMetaTxn._transferFrom` (`:584-597`), which **reverts if the
  witness is zero** (`revertConfusedDeputy`).
- **Intent:** the witness is over slippage only (`_hashSlippage`,
  `src/SettlerIntent.sol:241-248`); the route (actions) is chosen by the trusted
  solver, gated by `onlySolver` (`:103-114`).

Guards: `setWitness` rejects re-entry (`:117-124`); `checkSpentWitness` after the
body asserts the witness was spent exactly once (`:622-624`).

**Why it is risky.** The whole authentication rests on "first action spends the
witness, witness covers everything." A VIP action that consumes the witness
*without* the witness actually covering the rest of the work — or a path that
reaches regular dispatch without spending the witness — silently unbinds the
signature from execution.

**Concrete failure modes.**
- A new VIP action added to `_dispatchVIP` that calls a transfer helper which
  does not carry the witness, or carries a *different* witness.
- A change to `_hashArrayOfBytes` / typehashes that makes the signed bytes
  diverge from the executed bytes (signature covers X, execution does Y).
- Intent flow: a bug in `onlySolver` (Theme 7) letting a non-solver submit
  arbitrary routes against a user's slippage-only signature.

**What to check (probes).**
- Every `_dispatchVIP` branch (taker, metatxn, intent, bridge): does it
  ultimately call a transfer that spends the witness for metatxn flavors?
- Confirm `SLIPPAGE_AND_ACTIONS_TYPEHASH` / `SLIPPAGE_TYPEHASH`
  (`src/SettlerAbstract.sol:13-17`) and the witness type-suffix strings
  (`Permit2Payment.sol:580-581`, `:643-645`) exactly match what is hashed and
  what Permit2 will reconstruct. The constructors assert these
  (`SettlerAbstract.sol:22-25`, `Permit2Payment.sol:548-557`, `:636-641`) — a
  change that breaks an assert is a deploy-time failure; a change that *passes*
  asserts but desyncs the off-chain encoder is a silent auth break (see Theme D).
- Confirm `checkSpentWitness` cannot be bypassed by any action ordering.

---

## Theme 4 — Reliance on environmental and compiler assumptions

**Idea.** Behavior depends on specific compiler output, encoding widths, and
chain semantics. These hold on mainstream targets but can silently break on a new
or exotic one (portability bugs).

**How it works here.**
- **Function-pointer width.** `TransientStorage` packs an internal function
  pointer into 16 bits (`Permit2Payment.sol:77-83`, mask `0xffff`). The comment
  (`:49-53`) admits this assumption "might be possible to violate" on chains not
  using the IR pipeline / not enforcing the size limit, but relies on
  `foundry.toml` enforcing `via_ir`.
- **Transient storage existence.** The whole reentrancy/callback machine assumes
  EIP-1153 (`tload`/`tstore`).
- **`block.chainid` non-aliasing.** `CrossChainReceiverFactory._hashLeaf`
  (`src/CrossChainReceiverFactory.sol:361-375`) assumes `block.chainid` cannot
  alias a valid tree node and "cannot exceed 2**53 - 1."
- **`selfdestruct` semantics.** `CrossChainReceiverFactory.cleanup` (`:1029-1045`)
  relies on same-transaction create2+destruct to actually remove code post-Cancun.
- **Solc versions differ by component** (see `CLAUDE.md`): core `^0.8.25`, chains
  `=0.8.34`, AllowanceHolder/Deployer `=0.8.25`, MultiCall/CrossChainReceiver
  `0.8.28` on the *london* EVM. EVM-version mismatches change opcode availability.

**Why it is risky.** A truncated function pointer dispatches to the wrong
callback. A chain without transient storage breaks the reentrancy guard. A chainid
that aliases a node forges a Merkle leaf. A london-EVM contract using a
post-london opcode fails to deploy or misbehaves.

**Concrete failure modes.**
- Adding a chain (`src/chains/<New>/`) that lacks EIP-1153 → silent loss of the
  reentrancy guard.
- A contract grows such that the IR pipeline emits a >2-byte function pointer →
  packed callback corrupted.
- Building a london-EVM component with osaka-only assumptions, or vice versa.

**What to check (probes).**
- For any new chain: verify EIP-1153, EIP-1014 (create2), and the specific EVM
  features the base assumes are available; confirm `chain_config.json` and the
  per-chain solc/EVM settings match the component's pragma.
- Any change that grows a contract near the 24KB limit: re-confirm the
  function-pointer-width CI check still passes.
- Any use of `block.chainid` inside a hash domain: confirm the non-aliasing
  argument still holds.

---

## Theme 5 — Callback and confused-deputy exposure

**Idea.** The settler makes outbound calls and receives callbacks. Correctness
requires rigorously separating *trusted* counterparties (pools derived from
trusted initcode) from *arbitrary* ones. Any gap lets the contract be driven as a
deputy for an attacker.

**How it works here — the worked example (UniswapV3Fork).** This is the canonical
pattern; study it as the template for all callback-based integrations.

1. `_setOperatorAndCall(pool, data, callbackSelector, _uniV3ForkCallback)` is
   invoked (`src/core/UniswapV3Fork.sol:172-174`). It stores the *expected*
   operator (the pool) + selector + callback in `_OPERATOR_SLOT`.
2. The pool address is **derived deterministically** from
   `(factory, initHash, token0, token1, poolId)` via `_toPool`
   (`:278-309`) using CREATE2 address derivation. The pool is *not* taken from
   user calldata directly — it is computed from trusted constants.
3. The pool calls back. The `fallback` (`Permit2Payment.sol:235-249`) loads the
   callback via `getAndClearCallback` (`:98-111`), which **only returns a
   non-null callback if `caller() == storedOperator` and the incoming selector
   matches**. So only the *expected pool* can drive the callback.
4. `uniswapV3SwapCallback` (`UniswapV3Fork.sol:334-346`) decodes `payer` from the
   forwarded `data` and calls `_pay` (`:348-373`), which either transfers the
   settler's own tokens (`payer == address(this)`) or pulls via Permit2/AH
   (`payer == address(0)`).

The `_setOperatorAndCall` NatSpec (`Permit2Payment.sol:199-207`) is the load-bearing
warning: `target` **must** be derived from trusted initcode; it must not be
user-supplied, must not modify the spender, and (if it relays a permit) must relay
it unmodified. `AddressDerivation.deriveDeterministicContract` is the sanctioned
mechanism.

**Restricted targets.** `_isRestrictedTarget` forbids using Permit2
(`Permit2Payment.sol:187-189`) and AllowanceHolder
(`:398-400`) as arbitrary call targets; chains may add more (e.g. Bebop). This
prevents an action from being tricked into calling Permit2/AH with attacker
calldata. Note `executeWithPermit` (`Settler.sol:138-159`) **intentionally skips**
`_isRestrictedTarget(token)` on the permit token, justified by the claim that
permit selectors don't clash with restricted-target selectors (`:141-143`).

**Why it is risky.** The entire model is "the only address that can call back is
one we derived from trusted code." A wrong `initHash`/`factory` (Theme 2) makes
the derived address wrong → either the call fails or, if an attacker can deploy
to the derived address, they can drive the callback. A new restricted target not
added to `_isRestrictedTarget`, or a selector collision, reopens the deputy path.

**Concrete failure modes.**
- A new integration takes the pool/target address **from calldata** and calls it
  without deriving it from trusted initcode → arbitrary call as the settler.
- A callback handler does not re-verify `caller()`/selector (relies on the
  fallback) but is reachable by another path.
- A new privileged external contract (router, factory) is added but not added to
  `_isRestrictedTarget`.
- The `executeWithPermit` selector-non-clash assumption is violated by a newly
  supported permit method.

**What to check (probes).**
- For every callback-based action: is the callback target **derived**
  (CREATE2/initcode) or **user-supplied**? User-supplied targets are only safe if
  they cannot be made to act as the settler against trusted contracts.
- Confirm each integration routes its callback through `_setOperatorAndCall` so
  the fallback authentication applies; confirm `checkSpentOperatorAndCallback`
  runs after.
- Enumerate all addresses the settler may `call`/`delegatecall`; confirm
  privileged ones are in `_isRestrictedTarget` for every flavor.
- Re-examine the `executeWithPermit` non-clash claim whenever a permit method is
  added.

---

## Theme 6 — Sensitivity to inheritance and resolution order

**Idea.** Identity (`_msgSender`, `_operator`, `_isForwarded`,
`_isRestrictedTarget`, `_msgData`) is resolved through a deep `super` chain.
Reordering bases silently changes *who is treated as the payer vs. the authorized
party* — an authentication bug disguised as a refactor.

**How it works here.** There are explicit `DANGER: do not reorder` comments:
- `SettlerIntent` (`src/SettlerIntent.sol:26-27`): *"do not reorder the
  inheritance list here. You will get shocking and incorrect results inside
  `MultiCallContext` if `super._msgSender` is `Permit2PaymentMetaTxn._msgSender`."*
- `Permit2PaymentTakerSubmitted` (`Permit2Payment.sol:356-357`) and
  `Permit2PaymentMetaTxn` (`:545-546`): *"the order of the base contracts here is
  very significant for the use of `super`."*

The identity split is the crux:
- `_operator()` returns the **actual caller** (`Permit2PaymentBase._operator` →
  `super._msgSender()`, `:191-193`).
- `_msgSender()` returns the **transient payer**
  (`Permit2PaymentBase._msgSender` → `TransientStorage.getPayer()`, `:195-197`).

So "operator" = who sent the transaction; "msgSender" = on whose behalf funds
move. For taker-submitted these coincide (payer is set to the operator in the
`takerSubmitted` modifier, `:507-512`). For metatxn they **must differ** — the
modifier even reverts `ConfusedDeputy` if `_operator() == msgSender`
(`:615-617`). The many `_msgSender`/`_isRestrictedTarget` override stubs in
`Settler.sol`, `SettlerMetaTxn.sol`, `SettlerIntent.sol` exist solely to thread
C3 linearization correctly ("Solidity inheritance is stupid").

**Why it is risky.** If a refactor causes `_msgSender()` to resolve to the
operator (or vice versa) in a context where they differ, the settler will pull
funds from, or attribute authorization to, the **wrong** address.

**Concrete failure modes.**
- Reordering `SettlerIntent`'s bases so `super._msgSender` resolves to the
  metatxn implementation inside `MultiCallContext` → wrong signer identity for
  intents.
- Adding a base to a flavor without updating the `override(...)` lists →
  compilation may still succeed but resolve to an unintended implementation.
- A new flavor that forgets to set/clear the payer correctly → `_msgSender()`
  returns stale/zero.

**What to check (probes).**
- On any change to a contract's base list or any `_msgSender`/`_operator`/
  `_isForwarded`/`_isRestrictedTarget`/`_msgData` override: manually compute the
  C3 linearization and confirm each resolves to the intended implementation.
- Confirm the `_operator() != _msgSender()` invariant for metatxn/intent and the
  `==` arrangement for taker-submitted.
- Confirm payer is always set on entry and cleared on exit on every entrypoint
  (`takerSubmitted` / `metaTx` modifiers).

---

## Theme 7 — Integrity of hand-maintained data structures

**Idea.** Privileged state is managed in bespoke assembly for size. Subtle bugs
corrupt the structure, orphan entries, or leave stale entries authorized.

**How it works here.** The **intent solver allow-list**
(`src/SettlerIntent.sol:29-188`) is a Safe-style circular singly-linked list in
storage, manipulated entirely in assembly:
- Membership test is `_$()[query] != 0` (a non-member maps to zero).
- `setSolver` (`:120-188`) adds/removes with bit-twiddled "expected vs new"
  values (`:164-165`), defers the revert to the end for size (`:179-186`), and
  forbids `solver == 0` (`:144`) because it would corrupt the sentinel structure.
- `onlySolver` (`:103-114`) is the gate on intent `executeMetaTxn`; a bug here
  means an unauthorized address can submit arbitrary routes against user
  slippage-only signatures (ties to Theme 3).
- `getSolvers` (`:192-231`) is explicitly *"not intended to be called on-chain"*
  due to an obvious DoS vector.

**Why it is risky.** This is the authorization root for the entire intent flavor.
An off-by-one in the slot math, a missed sentinel update, or an unhandled edge
(adding an existing solver, removing the sentinel) can either brick the list or
silently authorize the wrong principal.

**Concrete failure modes.**
- Removing a solver but failing to relink `prev` → list traversal breaks
  (`getSolvers` loops or truncates) and/or a removed solver stays authorized.
- Adding with a wrong `prev` that still passes the deferred check.
- Any assembly edit that clobbers `_SOLVER_LIST_BASE_SLOT` neighbors.

**What to check (probes).**
- Re-derive the `setSolver` add/remove invariants by hand and confirm the
  assembly matches the commented Solidity (`:123-135`).
- Confirm `onlySolver` reads the exact same slot derivation as `setSolver` writes.
- Fuzz/property test: after any sequence of add/remove, the list is well-formed
  and `getSolvers` matches the set of authorized addresses.

---

## Theme 8 — Balance-based accounting and custody assumptions

**Idea.** Settlement reasons about *balance deltas* and assumes the user's bought
amount comes **directly from the settler**, not from some other exchange of
value. Stray/donated/externally-sourced balances can satisfy checks meant to
validate a genuine swap.

**How it works here.** `_checkSlippageAndTransfer`
(`src/SettlerBase.sol:86-115`) is *deliberately* gas-inefficient and forgoes
custody optimization on the final hop. Its comment (`:87-91`) explains why:
> *"Because `ISettlerActions.BASIC` could interact with an intents-based
> settlement mechanism, we must ensure that the user's want token increase is
> coming directly from us instead of from some other form of exchange of value."*

It measures `amountOut = buyToken.balanceOf(address(this))` (or ETH balance) and
reverts `TooMuchSlippage` if below `minAmountOut`. Intent forces a mandatory
non-zero check (`SettlerIntent._mandatorySlippageCheck`, `:237-239`;
`SettlerBase._checkSlippageAndTransfer`, `:94-95`); taker/metatxn allow the
`(minAmountOut == 0 && buyToken == 0)` skip (`:96-98`). `POSITIVE_SLIPPAGE`
(`SettlerBase._dispatch`, `:158-175`) and `bps` math throughout run in
`unchecked` blocks and use whole-balance arithmetic.

The `bps` semantics also matter: actions sell `balanceOf(this) * bps / BASIS`
(e.g. `UniswapV3Fork.sellToUniswapV3`, `:73`), so the settler's *entire* current
balance of the sell token is the base — any pre-existing balance is swept in.

**Why it is risky.** Whole-balance accounting cannot distinguish "tokens that
arrived as genuine swap output" from "tokens already here / donated / produced by
a side exchange." The slippage guard's protection rests on the "directly from us"
property; an action that lets value arrive another way undermines it.

**Concrete failure modes.**
- A new action that credits the buy token via a path the final-hop check cannot
  attribute → user appears satisfied by unrelated balance.
- A `bps`-based action sweeping a pre-existing balance the user didn't intend to
  sell (cross-action interaction).
- `unchecked` arithmetic overflow in positive-slippage / fee math producing a
  wrong payout.

**What to check (probes).**
- For each new action, ask: can it increase `buyToken.balanceOf(this)` without
  that increase being the genuine output of *this* swap? If yes, does the
  "directly from us" invariant still hold?
- Confirm any `unchecked` block's operands cannot overflow given realistic token
  supplies (the code argues reserves are ≤128 bits — verify per token type).
- Confirm fee-on-transfer / rebasing tokens cannot desync the measured delta from
  the intended amount (ties to Scope A).

---

## Theme 9 — Tight coupling to deployment and registry state

**Idea.** Instances assume a precise relationship with the deployer registry at
both construction and runtime. Deployment-ordering or registry mismatches render
an instance invalid, unreachable, or impersonable.

**How it works here.**
- **Construction assert.** `SettlerBase` constructor
  (`src/SettlerBase.sol:69-76`) asserts
  `IERC721Owner(DEPLOYER).ownerOf(_tokenId()) == address(this)` (except chainid
  31337). `BridgeSettlerBase` does the same (`src/bridge/BridgeSettlerBase.sol:34-41`).
  This couples deploy scripts (`sh/deploy_new_chain.sh`,
  `sh/common_deploy_settler.sh`) and the `gitCommit` constructor arg tightly to
  registry state.
- **Runtime discovery.** The README mandates resolving the live address via
  `ownerOf(featureId)`, with a `prev(featureId)` fallback during the 0x API
  "dwell" window, and **never hardcoding**. A revert from `ownerOf` means paused.
- **Bridge genuineness check.** `BridgeSettlerBase._requireValidSettler`
  (`src/bridge/BridgeSettlerBase.sol:43-56`) re-implements the README's
  `ownerOf || prev` check before delegating a swap (ties to Theme F).

**Why it is risky.** If discovery logic, dwell handling, or the construction
assert diverge from registry behavior, callers may target a paused, stale, or
counterfeit instance, or a deploy may silently brick.

**Concrete failure modes.**
- A deploy script change that registers ownership *after* construction → the
  constructor assert reverts and deployment fails (fail-safe, but a footgun).
- An integrator hardcoding an address and missing a dwell-time rotation.
- The bridge's `_requireValidSettler` drifting from the registry's actual
  `ownerOf`/`prev` semantics → either rejecting valid settlers or accepting
  stale ones.

**What to check (probes).**
- Confirm the construction assert matches the deploy script ordering and the
  `gitCommit` argument wiring.
- Confirm `_requireValidSettler` uses the same feature id (2) and the same
  `ownerOf || prev` logic as the README's reference code.
- Confirm pause (revert) and dwell (`prev`) semantics are handled wherever the
  registry is read.

---

## Theme 10 — Divergent code paths with different trust profiles

**Idea.** Different modes delegate trust differently — sometimes relying on an
external component to enforce a constraint not re-checked locally. A new mode that
copies a path but not all its preconditions inherits a weaker check set.

**How it works here.** The **forwarded (AllowanceHolder) path** vs. the **Permit2
path** in `Permit2PaymentTakerSubmitted._transferFrom`
(`src/core/Permit2Payment.sol:402-471`):
- *Forwarded:* requires `sig.length == 0` (`:409-413`), `nonce == 0` (`:415`),
  checks the deadline manually (`:416-422`), and **does not check
  `requestedAmount`** because *"it's checked by AllowanceHolder itself"* (`:423`).
  It then calls `_allowanceHolderTransferFrom` (`:473-505`).
- *Permit2:* builds and calls `permitTransferFrom` in assembly (`:441-469`).

Meta-transaction flavors **deliberately disable** the forwarded path:
`Permit2PaymentMetaTxn._allowanceHolderTransferFrom` reverts `ConfusedDeputy`
(`:599-601`), and the `metaTx` modifier reverts `ForwarderNotAllowed` if
`_isForwarded()` (`:608-614`). The `takerSubmitted`/`metaTx` modifiers are also
mutually exclusive per flavor (each reverts in the wrong flavor, `:514-517`,
`:603-606`). The intent flavor additionally hard-codes `_isForwarded()` to false
(`SettlerIntent._isForwarded`, `:260-262`).

The Intent `_toCanonicalSellAmount` (`Permit2Payment.sol:650-660`) adds yet
another profile: it only applies proportional (`bps`-style) sell amounts when the
caller's `codehash == _BRIDGE_WALLET_CODEHASH` (`:647-648`) — a trust decision
keyed on bytecode identity.

**Why it is risky.** Each path is safe only with its full set of preconditions. A
new flavor or action that reuses a transfer helper without re-establishing
"forwarded ⇒ sig empty ∧ nonce 0 ∧ amount enforced by AH" (or without disabling
forwarding where it must be off) inherits an unauthenticated transfer.

**Concrete failure modes.**
- A new flavor that forgets to disable the forwarded path → unauthenticated
  AllowanceHolder transfer.
- A transfer helper reused without the `sig.length == 0` / `nonce == 0` guards.
- A change to the codehash-keyed branch that lets a non-bridge wallet trigger the
  proportional-amount logic, or that goes stale when the bridge wallet code
  changes.

**What to check (probes).**
- For every entrypoint/flavor: which transfer path can it reach, and are *all*
  preconditions for that path enforced on that route?
- Confirm `metaTx` and `takerSubmitted` remain mutually exclusive per flavor and
  that forwarding is disabled wherever required.
- Re-validate `_BRIDGE_WALLET_CODEHASH` against the current bridge-wallet
  bytecode; confirm the codehash gate cannot be spoofed.

---

# Part 2 — Audit Scope Notes (from 0x)

These are the areas 0x flagged for disproportionate attention. They are *where
the themes above bite hardest*, with concrete anchors.

## Scope A — The ERC-721 registry, NFT semantics, and "weird" tokens

Two token-shaped trust surfaces converge:

1. **The registry is an ERC-721 NFT.** Discovery (`ownerOf`), pausing (revert),
   and dwell (`prev`) are all NFT-call semantics that on-chain *and* off-chain
   consumers must interpret identically (ties to Theme 9). The bridge re-encodes
   this in `_requireValidSettler` (`src/bridge/BridgeSettlerBase.sol:43-56`).
2. **ERC-20 "weird tokens" are a first-class hazard.** Because settlement relies
   on balance deltas (Theme 8) and `bps`-of-balance sell amounts, the dangerous
   classes are:
   - **Fee-on-transfer / deflationary:** measured received amount < nominal; the
     "directly from us" slippage check and `bps` math can be skewed. Several
     actions carry an explicit `feeOnTransfer` flag (e.g. `UNISWAPV4`,
     `BALANCERV3`, `EKUBO` in `ISettlerActions.sol`) — verify it is honored.
   - **Rebasing:** balance changes out from under the settler between actions.
   - **Missing-return / non-reverting:** handled via `SafeTransferLib`
     (`src/vendor/SafeTransferLib.sol`) — confirm every transfer goes through it.
   - **Reentrant / ERC-777 / double-entrypoint / hooked (ERC-20 with callbacks):**
     can re-enter during a transfer; the `_PAYER_SLOT` guard (Theme 0.4) is the
     backstop — confirm it actually covers the path.

**Review lens.** For every token-touching action, ask which weird-token class
could make the balance-delta accounting lie, whether `feeOnTransfer` handling is
correct, and whether the slippage check still protects the user when the token
misbehaves.

## Scope B — Chain proliferation: skip most chains, keep Mainnet

There are 20+ chain directories (`src/chains/`), each with four flavor files plus
a `Common.sol`. Most are thin, near-identical configs over `SettlerBase`.

**Guidance from 0x:** you can largely **skip the per-chain directories** in deep
review and concentrate on **Mainnet** (`src/chains/Mainnet/Common.sol`), whose
mixin has the most integrations and therefore the most novel code. The risk that
*does* live in the other chains is **Theme 2 (copy/paste drift)** and **Theme 4
(environmental assumptions)**.

**Review lens.** Diff each chain's `Common.sol _dispatch` and `_uniV3ForkInfo`
against the canonical base/Mainnet versions to confirm faithful supersets and
correct constants; confirm each chain supports the EVM features the base assumes;
spend the remaining budget on Mainnet's integrations and `src/core/`.

## Scope C — The fork integrations (and the Lido pattern reuses them)

`src/core/univ3forks/` holds 25+ Uniswap-V3-style fork configs (Aerodrome,
Algebra, Camelot, Pancake, Sushi, Velodrome Slipstream, …). Each is "the same
swap/callback code with different constants": a `factory`, an `initHash`, a
`forkId`, and a callback selector, wired in `_uniV3ForkInfo`
(`src/chains/Mainnet/Common.sol:203`) and consumed by `_toPool`
(`src/core/UniswapV3Fork.sol:278-309`) and the callback path (Theme 5).

**Why interesting.** A wrong `initHash`/`factory`/fee-bit layout silently points
the settler at the wrong pool or breaks callback authentication (Theme 5 + Theme
2). One subtle constant error can be copied across many forks. Note the EraVM
variant (`_isEraVmUniV3Fork`, `:273-275`; `uniswapV3InitHashEraVm` in
`src/core/univ3forks/UniswapV3.sol:24`) uses a *different* derivation — easy to
get wrong.

**The same pattern is being applied for Lido.** A Lido-style integration reuses
the fork shape, so the same class of constant/callback-authentication mistakes
applies — **plus** Lido-specific wrap/unwrap (stETH↔wstETH) and the rebasing
nature of stETH (Scope A, Theme 8). Treat a new Lido entry with the same scrutiny
as a new fork *and* a new weird-token integration.

**Review lens.** For each fork/Lido entry: (1) verify `factory`/`initHash`/
`forkId` against an authoritative source; (2) confirm `_toPool` derives an
address that only the genuine pool can occupy; (3) confirm the callback selector
matches the fork's actual callback; (4) for Lido, verify wrap/unwrap math and
rebasing handling.

## Scope D — Off-chain transaction encoding is part of the trust boundary

Because on-chain decoding is intentionally lax (Theme 1), **the off-chain encoder
that builds the action stream and the signed structs is a security-relevant
component**.

- A wrong offset/selector/amount/recipient in the encoder is *not* caught by the
  decoder; it either reverts opaquely or executes something unintended.
- For signed flows, the encoder must produce *exactly* the bytes the on-chain
  witness hashing expects. `SettlerMetaTxn._hashArrayOfBytes`
  (`src/SettlerMetaTxn.sol:29-52`) hashes each action's bytes; the typehashes
  (`src/SettlerAbstract.sol:11-17`) and witness suffixes
  (`src/core/Permit2Payment.sol:580-581`, `:643-645`) must match the off-chain
  EIP-712 layout byte-for-byte. Any drift breaks signature validation or, worse,
  unbinds the signature from execution (Theme 3).
- VIP action argument ordering is itself a convention: `ISettlerActions`
  (`src/ISettlerActions.sol:7-9`) states VIP actions must start with
  `recipient` then `permit`, and `minBuyAmount` must be last, "to ensure
  compatibility with `executeWithPermit`" — which reads the token from a fixed
  calldata offset (`Settler.sol:144-159`). An encoder that violates this ordering
  silently mis-targets the permit.

**Review lens.** Treat encoder ↔ decoder as one unit. Confirm the encoder cannot
emit calldata whose lax-decoded meaning differs from the intended one; confirm the
signed-struct layout matches on-chain hashing exactly; confirm VIP argument
ordering matches the `executeWithPermit` offset assumptions.

## Scope E — `src/core/` is the interesting scope

`src/core/` holds the real logic: `RfqOrderSettlement`, `UniswapV3Fork`,
`UniswapV2`, `UniswapV4`, `Velodrome`/`VelodromeAlt`, `MaverickV2`, `BalancerV3`,
`EkuboV2`/`V3`, `EulerSwap`, `MakerPSM`, `DodoV1`/`V2`, `Bebop`, `Hanji`,
`Renegade`, `NucleusTeller`, the bridge actions (`Relay`, `LayerZeroOFT`, `CCIP`,
`Across`, `DeBridge`, `Mayan`, `StargateV2`), and the `Permit2Payment` layer.

This is the highest-value surface because:
- New attack surface enters here (every new DEX = a new mixin).
- Themes 1, 5, and 8 concentrate here (novel calldata, novel callbacks, novel
  balance accounting).
- `Permit2Payment.sol` is the crossroads of identity resolution (Theme 6),
  callback authentication (Theme 5), the witness/authorization machinery (Theme
  3), and the forwarded-path trust split (Theme 10).

**Review lens.** Prioritize `src/core/` over chain glue. For each mixin run the
three standing questions: **(1)** does it revert on malformed/aliased input
(Theme 1)? **(2)** can its callback be spoofed / is its target trusted-derived
(Theme 5)? **(3)** can its balance accounting be fooled, including by weird
tokens (Theme 8 + Scope A)?

## Scope F — Bridge: cross-chain logic is isolated from swap logic

`BridgeSettler` (tokenId 5) is deliberately **isolated from the swap engine**. It
does not embed DEX integrations; its `_dispatch`
(`src/bridge/BridgeSettlerBase.sol:58-113`) handles only bridge/relay actions
(`SETTLER_SWAP`, `BASIC`, `BRIDGE_ERC20_TO_RELAY`, `BRIDGE_NATIVE_TO_RELAY`,
`BRIDGE_TO_LAYER_ZERO_OFT`, `UNDERPAYMENT_CHECK`, `BRIDGE_TO_CCIP`). When it needs
a swap it **delegates to the canonical taker-submitted Settler** via
`SETTLER_SWAP` (`:59-81`), first validating the target with `_requireValidSettler`
(`:43-56`).

How the delegation works and where the isolation can leak:
- **Native path** (`:64-71`): `settler.call{value: amount}(settlerData)` with
  arbitrary `settlerData`. The code comment warns this is **MEV-susceptible** —
  "Eth sent to Settler is available to any action being executed making this call
  subsectible to MEV attacks that force the swap to its Slippage limit."
- **ERC-20 path** (`:72-81`): approves AllowanceHolder
  (`safeApproveIfBelow`) and calls `ALLOWANCE_HOLDER.exec(settler, token, amount,
  settler, settlerData)`. Same documented MEV exposure if `settlerData` starts
  with a VIP action.
- **The safety rests on:** (a) `_requireValidSettler` proving the target is the
  genuine, registry-current settler (Theme 9); (b) the genuine settler's own
  `_isRestrictedTarget`/VIP handling (Theme 5). The bridge passes *arbitrary*
  `settlerData` "as we know it is not a restricted target" — i.e. the only
  reason this is safe is that the target was validated.

**Review lens.** Confirm `_requireValidSettler` cannot be bypassed and matches
registry semantics; confirm the bridge never treats a restricted target as a swap
target; treat the documented MEV exposure as a fixed, accepted boundary and flag
any change that widens it (e.g. relaxing the validity check, or letting
`settlerData`/`settler` be chosen less restrictively).

## Scope G — `CrossChainReceiverFactory`: 0x flagged "an interesting bug — find it"

`src/CrossChainReceiverFactory.sol` (`pragma =0.8.34`, ~1225 lines) is the most
assumption-dense contract in the tree. It is a **factory + counterfactual proxy
account**: `deploy` (`:399-441`) CREATE2-deploys a minimal proxy whose address is
derived from a Merkle `root` and an `initialOwner`; the proxy delegatecalls back
into this implementation. The account supports two signature schemes
(`isValidSignature`, `:290-359`), an EIP-712 `MultiCall` meta-transaction
(`metaTx`, `:882-1027`), Permit2 unordered-nonce bookkeeping (`_useUnorderedNonce`,
`:675-701`), native/wrapped-native juggling, and `selfdestruct` cleanup.

I have **not confirmed a definitive exploit**. Below are the highest-value
candidate areas, framed honestly as *leads* (each maps to Theme 1 and/or Theme 4
— assumption boundaries among multiple hand-written decoders/hashers over the same
bytes). An audit agent should treat these as prioritized hypotheses to prove or
disprove.

1. **Dual signature decoding ambiguity** (`isValidSignature`, `:290-359`).
   The function chooses between a *Merkle-proof* signature and an *ERC-7739*
   nested signature based on whether the first word decodes as a clean address
   (`validOwner := iszero(shr(0xa0, originalOwner))`, `:336-338`). The security
   argument is a stated **96-bit hardness** claim (`:305-313`) that a signature
   cannot validly decode as *both*. **Probe:** can a boundary-length or crafted
   signature be steered down the wrong branch? Is the `signature.length >> 6 == 0`
   ERC-7739 empty-sentinel early-return (`:318-324`) abusable for a hash of
   `0x7739...`?

2. **Merkle root with empty/short proofs** (`_getMerkleRoot`, `:1047-1080`;
   `_verifyDeploymentRootHash`, `:1082-1105`). With `proof.length == 0`, `root ==
   leaf`. **Probe:** can a length-0/1 proof assert membership of an
   attacker-chosen `hash`, given the root must re-derive `address(this)` from
   `(root, originalOwner)`? Confirm the leaf construction's chainid-non-aliasing
   assumption (`_hashLeaf`, `:361-375`, Theme 4) actually holds.

3. **`metaTx` nonce/owner/relayer packing** (`:882-947`). Upper 160 bits of
   `nonce` encode the owner; upper bits of `deadline` optionally encode a
   permitted relayer (`:890-899`). Two branches build the signing hash with
   *different domain separators* — real (`_eip712SigningHash`, `:729-743`) vs.
   sentinel (`_nonEip712SigningHash`, `:752-761`). **Probe:** is the relayer
   binding actually covered by the signed hash? Can `deadlineForHashing` vs. the
   masked `deadline` be played against each other? Is the
   "ownership-transferred-back" comment (`:933-939`) an exploitable replay window?

4. **Nonce-invalidation ordering** (`_useUnorderedNonce`, `:675-701`, called at
   `:947` *before* the external `multicall` at `:990-991`). **Probe:** can the
   pre-call native/wrapped withdraw (`:949-982`) or the multicall re-enter
   `metaTx` with the same nonce before invalidation is observable? Confirm the
   Permit2 bitmap read/write cannot desync.

5. **`call(..., ppm, patchOffset, ...)` amount patching** (`:594-673`). Computes
   `patchBytes = ppm * balance / 1e6` and `mstore`s a full word at `patchOffset`
   into copied calldata (`:652-654`); the bounds check only guarantees
   `patchOffset + 31 < data.length` (`:604-610`). **Probe:** can the patch clobber
   adjacent encoded fields the target misinterprets? Does the native-vs-ERC20
   branch select `value` consistently with the patched amount (`:634`, `:647`)?

6. **`cleanup`/`selfdestruct` post-Cancun** (`:1029-1045`). `deploy(setOwnerNot
   Cleanup=false)` relies on `cleanup` self-destructing in the *same* tx as the
   CREATE2 (the only case post-Cancun where code is actually removed). **Probe:**
   does the `_MISSING_WNATIVE` force-to-`setOwner` (`:406`) and the same-tx
   assumption always hold? Can a proxy left un-cleaned be re-used adversarially?

7. **`receive()` auto-wrap + `getFromMulticall` sentinel substitution**
   (`receive`, `:1211-1223`; `getFromMulticall`, `:483-562`). The proxy forwards
   incoming native to wrapped-native; `getFromMulticall` substitutes `caller()`
   for the `_ADDRESS_THIS_SENTINEL` recipient (`:487-490`). **Probe:** can these
   conveniences be combined to redirect funds or strand value in `MultiCall`?

**Unifying review lens.** The bug, if present, most likely lives at one of these
*assumption boundaries* (clean padding, length bounds, chainid non-aliasing,
domain-separator selection, same-tx self-destruct, nonce-before-call) rather than
in the high-level control flow. Prove each assumption holds for adversarial inputs.

---

## Part 3 — Per-change review checklist (operational)

When reviewing a diff, work top to bottom:

1. **Locate** the change in §0 (which flavor, which dispatch tier, which layer).
2. **Decode safety (Theme 1):** if it touches action handling, does it revert on
   truncated/aliased input?
3. **Copy/paste (Theme 2):** if it touches `_dispatch`/`_dispatchVIP`/fork
   constants, are all mirrors updated?
4. **Authorization (Themes 3, 7, 10):** does it preserve "first action spends the
   witness," the solver-list invariants, and the per-path transfer preconditions?
5. **Callbacks/targets (Theme 5):** is any new external target trusted-derived?
   Is any new privileged contract added to `_isRestrictedTarget`?
6. **Identity (Theme 6):** if it touches base lists or `_msgSender`/`_operator`/
   override stubs, recompute resolution.
7. **Accounting (Theme 8 + Scope A):** can balance deltas be fooled? Weird tokens?
   `unchecked` overflow?
8. **Environment (Theme 4):** new chain / size growth / chainid-in-hash / EVM
   version?
9. **Registry (Theme 9):** construction assert + runtime discovery still correct?
10. **Tests:** per `CLAUDE.md`, integration tests must run against **real** forked
    contracts (no mocks of the contract-under-test or of infrastructure like
    Permit2). A change without a test that exercises the real path is incomplete.

---

## Appendix — File map (for navigation)

| Area | Path | Notes |
|------|------|-------|
| Lax decoder | `src/SettlerBase.sol:31-54` | `CalldataDecoder.decodeCall` |
| Shared action engine | `src/SettlerBase.sol:117-181` | `_dispatch` (copy/pasted to Mainnet) |
| Taker flavor | `src/Settler.sol` | `execute`, `executeWithPermit`, `_dispatchVIP` |
| MetaTxn flavor | `src/SettlerMetaTxn.sol` | witness hashing, `_executeMetaTxn` |
| Intent flavor | `src/SettlerIntent.sol` | solver list, `onlySolver`, slippage-only witness |
| Identity/abstract | `src/SettlerAbstract.sol`, `src/Context.sol` | typehashes, constants |
| Payment + transient | `src/core/Permit2Payment.sol` | `TransientStorage`, transfer paths, modifiers |
| Payment interface | `src/core/Permit2PaymentAbstract.sol` | virtual surface |
| Callback template | `src/core/UniswapV3Fork.sol` | `_setOperatorAndCall`, `_toPool`, callback |
| Action catalog | `src/ISettlerActions.sol` | selector definitions + VIP ordering rule |
| Chain mixins | `src/chains/<Chain>/Common.sol` | Mainnet is richest |
| Fork configs | `src/core/univ3forks/*.sol` | factory/initHash/forkId per fork |
| Bridge | `src/bridge/BridgeSettler*.sol` | isolated engine, delegates swaps |
| Cross-chain account | `src/CrossChainReceiverFactory.sol` | flagged bug-hunt target |
| Errors | `src/core/SettlerErrors.sol` | all custom errors live here |

## Appendix — Summary table of themes & scope

| # | Theme / Scope | One-line risk |
|---|---------------|----------------|
| 1 | Unchecked input decoding | Safety delegated to every consumer reverting on garbage/aliased input |
| 2 | Duplicated logic | Copy/pasted dispatch & fork constants drift out of sync |
| 3 | Positional authorization | A path decouples the signature/witness from executed work |
| 4 | Environmental assumptions | Packing/hash/EVM assumptions break on a new chain/toolchain |
| 5 | Callback / confused deputy | Untrusted target or selector collision relays attacker intent |
| 6 | Inheritance order | Refactor swaps payer vs. operator identity |
| 7 | Hand-maintained structures | Assembly solver-list bug orphans or mis-authorizes |
| 8 | Balance accounting | Stray/donated/weird-token balance satisfies a swap-output check |
| 9 | Registry coupling | Deploy/dwell/genuineness mismatch points callers at a bad instance |
| 10 | Divergent trust profiles | A new mode copies a path but not its safety preconditions |
| A | NFT + weird tokens | Balance-delta accounting lies for FoT/rebasing/reentrant tokens |
| B | Chain proliferation | Skip most chains, focus on Mainnet; watch for divergence |
| C | Fork (+ Lido) configs | One wrong constant/callback shape copied across many forks |
| D | Off-chain encoding | Encoder bugs are unguarded by the lax on-chain decoder |
| E | `src/core/` | Highest-value surface; every new DEX adds attack surface here |
| F | Bridge isolation | Confused-deputy / MEV boundary around the delegated swap |
| G | `CrossChainReceiverFactory` | Assumption-boundary bug among multiple hand-rolled decoders |
