# 0x Settler

Settler executes token swaps for the 0x API. Deployed contracts are immutable, hold user funds during a transaction, and sit near the 24 KB size limit. Reviewers expect the smallest diff that does the job.

`README.md` covers the product; `CONTRIBUTING.md` covers what a PR must justify.

## Map

- `src/Settler.sol`, `SettlerMetaTxn.sol`, `SettlerIntent.sol`: the taker-submitted, metatransaction and intent flavors. They share `SettlerBase.sol`. `src/bridge/BridgeSettler.sol` is the fourth flavor.
- `src/core/`: actions, venue integrations and payment code shared by the flavors.
- `src/chains/<Chain>/Common.sol`: which actions each chain supports. Each chain also has one file per flavor.
- `src/ISettlerActions.sol`: action signatures and the argument-order rules in its header.
- `src/core/SettlerErrors.sol`: every custom error.
- `UNISWAPV3_FORKS.md`: UniswapV3 fork IDs and upgradeability notes.
- The default branch is `master`.

## How to work

- **Read the history.** Read the code and its history (`git log -p`, `git blame`) before you change something that looks wrong. Much of this codebase is deliberate.
- **Copy the closest example:** a sibling action, fork entry, test, deploy script or changelog line.
- **Keep the diff small.** Change only what the task needs. Do not reformat untouched code or remove the blank line after the header comment in `ISettlerActions.sol` (it keeps that comment out of `TRANSFER_FROM`'s natspec).
- **Justify every check.** Add a check, branch, parameter or helper only when you can name the input that needs it. Remove unused parameters and helpers that only wrap one call.
- **Working is not the same as correct.** A passing local test says little about code that talks to deployed contracts. Prove behavior on real chain state: fork tests through Settler against live pools, `cast` reads of storage and bytecode, and traces of real transactions. Record the chain and block.
- **Show your evidence.** For each verification claim, give the commands, inputs and results a reviewer needs to repeat it. Report what you did not verify. Never report a check you did not run.
- **Dry-run scripts.** Run deploy and admin scripts on a fork before anyone runs them for real.
- **State tradeoffs.** Explain the tradeoffs you make. Ask when the choice depends on the user's priorities.
- **Stop when blocked.** If something cannot be tested or verified, say so and stop the work that depends on it.

## Solidity

### Gas and size

- **Measure.** Measure gas and deployed bytecode size for any optimization, and record how. When gas is equal, choose the smaller bytecode.
- **Prefer Solidity.** Use assembly where it measurably saves gas or size, or where Solidity cannot express the operation, and say why in a comment when the reason is not obvious. Mark assembly `memory-safe` when it is.
- **Duplicated code.** Update every copy of code duplicated for gas, such as the `_dispatchVIP` copies in every chain's flavor files, and say in each copy that it is duplicated.

### Assembly style

- Write numbers in hex (`0x20`, not `32`). Named Solidity constants stay decimal.
- Put the literal on the left of commutative operations (`add(0x40, ptr)`), and flip comparisons to keep it there (`gt(C, x)` for `x < C`).
- Build selectors and padded values by shifting rather than masking where you can, and avoid `PUSH32` (see `src/vendor/SafeTransferLib.sol`).
- Combine revert conditions into one branch with `src/utils/FastLogic.sol`.
- Treat any nonzero `bool` as true.
- Revert with a left-padded `uint32` selector: `mstore(0x00, 0x12345678) revert(0x1c, 0x04)`. Define every custom error in `SettlerErrors.sol`.

### Inputs and calls

- **ABI encoding.** Accept any valid encoding, including non-strict ones. `CalldataDecoder` skips bounds checks on purpose.
- **Invalid input.** Reject it where it enters rather than silently cleaning it or falling back to a default. Assembly that needs clean bits cleans the narrow values it takes from the stack.
- **Empty calls.** Treat a call to an address with no code, or a call that returns too little data, as a failure unless the target's verified code rules it out.
- **Units.** Name them (shares or assets, wei or tokens) and state the rounding direction in fixed-point math.
- **External functions.** Do not add one without a strong reason; each adds attack surface. `msg.sender == address(this)` does not protect one, because `BASIC` can make Settler call itself.
- **Events.** Tell the data team before you add or change one.
- **Arbitrary calls.** Check `_isRestrictedTarget` first, or state in a comment why no restricted selector can be reached.

## Callbacks

- **One path.** Route every venue callback through `_setOperatorAndCall` (`src/core/Permit2Payment.sol`). It records the expected caller, selector and handler, clears them before the handler runs, and reverts if the callback never comes.
- **Trusted caller.** The expected caller must be an address an attacker cannot control: a pool derived from its deployer and init hash, or a fixed contract such as a vault or `PoolManager`.
- **Unchanged data.** UniswapV3 callback decoding skips bounds checks because the pool must return Settler's callback data unchanged, including its length. That data selects the payment mode and token, and may carry the taker's permit and signature. A pool that alters it can make Settler pay the wrong token or amount, or spend the wrong Permit2 permit.
- **Amounts.** Allow partial fills: the amount a callback asks for is the fill amount. Find out who controls the token, amount and destination in the callback. Where the venue does not enforce the action's limits, Settler must (for example, never pay more than the sell amount).

## Actions

- **Prefer `BASIC`** when the solver only needs to insert an amount into calldata. Add a new action only when Settler must pay in a callback, compute a value at runtime, or enforce something the venue cannot.
- **Match siblings.** `recipient` first; VIP actions take `recipient` then `permit`; `minBuyAmount` last. Reuse sibling names such as `zeroForOne`, and use the ERC-7528 address for native tokens.
- **Explicit fields.** If Settler reads a field, make it an action argument, not an offset into opaque `bytes`.
- **Direct output.** Add a `recipient` so output can go straight to the taker when the venue allows it.
- **Slippage.** Check a per-leg `minBuyAmount` against the amount the venue returns or transfers. Never prove a leg's output from the recipient's balance change around an external call; another transfer in the same transaction can inflate it. If the venue reports no output amount, drop the per-leg minimum and rely on the final slippage check. The final check measures only what Settler holds, so output that relies on it must pass through Settler.

## Integrating a venue

Before adding a DEX or UniswapV3 fork, identify which contracts and returned values the action trusts, and show that:

1. **Bytecode:** their source (public or supplied privately) recompiles to exactly the deployed bytecode.
2. **Pool addresses:** for CREATE2 pools, real pool addresses recompute from the contract that deploys the pool (which may differ from the factory), its salt and its init hash.
3. **No admin control:** no admin can change the behavior Settler relies on. No upgradeable pools, replaceable code or repointable addresses. An upgradeable factory with immutable pools is acceptable.
4. **Callback data:** the venue passes callback data (the `data` argument of `swap` for UniswapV3 forks) to the callback unchanged.
5. **Callback ABI:** the callback's selector, arguments and amount signs match what Settler handles. A fork that renames its callback has a different selector.

Report how you checked each point. If any point fails or cannot be checked, stop and report it. A new action needs a fork test against live contracts. A new UniswapV3 fork needs one when its address derivation, callback or swap behavior differs from existing forks.

## Tests

- **End to end on a fork.** Integration tests sign and submit through Settler's entry point, trade against the live venue, and assert what the taker receives.
- **No mocks of what you test.** Never mock the contract under test or infrastructure such as Permit2 or the UniswapV4 `PoolManager`. Unit tests may mock an external venue's return values or hard-to-reach errors.
- **Extend, don't duplicate.** Add to the existing test contract for the feature or venue rather than writing a parallel one.
- **Tests must fail when the code is wrong.** Assert amounts, recipients and revert reasons, and test both swap directions. Ask whether the test would still pass with a dead router, the wrong recipient or the wrong token.
- **Bugs.** First add a test that fails, then fix the bug.
- **Gas snapshots.** Measure gas only around the action, and use constants or immutables in tests so the numbers stay accurate.
- **RPC URLs.** Fork tests need variables such as `MAINNET_RPC_URL`. If they are not set, ask the user for them.

## Commands

Use the compiler, EVM and optimizer settings in CI (`.github/workflows/test.yml`, `integration.yml`, `size.yml`).

```bash
forge build --skip MultiCall.sol --skip CrossChainReceiverFactory.sol --skip SafeGuard.sol --skip AllowanceHolder.sol --skip Deployer.sol --skip 'src/chains/*' --skip 'test/*' --skip 'script/*'
forge build --sizes -- src/chains/<Chain>          # per-chain size check
forge test                                          # unit tests
FOUNDRY_PROFILE=integration forge test --skip 'src/*' --skip 'test/integration/arbitrum/*'   # fork tests; writes gas snapshots; Arbitrum runs separately via ./arbos-forge
COMPARE_GIT_SHA=$(git merge-base HEAD master) npm run compare_gas                            # gas vs master
npm run check_vips                                  # VIP signatures vs ISettlerActions.sol
forge fmt <files you changed>                       # never format the whole tree
```

## Comments and writing

- **What to comment.** Only what a reader cannot get from the code: derivations, odd encodings, external facts (with a link), policy choices, invariants, and duplicated code that must change together.
- **Current behavior only.** Comments describe what the code does now. Put change history in commit messages.
- **Existing comments.** Keep correct ones; fix ones your change makes wrong, including names they mention.
- **Plain words.** In comments, commits, PRs and replies, use plain words and active voice. Define the terms and assumptions a reader without your conversation needs. Do not invent jargon.
- **Nothing private.** Leave no TODOs. Never mention Slack, chats, private links, task IDs or plan labels in code, commits or PRs.

## Git and pull requests

- **Staging.** Stage only the files you meant to change, and read `git diff --staged` before committing.
- **Authorship.** Commit as the human you work for. End each commit message with a `Co-Authored-By:` line naming you (model or agent, and an email from your maker).
- **History.** Never rewrite published history: no force-push, and no deleting and recreating a remote branch. Never pass `-f` or `--force` to override a tool's safety check.
- **Permission.** Push, open PRs or post comments only when asked. Keep each PR to one concern.
- **PR descriptions.** Write plain prose: the business case, why current code does not cover it, what changed, alternatives you rejected (`CONTRIBUTING.md` requires these), and the gas and size effect. For a new venue, say how you ran each check. Leave out test counts, lists of commands run, and generic headers.
- **Changelog.** Add a `CHANGELOG.md` entry under `[Unreleased]` for any user-visible change. Name every chain it affects and match the wording of earlier entries.
- **Frozen files.** Do not edit files that must match a deployed or third-party version: `audits/` (including file names), `sh/initial_description_*.md` (uploaded on chain at deploy), and `src/vendor/SafeTransferLib_Solmate.sol` (keeps AllowanceHolder byte-for-byte identical).
- **No new docs.** Do not create documentation files unless asked.

## Code Review Rules

Flag a PR that breaks a rule above. Also check that:

- a human has reviewed any AI-written change (`CONTRIBUTING.md`);
- CI passes, including the size check;
- affected gas snapshots are regenerated and committed;
- the description matches the code.
