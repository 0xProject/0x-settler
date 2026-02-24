# 0x Settler - Development Guide

## Business Context

0x Settler is a gas-optimized DEX aggregator settlement system that executes token swaps without holding passive allowances. It leverages [Permit2](https://github.com/Uniswap/permit2) for secure, one-time token transfers and supports multiple execution modes:

- **Taker-Submitted (tokenId=2)**: Direct user transactions
- **MetaTxn (tokenId=3)**: Gasless/relayed transactions where users sign over actions
- **Intent (tokenId=4)**: Solver-authorized execution with user-signed slippage constraints
- **Bridge Settler (tokenId=5)**: Cross-chain swap execution

Key addresses:
- Deployer/Registry: `0x00000000000004533Fe15556B1E086BB1A72cEae`
- Permit2: `0x000000000022D473030F116dDEE9F6B43aC78BA3`
- AllowanceHolder (Cancun): `0x0000000000001fF3684f28c67538d4D072C22734`
- CrossChainReceiverFactory: `0x00000000000000304861c3aDfb80dd5ebeC96325`

## Architecture Overview

### Three-Flavor Settlement Pattern

```
SettlerAbstract (virtual dispatch interface)
    |
    +-- SettlerBase (RFQ + UniV3 + UniV2 + Velodrome + Basic)
    |       |
    |       +-- Settler (TakerSubmitted, tokenId=2)
    |       +-- SettlerMetaTxn (tokenId=3)
    |               |
    |               +-- SettlerIntent (tokenId=4)
    |
    +-- BridgeSettlerBase (tokenId=5)
```

Each chain has its own `Common.sol` mixin that inherits from `SettlerBase` and adds chain-specific DEX support (e.g., `MainnetMixin` adds MakerPSM, MaverickV2, DodoV1/V2, UniswapV4, BalancerV3, Ekubo, EulerSwap).

### Directory Structure

```
src/
├── Settler.sol              # TakerSubmitted base
├── SettlerMetaTxn.sol       # MetaTxn base
├── SettlerIntent.sol        # Intent base
├── SettlerBase.sol          # Common settlement logic + CalldataDecoder
├── SettlerAbstract.sol      # Virtual dispatch interface
├── ISettlerActions.sol      # Action selector definitions
│
├── chains/                  # Chain-specific implementations (~27 chains)
│   └── <ChainName>/
│       ├── Common.sol       # Chain mixin (DEX integrations)
│       ├── TakerSubmitted.sol
│       ├── MetaTxn.sol
│       ├── Intent.sol
│       └── BridgeSettler.sol
│
├── core/                    # Action implementations (mixins)
│   ├── Basic.sol            # Generic pool interactions
│   ├── RfqOrderSettlement.sol
│   ├── UniswapV3Fork.sol    # V3 + 30+ forks
│   ├── UniswapV2.sol
│   ├── UniswapV4.sol
│   ├── Velodrome.sol
│   ├── MakerPSM.sol
│   ├── MaverickV2.sol
│   ├── DodoV1.sol, DodoV2.sol
│   ├── BalancerV3.sol
│   ├── Ekubo.sol
│   ├── EulerSwap.sol
│   ├── Permit2Payment.sol   # Transient storage + Permit2 integration
│   ├── SettlerErrors.sol    # Custom errors
│   └── univ3forks/          # UniV3 fork configurations
│
├── allowanceholder/         # AllowanceHolder integration
├── bridge/                  # Cross-chain bridge support
├── deployer/                # Deployment infrastructure
├── multicall/               # ERC-2771 multicall forwarding
├── utils/                   # Utilities (512Math, UnsafeMath, etc.)
└── vendor/                  # Vendored libraries (SafeTransferLib, FullMath)

test/
├── integration/             # Fork tests (run with FOUNDRY_PROFILE=integration)
├── unit/                    # Unit tests
└── utils/                   # Test utilities (Permit2Signature, ActionDataBuilder)
```

### Key Design Patterns

#### 1. Action Dispatch System

Actions are identified by 4-byte selectors from `ISettlerActions`. Dispatch happens at two levels:
- **VIP dispatch** (first action only): Direct Permit2 transfers (`TRANSFER_FROM`, `UNISWAPV3_VIP`, etc.)
- **Regular dispatch** (all actions): Pool interactions using settler-held balances

```solidity
// In Settler.execute()
if (!_dispatchVIP(action, data)) {
    if (!_dispatch(0, action, data)) {
        revertActionInvalid(0, action, data);
    }
}
```

#### 2. Transient Storage for Reentrancy

Uses EIP-1153 transient storage (`tload`/`tstore`) for:
- `_OPERATOR_SLOT`: Active operator + callback selector + callback function pointer
- `_WITNESS_SLOT`: EIP-712 witness hash for metatxns
- `_PAYER_SLOT`: Current payer (implicit reentrancy guard)

#### 3. CalldataDecoder (Lax Decoding)

Custom ABI decoder in `SettlerBase.sol` that:
- Omits bounds/overflow checking for gas efficiency
- Allows negative offsets and calldata aliasing
- Enables advanced calldata reuse patterns

#### 4. Mixin-Based Composition

Chain-specific functionality is composed via mixins. When adding a new DEX:
1. Create action implementation in `src/core/`
2. Add to chain's `Common.sol` mixin
3. Add action selector to `ISettlerActions.sol`
4. Implement in `_dispatch()` and optionally `_dispatchVIP()`

## Solidity Contribution Guidelines

### General Principles

- **Think first, code second**: Minimize lines changed; consider ripple effects
- **Prefer simplicity**: Fewer moving parts = fewer bugs and lower audit overhead
- **Contract size matters**: This codebase is at the edge of the 24KB limit

### Assembly Usage

| Rule | Rationale |
|------|-----------|
| Use assembly only when essential | Keeps code readable and auditable |
| Assembly is mandatory for low-level external calls | Full control over call parameters & return data, saves gas |
| Precede every assembly block with: brief justification + equivalent Solidity pseudocode | Documents intent for reviewers |
| Mark assembly blocks `memory-safe` when criteria are met | Enables compiler optimizations |

### Gas Optimization

- Keep a dedicated **Gas Optimization** section in PR descriptions
- Prefer `calldata` over `memory` for function arguments
- Limit storage operations; use transient storage where possible
- Use `unchecked` blocks for safe arithmetic
- Use `DANGEROUS_freeMemory` modifier sparingly (see `FreeMemory.sol`)

```bash
npm run snapshot:main   # captures gas baseline from main
npm run diff:main       # compares your branch vs. main
```

### Stack Too Deep Solutions

1. **Scoped blocks**: Wrap code in `{ ... }` to drop unused vars
2. **Internal helper functions**: Encapsulate logic to shorten call frames
3. **Struct hack (tests only)**: Bundle locals into a temporary struct
4. **Refactor first**: Delete unnecessary variables before other tricks

### Error Handling

Use custom errors (defined in `src/core/SettlerErrors.sol`) with the if/revert pattern:

```solidity
if (amount == 0) revert AmountMustBePositive();
```

For code size optimization, implement reverts in assembly. Solidity generates right-padded `bytes4` constants which are expensive; assembly allows left-padded `uint32` constants that consume less contract size:

```solidity
// Assembly revert saves contract size
assembly ("memory-safe") {
    mstore(0, 0x12345678) // uint32 selector, left-padded
    revert(0x1c, 0x04)
}
```

Errors must always be defined in `SettlerErrors.sol` regardless of whether thrown from Solidity or assembly.

### Security Checklist

- Review every change with an adversarial mindset
- Favor the simplest design that meets requirements
- After coding, ask: "What new attack surface did I introduce?"
- Reject any change that raises security risk without strong justification
- **Confused Deputy Prevention**: Always check `_isRestrictedTarget()` before arbitrary calls
- **Callback Security**: Verify callbacks come from trusted addresses (derived via initHash)

### Reentrancy Protection

Follow the Checks-Effects-Interactions (CEI) pattern: all state changes before external calls. This codebase also uses transient storage (`_PAYER_SLOT`) as an implicit reentrancy guard:

```solidity
modifier takerSubmitted() override {
    address msgSender = _operator();
    TransientStorage.setPayer(msgSender);  // Sets guard
    _;
    TransientStorage.clearPayer(msgSender); // Clears guard
}
```

## Testing Guidelines

### Core Testing Principles

**Every feature or change MUST have comprehensive tests before creating a PR.** This is non-negotiable for maintaining code quality and preventing regressions.

### CRITICAL: Test the Real Contract, Not Mocks

**DO NOT write mocks that replicate production logic and then test the mocks.** This anti-pattern has directly caused production bugs in this codebase.

```solidity
// ❌ WRONG: Testing a mock instead of production code
contract MockSettler {
    function execute(...) { /* your guess at how it should work */ }
}
function test_execute() {
    MockSettler mock = new MockSettler();
    mock.execute(...);
}

// ✅ CORRECT: Test the actual production contract
function test_execute() {
    Settler settler = new Settler(...);  // The REAL contract
    settler.execute(...);
}
```

| Test Type | Mocks Allowed? | What to Test Against |
|-----------|----------------|---------------------|
| Unit tests | Sparingly, for external dependencies only | Real contract-under-test; may mock external calls |
| Integration tests | **NO** | Real contracts on chain forks |

**Integration tests are where most bugs are caught.** They must use real, live contracts via chain fork tests.

**Infrastructure contracts (Permit2, UniswapV4 PoolManager, etc.):**
- Do NOT mock these, even in unit tests
- Deploy the real contracts into the test environment
- These contracts are critical to correctness and must be tested authentically

**When mocks ARE appropriate (unit tests only):**
- Controlling specific return values from external AMM pools
- Simulating error conditions that are hard to trigger naturally
- NEVER for the contract-under-test itself
- NEVER for infrastructure contracts (Permit2, etc.)
- NEVER in integration tests

### When to Write Tests

- **New Features/Actions**: Write tests demonstrating the complete flow and all edge cases
- **Bug Fixes**: Add tests that reproduce the bug and verify the fix
- **Refactoring**: Ensure existing tests still pass; add new ones if behavior changes
- **Gas Optimizations**: Include benchmark tests showing before/after comparisons

### Types of Tests

- **Unit tests**: Happy paths, failure cases, edge cases, revert conditions. Name format: `test_FeatureName_Scenario_Outcome()`
- **Integration tests (fork tests)**: Live against forked mainnet state. Inherit from `BasePairTest`:

```solidity
abstract contract BasePairTest is Test, GasSnapshot, Permit2Signature, MainnetDefaultFork {
    function fromToken() internal view virtual returns (IERC20);
    function toToken() internal view virtual returns (IERC20);
    function amount() internal view virtual returns (uint256);
}
```

- **Fuzz tests**: Highly encouraged. Foundry is configured for 100,000 fuzz runs. Use `bound()` and `vm.assume()` to constrain inputs.

```solidity
function testFuzz_myFeature(uint256 amount, address user) public {
    amount = bound(amount, 1, type(uint128).max);
    vm.assume(user != address(0));
    // Test logic
}
```

### Test Commands

**IMPORTANT:** The canonical test commands are defined in the CI workflow files. Before running tests, read these files to get the exact commands:

- `.github/workflows/test.yml` - Unit tests, build steps, and special contract tests
- `.github/workflows/integration.yml` - Integration/fork tests

**RPC URLs Required:** Many tests require RPC URLs for forked network access. If you need to run integration tests or fork tests and don't have the RPC URLs configured, use the `AskUserQuestion` tool to request them from the user. Required environment variables include:
- `MAINNET_RPC_URL`
- `BNB_MAINNET_RPC_URL`
- `PLASMA_MAINNET_RPC_URL`
- `ARBITRUM_MAINNET_RPC_URL`
- `BASE_MAINNET_RPC_URL`
- `MONAD_MAINNET_RPC_URL`

## Development Workflow

### Prerequisites

Foundry v1.5.1, Node.js 18.x, and git submodules (`git submodule update --recursive --init`).

### Solc Versions

The codebase uses multiple Solidity compiler versions for different contracts:

| Component | Solc Version | EVM Version | Optimizer Runs |
|-----------|--------------|-------------|----------------|
| Main contracts (`src/`) | 0.8.25 | cancun | 2,000 |
| UniswapV4 (`lib/v4-core/`) | 0.8.26 | cancun | 2,000 |
| MultiCall | 0.8.28 | london | 1,000,000 |
| CrossChainReceiverFactory | 0.8.28 | london | 1,000,000 |
| EulerSwapBUSL tests | 0.8.28 | cancun | 2,000 |

### Building

```bash
# Standard build (skips special contracts)
forge build --skip MultiCall.sol --skip CrossChainReceiverFactory.sol --skip 'test/*'

# Build MultiCall (requires london EVM)
FOUNDRY_EVM_VERSION=london FOUNDRY_OPTIMIZER_RUNS=1000000 FOUNDRY_SOLC_VERSION=0.8.28 \
  forge build -- src/multicall/MultiCall.sol

# Build CrossChainReceiverFactory (requires london EVM)
FOUNDRY_EVM_VERSION=london FOUNDRY_OPTIMIZER_RUNS=1000000 FOUNDRY_SOLC_VERSION=0.8.28 \
  forge build -- src/CrossChainReceiverFactory.sol

# Build UniswapV4 dependencies
FOUNDRY_SOLC_VERSION=0.8.26 forge build -- lib/v4-core/src/PoolManager.sol

# Check contract sizes
forge build --sizes --skip MultiCall.sol --skip CrossChainReceiverFactory.sol --skip 'test/*'

# Format code
forge fmt
```

### Foundry Configuration

Key settings in `foundry.toml`:
- `solc_version = "0.8.25"` (default)
- `via_ir = true` (required for contract size)
- `optimizer_runs = 2_000`
- `evm_version = "cancun"`
- `fuzz.runs = 100_000`
- Unit tests exclude `test/integration/*`
- Integration tests (`FOUNDRY_PROFILE=integration`) only match `test/integration/*`

### Commit Hygiene

**Stage only files you intentionally modified** (no `git add .`). Always run `git diff --staged` before committing.

```bash
# ✅ Stage specific files and review
git add src/core/MyFeature.sol test/unit/MyFeatureTest.t.sol
git diff --staged
git commit -m "Fix bug in MyFeature"
```

### Before Committing

```bash
# Build (matches CI)
forge build --skip MultiCall.sol --skip CrossChainReceiverFactory.sol --skip 'test/*'

# Run unit tests
forge test

# Check formatting
forge fmt --check

# Gas comparison (requires npm install)
npm run compare_gas

# Gas diff vs main
npm run diff:main
```

### CI Workflow

See `.github/workflows/test.yml` and `.github/workflows/integration.yml` for the full CI pipeline (builds, unit tests, integration tests, gas comparison).

### Adding a New Chain

1. Create chain directory: `src/chains/<ChainName>/`
2. Create `Common.sol` with chain-specific mixin
3. Create flavor files: `TakerSubmitted.sol`, `MetaTxn.sol`, `Intent.sol`, `BridgeSettler.sol`
4. Configure UniV3 forks in `_uniV3ForkInfo()`
5. Set `_POOL_MANAGER()` if UniswapV4 is available
6. Add to `chain_config.json`

### Adding a New DEX Integration

1. Create action mixin in `src/core/<DexName>.sol`
2. Add action selector to `ISettlerActions.sol`
3. Add to relevant chain mixins' `_dispatch()` method
4. Add VIP variant if it supports callback-based Permit2 payment
5. Write integration tests

## Key Constants

```solidity
uint256 internal constant BASIS = 10_000;  // BPS denominator
IERC20 internal constant ETH_ADDRESS = IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);
```

## Critical Reminders

### DO NOT

- Create documentation files unless explicitly requested
- Make up performance numbers or generic justifications for changes
- Add features beyond what was asked (no over-engineering)
- Modify the `_dispatch` copy/paste pattern without updating all locations
- Create standalone test files; use the project's test infrastructure

### ALWAYS

- Read relevant existing code before making changes
- Check gas impact with `npm run diff:main`
- Follow existing patterns in chain-specific code
- Mark assembly blocks `memory-safe` when appropriate
- Update both `_dispatch()` and `_dispatchVIP()` when adding VIP actions
- Consider all three settler flavors when making changes
- Measure performance changes properly; let improvements stand on technical merit

### Contract Size Constraints

The codebase is at the edge of the 24KB contract size limit:
- `via_ir = true` is required
- Functions are often written in assembly to save bytes
- ABI encoding is done manually to reduce size
- `DANGEROUS_freeMemory` modifier allows memory reuse
- Unused code paths should be removed, not commented out

## Using Cast

### Settler-Specific Commands

```bash
# Get current Settler address from deployer
cast call 0x00000000000004533Fe15556B1E086BB1A72cEae "ownerOf(uint256)(address)" 2

# Check previous Settler (dwell time)
cast call 0x00000000000004533Fe15556B1E086BB1A72cEae "prev(uint128)(address)" 2

# Get next Settler address
cast call 0x00000000000004533Fe15556B1E086BB1A72cEae "next(uint128)(address)" 2

# Trace a transaction
cast run <txhash> --rpc-url $RPC_URL
```

### Forge Standard Library

See `lib/forge-std/src/*.sol` for cheatcodes and utilities that streamline testing (e.g., `Vm.sol`, `Test.sol`, `StdCheats.sol`).
