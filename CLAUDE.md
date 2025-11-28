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

Always use custom errors with the revert pattern instead of require statements:

```solidity
// ❌ Don't use require with string messages
require(amount > 0, "Amount must be positive");
require(to != address(0), "Cannot transfer to zero address");

// ✅ Do use custom errors with if/revert pattern
error AmountMustBePositive();
error CannotTransferToZeroAddress();

if (amount == 0) revert AmountMustBePositive();
if (to == address(0)) revert CannotTransferToZeroAddress();
```

**Benefits of custom errors:**
- More gas efficient than require strings
- Better error identification in tests and debugging
- Cleaner, more professional code
- Consistent with modern Solidity best practices

Custom errors for this project are defined in `src/core/SettlerErrors.sol`.

### Security Checklist

- Review every change with an adversarial mindset
- Favor the simplest design that meets requirements
- After coding, ask: "What new attack surface did I introduce?"
- Reject any change that raises security risk without strong justification
- **Confused Deputy Prevention**: Always check `_isRestrictedTarget()` before arbitrary calls
- **Callback Security**: Verify callbacks come from trusted addresses (derived via initHash)

### Reentrancy Protection

**All external functions MUST be protected against reentrancy attacks.**

#### Checks-Effects-Interactions Pattern

Always follow the Checks-Effects-Interactions (CEI) pattern as your first choice:

```solidity
// ✅ Correct: CEI pattern
function withdraw(uint256 amount) external {
    // 1. Checks
    if (balances[msg.sender] < amount) revert InsufficientBalance();

    // 2. Effects (state changes BEFORE external calls)
    balances[msg.sender] -= amount;

    // 3. Interactions (external calls LAST)
    (bool success,) = msg.sender.call{value: amount}("");
    if (!success) revert TransferFailed();
}

// ❌ Wrong: State change after external call
function withdrawUnsafe(uint256 amount) external {
    if (balances[msg.sender] < amount) revert InsufficientBalance();
    (bool success,) = msg.sender.call{value: amount}("");
    if (!success) revert TransferFailed();
    balances[msg.sender] -= amount; // VULNERABLE!
}
```

#### This Codebase: Transient Storage Guard

This codebase uses transient storage (`_PAYER_SLOT`) as an implicit reentrancy guard instead of traditional storage-based locks:

```solidity
modifier takerSubmitted() override {
    address msgSender = _operator();
    TransientStorage.setPayer(msgSender);  // Sets guard
    _;
    TransientStorage.clearPayer(msgSender); // Clears guard
}
```

#### Key Rules for Reentrancy Safety

1. **Default to CEI pattern**: This should be your first choice for all functions
2. **State changes before calls**: Update all state variables before making external calls
3. **Review all external calls**: Any `.call()`, `.transfer()`, `.send()`, or calls to other contracts
4. **Consider read-only reentrancy**: Even view functions called during state changes can be attack vectors
5. **Test reentrancy scenarios**: Write tests that attempt reentrancy attacks on your functions

## Testing Guidelines

### Core Testing Principles

**Every feature or change MUST have comprehensive tests before creating a PR.** This is non-negotiable for maintaining code quality and preventing regressions.

### When to Write Tests

- **New Features/Actions**: Write tests demonstrating the complete flow and all edge cases
- **Bug Fixes**: Add tests that reproduce the bug and verify the fix
- **Refactoring**: Ensure existing tests still pass; add new ones if behavior changes
- **Gas Optimizations**: Include benchmark tests showing before/after comparisons

### Types of Tests

#### Unit Tests
- Test both happy paths and failure cases
- Include edge cases and boundary conditions
- Test revert conditions with specific error messages
- Use descriptive names: `test_FeatureName_SpecificScenario_ExpectedOutcome()`

#### Integration Tests (Fork Tests)
- Live against forked mainnet state
- Inherit from `BasePairTest` which provides:
  - Fork setup with `vm.createSelectFork()`
  - Permit2 signature helpers (`Permit2Signature`)
  - Token dealing and approval utilities
  - Gas snapshot integration (`GasSnapshot`)

```solidity
abstract contract BasePairTest is Test, GasSnapshot, Permit2Signature, MainnetDefaultFork {
    function fromToken() internal view virtual returns (IERC20);
    function toToken() internal view virtual returns (IERC20);
    function amount() internal view virtual returns (uint256);
}
```

#### Fuzz Tests
- **Fuzz tests are highly encouraged** for all new functionality
- Foundry is configured for 100,000 fuzz runs
- Use `bound()` and `vm.assume()` to constrain inputs

```solidity
function testFuzz_myFeature(uint256 amount, address user) public {
    amount = bound(amount, 1, type(uint128).max);
    vm.assume(user != address(0));
    // Test logic
}
```

### Test Commands

```bash
# Unit tests (default profile)
forge test

# Integration tests (fork tests, requires RPC URLs)
FOUNDRY_PROFILE=integration forge test

# Specific test
forge test --match-test testName

# Coverage
forge coverage
```

### Testing Best Practices

- **Don't write redundant tests**: If something is already sufficiently tested, don't duplicate
- **Focus on what changed**: Ensure tests encapsulate your specific changes
- **Test downstream consequences**: Consider ripple effects of your changes
- **Update broken tests thoughtfully**: If your change breaks existing tests, understand why
- **Use test utilities**: Leverage `test/utils/` helpers (Permit2Signature, ActionDataBuilder)

### Testing Checklist Before PR

- [ ] All new functions have unit tests
- [ ] Critical paths have fuzz tests with random inputs
- [ ] Edge cases and revert scenarios are tested
- [ ] Gas benchmarks included for optimizations
- [ ] All tests pass: `forge test`
- [ ] Integration tests pass: `FOUNDRY_PROFILE=integration forge test`

## Development Workflow

### Prerequisites

- **Foundry**: v1.3.0 (install via `foundryup`)
- **Node.js**: 18.x (for npm scripts and gas comparison)
- **Git submodules**: Run `git submodule update --recursive --init`

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

### Running Tests

```bash
# Unit tests only (default profile, excludes integration/)
forge test

# Integration tests (fork tests, requires RPC URLs)
FOUNDRY_PROFILE=integration forge test

# Specific test
forge test --match-test testName

# EulerSwap math tests (requires 0.8.28)
FOUNDRY_SOLC_VERSION=0.8.28 forge test --mp test/0.8.28/EulerSwapBUSL.t.sol

# MultiCall tests
forge test --mp test/0.8.25/MultiCall.t.sol

# CrossChainReceiverFactory tests
forge test --mp test/unit/CrossChainReceiverFactory.t.sol

# All unit tests with random fuzz seed (as CI does)
FOUNDRY_FUZZ_SEED="0x$(python3 -c 'import secrets; print(secrets.token_hex(32))')" forge test
```

### Environment Variables

For fork tests and integration tests, set these RPC URLs:

```bash
export MAINNET_RPC_URL="https://..."
export BNB_MAINNET_RPC_URL="https://..."
export PLASMA_MAINNET_RPC_URL="https://..."
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

CI runs these checks on every PR:
1. Build main contracts
2. Build special contracts (MultiCall, CrossChainReceiverFactory, UniswapV4)
3. Run EulerSwap math tests (solc 0.8.28)
4. Run MultiCall tests
5. Run CrossChainReceiverFactory tests
6. Run all other unit tests
7. Run integration tests (fork tests)
8. Gas comparison

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

### Continuous Learning

- Consult official Solidity docs and relevant project references when uncertain
- Borrow battle-tested patterns from audited codebases
- Review the README.md for protocol-level understanding

## Using Cast and Forge

Cast is Foundry's Swiss Army knife for interacting with Ethereum from the command line. **Use Cast for blockchain utilities and quick operations** rather than writing custom scripts for common tasks.

### When to Use Cast vs Custom Code

**Use Cast for:**
- Quick keccak256 hashing of function signatures or data
- Reading contract state, storage slots, balances
- Sending simple transactions
- Converting between data formats (hex, decimal, wei, ether)
- Getting blockchain data (gas price, nonce, block info)
- Debugging transactions with traces
- Computing contract addresses before deployment

**Write custom code when:**
- Building complex multi-step interactions
- Implementing business logic
- Creating reusable libraries or contracts
- Needing programmatic control flow

### Common Cast Utilities

```bash
# Compute keccak256 hash
cast keccak "transfer(address,uint256)"

# Generate function selector (4-byte signature)
cast sig "transfer(address,uint256)"

# Get function name from selector
cast 4byte 0xa9059cbb

# Compute function selector for Settler
cast sig "execute(AllowedSlippage,bytes[],bytes32)"

# Decode calldata
cast calldata-decode "execute((address,address,uint256),bytes[],bytes32)" <calldata>
```

### Settler-Specific Commands

```bash
# Get current Settler address from deployer
cast call 0x00000000000004533Fe15556B1E086BB1A72cEae "ownerOf(uint256)(address)" 2

# Check previous Settler (dwell time)
cast call 0x00000000000004533Fe15556B1E086BB1A72cEae "prev(uint128)(address)" 2

# Get next Settler address
cast call 0x00000000000004533Fe15556B1E086BB1A72cEae "next(uint128)(address)" 2
```

### Debugging

```bash
# Trace a transaction
cast run <txhash> --rpc-url $RPC_URL

# Decode error selector
cast 4byte <selector>
```

### Integration with Tests and Scripts

In Forge tests and scripts, you can leverage Cast-like functionality through `vm` cheatcodes:

```solidity
// Equivalent to cast keccak
bytes32 hash = keccak256("transfer(address,uint256)");

// Reading storage - equivalent to cast storage
bytes32 value = vm.load(address(contract), bytes32(uint256(0)));

// Labels for clarity in traces
vm.label(address(token), "WETH");
vm.label(address(settler), "Settler");
```

### Best Practices

1. **Use Cast for prototyping**: Before writing a complex script, test your calls with Cast
2. **Verify with Cast**: After deployments, use Cast to verify contract state
3. **Debug with Cast**: Use `cast run` to debug failed transactions
4. **Prefer Cast for one-offs**: Don't write scripts for operations Cast can handle
5. **Chain Cast commands**: Combine with shell scripting for powerful workflows

```bash
# Example: Get function selector and use it
SELECTOR=$(cast sig "transfer(address,uint256)")
cast call $CONTRACT $SELECTOR $RECIPIENT $AMOUNT --rpc-url $RPC_URL
```
