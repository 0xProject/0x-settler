# Contributing to 0x Settler

Thank you for your interest in contributing to 0x Settler! This document provides guidelines and information for contributors.

## Getting Started

### Prerequisites

- [Foundry](https://getfoundry.sh/) - Solidity development framework
- Node.js and npm (for gas comparison scripts)
- Access to RPC endpoints for integration tests (see [CLAUDE.md](CLAUDE.md) for details)

### Building

```bash
forge build --skip MultiCall.sol --skip CrossChainReceiverFactory.sol --skip 'test/*'
```

### Running Tests

Refer to the CI workflow files for canonical test commands:
- `.github/workflows/test.yml` - Unit tests and build steps
- `.github/workflows/integration.yml` - Integration/fork tests

```bash
# Run unit tests
forge test

# Run integration tests (requires RPC URLs)
FOUNDRY_PROFILE=integration forge test
```

## How to Contribute

### Reporting Bugs

1. Check if the bug has already been reported in [Issues](https://github.com/0xProject/0x-settler/issues)
2. If not, open a new issue with:
   - A clear description of the bug
   - Steps to reproduce
   - Expected vs actual behavior
   - Relevant logs or error messages

**Security vulnerabilities** should NOT be reported via GitHub Issues. See [SECURITY.md](SECURITY.md) for responsible disclosure guidelines.

### Submitting Pull Requests

1. Fork the repository
2. Create a feature branch from `main`
3. Make your changes following the coding standards below
4. Ensure all tests pass
5. Submit a pull request

### Coding Standards

This is a security-critical, gas-optimized codebase. Please follow these guidelines:

#### General Principles

- **Think first, code second**: Minimize lines changed; consider ripple effects
- **Prefer simplicity**: Fewer moving parts = fewer bugs and lower audit overhead
- **Contract size matters**: This codebase is at the edge of the 24KB limit

#### Code Quality

- Code must pass linting: `forge fmt --check`
- Code must be properly typed with Solidity
- Follow existing patterns in the codebase

#### Testing Requirements

- Every feature or change MUST have comprehensive tests
- Unit tests for happy paths, failure cases, edge cases, and revert conditions
- Integration tests should use real contracts via chain fork tests
- Fuzz tests are highly encouraged

#### Gas Optimization

```bash
npm run snapshot:main   # Captures gas baseline from main
npm run diff:main       # Compares your branch vs. main
```

#### Before Committing

```bash
# Build
forge build --skip MultiCall.sol --skip CrossChainReceiverFactory.sol --skip 'test/*'

# Run unit tests
forge test

# Check formatting
forge fmt --check

# Gas comparison
npm run compare_gas
```

### Commit Hygiene

- Stage only files you intentionally modified (avoid `git add .`)
- Always run `git diff --staged` before committing
- Write clear, descriptive commit messages

## Development Resources

- [README.md](README.md) - Project overview and deployment documentation
- [CLAUDE.md](CLAUDE.md) - Detailed development guide and architecture
- [CHANGELOG.md](CHANGELOG.md) - Version history and changes

## Code of Conduct

Please be respectful and constructive in all interactions. We're all here to build great software together.

## License

By contributing, you agree that your contributions will be licensed under the [MIT License](LICENSE.txt).
