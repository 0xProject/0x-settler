# 0x DAO Settler Feature

This feature slot is authorized to the [0x DAO](https://0x.org/) multisig for
deploying settlement contracts through the 0x Settler
[Deployer](https://github.com/0xProject/0x-settler). Full source code and
audits are found at
[0xProject/0x-settler](https://github.com/0xProject/0x-settler).

## Bug Bounty

If you've found a bug, you may be eligible for a bounty under the 0x [bug bounty
program](https://0x.org/docs/developer-resources/bounties). Please see that link
for eligibility requirements as well as the advertised payout tiers. If you have
any findings, send an email to [mailto:security@0x.org](security@0x.org) with
the subject line "BUG BOUNTY". Please describe the bug that you've found **in
detail** and ideally provide a proof-of-concept exploit.

## Authorization

The 0x DAO multisig is authorized to deploy contract instances under this
feature. The DAO multisig address is deterministically derived from the Safe
factory available on each chain, using the DAO's signer set and threshold.

Contracts deployed under this feature inherit the same security properties as
other 0x Settler instances: they do not hold allowances or token balances between
operations, and rely on [Permit2](https://github.com/Uniswap/permit2) for
secure, one-time token transfers.
