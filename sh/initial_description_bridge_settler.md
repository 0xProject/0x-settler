# 0x Bridge Settler

[0x](https://0x.org/)'s settlement contracts for cross-chain operations
utilising [Permit2](https://github.com/Uniswap/permit2) patterns to perform
swaps without any passive allowance. Full source code and audits are found at
[0xProject/0x-settler](https://github.com/0xProject/0x-settler).

## Bug Bounty

If you've found a bug, you may be eligible for a bounty under the 0x [bug bounty
program](https://0x.org/docs/developer-resources/bounties). Please see that link
for eligibility requirements as well as the advertised payout tiers. If you have
any findings, send an email to [mailto:security@0x.org](security@0x.org) with
the subject line "BUG BOUNTY". Please describe the bug that you've found **in
detail** and ideally provide a proof-of-concept exploit.

## Architecture

### Allowances

`BridgeSettler` does not hold allowances, nor does it hold token balances
between swaps. This provides an enhanced security posture. `BridgeSettler`
relies on the aforementioned `Permit2` contract to hold allowances. Some
taker-submitted actions are made using a gas-optimized allowance contract,
`AllowanceHolder`, which can be found at
0x0000000000001fF3684f28c67538d4D072C22734.

`BridgeSettler` allows arbitrary calls to other contracts. Therefore it is of
the utmost importance that _**bridge settler does not hold token balances or
allowances**_.

### `ISignatureTransfer` vs `IAllowanceTransfer`

In order to remove the risk that passive allowances could be exploited, 0x
Bridge Settler **does not** support the typical `Permit2` pattern of time-bound,
value-bound allowances set via an ECDSA or
[ERC1271](https://eips.ethereum.org/EIPS/eip-1271) signature. This is the
`IAllowanceTransfer` half of `Permit2`. Instead, 0x Settler only supports the
`ISignatureTransfer` interface, which requires a single-use signature (which we
refer to as a coupon) be submitted with every transaction.

This provides enhanced security at the cost of some gas and inconvenience. For
those users/integrators for whom this is too much of a cost, an alternative
allowance target, `AllowanceHolder` is provided (see above).

### Actions

0x Bridge Settler settles bridging operations by performing a sequence of
actions encoded in calldata. Actions are ABIEncoded with a selector. See
`IBridgeSettlerActions` for the available options. Typically, actions are
parametrized to match the parameters required by the underlying bridge going to
be used.

## Action encoding

The action encoding is not stable. Do not rely on the action encoding being
preserved between 0x Settler instances. See [0x's developer
documentation](https://0x.org/docs/developer-resources/settler) for a detailed
explanation.

Typically, actions are only added to `IBridgeSettlerActions` for 2 reasons: 1)
to gas-optimize a cross-chain path; 2) to provide compatibility with a bridge
that does not support typical `ERC20.approve`...`ERC20.transferFrom` flows.
