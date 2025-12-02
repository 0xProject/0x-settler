# 0x Cross-chain Intent Settler

[0x](https://0x.org/)'s settlement contracts for cross-chain intents utilising
[Permit2](https://github.com/Uniswap/permit2) to perform swaps without any
passive allowance. Full source code and audits are found at
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

`CrossChainIntentSettler` does not hold allowances, nor does it hold token
balances between swaps. This provides an enhanced security posture.
`CrossChainIntentSettler` relies on the aforementioned `Permit2` contract to
hold allowances.

`CrossChainIntentSettler` allows arbitrary calls to other contracts.  Therefore
it is of the utmost importance that _**settler does not hold token balances or
allowances**_.

### `ISignatureTransfer` vs `IAllowanceTransfer`

In order to remove the risk that passive allowances could be exploited, 0x
Settler **does not** support the typical `Permit2` pattern of time-bound,
value-bound allowances set via an ECDSA or
[ERC1271](https://eips.ethereum.org/EIPS/eip-1271) signature. This is the
`IAllowanceTransfer` half of `Permit2`. Instead, 0x Settler only supports the
`ISignatureTransfer` interface, which requires a single-use signature (called a
coupon) be submitted with every transaction.

This provides enhanced security at the cost of some gas and inconvenience.

### Actions

0x Cross Chain Intent Settler settles swaps by performing a sequence of actions
encoded in calldata. Actions are ABIEncoded with a selector. See
`ICrossChainIntentSettlerActions` for the available options. Typically, actions
are parametrized by the `recipient` where tokens are sent after the trade and
the `bps` specifying a proportion of the `Settler` contract's token balance to
be liquidated in the action.

## Action encoding

The action encoding is not stable. Do not rely on the action encoding being
preserved between 0x Settler instances. See [0x's developer
documentation](https://0x.org/docs/developer-resources/settler) for a detailed
explanation.

Typically, actions are only added to `ICrossChainIntentSettlerActions` for 2
reasons: 1) to gas-optimize a high-volume settlement path; 2) to provide
compatibility with a liquidity source that does not support typical
`ERC20.approve`...`ERC20.transferFrom` flows.

## Cross-chain Intents

This instance of `Settler` supports swaps where the received token may be
located on a different network than the sent token. Furthermore, the execution
path is not dictated in the encoded calldata, and is instead decided by the
solver. A solver may decide to use other instances of `Settler`, or any other
way. It also supports swaps where the tokens are located on the same network.

This instance of `Settler` supports swaps where the submitting address is not
the taker. This means that we must provide an alternative mechanism for
authorizing a swap that ensures the signed-over swap is not
malleable. Settlement of intents is facilitated by the `executeMetaTxn` entry
point and uses the "witness" functionality of `Permit2` to ensure that the
taker's signature is over the tokens being sent and the tokens being
received. In contrast to the "metatransaction" flow, the taker *ONLY* signs the
tokens to be sent and the tokens to be received. In a way, settling an intent is
analogous to a short-lived limit order.

Settlement of cross-chain intents is permissioned, as it requires the action of
a new actor, i.e. permissioned `relayers`. These relayers have the task of
verifying the intent is executable, and monitoring onchain (i.e. by monitoring
of `CrossChainIntentSettler` events) or offchain (i.e. signed intents via API)
user-generated intents, and prompting an auction to notify the solvers. These
relayers are also compensated by a relayer-pre-set `amount` or `bpsAmount`. The
`Settler` instance will initially retain 0% of this fee, but may activate an up
to 30% fee share. Integrating frontends may act as a `relayer`. Furthermore,
they also have the task of moving the source token to the destination chain, and
are encouraged to use the `BridgeSettler` instance.

The list of active `relayers` is updated by the 0x DAO, and is adjusted based
on, in order of importance:

1. delegated ZRX/WZRX stake
2. speed in relaying orders

Intents go through an auction for the winning solver to be able to fill the
order. An intent may specify a selected `solver`, thus giving priority to a
particular solver to execute the swap (i.e. a prearranged agreement between the
user and the solver).  Once an intent is filled on the destination chain, source
tokens are sent to the `relayers` by submitting a ZK proof. Proofs are submitted
in batches, but a relayer may decide to self-generate and submit it to unlock
the tokens faster.

The restriction of participants to relayers and the winning solver avoids
leakage of surplus value to MEV. Obviously, the settlement of the order for *at
least* the specified amount to be received is guaranteed by the
contracts. Cross-chain intent settlement is permissioned so that in the case
that it is possible, the taker receives more than the minimum specified in the
signature, up to the value that the market supports. `Permit2` allows the
combination of the authorization of the token transfer as well as confirming the
user's intention to receive the specified amount of the other token. This
results in the taker signing a single
[EIP712](https://eips.ethereum.org/EIPS/eip-712) struct.
