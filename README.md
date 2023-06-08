# 0x Settler

Proof of concept settlement contracts utilising [Permit2](https://github.com/Uniswap/permit2) to perform swaps without any passive allowances to the contract.

### Custody

Custody, not like the delicious custardy, is when the token(s) being traded are temporarily owned by the Settler contract. This sometimes implies an additional, non-optimal transfer. There are multiple reasons that Settler takes custody of the token, here are a few:

- In the middle of a Multihop trade
- To distribute positive slippage from an AMM
- To pay fees to a fee recipient in the buy token from an AMM
- Trading against an ineffeciant AMM that only supports `transferFrom(msg.sender)` (e.g Curve)

For the above reasons, there are settlement paths in Settler which allow for custody of the sell token or the buy token. You will see the usage of `custody` to represent this. Sell token or Buy token or both custody is represented by `custody`.

With Permit2, on the Sell token, we can skip custody by utilising `PermitBatch` which can specify multiple recipients of the sell token. For example:

1. UniswapV3 Pool
2. Fee recipient

## Gas usage

Gas cost snapshots are stored under `./forge-snapshots`. The scope is minimized by using [forge-gas-snapshot](https://github.com/marktoda/forge-gas-snapshot).

There is an initial cost for Permit2 when the token has not been previously used. This adds some non-negligble cost as the storage is changed from a 0 for the first time. For this reason we compare warm (where the nonce is non-0) and cold.

Note: The following is more akin to `gasLimit` than it is `gasUsed`, this is due to the difficulty in calculating pinpoint costs (and rebates) in Foundry tests. Real world usage will be slightly lower, but it serves as a useful comparison.

[//]: # "BEGIN TABLES"

| VIP                | DEX        | Pair      | Gas    | %      |
| ------------------ | ---------- | --------- | ------ | ------ |
| 0x V4 VIP          | Uniswap V3 | USDC/WETH | 125193 | 0.00%  |
| 0x V4 Multiplex    | Uniswap V3 | USDC/WETH | 138694 | 10.78% |
| Settler VIP (warm) | Uniswap V3 | USDC/WETH | 134505 | 7.44%  |
| UniswapRouter V3   | Uniswap V3 | USDC/WETH | 126392 | 0.96%  |
|                    |            |           |        |        |
| 0x V4 VIP          | Uniswap V3 | DAI/WETH  | 112859 | 0.00%  |
| 0x V4 Multiplex    | Uniswap V3 | DAI/WETH  | 126360 | 11.96% |
| Settler VIP (warm) | Uniswap V3 | DAI/WETH  | 122171 | 8.25%  |
| UniswapRouter V3   | Uniswap V3 | DAI/WETH  | 114058 | 1.06%  |
|                    |            |           |        |        |
| 0x V4 VIP          | Uniswap V3 | USDT/WETH | 115447 | 0.00%  |
| 0x V4 Multiplex    | Uniswap V3 | USDT/WETH | 128948 | 11.69% |
| Settler VIP (warm) | Uniswap V3 | USDT/WETH | 124825 | 8.12%  |
| UniswapRouter V3   | Uniswap V3 | USDT/WETH | 116518 | 0.93%  |
|                    |            |           |        |        |

| Custody              | DEX        | Pair      | Gas    | %       |
| -------------------- | ---------- | --------- | ------ | ------- |
| 0x V4 TransformERC20 | Uniswap V3 | USDC/WETH | 246402 | 0.00%   |
| Settler              | Uniswap V3 | USDC/WETH | 161360 | -34.51% |
|                      |            |           |        |         |
| 0x V4 TransformERC20 | Uniswap V3 | DAI/WETH  | 223632 | 0.00%   |
| Settler              | Uniswap V3 | DAI/WETH  | 145683 | -34.86% |
|                      |            |           |        |         |
| 0x V4 TransformERC20 | Uniswap V3 | USDT/WETH | 230312 | 0.00%   |
| Settler              | Uniswap V3 | USDT/WETH | 151764 | -34.11% |
|                      |            |           |        |         |

| MetaTransactions | DEX        | Pair      | Gas    | %       |
| ---------------- | ---------- | --------- | ------ | ------- |
| 0x V4 Multiplex  | Uniswap V3 | USDC/WETH | 253504 | 0.00%   |
| Settler          | Uniswap V3 | USDC/WETH | 167288 | -34.01% |
|                  |            |           |        |         |
| 0x V4 Multiplex  | Uniswap V3 | DAI/WETH  | 241170 | 0.00%   |
| Settler          | Uniswap V3 | DAI/WETH  | 151611 | -37.14% |
|                  |            |           |        |         |
| 0x V4 Multiplex  | Uniswap V3 | USDT/WETH | 243758 | 0.00%   |
| Settler          | Uniswap V3 | USDT/WETH | 157692 | -35.31% |
|                  |            |           |        |         |

| OTC     | DEX     | Pair      | Gas    | %      |
| ------- | ------- | --------- | ------ | ------ |
| 0x V4   | 0x V4   | USDC/WETH | 112785 | 0.00%  |
| Settler | Settler | USDC/WETH | 113732 | 0.84%  |
| Settler | 0x V4   | USDC/WETH | 174977 | 55.14% |
|         |         |           |        |        |
| 0x V4   | 0x V4   | DAI/WETH  | 93311  | 0.00%  |
| Settler | Settler | DAI/WETH  | 94258  | 1.01%  |
| Settler | 0x V4   | DAI/WETH  | 145780 | 56.23% |
|         |         |           |        |        |
| 0x V4   | 0x V4   | USDT/WETH | 104423 | 0.00%  |
| Settler | Settler | USDT/WETH | 105370 | 0.91%  |
| Settler | 0x V4   | USDT/WETH | 160683 | 53.88% |
|         |         |           |        |        |

| Curve             | DEX   | Pair      | Gas    | %       |
| ----------------- | ----- | --------- | ------ | ------- |
|                   |       |           |        |         |
|                   |       |           |        |         |
| 0x V4             | Curve | USDT/WETH | 392850 | 0.00%   |
| Settler           | Curve | USDT/WETH | 357235 | -9.07%  |
| Curve             | Curve | USDT/WETH | 281649 | -28.31% |
| Curve Swap Router | Curve | USDT/WETH | 351801 | -10.45% |
|                   |       |           |        |         |

| Buy token fee     | DEX        | Pair      | Gas    | %       |
| ----------------- | ---------- | --------- | ------ | ------- |
| Settler - custody | Uniswap V3 | USDC/WETH | 173607 | 0.00%   |
| Settler           | OTC        | USDC/WETH | 133644 | -23.02% |
|                   |            |           |        |         |
| Settler - custody | Uniswap V3 | DAI/WETH  | 161273 | 0.00%   |
| Settler           | OTC        | DAI/WETH  | 114170 | -29.21% |
|                   |            |           |        |         |
| Settler - custody | Uniswap V3 | USDT/WETH | 163927 | 0.00%   |
| Settler           | OTC        | USDT/WETH | 125282 | -23.57% |
|                   |            |           |        |         |

| Sell token fee | DEX        | Pair      | Gas    | %       |
| -------------- | ---------- | --------- | ------ | ------- |
| Settler        | Uniswap V3 | USDC/WETH | 155623 | 0.00%   |
| Settler        | OTC        | USDC/WETH | 137975 | -11.34% |
|                |            |           |        |         |
| Settler        | Uniswap V3 | DAI/WETH  | 139115 | 0.00%   |
| Settler        | OTC        | DAI/WETH  | 114327 | -17.82% |
|                |            |           |        |         |
| Settler        | Uniswap V3 | USDT/WETH | 142881 | 0.00%   |
| Settler        | OTC        | USDT/WETH | 126551 | -11.43% |
|                |            |           |        |         |

[//]: # "END TABLES"

### Settler vs X

#### Settler vs 0xV4

The Settler contracts must perform additional work over 0xV4, namely, invalidate the state of the `Permit2` signed message, this is essentially an additional `SSTORE` that must always be performed.
On the otherside, currently Settler does not need to perform the same Feature implementation lookup that 0xV4 requires as a proxy. Settler also does not need to maintain re-entrancy guards as there is no state or TVL to protect.

With the Curve VIP, 0xV4 has to use a LiquidityProviderSandbox as calling untrusted/arbitrary code is a risk in the protocol.

OTC has noticeable overhead as it is optimized to be interacted with directly in 0xV4. It lacks `recipient` parameters (to avoid extra transfers) and it also lacks a payment callback when the caller is a contract.

#### Settler vs Curve

The Curve pool does not allow for a `recipient` to be specified, nor does it allow for tokens to be `transfer` into the pool. Due to these limitations there is overhead from the `transfer` out of the Settler contract to the user.
This same limitation applies to the Curve Swap Router.

## Actions

See [ISettlerActions](https://github.com/0xProject/0x-settler/blob/master/src/ISettlerActions.sol) for a list of actions and their parameters.

## TODO

- [x] UniV3 VIP with a single `transferFrom(user, pool)` using Permit2 in `uniswapV3SwapCallback`
- [x] Curve
- [x] MetaTxn
- [x] Consolidate warmNonce vs coldNonce naming (let's assume warm by default unless otherwise specified)
- [ ] WETH wrap/unwrap
- [ ] Payable OTC (ETH)
- [ ] Sell token fees
- [x] Buy token fees
- [x] consider using argument encoding for action names, ala solidity function encoding
- [ ] can we support all dexes without hitting the contract size limit and requiring `DELEGATECALL's`
- [ ] set up some mocks for faster unit testing

## VIPs

We've continued on with the terminology of VIPs. Recall from 0xV4 that VIPs are a special settlement path in order to minimize gas costs.

### UniswapV3 VIP

This settlement path is optimized by performing the Permit2 in the `uniswapV3SwapCallback` function performing a `permit2TransferFrom` and avoiding an additional `transfer`. This is further benefitted from tokens being sent to a pool with an already initialized balance, rathan than to 0xSettler as a temporary intermediary.

The action `UNISWAPV3_PERMIT2_SWAP_EXACT_IN` exposes this behaviour and it should not be used with any other `PERMIT2` action (e.g `PERMIT2_TRANSFER_FROM`).

# Risk

Since Settler has no outstanding allowances, and no usage of `transferFrom` or arbitrary calls, overall risk of user funds loss is greatly reduced.

Permit2 allowances (with short dated expiration) still has some risk. Namely, `Alice` permit2 being intercepted and a malicious transaction from `Mallory`, which spends `Alice`'s funds, transferring it to `Mallory`.

To protect funds we must validate the actions being performed originate from the Permit2 signer. This is simple in the case where `msg.sender/tx.origin` is the signer of the Permit2 message. To support MetaTransactions we utilise the Witness functionality of Permit2 to ensure the actions are intentional from `Alice` as `msg.sender/tx.origin` is a different address.

## Gas Comparisons

Day by day it gets harder to get a fair real world gas comparison. With rebates and token balances initialized or not, and the difficulty of setting up the world, touching storage, then performing the test.

To make gas comparisons fair we will use the following methodology:

- Market Makers have balances of both tokens. Since AMM Pools have non-zero balances of both tokens this is a fair comparison.
- The Taker does not have a balance of the token being bought.
- Fee Recipient has a non-zero balance of the fee tokens.
- Nonces for Permit2 and Otc orders (0x V4) are initialized.
- `setUp` is used as much as possible with limited setup performed in the test. Warmup trades are avoided completely as to not warm up storage access.
