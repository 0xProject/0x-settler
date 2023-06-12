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
| 0x V4 VIP          | Uniswap V3 | USDC/WETH | 124188 | 0.00%  |
| 0x V4 Multiplex    | Uniswap V3 | USDC/WETH | 137689 | 10.87% |
| Settler VIP (warm) | Uniswap V3 | USDC/WETH | 133027 | 7.12%  |
| UniswapRouter V3   | Uniswap V3 | USDC/WETH | 125387 | 0.97%  |
|                    |            |           |        |        |
| 0x V4 VIP          | Uniswap V3 | DAI/WETH  | 111997 | 0.00%  |
| 0x V4 Multiplex    | Uniswap V3 | DAI/WETH  | 125498 | 12.05% |
| Settler VIP (warm) | Uniswap V3 | DAI/WETH  | 120836 | 7.89%  |
| UniswapRouter V3   | Uniswap V3 | DAI/WETH  | 113196 | 1.07%  |
|                    |            |           |        |        |
| 0x V4 VIP          | Uniswap V3 | USDT/WETH | 115479 | 0.00%  |
| 0x V4 Multiplex    | Uniswap V3 | USDT/WETH | 128980 | 11.69% |
| Settler VIP (warm) | Uniswap V3 | USDT/WETH | 124359 | 7.69%  |
| UniswapRouter V3   | Uniswap V3 | USDT/WETH | 116550 | 0.93%  |
|                    |            |           |        |        |

| Custody              | DEX        | Pair      | Gas    | %       |
| -------------------- | ---------- | --------- | ------ | ------- |
| 0x V4 TransformERC20 | Uniswap V3 | USDC/WETH | 245397 | 0.00%   |
| Settler              | Uniswap V3 | USDC/WETH | 159751 | -34.90% |
|                      |            |           |        |         |
| 0x V4 TransformERC20 | Uniswap V3 | DAI/WETH  | 222770 | 0.00%   |
| Settler              | Uniswap V3 | DAI/WETH  | 144217 | -35.26% |
|                      |            |           |        |         |
| 0x V4 TransformERC20 | Uniswap V3 | USDT/WETH | 230344 | 0.00%   |
| Settler              | Uniswap V3 | USDT/WETH | 151167 | -34.37% |
|                      |            |           |        |         |

| MetaTransactions | DEX        | Pair      | Gas    | %       |
| ---------------- | ---------- | --------- | ------ | ------- |
| 0x V4 Multiplex  | Uniswap V3 | USDC/WETH | 252499 | 0.00%   |
| Settler          | Uniswap V3 | USDC/WETH | 165264 | -34.55% |
|                  |            |           |        |         |
| 0x V4 Multiplex  | Uniswap V3 | DAI/WETH  | 240308 | 0.00%   |
| Settler          | Uniswap V3 | DAI/WETH  | 149730 | -37.69% |
|                  |            |           |        |         |
| 0x V4 Multiplex  | Uniswap V3 | USDT/WETH | 243790 | 0.00%   |
| Settler          | Uniswap V3 | USDT/WETH | 156680 | -35.73% |
|                  |            |           |        |         |

| OTC     | DEX     | Pair      | Gas    | %      |
| ------- | ------- | --------- | ------ | ------ |
| 0x V4   | 0x V4   | USDC/WETH | 112785 | 0.00%  |
| Settler | Settler | USDC/WETH | 113220 | 0.39%  |
| Settler | 0x V4   | USDC/WETH | 174481 | 54.70% |
|         |         |           |        |        |
| 0x V4   | 0x V4   | DAI/WETH  | 93311  | 0.00%  |
| Settler | Settler | DAI/WETH  | 93746  | 0.47%  |
| Settler | 0x V4   | DAI/WETH  | 145284 | 55.70% |
|         |         |           |        |        |
| 0x V4   | 0x V4   | USDT/WETH | 104423 | 0.00%  |
| Settler | Settler | USDT/WETH | 104858 | 0.42%  |
| Settler | 0x V4   | USDT/WETH | 160187 | 53.40% |
|         |         |           |        |        |

| Curve             | DEX   | Pair      | Gas    | %       |
| ----------------- | ----- | --------- | ------ | ------- |
|                   |       |           |        |         |
|                   |       |           |        |         |
| 0x V4             | Curve | USDT/WETH | 467360 | 0.00%   |
| Settler           | Curve | USDT/WETH | 431416 | -7.69%  |
| Curve             | Curve | USDT/WETH | 356159 | -23.79% |
| Curve Swap Router | Curve | USDT/WETH | 426311 | -8.78%  |
|                   |       |           |        |         |

| Buy token fee     | DEX        | Pair      | Gas    | %       |
| ----------------- | ---------- | --------- | ------ | ------- |
| Settler - custody | Uniswap V3 | USDC/WETH | 171879 | 0.00%   |
| Settler           | OTC        | USDC/WETH | 132969 | -22.64% |
|                   |            |           |        |         |
| Settler - custody | Uniswap V3 | DAI/WETH  | 159688 | 0.00%   |
| Settler           | OTC        | DAI/WETH  | 113495 | -28.93% |
|                   |            |           |        |         |
| Settler - custody | Uniswap V3 | USDT/WETH | 163211 | 0.00%   |
| Settler           | OTC        | USDT/WETH | 124607 | -23.65% |
|                   |            |           |        |         |

| Sell token fee | DEX        | Pair      | Gas    | %       |
| -------------- | ---------- | --------- | ------ | ------- |
| Settler        | Uniswap V3 | USDC/WETH | 154201 | 0.00%   |
| Settler        | OTC        | USDC/WETH | 137339 | -10.94% |
|                |            |           |        |         |
| Settler        | Uniswap V3 | DAI/WETH  | 137836 | 0.00%   |
| Settler        | OTC        | DAI/WETH  | 113691 | -17.52% |
|                |            |           |        |         |
| Settler        | Uniswap V3 | USDT/WETH | 142471 | 0.00%   |
| Settler        | OTC        | USDT/WETH | 125915 | -11.62% |
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
