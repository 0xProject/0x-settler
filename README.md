# 0x Settler

Proof of concept settlement contracts utilising [Permit2](https://github.com/Uniswap/permit2) to perform swaps without any passive allowances to the contract.

## Gas usage

Gas cost snapshots are stored under `./forge-snapshots`. The scope is minimized by using [forge-gas-snapshot](https://github.com/marktoda/forge-gas-snapshot).

There is an initial cost for Permit2 when the token has not been previously used. This adds some non-negligble cost as the storage is changed from a 0 for the first time. For this reason we compare warm (where the nonce is non-0) and cold.

Note: The following is more akin to `gasLimit` than it is `gasUsed`, this is due to the difficulty in calculating pinpoint costs (and rebates) in Foundry tests. Real world usage will be slightly lower, but it serves as a useful comparison.

[//]: # "BEGIN TABLES"

| VIP                | DEX        | Pair      | Gas    | %      |
| ------------------ | ---------- | --------- | ------ | ------ |
| 0x V4 VIP          | Uniswap V3 | USDC/WETH | 125217 | 0.00%  |
| 0x V4 Multiplex    | Uniswap V3 | USDC/WETH | 138718 | 10.78% |
| Settler VIP (warm) | Uniswap V3 | USDC/WETH | 123552 | -1.33% |
| Settler VIP (cold) | Uniswap V3 | USDC/WETH | 152189 | 21.54% |
| UniswapRouter V3   | Uniswap V3 | USDC/WETH | 126416 | 0.96%  |
|                    |            |           |        |        |
| 0x V4 VIP          | Uniswap V3 | DAI/WETH  | 104304 | 0.00%  |
| 0x V4 Multiplex    | Uniswap V3 | DAI/WETH  | 117805 | 12.94% |
| Settler VIP (warm) | Uniswap V3 | DAI/WETH  | 109139 | 4.64%  |
| Settler VIP (cold) | Uniswap V3 | DAI/WETH  | 130043 | 24.68% |
| UniswapRouter V3   | Uniswap V3 | DAI/WETH  | 105503 | 1.15%  |
|                    |            |           |        |        |
| 0x V4 VIP          | Uniswap V3 | USDT/WETH | 115447 | 0.00%  |
| 0x V4 Multiplex    | Uniswap V3 | USDT/WETH | 128948 | 11.69% |
| Settler VIP (warm) | Uniswap V3 | USDT/WETH | 118348 | 2.51%  |
| Settler VIP (cold) | Uniswap V3 | USDT/WETH | 141577 | 22.63% |
| UniswapRouter V3   | Uniswap V3 | USDT/WETH | 116518 | 0.93%  |
|                    |            |           |        |        |

| Custody              | DEX        | Pair      | Gas    | %       |
| -------------------- | ---------- | --------- | ------ | ------- |
| 0x V4 TransformERC20 | Uniswap V3 | USDC/WETH | 246426 | 0.00%   |
| Settler              | Uniswap V3 | USDC/WETH | 163874 | -33.50% |
|                      |            |           |        |         |
| 0x V4 TransformERC20 | Uniswap V3 | DAI/WETH  | 215077 | 0.00%   |
| Settler              | Uniswap V3 | DAI/WETH  | 139618 | -35.08% |
|                      |            |           |        |         |
| 0x V4 TransformERC20 | Uniswap V3 | USDT/WETH | 230312 | 0.00%   |
| Settler              | Uniswap V3 | USDT/WETH | 154254 | -33.02% |
|                      |            |           |        |         |

| MetaTransactions | DEX        | Pair      | Gas    | %       |
| ---------------- | ---------- | --------- | ------ | ------- |
| 0x V4 Multiplex  | Uniswap V3 | USDC/WETH | 253528 | 0.00%   |
| Settler          | Uniswap V3 | USDC/WETH | 171942 | -32.18% |
|                  |            |           |        |         |
| 0x V4 Multiplex  | Uniswap V3 | DAI/WETH  | 232615 | 0.00%   |
| Settler          | Uniswap V3 | DAI/WETH  | 147686 | -36.51% |
|                  |            |           |        |         |
| 0x V4 Multiplex  | Uniswap V3 | USDT/WETH | 243758 | 0.00%   |
| Settler          | Uniswap V3 | USDT/WETH | 162322 | -33.41% |
|                  |            |           |        |         |

| OTC     | DEX     | Pair      | Gas    | %      |
| ------- | ------- | --------- | ------ | ------ |
| 0x V4   | 0x V4   | USDC/WETH | 129885 | 0.00%  |
| Settler | Settler | USDC/WETH | 128176 | -1.32% |
| Settler | 0x V4   | USDC/WETH | 192623 | 48.30% |
|         |         |           |        |        |
| 0x V4   | 0x V4   | DAI/WETH  | 110411 | 0.00%  |
| Settler | Settler | DAI/WETH  | 108702 | -1.55% |
| Settler | 0x V4   | DAI/WETH  | 163426 | 48.02% |
|         |         |           |        |        |
| 0x V4   | 0x V4   | USDT/WETH | 121523 | 0.00%  |
| Settler | Settler | USDT/WETH | 119814 | -1.41% |
| Settler | 0x V4   | USDT/WETH | 178329 | 46.75% |
|         |         |           |        |        |

| Curve             | DEX   | Pair      | Gas    | %       |
| ----------------- | ----- | --------- | ------ | ------- |
|                   |       |           |        |         |
|                   |       |           |        |         |
| 0x V4             | Curve | USDT/WETH | 405585 | 0.00%   |
| Settler           | Curve | USDT/WETH | 370507 | -8.65%  |
| Curve             | Curve | USDT/WETH | 294384 | -27.42% |
| Curve Swap Router | Curve | USDT/WETH | 364536 | -10.12% |
|                   |       |           |        |         |

| Buy token fee | DEX        | Pair      | Gas    | %     |
| ------------- | ---------- | --------- | ------ | ----- |
| Settler       | Uniswap V3 | USDC/WETH | 220770 | 0.00% |
|               |            |           |        |       |
| Settler       | Uniswap V3 | DAI/WETH  | 196514 | 0.00% |
|               |            |           |        |       |
| Settler       | Uniswap V3 | USDT/WETH | 211150 | 0.00% |
|               |            |           |        |       |

[//]: # "END TABLES"

We also compare cold and warm with `transferFrom`, where the recipient has a balance or not of the token.

|                                                   | gas   |
| ------------------------------------------------- | ----- |
| transferFrom (cold)                               | 65243 |
| transferFrom (warm)                               | 26725 |
| permit2 permitTransferFrom (warm, cold recipient) | 55169 |
| permit2 permitTransferFrom (warm, warm recipient) | 30370 |
| permit2 permitTransferFrom (cold, cold recipient) | 81586 |
| permit2 permitTransferFrom (cold, warm recipient) | 61665 |

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
- [ ] consider using argument encoding for action names, ala solidity function encoding
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

- Market Makers have balances of both tokens. Since Pools have non-zero balances of both tokens this is a fair comparison.
- Nonces for Permit2 and Otc orders (0x V4) are assumed to be initialized. We set this manually in `setUp` rather than by performing additional trades to avoid gas metering and warming up storage access as much as possible
- The taker does not have a balance of the token being bought
