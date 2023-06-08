# 0x Settler

Proof of concept settlement contracts utilising [Permit2](https://github.com/Uniswap/permit2) to perform swaps without any passive allowances to the contract.

## Gas usage

Gas cost snapshots are stored under `./forge-snapshots`. The scope is minimized by using [forge-gas-snapshot](https://github.com/marktoda/forge-gas-snapshot).

There is an initial cost for Permit2 when the token has not been previously used. This adds some non-negligble cost as the storage is changed from a 0 for the first time. For this reason we compare warm (where the nonce is non-0) and cold.

Note: The following is more akin to `gasLimit` than it is `gasUsed`, this is due to the difficulty in calculating pinpoint costs (and rebates) in Foundry tests. Real world usage will be slightly lower, but it serves as a useful comparison.

[//]: # "BEGIN TABLES"

| VIP                | DEX        | Pair      | Gas    | %      |
| ------------------ | ---------- | --------- | ------ | ------ |
| 0x V4 VIP          | Uniswap V3 | USDC/WETH | 125266 | 0.00%  |
| 0x V4 Multiplex    | Uniswap V3 | USDC/WETH | 138767 | 10.78% |
| Settler VIP (warm) | Uniswap V3 | USDC/WETH | 122968 | -1.83% |
| Settler VIP (cold) | Uniswap V3 | USDC/WETH | 152189 | 21.49% |
| UniswapRouter V3   | Uniswap V3 | USDC/WETH | 126465 | 0.96%  |
|                    |            |           |        |        |
| 0x V4 VIP          | Uniswap V3 | DAI/WETH  | 112920 | 0.00%  |
| 0x V4 Multiplex    | Uniswap V3 | DAI/WETH  | 126436 | 11.97% |
| Settler VIP (warm) | Uniswap V3 | DAI/WETH  | 117122 | 3.72%  |
| Settler VIP (cold) | Uniswap V3 | DAI/WETH  | 130043 | 15.16% |
| UniswapRouter V3   | Uniswap V3 | DAI/WETH  | 114119 | 1.06%  |
|                    |            |           |        |        |
| 0x V4 VIP          | Uniswap V3 | USDT/WETH | 115491 | 0.00%  |
| 0x V4 Multiplex    | Uniswap V3 | USDT/WETH | 128992 | 11.69% |
| Settler VIP (warm) | Uniswap V3 | USDT/WETH | 117759 | 1.96%  |
| Settler VIP (cold) | Uniswap V3 | USDT/WETH | 141577 | 22.59% |
| UniswapRouter V3   | Uniswap V3 | USDT/WETH | 116562 | 0.93%  |
|                    |            |           |        |        |

| Custody              | DEX        | Pair      | Gas    | %       |
| -------------------- | ---------- | --------- | ------ | ------- |
| 0x V4 TransformERC20 | Uniswap V3 | USDC/WETH | 246475 | 0.00%   |
| Settler              | Uniswap V3 | USDC/WETH | 163212 | -33.78% |
|                      |            |           |        |         |
| 0x V4 TransformERC20 | Uniswap V3 | DAI/WETH  | 223693 | 0.00%   |
| Settler              | Uniswap V3 | DAI/WETH  | 147523 | -34.05% |
|                      |            |           |        |         |
| 0x V4 TransformERC20 | Uniswap V3 | USDT/WETH | 230356 | 0.00%   |
| Settler              | Uniswap V3 | USDT/WETH | 153587 | -33.33% |
|                      |            |           |        |         |

| MetaTransactions | DEX        | Pair      | Gas    | %       |
| ---------------- | ---------- | --------- | ------ | ------- |
| 0x V4 Multiplex  | Uniswap V3 | USDC/WETH | 253577 | 0.00%   |
| Settler          | Uniswap V3 | USDC/WETH | 169141 | -33.30% |
|                  |            |           |        |         |
| 0x V4 Multiplex  | Uniswap V3 | DAI/WETH  | 241231 | 0.00%   |
| Settler          | Uniswap V3 | DAI/WETH  | 153452 | -36.39% |
|                  |            |           |        |         |
| 0x V4 Multiplex  | Uniswap V3 | USDT/WETH | 243802 | 0.00%   |
| Settler          | Uniswap V3 | USDT/WETH | 159516 | -34.57% |
|                  |            |           |        |         |

| OTC     | DEX     | Pair      | Gas    | %      |
| ------- | ------- | --------- | ------ | ------ |
| 0x V4   | 0x V4   | USDC/WETH | 112785 | 0.00%  |
| Settler | Settler | USDC/WETH | 110786 | -1.77% |
| Settler | 0x V4   | USDC/WETH | 174912 | 55.08% |
|         |         |           |        |        |
| 0x V4   | 0x V4   | DAI/WETH  | 93311  | 0.00%  |
| Settler | Settler | DAI/WETH  | 91312  | -2.14% |
| Settler | 0x V4   | DAI/WETH  | 145715 | 56.16% |
|         |         |           |        |        |
| 0x V4   | 0x V4   | USDT/WETH | 104423 | 0.00%  |
| Settler | Settler | USDT/WETH | 102424 | -1.91% |
| Settler | 0x V4   | USDT/WETH | 160618 | 53.81% |
|         |         |           |        |        |

| Curve             | DEX   | Pair      | Gas    | %       |
| ----------------- | ----- | --------- | ------ | ------- |
|                   |       |           |        |         |
|                   |       |           |        |         |
| 0x V4             | Curve | USDT/WETH | 399056 | 0.00%   |
| Settler           | Curve | USDT/WETH | 363328 | -8.95%  |
| Curve             | Curve | USDT/WETH | 287855 | -27.87% |
| Curve Swap Router | Curve | USDT/WETH | 358007 | -10.29% |
|                   |       |           |        |         |

| Buy token fee     | DEX        | Pair      | Gas    | %       |
| ----------------- | ---------- | --------- | ------ | ------- |
| Settler - custody | Uniswap V3 | USDC/WETH | 202930 | 0.00%   |
| Settler - custody | OTC        | USDC/WETH | 149896 | -26.13% |
| Settler           | OTC        | USDC/WETH | 130771 | -35.56% |
|                   |            |           |        |         |
| Settler - custody | Uniswap V3 | DAI/WETH  | 187241 | 0.00%   |
| Settler - custody | OTC        | DAI/WETH  | 130422 | -30.35% |
| Settler           | OTC        | DAI/WETH  | 111297 | -40.56% |
|                   |            |           |        |         |
| Settler - custody | Uniswap V3 | USDT/WETH | 193305 | 0.00%   |
| Settler - custody | OTC        | USDT/WETH | 141534 | -26.78% |
| Settler           | OTC        | USDT/WETH | 122409 | -36.68% |
|                   |            |           |        |         |

| Sell token fee    | DEX        | Pair      | Gas    | %       |
| ----------------- | ---------- | --------- | ------ | ------- |
| Settler - custody | Uniswap V3 | USDC/WETH | 183998 | 0.00%   |
| Settler           | OTC        | USDC/WETH | 135102 | -26.57% |
|                   |            |           |        |         |
| Settler - custody | Uniswap V3 | DAI/WETH  | 154541 | 0.00%   |
| Settler           | OTC        | DAI/WETH  | 111454 | -27.88% |
|                   |            |           |        |         |
| Settler - custody | Uniswap V3 | USDT/WETH | 170345 | 0.00%   |
| Settler           | OTC        | USDT/WETH | 123678 | -27.40% |
|                   |            |           |        |         |

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
