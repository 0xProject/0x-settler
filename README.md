# 0x Settler

Proof of concept settlement contracts utilising [Permit2](https://github.com/Uniswap/permit2) to perform swaps without any passive allowances to the contract.

## Gas usage

Gas cost snapshots are stored under `./forge-snapshots`. The scope is minimized by using [forge-gas-snapshot](https://github.com/marktoda/forge-gas-snapshot).

There is an initial cost for Permit2 when the token has not been previously used. This adds some non-negligble cost as the storage is changed from a 0 for the first time. For this reason we compare warm (where the nonce is non-0) and cold.

Note: The following is more akin to `gasLimit` than it is `gasUsed`, this is due to the difficulty in calculating pinpoint costs (and rebates) in Foundry tests. Real world usage will be slightly lower, but it serves as a useful comparison.

[//]: # "BEGIN TABLES"

| VIP                | DEX        | Pair      | Gas    | %      |
| ------------------ | ---------- | --------- | ------ | ------ |
| 0x V4 VIP          | Uniswap V3 | USDC/WETH | 124953 | 0.00%  |
| 0x V4 Multiplex    | Uniswap V3 | USDC/WETH | 138517 | 10.86% |
| Settler VIP (warm) | Uniswap V3 | USDC/WETH | 123358 | -1.28% |
| Settler VIP (cold) | Uniswap V3 | USDC/WETH | 152189 | 21.80% |
| UniswapRouter V3   | Uniswap V3 | USDC/WETH | 125994 | 0.83%  |
|                    |            |           |        |        |
| 0x V4 VIP          | Uniswap V3 | DAI/WETH  | 112500 | 0.00%  |
| 0x V4 Multiplex    | Uniswap V3 | DAI/WETH  | 126061 | 12.05% |
| Settler VIP (warm) | Uniswap V3 | DAI/WETH  | 117390 | 4.35%  |
| Settler VIP (cold) | Uniswap V3 | DAI/WETH  | 130043 | 15.59% |
| UniswapRouter V3   | Uniswap V3 | DAI/WETH  | 113541 | 0.93%  |
|                    |            |           |        |        |
| 0x V4 VIP          | Uniswap V3 | USDT/WETH | 115284 | 0.00%  |
| 0x V4 Multiplex    | Uniswap V3 | USDT/WETH | 128848 | 11.77% |
| Settler VIP (warm) | Uniswap V3 | USDT/WETH | 118240 | 2.56%  |
| Settler VIP (cold) | Uniswap V3 | USDT/WETH | 141577 | 22.81% |
| UniswapRouter V3   | Uniswap V3 | USDT/WETH | 116197 | 0.79%  |
|                    |            |           |        |        |

| Custody              | DEX        | Pair      | Gas    | %       |
| -------------------- | ---------- | --------- | ------ | ------- |
| 0x V4 TransformERC20 | Uniswap V3 | USDC/WETH | 246211 | 0.00%   |
| Settler              | Uniswap V3 | USDC/WETH | 163685 | -33.52% |
|                      |            |           |        |         |
| 0x V4 TransformERC20 | Uniswap V3 | DAI/WETH  | 223322 | 0.00%   |
| Settler              | Uniswap V3 | DAI/WETH  | 147868 | -33.79% |
|                      |            |           |        |         |
| 0x V4 TransformERC20 | Uniswap V3 | USDT/WETH | 230198 | 0.00%   |
| Settler              | Uniswap V3 | USDT/WETH | 154145 | -33.04% |
|                      |            |           |        |         |

| MetaTransactions | DEX        | Pair      | Gas    | %       |
| ---------------- | ---------- | --------- | ------ | ------- |
| 0x V4 Multiplex  | Uniswap V3 | USDC/WETH | 253298 | 0.00%   |
| Settler          | Uniswap V3 | USDC/WETH | 171724 | -32.20% |
|                  |            |           |        |         |
| 0x V4 Multiplex  | Uniswap V3 | DAI/WETH  | 240845 | 0.00%   |
| Settler          | Uniswap V3 | DAI/WETH  | 155907 | -35.27% |
|                  |            |           |        |         |
| 0x V4 Multiplex  | Uniswap V3 | USDT/WETH | 243629 | 0.00%   |
| Settler          | Uniswap V3 | USDT/WETH | 162184 | -33.43% |
|                  |            |           |        |         |

| OTC     | DEX     | Pair      | Gas    | %      |
| ------- | ------- | --------- | ------ | ------ |
| 0x V4   | 0x V4   | USDC/WETH | 129645 | 0.00%  |
| Settler | Settler | USDC/WETH | 128150 | -1.15% |
| Settler | 0x V4   | USDC/WETH | 192598 | 48.56% |
|         |         |           |        |        |
| 0x V4   | 0x V4   | DAI/WETH  | 110171 | 0.00%  |
| Settler | Settler | DAI/WETH  | 108661 | -1.37% |
| Settler | 0x V4   | DAI/WETH  | 163380 | 48.30% |
|         |         |           |        |        |
| 0x V4   | 0x V4   | USDT/WETH | 121283 | 0.00%  |
| Settler | Settler | USDT/WETH | 119773 | -1.25% |
| Settler | 0x V4   | USDT/WETH | 178283 | 47.00% |
|         |         |           |        |        |

| Curve             | DEX   | Pair      | Gas    | %       |
| ----------------- | ----- | --------- | ------ | ------- |
|                   |       |           |        |         |
|                   |       |           |        |         |
| 0x V4             | Curve | USDT/WETH | 399010 | 0.00%   |
| Settler           | Curve | USDT/WETH | 363986 | -8.78%  |
| Curve             | Curve | USDT/WETH | 287702 | -27.90% |
| Curve Swap Router | Curve | USDT/WETH | 357982 | -10.28% |
|                   |       |           |        |         |

| Buy token fee | DEX        | Pair      | Gas    | %     |
| ------------- | ---------- | --------- | ------ | ----- |
| Settler       | Uniswap V3 | USDC/WETH | 220519 | 0.00% |
|               |            |           |        |       |
| Settler       | Uniswap V3 | DAI/WETH  | 204690 | 0.00% |
|               |            |           |        |       |
| Settler       | Uniswap V3 | USDT/WETH | 210967 | 0.00% |
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

|                                   | arguments                                                                                                                                                                        | note                                                                                                                |
| --------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------- |
| `PERMIT2_TRANSFER_FROM`           | `permit: ISignatureTransfer.PermitTransferFrom, signature: bytes`                                                                                                                | Uses `Permit2` with a signed payload from `msg.sender` to transfer funds from the user into the 0xSettler contract. |
| `SETTLER_OTC`                     | `order: OtcOrder, makerPermit: ISignatureTransfer.PermitTransferFrom, makerSig: bytes, takerPermit: ISignatureTransfer.PermitTransferFrom, takerSig: bytes, fillAmount: uint128` | Trades against 0xV4 OTC order using the contracts balance for funding                                               |
| `ZERO_EX_OTC`                     | `order: IZeroEx.OtcOrder, signature: IZeroEx.Signature, sellAmount: uint256`                                                                                                     | Trades against 0xV4 OTC order using the contracts balance for funding                                               |
| `UNISWAPV3_SWAP_EXACT_IN`         | `recipient: address, amountIn: uint256, amountOutMin: uint256, path: bytes`                                                                                                      | Trades against UniswapV3 using the contracts balance for funding                                                    |
| `UNISWAPV3_PERMIT2_SWAP_EXACT_IN` | `recipient: address, amountIn: uint256, amountOutMin: uint256, path: bytes, permit2Data: bytes permit: ISignatureTransfer.PermitTransferFrom, signature: bytes()`                | Trades against UniswapV3 using the Permit2 for funding                                                              |
| `CURVE_UINT256_EXCHANGE`          | `pool: address, sellToken: address, fromTokenIndex: uint256, toTokenIndex: uint256, sellAmount: uint256, minBuyAmount: uint256`                                                  | Trades against Curve (uint256 variants) using the contracts balance for funding                                     |
| `TRANSFER_OUT`                    | `token: address`                                                                                                                                                                 | Transfers out the contracts balance of `token` to `msg.sender`                                                      |

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
