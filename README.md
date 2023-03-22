# 0x Settler

Proof of concept settlement contracts utilizing [Permit2](https://github.com/Uniswap/permit2) to perform trades without any passive allowance.

With no passive allowances, changes to this suite of contracts can be made without and audit.

## Gas usage

Gas cost snapshots are stored under `./forge-snapshots`. The scope is minimized by using [forge-gas-snapshot](https://github.com/marktoda/forge-gas-snapshot).

There is an initial cost for Permit2 when the token has not been previously used. This adds some non-negligble cost as the storage is changed from a 0 for the first time. For this reason we compare warm (where the nonce is non-0) and cold.

Note: The following is more akin to `gasLimit` than it is `gasUsed`, this is due to the difficulty in calculating pinpoint costs (and rebates) in Foundry tests. Real world usage will be slightly lower, but it serves as a useful comparison.

|                                 | pair      | gas    |
| ------------------------------- | --------- | ------ |
| **UniswapV3**                   |           |        |
| UniswapRouterV3                 | USDC/WETH | 118607 |
| Settler UniswapV3 VIP (warm)    | USDC/WETH | 124526 |
| Settler UniswapV3 VIP (cold)    | USDC/WETH | 148918 |
| Settler UniswapV3 (cold)        | USDC/WETH | 161081 |
| ZeroEx UniswapV3 VIP            | USDC/WETH | 122582 |
| ZeroEx Multiplex UniswapV3      | USDC/WETH | 135857 |
| ZeroEx UniswapV3 TransformERC20 | USDC/WETH | 243334 |
|                                 |           |        |
| UniswapRouterV3                 | DAI/WETH  | 120625 |
| Settler UniswapV3 VIP (warm)    | DAI/WETH  | 126543 |
| Settler UniswapV3 VIP (cold)    | DAI/WETH  | 150935 |
| Settler UniswapV3 (cold)        | DAI/WETH  | 159756 |
| ZeroEx UniswapV3 VIP            | DAI/WETH  | 124601 |
| ZeroEx Multiplex UniswapV3      | DAI/WETH  | 137876 |
| ZeroEx UniswapV3 TransformERC20 | DAI/WETH  | 236929 |
| **Curve**                       |           |        |
| Curve pool                      | USDT/WETH | 299164 |
| Settler Curve VIP (warm)        | USDT/WETH | 365910 |
| ZeroEx Curve VIP                | USDT/WETH | 417748 |
| ZeroEx Curve TransformERC20     | USDT/WETH | 420654 |
| Curve Swap Router               | USDT/WETH | 374378 |
| **OTCOrder**                    |           |        |
| ZeroEx OTC VIP                  | USDC/WETH | 115910 |
| Settler OTC                     | USDC/WETH | 187771 |
|                                 |           |        |
| ZeroEx OTC VIP                  | DAI/WETH  | 111734 |
| Settler OTC                     | DAI/WETH  | 177321 |
|                                 |           |        |
| ZeroEx OTC VIP                  | USDT/WETH | 120846 |
| Settler OTC                     | USDT/WETH | 182763 |

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

|                                   | arguments                                                                                                                                                         | note                                                                                                                |
| --------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------- |
| `PERMIT2_TRANSFER_FROM`           | `permit: ISignatureTransfer.PermitTransferFrom, signature: bytes`                                                                                                 | Uses `Permit2` with a signed payload from `msg.sender` to transfer funds from the user into the 0xSettler contract. |
| `ZERO_EX_OTC`                     | `order: IZeroEx.OtcOrder, signature: IZeroEx.Signature, sellAmount: uint256`                                                                                      | Trades against ZeroEx OTC order using the contracts balance for funding                                             |
| `UNISWAPV3_SWAP_EXACT_IN`         | `recipient: address, amountIn: uint256, amountOutMin: uint256, path: bytes`                                                                                       | Trades against UniswapV3 using the contracts balance for funding                                                    |
| `UNISWAPV3_PERMIT2_SWAP_EXACT_IN` | `recipient: address, amountIn: uint256, amountOutMin: uint256, path: bytes, permit2Data: bytes permit: ISignatureTransfer.PermitTransferFrom, signature: bytes()` | Trades against UniswapV3 using the Permit2 for funding                                                              |
| `CURVE_UINT256_EXCHANGE`          | `pool: address, sellToken: address, fromTokenIndex: uint256, toTokenIndex: uint256, sellAmount: uint256, minBuyAmount: uint256`                                   | Trades against Curve (uint256 variants) using the contracts balance for funding                                     |
| `TRANSFER_OUT`                    | `token: address`                                                                                                                                                  | Transfers out the contracts balance of `token` to `msg.sender`                                                      |

## TODO

- [x] UniV3 VIP with a single `transferFrom(user, pool)` using Permit2 in `uniswapV3SwapCallback`
- [x] Curve
- [ ] MetaTxn
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

Permit2 allowances (with short dated expiration) still opens up the contracts to some risk of user funds. Namely, `Alice` permit2 being intercepted and a malicious transaction from `Mallory`, which spends `Alice`'s money and transfers it to `Mallory`.

To protect funds we must validate the actions being performed originate from the Permit2 signer. This is simple in the case where `msg.sender/tx.origin` is the signer of the Permit2 message. To support MetaTransactions we will need to employ the Witness functionality of Permit2 to ensure the actions are intentional from `Alice` as `msg.sender/tx.origin` is a different address.
