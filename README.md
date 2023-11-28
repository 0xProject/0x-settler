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
| 0x V4 VIP          | Uniswap V3 | USDC/WETH | 125081 | 0.00%  |
| 0x V4 Multiplex    | Uniswap V3 | USDC/WETH | 138651 | 10.85% |
| Settler VIP (warm) | Uniswap V3 | USDC/WETH | 132955 | 6.30%  |
| UniswapRouter V3   | Uniswap V3 | USDC/WETH | 126122 | 0.83%  |
|                    |            |           |        |        |
| 0x V4 VIP          | Uniswap V3 | DAI/WETH  | 103788 | 0.00%  |
| 0x V4 Multiplex    | Uniswap V3 | DAI/WETH  | 117358 | 13.07% |
| Settler VIP (warm) | Uniswap V3 | DAI/WETH  | 111662 | 7.59%  |
| UniswapRouter V3   | Uniswap V3 | DAI/WETH  | 104829 | 1.00%  |
|                    |            |           |        |        |
| 0x V4 VIP          | Uniswap V3 | USDT/WETH | 115347 | 0.00%  |
| 0x V4 Multiplex    | Uniswap V3 | USDT/WETH | 128917 | 11.76% |
| Settler VIP (warm) | Uniswap V3 | USDT/WETH | 123253 | 6.85%  |
| UniswapRouter V3   | Uniswap V3 | USDT/WETH | 116260 | 0.79%  |
|                    |            |           |        |        |

| Custody              | DEX        | Pair      | Gas    | %       |
| -------------------- | ---------- | --------- | ------ | ------- |
| 0x V4 TransformERC20 | Uniswap V3 | USDC/WETH | 246339 | 0.00%   |
| Settler              | Uniswap V3 | USDC/WETH | 162692 | -33.96% |
|                      |            |           |        |         |
| 0x V4 TransformERC20 | Uniswap V3 | DAI/WETH  | 214610 | 0.00%   |
| Settler              | Uniswap V3 | DAI/WETH  | 137343 | -36.00% |
|                      |            |           |        |         |
| 0x V4 TransformERC20 | Uniswap V3 | USDT/WETH | 230261 | 0.00%   |
| Settler              | Uniswap V3 | USDT/WETH | 152790 | -33.64% |
|                      |            |           |        |         |

| MetaTransactions | DEX        | Pair      | Gas    | %       |
| ---------------- | ---------- | --------- | ------ | ------- |
| 0x V4 Multiplex  | Uniswap V3 | USDC/WETH | 253428 | 0.00%   |
| Settler          | Uniswap V3 | USDC/WETH | 168784 | -33.40% |
|                  |            |           |        |         |
| 0x V4 Multiplex  | Uniswap V3 | DAI/WETH  | 232135 | 0.00%   |
| Settler          | Uniswap V3 | DAI/WETH  | 143435 | -38.21% |
|                  |            |           |        |         |
| 0x V4 Multiplex  | Uniswap V3 | USDT/WETH | 243694 | 0.00%   |
| Settler          | Uniswap V3 | USDT/WETH | 158882 | -34.80% |
|                  |            |           |        |         |

| OTC     | DEX     | Pair      | Gas    | %      |
| ------- | ------- | --------- | ------ | ------ |
| 0x V4   | 0x V4   | USDC/WETH | 112545 | 0.00%  |
| Settler | Settler | USDC/WETH | 113241 | 0.62%  |
| Settler | 0x V4   | USDC/WETH | 175044 | 55.53% |
|         |         |           |        |        |
| 0x V4   | 0x V4   | DAI/WETH  | 93071  | 0.00%  |
| Settler | Settler | DAI/WETH  | 93758  | 0.74%  |
| Settler | 0x V4   | DAI/WETH  | 145847 | 56.71% |
|         |         |           |        |        |
| 0x V4   | 0x V4   | USDT/WETH | 104183 | 0.00%  |
| Settler | Settler | USDT/WETH | 104870 | 0.66%  |
| Settler | 0x V4   | USDT/WETH | 160750 | 54.30% |
|         |         |           |        |        |

| Curve             | DEX   | Pair      | Gas    | %       |
| ----------------- | ----- | --------- | ------ | ------- |
|                   |       |           |        |         |
|                   |       |           |        |         |
| 0x V4             | Curve | USDT/WETH | 466096 | 0.00%   |
| Settler           | Curve | USDT/WETH | 429861 | -7.77%  |
| Curve             | Curve | USDT/WETH | 354788 | -23.88% |
| Curve Swap Router | Curve | USDT/WETH | 425068 | -8.80%  |
|                   |       |           |        |         |

| Buy token fee     | DEX        | Pair      | Gas    | %       |
| ----------------- | ---------- | --------- | ------ | ------- |
| Settler - custody | Uniswap V3 | USDC/WETH | 171451 | 0.00%   |
| Settler           | OTC        | USDC/WETH | 133644 | -22.05% |
|                   |            |           |        |         |
| Settler - custody | Uniswap V3 | DAI/WETH  | 150158 | 0.00%   |
| Settler           | OTC        | DAI/WETH  | 114170 | -23.97% |
|                   |            |           |        |         |
| Settler - custody | Uniswap V3 | USDT/WETH | 161749 | 0.00%   |
| Settler           | OTC        | USDT/WETH | 125282 | -22.55% |
|                   |            |           |        |         |

| Sell token fee | DEX        | Pair      | Gas    | %       |
| -------------- | ---------- | --------- | ------ | ------- |
| Settler        | Uniswap V3 | USDC/WETH | 178981 | 0.00%   |
| Settler        | OTC        | USDC/WETH | 137975 | -22.91% |
|                |            |           |        |         |
| Settler        | Uniswap V3 | DAI/WETH  | 149576 | 0.00%   |
| Settler        | OTC        | DAI/WETH  | 114327 | -23.57% |
|                |            |           |        |         |
| Settler        | Uniswap V3 | USDT/WETH | 166807 | 0.00%   |
| Settler        | OTC        | USDT/WETH | 126551 | -24.13% |
| Settler        | Curve      | USDT/WETH | 446274 | 167.54% |
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
- [x] WETH wrap/unwrap
- [ ] Payable OTC (ETH)
- [x] Sell token fees
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

# Technical Reference

We utilise Permit2 transfers with an `SignatureTransfer`. Allowing users to sign a coupon allowing our contracts to move their tokens. Permit2 uses `PermitTransferFrom` struct for single transgers and `PermitBatchTransferFrom` for batch transfers.

Permit2 provides the following guarantees:

- Funds can only be transferred from the user who signed the Permit2 coupon
- Funds can only be transferred by the `spender` specified in the Permit2 coupon
- Settler may only transfer an amount up to the amount specified in the Permit2 coupon
- Settler may only transfer a token specified in the Permit2 coupon
- Coupons expire after a certain time specified as `deadline`
- Coupons can only be used once

```solidity
struct TokenPermissions {
    // ERC20 token address
    address token;
    // the maximum amount that can be spent
    uint256 amount;
}

struct PermitTransferFrom {
    TokenPermissions permitted;
    // a unique value for every token owner's signature to prevent signature replays
    uint256 nonce;
    // deadline on the permit signature
    uint256 deadline;
}

struct PermitBatchTransferFrom {
    // the tokens and corresponding amounts permitted for a transfer
    TokenPermissions[] permitted;
    // a unique value for every token owner's signature to prevent signature replays
    uint256 nonce;
    // deadline on the permit signature
    uint256 deadline;
}
```

With this it is simple to transfer the user assets to a specific destination, as well as take fixed fees. The biggest restriction is that we must consume this permit entirely once. We cannot perform the permit transfer at different times consuming different amounts.

The User signs a Permit2 coupon, giving Settler the ability to spend a specific amount of their funds for a time duration. The EIP712 type the user signs is as follows:

```solidity
PermitTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline)
TokenPermissions(address token,uint256 amount)
```

This signed coupon is then provided in the calldata to the `Settler.execute` function.

Due to this design, the user is prompted for an action two times when performing a trade. Once to sign the Permit2 coupon, and once to call the `Settler.execute` function. This is a tradeoff we are willing to make to avoid passive allowances.

In a MetaTransaction flow, the user is prompted only once.

## Token Transfer Flow

```mermaid
sequenceDiagram
    autonumber
    User->>Settler: execute
    rect rgba(133, 81, 231, 0.5)
        Settler->>Permit2: permitTransfer
        Permit2->>USDC: transferFrom(User, Settler)
        USDC-->>Settler: transfer
    end
    Settler->>UniswapV3: swap
    UniswapV3->>WETH: transfer(Settler)
    WETH-->>Settler: transfer
    UniswapV3->>Settler: uniswapV3Callback
    Settler->>USDC: transfer(UniswapV3)
    USDC-->>UniswapV3: transfer
    Settler->>WETH: balanceOf(Settler)
    Settler->>WETH: transfer(User)
    WETH-->>User: transfer
```

The above example shows the simplest form of settlement in Settler. We abuse some of the sequence diagram notation to get the point across. Token transfers are represented by dashes (-->). Normal contract calls are represented by solid lines. Highlighted in colour is the Permit2 interaction.

For the sake of brevity, following diagrams will have a simplified representation to showcase the internal flow. This is what we are actually interested in describing. The initial user interaction (e.g their call to Settler) and the final transfer is omitted unless it is relevant to highlight in the flow. Function calls to the DEX may only be representative of the flow, not the accurate function name.

Below is the simplified version of the above flow.

```mermaid
sequenceDiagram
    autonumber
    rect rgba(133, 81, 231, 0.5)
        USDC-->>Settler: permitTransfer
    end
    Settler->>UniswapV3: swap
    WETH-->>Settler: transfer
    UniswapV3->>Settler: uniswapV3Callback
    USDC-->>UniswapV3: transfer
```

## Basic Flow

This is the most basic flow and a flow that a number of dexes support. Essentially it is the "call function on DEX, DEX takes tokens from us, DEX gives us tokens". It has ineffeciences as `transferFrom` is more gas expensive than `transfer` and we are required to check/set allowances to the DEX. Typically this DEX also does not support a `recipient` field, introducing yet another needless `transfer` in simple swaps.

```mermaid
sequenceDiagram
    autonumber
    rect rgba(133, 81, 231, 0.5)
        USDC-->>Settler: permitTransfer
    end
    Settler->>DEX: swap
    USDC-->>DEX: transfer
    WETH-->>Settler: transfer
    WETH-->>User: transfer
```

## VIPs

Settler has a number of specialised fill flows and will add more overtime as we add support for more dexes.

### UniswapV3

```mermaid
sequenceDiagram
    autonumber
    Settler->>UniswapV3: swap
    WETH-->>User: transfer
    UniswapV3->>Settler: uniswapV3Callback
    rect rgba(133, 81, 231, 0.5)
        USDC-->>UniswapV3: permitTransfer
    end
```

In this flow we avoid extraneous transfers with two optimisations. Firstly, we utilise the `recipient` field of UniswapV3, providing the User as the recipient and avoiding an extra transfer. Secondly during the `uniswapV3Callback` we execute the Permit2 transfer, paying the UniswapV3 pool instead of the Settler contract, avoiding an extra transfer.

This allows us to achieve **no custody** during this flow and is an extremely gas efficient way to fill a single UniswapV3 pool, or single chain of UniswapV3 pools.

Note this has the following limitations:

- Single UniswapV3 pool or single chain of pools (e.g ETH->DAI->USDC)
- Cannot support a split between pools (e.g ETH->USDC 5bps and ETH->USDC 1bps) as Permit2 transfer can only occur once. a 0xV4 equivalent would be `sellTokenForTokenToUniswapV3` as opposed to `MultiPlex[sellTokenForEthToUniswapV3,sellTokenForEthToUniswapV3]`.

## OTC

```mermaid
sequenceDiagram
    autonumber
    rect rgba(133, 81, 231, 0.5)
        WETH-->>User: permitWitnessTransferFrom
    end
    rect rgba(133, 81, 231, 0.5)
        USDC-->>Market Maker: permitTransfer
    end
```

For OTC we utilize 2 Permit2 Transfers, one for the `Market Maker->User` and another for `User->Market Maker`. This allows us to achieve **no custody** during this flow and is an extremely gas efficient way to fill OTC orders. We simply validate the OTC order (e.g Taker/tx.origin).

Note the `permitWitnessTransferFrom`, we utilise the `Witness` functionality of Permit2 which allows arbitrary data to be attached to the Permit2 coupon. This arbitrary data is the actual OTC order itself, containing the taker/tx.origin and maker/taker amount and token fields.

```solidity
struct OtcOrder {
    address makerToken;
    address takerToken;
    uint128 makerAmount;
    uint128 takerAmount;
    address maker;
    address taker;
    address txOrigin;
}
```

A Market maker signs a slightly different Permit2 coupon than a User which contains these additional fields. The EIP712 type the Market Maker signs is as follows:

```solidity
PermitWitnessTransferFrom(TokenPermissions permitted, address spender, uint256 nonce, uint256 deadline, OtcOrder order)
OtcOrder(address makerToken,address takerToken,uint128 makerAmount,uint128 takerAmount,address maker,address taker,address txOrigin)
TokenPermissions(address token,uint256 amount)"
```

We use the Permit2 guarantees of a Permit2 coupon to ensure the following:

- OTC Order cannot be filled more than once
- OTC Orders expire
- OTC Orders are signed by the Market Maker

## Fees in Basic Flow

In the most Basic flow, Settler has **taken custody**, usually in both assets. So a fee can be paid out be Settler.

### Sell token fee

```mermaid
sequenceDiagram
    autonumber
    rect rgba(133, 81, 231, 0.5)
        USDC-->>Settler: permitTransfer
    end
    opt sell token fee
        USDC-->>Fee Recipient: transfer
    end
    Settler->>DEX: swap
    USDC-->>DEX: transfer
    WETH-->>Settler: transfer
    WETH-->>User: transfer
```

It is also possible to utilise Permit2 to pay out the Sell token fee using a batch permit, where the second item in the batch is the amount to payout.

```mermaid
sequenceDiagram
    autonumber
    rect rgba(133, 81, 231, 0.5)
        USDC-->>Settler: permitTransfer
        opt sell token fee
            USDC-->>Fee Recipient: transfer
        end
    end
    Settler->>DEX: swap
    USDC-->>DEX: transfer
    WETH-->>Settler: transfer
    WETH-->>User: transfer
```

### Buy token fee

```mermaid
sequenceDiagram
    autonumber
    rect rgba(133, 81, 231, 0.5)
        USDC-->>Settler: permitTransfer
    end
    Settler->>DEX: swap
    USDC-->>DEX: transfer
    WETH-->>Settler: transfer
    opt buy token fee
        WETH-->>Fee Recipient: transfer
    end
    WETH-->>User: transfer
```

## Fees via Permit2

It is possible to collect fees via Permit2, which is typically in the token that the Permit2 is offloading (e.g the sell token for that counterparty). To perform this we use the Permit2 batch functionality where the second item in the batch is the fee.

Note: This is still not entirely finalised and may change.

### OTC fees via Permit2

```mermaid
sequenceDiagram
    autonumber
    rect rgba(133, 81, 231, 0.5)
        Settler->>Permit2: permitWitnessTransfer
        WETH-->>User: transfer
        opt buy token fee
            WETH-->>Fee Recipient: transfer
        end
    end
    rect rgba(133, 81, 231, 0.5)
        Settler->>Permit2: permitTransfer
        USDC-->>Market Maker: transfer
        opt sell token fee
            USDC-->>Fee Recipient: transfer
        end
    end
```

Using the Batch functionality we can one or more transfers from either the User or the Market Maker. Allowing us to take either a buy token feel or a sell token fee, or both, during OTC order settlement.

This allows us to achieve **no custody** during this flow and is an extremely gas efficient way to fill OTC orders with fees.

### Uniswap VIP sell token fees via Permit2

```mermaid
sequenceDiagram
    autonumber
    Settler->>UniswapV3: swap
    WETH-->>User: transfer
    UniswapV3->>Settler: uniswapV3Callback
    rect rgba(133, 81, 231, 0.5)
        USDC-->>UniswapV3: permitTransfer
        opt sell token fee
            USDC-->>Fee Recipient: transfer
        end
    end
```

It is possible to collect sell token fees via Permit2 with the UniswapV3 VIP as well, using the Permit2 batch functionality. This flow is similar to the OTC fees.

This allows us to achieve **no custody** during this flow and is an extremely gas efficient way to fill UnuswapV3 with sell token fees.

### Uniswap buy token fees via Permit2

```mermaid
sequenceDiagram
    autonumber
    Settler->>UniswapV3: swap
    WETH-->>Settler: transfer
    UniswapV3->>Settler: uniswapV3Callback
    rect rgba(133, 81, 231, 0.5)
        USDC-->>UniswapV3: permitTransfer
    end
    opt buy token fee
        WETH-->>Fee Recipient: transfer
    end
    WETH-->>User: transfer
```

Since UniswapV3 only supports a single `recipient`, to collect buy token fees, Settler must **take custody** of the buy token. These additional transfers makes settlement with UniswapV3 and buy token fees slightly more expensive than with sell token fees.

## MetaTransactions

Similar to OTC orders, MetaTransactions use the Permit2 with witness. In this case the witness is the MetaTransaction itself, containing the actions the user wants to execute. This gives MetaTransactions access to the same flows above, with a slightly different entrypoint to decode the actions from the Permit2 coupon, rather than the actions being provided directly in the arguments to the execute function.

The EIP712 type the user signs when wanting to perform a metatransaction is:

```
PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,bytes[] actions)
TokenPermissions(address token,uint256 amount)
```

Where `actions` is added and contains the encoded actions the to perform.
