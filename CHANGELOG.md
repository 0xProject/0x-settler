Master list of UniV3 forks:

  0. UniswapV3
  1. PancakeSwapV3
  2. SushiSwapV3
  3. SolidlyV3
  4. Velodrome/Aerodrome Slipstream
  5. CamelotV3/QuickSwapV3 (Algebra-like)
  6. AlienBaseV3
  7. BaseX
  8. SwapBasedV3
  9. Thruster
  10. BladeSwap (Algebra-like)
  11. Fenix (Algebra-like)
  12. ZebraV3
  13. Lynex (Algebra-like)
  14. DackieSwapV3
  15. Thick
  16. KinetixV3
  17. MetavaultV3
  18. BlasterV3
  19. MonoSwapV3
  20. RogueXV1
  21. SupSwapV3
  22. Kim (Algebra-like)
  23. SwapMode
  24. Swapsicle (Algebra-like)
  25. Panko
  26. Swapr (Algebra-like)
  27. SpookySwap
  28. Wagmi
  29. SwapX (Algebra-like)
  30. KodiakV3
  31. Bulla Exchange (Algebra-like)

---

## [Unreleased]

### Breaking changes

### Non-breaking changes

* Create new Settler version for intent-based settlement -- the taker only signs
  the slippage, not the actions
  * This is now `tokenId` 4
* Fix a bug in the BalancerV3 action resulting in incorrect decoding of callback
  returndata

## 2025-02-20

### Breaking changes

### Non-breaking changes

* Add UniswapV3 UniV3 fork to Monad Testnet

## 2025-02-12

### Breaking changes

### Non-breaking changes

* Deploy Settler to Unichain network
  * Add UniswapV3 UniV3 fork to Unichain
  * Add UniswapV4 actions to Unichain
* Deploy Settler to Berachain network
  * Add KodiakV3 UniV3 fork to Berachain
  * Add Bulla Exchange UniV3 (Algebra style) fork to Berachain
* Add UniswapV4 actions to Sepolia
* Add UniswapV4 actions to Ink
* Add BalancerV3 actions to Base
* Add BalancerV3 actions to Arbitrum

## 2025-01-23

### Breaking changes

* Remove `gemToken` and `psm` arguments from `MAKERPSM` action
  * This specializes and gas optimizes the action for the Lite PSM
    (0xf6e72Db5454dd049d0788e411b06CfAF16853042)
* `TRANSFER_FROM` is now a "VIP" action. It can only be executed as the first
  action of a swap
* Update Avalanche to the Cancun hardfork
  * This means that the AllowanceHolder address on Avalanche is now 0x0000000000001fF3684f28c67538d4D072C22734

### Non-breaking changes

* Add actions for UniswapV4
  * `UNISWAPV4`, `UNISWAPV4_VIP`, and `METATXN_UNISWAPV4_VIP`
  * See comments in [UniswapV4.sol](src/core/UniswapV4.sol) regarding how to
    encode `fills`
  * See comments in
    [FlashAccountingCommon.sol](src/core/FlashAccountingCommon.sol) regarding
    how to compute a perfect token hash function
* Add UniswapV4 actions to:
  * Mainnet
  * Arbitrum
  * Avalanche
  * Base
  * Blast
  * Bnb
  * Optimism
  * Polygon
  * WorldChain
* Add `msgSender()(address)` accessor on Base to retrieve the current taker
* Improve accuracy, gas, and convergence region coverage in SolidlyV1/VelodromeV2 action (`VELODROME`)
* Add DodoV1 actions to more chains
  * Add `DODOV1` action to Arbitrum
  * Add `DODOV1` action to Bnb
  * Add `DODOV1` action to Linea
  * Add `DODOV1` action to Mantle
  * Add `DODOV1` action to Polygon
  * Add `DODOV1` action to Scroll
* Add `rebateClaimer()(address)` function on Mainnet Settlers for gas rebate program
* Add SolidlyV3 UniV3 fork to Sonic
* Add Wagmi UniV3 fork to Sonic
* Add SwapX UniV3 (Algebra style) fork to Sonic
* Add actions for BalancerV3
  * `BALANCERV3`, `BALANCERV3_VIP`, and `METATXN_BALANCERV3_VIP`
  * See comments in [BalancerV3.sol](src/core/BalancerV3.sol) regarding how to
    encode `fills`
  * See comments in
    [FlashAccountingCommon.sol](src/core/FlashAccountingCommon.sol) regarding
    how to compute a perfect token hash function

## 2025-01-09

### Breaking changes

### Non-breaking changes

* Deploy Settler to Monad testnet chain

## 2024-12-18

### Breaking changes

### Non-breaking changes

* Deploy Settler to Ink chain
  * Add UniswapV3 UniV3 fork to Ink

## 2024-12-14

### Breaking changes

### Non-breaking changes

* Deploy Settler to Fantom Sonic network
  * Add UniswapV3 UniV3 fork to Sonic
  * Add SpookySwap UniV3 fork to Sonic

## 2024-12-12

### Breaking changes

### Non-breaking changes

* Deploy Settler to Taiko network
  * Add UniswapV3 UniV3 fork to Taiko
  * Add Swapsicle UniV3 (Algebra style) fork to Taiko
  * Add Panko UniV3 fork to Taiko
* Deploy Settler to World Chain network
  * Add UniswapV3 UniV3 fork to World Chain
  * Add DackieSwapV3 UniV3 fork to World Chain
* Deploy Settler to Gnosis chain
  * Add UniswapV3 UniV3 fork to Gnosis
  * Add SushiswapV3 UniV3 fork to Gnosis
  * Add Swapr UniV3 (Algebra style) fork to Gnosis

## 2024-10-08

### Breaking changes

### Non-breaking changes

* Add `DODOV2` Dodo V2 action on Mantle
* Deploy Settler to Mode network
  * Add SupSwapV3 UniV3 fork to Mode
  * Add Kim UniV3 (Algebra style) fork to Mode
  * Add SwapModeV3 UniV3 fork to Mode

## 2024-09-09

### Breaking changes

* Upgrade Bnb chain deployment to Cancun (Tycho) hardfork
  * This changes the `AllowanceHolder` address on that chain to
    `0x0000000000001fF3684f28c67538d4D072C22734`

### Non-breaking changes

* Add BlasterV3 UniV3 fork to Blast
* Add MonoSwapV3 UniV3 fork to Blast
* Add RogueXV1 UniV3 fork to Blast
  * This UniV3 fork has unusual integrations with perpetual futures; it may
    revert when a "normal" UniV3 fork wouldn't

## 2024-08-26

### Breaking changes

* Add slippage check parameter to `MAKERPSM` action to gas-optimize the new "lite" PSM
  * Note that for the "normal" PSM ("MCD PSM USDC A",
    0x89B78CfA322F6C5dE0aBcEecab66Aee45393cC5A), `amountOutMin` _**MUST**_ be
    zeroed, otherwise you will get an out-of-gas
* Special case a permitted (sell) amount of `type(uint256).max - 9_999` and
  above -- this introspects the taker's balance of the sell token and attempts
  to sell a proportion of it

### Non-breaking changes

* Added `prev` accessor function to `Deployer`
* Configure yield and gas for Deployer on Blast
* Deploy Settler to Mantle network
* Add `DODOV2` action to Arbitrum
* Add SolidlyV3 UniV3 fork to Arbitrum

## 2024-08-12

### Breaking changes

* Remove DodoV1 from all chains except Mainnet
  * Remove `DODOV1` action from Arbitrum
  * Remove `DODOV1` action from Avalanche
  * Remove `DODOV1` action from Base
  * Remove `DODOV1` action from Blast
  * Remove `DODOV1` action from Bnb
  * Remove `DODOV1` action from Linea
  * Remove `DODOV1` action from Optimism
  * Remove `DODOV1` action from Polygon
  * Remove `DODOV1` action from Scroll
  * Remove `DODOV1` action from Sepolia
  * (`DODOV1` action remains available on Mainnet)

### Non-breaking changes

* Arbiscan's "Cancun" issue has been fixed -- verify Settler on Arbiscan
* Link to 0x's Immunefi bug bounty page from `README.md`
* Add UniswapV3 UniV3 fork to Scroll
* Add new actions `MAVERICKV2`, `MAVERICKV2_VIP`, and `METATXN_MAVERICKV2_VIP`
  * Add MaverickV2 to Mainnet
  * Add MaverickV2 to Base
  * Add MaverickV2 to Arbitrum
  * Add MaverickV2 to Bnb
  * Add MaverickV2 to Scroll
  * Add MaverickV2 to Sepolia
* Add DackieSwapV3 UniV3 fork
  * Add DackieSwapV3 to Arbitrum
  * Add DackieSwapV3 to Base
  * Add DackieSwapV3 to Blast (new inithash)
  * Add DackieSwapV3 to Optimism
* Add Thick UniV3 fork to Base
* Add KinetixV3 UniV3 fork to Base
* Add new action `DODOV2`
  * Add DodoV2 to Avalanche
  * Add DodoV2 to Base
  * Add DodoV2 to Bnb
  * Add DodoV2 to Mainnet
  * Add DodoV2 to Polygon
  * Add DodoV2 to Scroll
* Add MetavaultV3 UniV3 fork to Scroll
* Add SushiswapV3 UniV3 fork to more chains
  * Add SushiswapV3 to Arbitrum
  * Add SushiswapV3 to Mainnet
  * Add SushiswapV3 to Optimism
* Add `prev` view function to `Deployer`

## 2024-07-29

* Configure Blast gas fee claims on Settler deployment
* Change Settler's `AllowanceHolder` integration to use `return` to signal non-ERC20 compliance (rather than `revert`)
  * `AllowanceHolder`'s own signal still uses `revert`, but this will only come up rarely
* Flatten Settler source files before deployment for ease of verification
* All chains redeployed to pick up above changes

## 2024-07-18

* Deployed Settler to Linea
* Added Lynex Algebra-style UniV3 fork to Linea
* Update Velodrome Slipstream factory address (and inithash) to migrated one
* Bug! Fixed wrong slippage actual value in `UNISWAPV2` action

## 2024-07-15

* Deployed Settler to Blast
* Added Thruster UniV3 fork to Blast
* Added BladeSwap Algebra-style UniV3 fork to Blast
* Added Fenix Algebra-style UniV3 fork to Blast
* Deployed Settler to Scroll
* Added ZebraV3 UniV3 fork to Scroll
* Added SolidlyV3 UniV3 fork to Base
* Added SwapBasedV3 UniV3 fork to Base
* Added support for `DODOV1` action to all chains
* Added support for `VELODROME` action to all chains

## 2024-06-27

* Add SushiswapV3 UniV3 fork to Polygon
* Added support for `DODOV1` action on Bnb
* Added support for `DODOV1` action on Polygon

## 2024-06-10

* Added extra anonymous argument to `execute` and `executeMetaTxn` for tracking
  zid and affiliate address
* Add SolidlyV3 UniV3 fork to Optimism
* Added support for `DODOV1` action on Arbitrum

## 2024-06-05

* The actions `MAKERPSM_SELL` and `MAKERPSM_BUY` actions have been combined into
  a single `MAKERPSM` action with a `buyGem` boolean flag
* Add support for AlgebraSwap-style UniV3 forks (single pool per token pair)
  * When using the UniV3 actions for an AlgebraSwap-style pool, the fee
    tier/pool ID must be passed as 0
* Add CamelotV3 AlgebraSwap-style UniV3 fork to Arbitrum
* Add QuickSwapV3 AlebraSwap-style UniV3 fork to Polygon
* Added support for `CURVE_TRICRYPTO_VIP` and `METATXN_CURVE_TRICRYPTO_VIP` on
  Arbitrum
* Bug! Fixed BNB Chain PancakeSwapV3 deployer address (it's the same as on all
  other chains)
* Added PancakeSwapV3 to Arbitrum UniV3 VIP
* Added BaseX to Base UniV3 VIP
