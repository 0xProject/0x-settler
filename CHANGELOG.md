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

---

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
* Add DackieSwapV3 UniV3 fork to Base
* Add Thick UniV3 fork to Base
* Add KinetixV3 UniV3 fork to Base

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
