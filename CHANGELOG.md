The actions `MAKERPSM_SELL` and `MAKERPSM_BUY` actions have been combined into a single `MAKERPSM` action with a `buyGem` boolean flag
Add support for AlgebraSwap-style UniV3 forks (single pool per token pair)
    When using the UniV3 actions for an AlgebraSwap-style pool, the fee tier/pool ID must be passed as 0
Add CamelotV3 AlgebraSwap-style UniV3 fork to Arbitrum
Add QuickSwapV3 AlebraSwap-style UniV3 fork to Polygon
Added support for `CURVE_TRICRYPTO_VIP` and `METATXN_CURVE_TRICRYPTO_VIP` on Arbitrum
Bug! Fixed BNB Chain PancakeSwapV3 deployer address (it's the same as on all other chains)
Added PancakeSwapV3 to Arbitrum UniV3 VIP
Renumbered SolidlyV3 UniV3 forkId from 2 to 3 on Mainnet (2 is reserved for Sushi)
Renumbered Velodrome Slipstream UniV3 forkId from 1 to 3 on Optimism (1 and 2 are reserved for Pancake and Sushi, respectively)
