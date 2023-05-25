import * as fs from "fs";
import { markdownTable } from "markdown-table";

/**
|                               | pair      | gas    |
| ----------------------------- | --------- | ------ |
| **UniswapV3**                 |           |        |
| UniswapRouterV3               | USDC/WETH | 123876 |
| Settler UniswapV3 VIP (warm)  | USDC/WETH | 141337 |
| Settler UniswapV3 VIP (cold)  | USDC/WETH | 174243 |
| Settler UniswapV3             | USDC/WETH |        |
| 0xV4 UniswapV3 VIP            | USDC/WETH | 154155 |
| 0xV4 Multiplex UniswapV3      | USDC/WETH | 167508 |
| 0xV4 UniswapV3 TransformERC20 | USDC/WETH | 273517 |
 */

// If you're reading this I am truly sorry

const readSnapshot = (name, pair) => [
  pair.split("-").join("/"),
  fs.existsSync(`.forge-snapshots/${name}_${pair}.snap`)
    ? fs.readFileSync(`.forge-snapshots/${name}_${pair}.snap`)
    : "N/A",
];

const pairs = ["USDC-WETH", "DAI-WETH", "USDT-WETH"];
const tables = [];
tables.push(
  // UniswapV3 comparisons
  markdownTable([
    ["", "DEX", "Pair", "Gas"],
    ...pairs
      .map((pair) => [
        [
          "UniswapRouter V3",
          "Uniswap V3",
          ...readSnapshot("uniswapRouter_uniswapV3", pair),
        ],
        [
          "Settler VIP (warm)",
          "Uniswap V3",
          ...readSnapshot("settler_uniswapV3VIP", pair),
        ],
        [
          "Settler VIP (cold)",
          "Uniswap V3",
          ...readSnapshot("settler_uniswapV3VIP_cold", pair),
        ],
        ["Settler", "Uniswap V3", ...readSnapshot("settler_uniswapV3", pair)],
        [
          "0x V4 VIP",
          "Uniswap V3",
          ...readSnapshot("zeroEx_uniswapV3VIP", pair),
        ],
        [
          "0x V4 Multiplex",
          "Uniswap V3",
          ...readSnapshot("zeroEx_uniswapV3VIP_multiplex1", pair),
        ],
        [
          "0x V4 TransformERC20",
          "Uniswap V3",
          ...readSnapshot("zeroEx_uniswapV3_transformERC20", pair),
        ],
        ["", "", "", ""],
      ])
      .flat(),
  ]),
  // MetaTransaction comparisons
  markdownTable([
    ["MetaTransactions", "DEX", "Pair", "Gas"],
    ...pairs
      .map((pair) => [
        [
          "Settler",
          "Uniswap V3",
          ...readSnapshot("settler_metaTxn_uniswapV3", pair),
        ],
        [
          "0x V4 Multiplex",
          "Uniswap V3",
          ...readSnapshot("zeroEx_metaTxn_uniswapV3", pair),
        ],
        ["", "", "", ""],
      ])
      .flat(),
  ]),
  // MetaTransaction comparisons
  markdownTable([
    ["OTC", "DEX", "Pair", "Gas"],
    ...pairs
      .map((pair) => [
        ["Settler", "Settler", ...readSnapshot("settler_otc", pair)],
        ["Settler", "0x V4", ...readSnapshot("settler_zeroExOtc", pair)],
        ["0x V4", "0x V4", ...readSnapshot("zeroEx_otcOrder", pair)],
        ["", "", "", ""],
      ])
      .flat(),
  ]),
  // Curve comparisons
  markdownTable([
    ["Curve", "DEX", "Pair", "Gas"],
    ...pairs
      .map((pair) => [
        ["Curve", "Curve", ...readSnapshot("curveV2Pool", pair)],
        [
          "Curve Swap Router",
          "Curve",
          ...readSnapshot("curveV2Pool_swapRouter", pair),
        ],
        ["Settler", "Curve", ...readSnapshot("settler_curveV2VIP", pair)],
        ["0x V4", "Curve", ...readSnapshot("zeroEx_curveV2VIP", pair)],
        ["", "", "", ""],
      ])
      .flat(),
  ])
);

tables.forEach((t) => console.log(t + "\n"));
