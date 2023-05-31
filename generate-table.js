import * as fs from "fs";
import { markdownTable } from "markdown-table";
import stringWidth from "string-width";

/**

| UniswapV3            | DEX        | Pair      | Gas    | %       |
| -------------------- | ---------- | --------- | ------ | ------- |
| UniswapRouter V3     | Uniswap V3 | USDC/WETH | 127268 | 0.00%   |
| Settler VIP (warm)   | Uniswap V3 | USDC/WETH | 123126 | -3.25%  |
| Settler VIP (cold)   | Uniswap V3 | USDC/WETH | 152189 | 19.58%  |
| Settler              | Uniswap V3 | USDC/WETH | 163457 | 28.44%  |
| 0x V4 VIP            | Uniswap V3 | USDC/WETH | 131239 | 3.12%   |
| 0x V4 Multiplex      | Uniswap V3 | USDC/WETH | 144847 | 13.81%  |
| 0x V4 TransformERC20 | Uniswap V3 | USDC/WETH | 250513 | 96.84%  |

 */

// If you're reading this I am truly sorry

const readSnapshot = (name, pair) =>
  fs.existsSync(`.forge-snapshots/${name}_${pair}.snap`)
    ? Number.parseInt(
        fs
          .readFileSync(`.forge-snapshots/${name}_${pair}.snap`)
          .toString()
          .replace(/\n/g, "")
      )
    : undefined;

const pairs = ["USDC-WETH", "DAI-WETH", "USDT-WETH"];
const tables = [];

/**
 * Reads in the snapshot from snapshot[2]_pair.snap, extracting the data and comparing it to the baseline snapshot.
 * The first item in snapshots is used as the baseline to compare against.
 *
 * @param {*} name human readable name for the snapshot group, e.g MetaTransactions
 * @param {*} snapshots array of [name, dex, filename]
 * @param {*} pairs array of "-"" separated pairs which exist as snapshots
 * @returns
 */
const generateTable = (name, snapshots, pairs) => {
  const data = [[name, "DEX", "Pair", "Gas", "%"]];
  for (const pair of pairs) {
    const baselineData = readSnapshot(snapshots[0][2], pair);
    for (const [snapshotName, snapshotDex, snapshotFilename] of snapshots) {
      const snapshotData = readSnapshot(snapshotFilename, pair);
      if (snapshotData === undefined) {
        continue;
      }
      const baselineComparePerc =
        (((snapshotData - baselineData) / baselineData) * 100).toFixed(2) + "%";

      data.push([
        snapshotName,
        snapshotDex,
        pair.split("-").join("/"),
        snapshotData,
        baselineComparePerc,
      ]);
    }
    data.push(["", "", "", ""]);
  }
  return data;
};

tables.push(
  // UniswapV3 comparisons
  markdownTable(
    generateTable(
      "Uniswap V3",
      [
        ["0x V4 VIP", "Uniswap V3", "zeroEx_uniswapV3VIP"],
        ["0x V4 Multiplex", "Uniswap V3", "zeroEx_uniswapV3VIP_multiplex1"],
        [
          "0x V4 TransformERC20",
          "Uniswap V3",
          "zeroEx_uniswapV3_transformERC20",
        ],
        ["Settler VIP (warm)", "Uniswap V3", "settler_uniswapV3VIP"],
        ["Settler VIP (cold)", "Uniswap V3", "settler_uniswapV3VIP_cold"],
        ["Settler", "Uniswap V3", "settler_uniswapV3"],
        ["UniswapRouter V3", "Uniswap V3", "uniswapRouter_uniswapV3"],
      ],
      pairs
    ),
    { stringLength: stringWidth }
  ),
  // MetaTransaction comparisons
  markdownTable(
    generateTable(
      "MetaTransactions",
      [
        ["0x V4 Multiplex", "Uniswap V3", "zeroEx_metaTxn_uniswapV3"],
        ["Settler", "Uniswap V3", "settler_metaTxn_uniswapV3"],
      ],
      pairs
    ),
    { stringLength: stringWidth }
  ),
  // OTC comparisons
  markdownTable(
    generateTable(
      "OTC",
      [
        ["0x V4", "0x V4", "zeroEx_otcOrder"],
        ["Settler", "Settler", "settler_otc"],
        ["Settler", "0x V4", "settler_zeroExOtc"],
      ],
      pairs
    ),
    { stringLength: stringWidth }
  ),
  // Curve comparisons
  markdownTable(
    generateTable(
      "Curve",
      [
        ["0x V4", "Curve", "zeroEx_curveV2VIP"],
        ["Settler", "Curve", "settler_curveV2VIP"],
        ["Curve", "Curve", "curveV2Pool"],
        ["Curve Swap Router", "Curve", "curveV2Pool_swapRouter"],
      ],
      pairs
    ),
    { stringLength: stringWidth }
  ),
  // Swap with fees comparisons
  markdownTable(
    generateTable(
      "Swap with Fees",
      [
        ["Settler", "Uniswap V3", "settler_uniswapV3_fee"],
        ["Settler", "Curve", "settler_curveV2_fee"],
      ],
      pairs
    ),
    { stringLength: stringWidth }
  )
);

tables.forEach((t) => console.log(t + "\n"));

const inputFile = "README.md";
const beginToken = `[//]: # "BEGIN TABLES"`;
const endToken = `[//]: # "END TABLES"`;
const contents = fs.readFileSync(inputFile, "utf8");
const tableData = tables.map((t) => t.toString()).join("\n\n");

const modifiedData = contents.replace(
  new RegExp(`\\${beginToken}[\\s\\S]*?\\${endToken}`, "g"),
  `${beginToken}\n\n${tableData}\n\n${endToken}`
);

fs.writeFileSync(inputFile, modifiedData);
