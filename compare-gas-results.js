import * as fs from "fs";
import { execSync } from "child_process";
import path from "path";
import chalk from "chalk";
import { markdownTable } from "markdown-table";
import stringWidth from "string-width";

const flavours = {
  [Number.NEGATIVE_INFINITY]: chalk.black.bgGreen,
  [-10]: chalk.black.bgGreen,
  [-5]: chalk.white,
  [1]: chalk.white,
  [5]: chalk.yellow,
  [10]: chalk.black.bgRed,
  [Number.POSITIVE_INFINITY]: chalk.black.bgRed,
};

const failOnThresholdPerc = 10;

const selectFlavour = (diffPerc) => {
  let selectedFlavour = chalk.white;
  for (let key of Object.keys(flavours).sort((a, b) => a - b)) {
    if (diffPerc <= Number(key)) {
      selectedFlavour = flavours[key];
      break;
    }
  }
  return selectedFlavour;
};

const collectGasComparisonsAsync = (comparisonCommitHash, filepath) => {
  const contents = Number(fs.readFileSync(filepath));
  let prevContents;
  try {
    prevContents = Number(
      execSync(`git show "${comparisonCommitHash}:${filepath}"`, {
        cwd: process.cwd(),
        stdio: ["pipe", "pipe", "ignore"], // ignore stderr
      }).toString()
    );
  } catch (e) {
    // New snapshots may not have a previous version
    prevContents = contents;
  }

  const diffPerc = ((contents - prevContents) / prevContents) * 100;
  return { filepath, contents, prevContents, diffPerc };
};

const processGasComparisons = (results) => {
  let maxDiffPerc = Number.NEGATIVE_INFINITY;
  let minDiffPerc = Number.POSITIVE_INFINITY;
  const tableData = [
    ["Snapshot", "Current", "Previous", "Diff"],
    ...results
      .sort((a, b) => a.diffPerc - b.diffPerc)
      .map((r) => {
        const { filepath, contents, prevContents, diffPerc } = r;
        maxDiffPerc = Math.max(maxDiffPerc, diffPerc);
        minDiffPerc = Math.min(minDiffPerc, diffPerc);
        if (diffPerc == 0) return;
        return [
          path.parse(filepath).name,
          contents,
          prevContents,
          selectFlavour(diffPerc)(` ${diffPerc.toFixed(2)}%`),
        ];
      })
      .filter((r) => r !== undefined),
  ];
  console.log(markdownTable(tableData, { stringLength: stringWidth }));

  if (Math.abs(maxDiffPerc) > failOnThresholdPerc) {
    console.log(
      flavours[Number.POSITIVE_INFINITY](
        "\n\tYou have angered Olon Degëlnomal, the dwarven lord of gas.\t"
      )
    );
    process.exit(1);
  }

  if (minDiffPerc < -failOnThresholdPerc) {
    console.log(
      flavours[Number.NEGATIVE_INFINITY](
        "\n\tOlon Degëlnomal, the dwarven lord of gas, is pleased with your contribution.\t"
      )
    );
  }
};

// Compare gas snapshot results with a previous commit.
// If you wish to compare with an earlier commit, set the COMPARE_GIT_SHA environment variable
const compareGasResults = async (dir) => {
  let comparisonCommitHash = execSync(`git rev-parse HEAD`, {
    cwd: process.cwd(),
  })
    .toString()
    .replace("\n", "");
  comparisonCommitHash = process.env.COMPARE_GIT_SHA || comparisonCommitHash;

  processGasComparisons(
    await Promise.all(
      fs
        .readdirSync(dir)
        .map((file) =>
          collectGasComparisonsAsync(comparisonCommitHash, path.join(dir, file))
        )
    )
  );
};

await compareGasResults(".forge-snapshots");
