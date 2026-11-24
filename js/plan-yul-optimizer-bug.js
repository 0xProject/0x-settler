import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import fs from "node:fs";

const fixedSets = [
  { name: "AllowanceHolder", paths: ["src/allowanceholder/AllowanceHolder.sol"], runs: "1000000" },
  // The deployment script imports both contracts and fixes their compiler through the Deployer pragma.
  { name: "Deployer and Safe module (new chain)", paths: ["script/DeploySafes.s.sol"], runs: "1000000" },
  { name: "Deployer (upgrade)", paths: ["src/deployer/Deployer.sol"] },
  { name: "SafeGuard", paths: ["src/deployer/SafeGuard.sol"], evm: "london", runs: "200" },
  { name: "MultiCall", paths: ["src/multicall/MultiCall.sol"], evm: "london", runs: "1000000" },
  { name: "CrossChainReceiverFactory", paths: ["src/CrossChainReceiverFactory.sol"], evm: "london", runs: "1000000" },
];

function chainSet(chain) {
  return {
    name: `${chain} Settlers`,
    paths: ["TakerSubmitted", "MetaTxn", "Intent", "BridgeSettler"].map(
      (flavor) => `src/chains/${chain}/${flavor}.sol`,
    ),
    flatten: true,
  };
}

function resolveSet(set, byPath) {
  const versions = new Set(set.paths.flatMap((path) => {
    const resolved = byPath.get(path);
    if (!resolved?.size) throw new Error(`${set.name}: forge did not resolve a compiler for ${path}`);
    return [...resolved];
  }));
  if (versions.size !== 1) {
    throw new Error(`${set.name}: sources resolve to several compilers: ${[...versions].join(", ")}`);
  }
  const [solc] = versions;
  if (!/^\d+\.\d+\.\d+$/.test(solc)) throw new Error(`Unexpected solc version: ${solc}`);
  const [major, minor, patch] = solc.split(".").map(Number);
  return { ...set, solc, affected: major === 0 && minor === 8 && patch >= 19 && patch <= 37 };
}

if (process.argv[2] === "--self-test") {
  const set = chainSet("Mainnet");
  assert.equal(set.paths.length, 4);
  assert.equal(set.flatten, true);
  assert(set.paths.includes("src/chains/Mainnet/BridgeSettler.sol"));
  for (const [version, affected] of [
    ["0.8.18", false], ["0.8.19", true], ["0.8.37", true], ["0.8.38", false], ["0.9.0", false],
  ]) {
    const byPath = new Map(set.paths.map((path) => [path, new Set([version])]));
    assert.equal(resolveSet(set, byPath).affected, affected);
  }
  assert.throws(() => resolveSet(set, new Map()), /did not resolve/);
  const byPath = new Map(set.paths.map((path) => [path, new Set(["0.8.34"])]));
  byPath.get(set.paths[0]).add("0.8.25");
  assert.throws(() => resolveSet(set, byPath), /several compilers/);
  byPath.set(set.paths[0], new Set(["0.8.34-nightly"]));
  assert.throws(() => resolveSet({ ...set, paths: [set.paths[0]] }, byPath), /Unexpected solc/);
  assert(fixedSets.some((set) => set.paths.includes("script/DeploySafes.s.sol") && set.runs === "1000000"));
  console.log("Compiler planning checks passed");
} else {
  const resolved = JSON.parse(execFileSync("forge", ["compiler", "resolve", "--json", "-v"], {
    encoding: "utf8",
  }));
  const byPath = new Map();
  for (const entries of Object.values(resolved)) {
    for (const { version, paths = [] } of entries) {
      for (const path of paths) {
        if (!byPath.has(path)) byPath.set(path, new Set());
        byPath.get(path).add(version);
      }
    }
  }
  const chains = Object.values(JSON.parse(fs.readFileSync("chain_config.json", "utf8")))
    .map(({ displayName }) => displayName)
    .filter((chain) => fs.existsSync(`src/chains/${chain}`));
  const sets = [...fixedSets, ...chains.map(chainSet)].map((set) => resolveSet(set, byPath));
  const versions = [...new Set(sets.filter((set) => set.affected).map((set) => set.solc))]
    .sort((a, b) => a.localeCompare(b, "en", { numeric: true }));

  for (const set of sets) {
    console.log(`${set.name}: solc ${set.solc}, ${set.affected ? "affected" : "not affected"}`);
  }
  const outputs = `sets=${JSON.stringify(sets)}\nversions=${JSON.stringify(versions)}\n`;
  if (process.env.GITHUB_OUTPUT) fs.appendFileSync(process.env.GITHUB_OUTPUT, outputs);
  else process.stdout.write(outputs);
}
