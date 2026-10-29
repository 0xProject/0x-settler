import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";

function artifacts(root, directory = "", found = new Map()) {
  for (const entry of fs.readdirSync(path.join(root, directory), { withFileTypes: true })) {
    const relative = path.join(directory, entry.name);
    // Build information file names include the full compiler version, which differs after patching.
    if (relative === "build-info") continue;
    if (entry.isDirectory()) artifacts(root, relative, found);
    else if (entry.name.endsWith(".json")) {
      const artifact = JSON.parse(fs.readFileSync(path.join(root, relative), "utf8"));
      found.set(relative, {
        bytecode: artifact.bytecode?.object,
        deployedBytecode: artifact.deployedBytecode?.object,
        compiler: artifact.metadata?.compiler?.version,
      });
    }
  }
  return found;
}

function compare(stock, patched) {
  const problems = [];
  let withCode = 0;
  for (const name of [...new Set([...stock.keys(), ...patched.keys()])].sort()) {
    const s = stock.get(name), p = patched.get(name);
    if (!s || !p) {
      problems.push(`${name}: missing from ${s ? "patched" : "stock"} output`);
      continue;
    }
    if (!s.compiler || !p.compiler) {
      problems.push(`${name}: compiler version missing from the artifact metadata`);
    } else if (s.compiler.split("+", 1)[0] !== p.compiler.split("+", 1)[0]) {
      problems.push(`${name}: compiled with ${s.compiler} and ${p.compiler}`);
    } else if (s.compiler === p.compiler) {
      problems.push(`${name}: both builds report the same compiler ${s.compiler}`);
    }
    for (const field of ["bytecode", "deployedBytecode"]) {
      if (typeof s[field] !== "string" || typeof p[field] !== "string") {
        problems.push(`${name}: ${field} missing from the artifact`);
      } else if (s[field] !== p[field]) {
        problems.push(`${name}: ${field} differs between stock and patched solc`);
      }
    }
    if ([s.bytecode, p.bytecode].some((code) => typeof code === "string" && code !== "" && code !== "0x")) {
      withCode++;
    }
  }
  if (!withCode) problems.push("No artifact with bytecode was compiled");
  return { problems, withCode };
}

if (process.argv[2] === "--self-test") {
  const stock = { bytecode: "0x6000", deployedBytecode: "0x00", compiler: "0.8.34+commit.80d5c536" };
  const patched = { ...stock, compiler: `${stock.compiler}.mod` };
  const check = (s, p) => compare(new Map([["C.sol/C.json", s]]), new Map([["C.sol/C.json", p]])).problems;
  assert.deepEqual(check(stock, patched), []);
  assert(check(stock, stock).some((message) => message.includes("same compiler")));
  assert(check(stock, { ...patched, compiler: "0.8.35+commit.12345678" }).length);
  assert(check(stock, { ...patched, compiler: undefined }).length);
  for (const field of ["bytecode", "deployedBytecode"]) {
    assert(check(stock, { ...patched, [field]: "0x6001" }).length);
    assert(check({ ...stock, [field]: undefined }, { ...patched, [field]: undefined }).length);
  }
  assert(check({ ...stock, bytecode: "0x" }, { ...patched, bytecode: "0x" }).length);
  assert(compare(new Map(), new Map()).problems.length);
  assert(check(stock, undefined).length);
  assert(check(undefined, patched).length);
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "compare-bytecode-"));
  try {
    fs.mkdirSync(path.join(root, "build-info"));
    fs.writeFileSync(path.join(root, "build-info/ignored.json"), "not artifact JSON");
    fs.mkdirSync(path.join(root, "C.sol"));
    fs.writeFileSync(path.join(root, "C.sol/C.json"), JSON.stringify({
      bytecode: { object: stock.bytecode }, deployedBytecode: { object: stock.deployedBytecode },
      metadata: { compiler: { version: stock.compiler } },
    }));
    assert.deepEqual([...artifacts(root)], [["C.sol/C.json", stock]]);
    fs.writeFileSync(path.join(root, "C.sol/C.json"), "invalid JSON");
    assert.throws(() => artifacts(root), SyntaxError);
  } finally {
    fs.rmSync(root, { recursive: true });
  }
  console.log("Bytecode comparison checks passed");
} else {
  const [stockDirectory, patchedDirectory] = process.argv.slice(2);
  const { problems, withCode } = compare(artifacts(stockDirectory), artifacts(patchedDirectory));
  console.log(`Compared ${withCode} artifacts with creation bytecode`);
  for (const problem of problems) console.error(problem);
  process.exitCode = problems.length ? 1 : 0;
}
