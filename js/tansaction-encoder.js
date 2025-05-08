import * as ethers from "ethers";
import * as fs from "fs";

const args = process.argv.slice(2);

const encode = (a, b) => new ethers.AbiCoder().encode(a, b);

const tx = ethers.Transaction.from(JSON.parse(args[0])).unsignedSerialized;
const digest = ethers.keccak256(tx);

const wallet = new ethers.Wallet(encode(["uint256"], [args[1]]));
const { r, s, v } = wallet.signingKey.sign(digest);

const vsNumber = BigInt(s) | (BigInt(v - 27) << 255n);
const vs = ethers.zeroPadValue(ethers.toBeHex(vsNumber), 32);

const encodedSig = encode(
  ["bytes32", "bytes32"],
  [r, vs]
);

const signaturesJson = JSON.parse(fs.readFileSync("./test/hardcoded/singleSignature.json", "utf-8"));
signaturesJson[args[2]] = encodedSig;
fs.writeFileSync("./test/hardcoded/singleSignature.json", JSON.stringify(signaturesJson, null, 2));

process.stdout.write(encodedSig);
