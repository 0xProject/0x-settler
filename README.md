# 0x Settler

Settlement contracts utilising [Permit2](https://github.com/Uniswap/permit2) to
perform swaps without any passive allowances to the contract.

## How do I find the most recent deployment?

The 0x Settler deployer/registry contract is deployed to
`0x00000000000004533Fe15556B1E086BB1A72cEae` across all chains (unless somebody
screwed up the vanity address and didn't update this document). The
deployer/registry is an ERC1967 UUPS upgradeable contract that implements an
ERC721-compatible NFT. To find the address of the most recent `Settler`
deployment, call `function ownerOf(uint256 tokenId) external view returns (address)`
with the `tokenId` set to the number of the feature that you wish to query. For
taker-submitted flows, the feature number is probably 2 unless something major
changed and nobody updated this document. Likewise, for gasless/metatransaction
flows, the feature number is probably 3. A reverting response indicates that
`Settler` is paused and you should not interact. Do not hardcode any `Settler`
address in your integration. _**ALWAYS**_ query the deployer/registry for the
address of the most recent `Settler` contract before building or signing a
transaction, metatransaction, or order.

### 0x API dwell time

There is some lag between the deployment of a new instance of 0x Settler and
when 0x API begins generating calldata targeting that instance. This allows 0x
to perform extensive end-to-end testing to ensure zero downtime for
integrators. During this "dwell" period, a strict comparison between the
[`.transaction.to`](https://0x.org/docs/api#tag/Swap/operation/swap::permit2::getQuote)
field of the API response and the result of querying
`IERC721(0x00000000000004533Fe15556B1E086BB1A72cEae).ownerOf(...)` will
fail. For this reason, there is a fallback. If `ownerOf` does not revert, but
the return value isn't the expected value, _**YOU SHOULD ALSO**_ query the
selector `function prev(uint128) external view returns (address)` with the same
argument. If the response from this function call does not revert and the result
is the expected address, then the 0x API is in the dwell time and you may
proceed as normal.

<details>
<summary>Example Solidity code for checking whether Settler is genuine</summary>

```Solidity
interface IERC721Tiny {
    function ownerOf(uint256 tokenId) external view returns (address);
}
interface IDeployerTiny is IERC721Tiny {
    function prev(uint128 featureId) external view returns (address);
}

error CounterfeitSettler(address);

function requireGenuineSettler(uint128 featureId, address allegedSettler)
    internal
    view
{
    IDeployerTiny deployer =
        IDeployerTiny(0x00000000000004533Fe15556B1E086BB1A72cEae);
    // Any revert in `ownerOf` or `prev` will be bubbled. Any error in
    // ABIDecoding the result will result in a revert without a reason string.
    if (deployer.ownerOf(featureId) != allegedSettler
        || deployer.prev(featureId) != allegedSettler) {
        revert CounterfeitSettler(allegedSettler);
    }
}
```

While the above code is the _**strongly recommended**_ approach, it is
comparatively gas-expensive. A more gas-optimized approach is demonstrated
below, but it does not cover the case where Settler has been paused due to a
bug.

```Solidity

function computeGenuineSettler(uint128 featureId, uint64 deployNonce)
    internal
    view
    returns (address)
{
    bytes32 salt = bytes32(
        uint256(featureId) << 128 | uint256(block.chainid) << 64
            | uint256(deployNonce)
    );
    // for London hardfork chains, substitute
    // 0x1774bbdc4a308eaf5967722c7a4708ea7a3097859cb8768a10611448c29981c3
    bytes32 shimInitHash =
        0x3bf3f97f0be1e2c00023033eefeb4fc062ac552ff36778b17060d90b6764902f;
    address shim =
        address(
            uint160(
                uint256(
                    keccak256(
                        abi.encodePacked(
                            bytes1(0xff),
                            0x00000000000004533Fe15556B1E086BB1A72cEae,
                            salt,
                            shimInitHash
                        )
                    )
                )
            )
        );
    address settler =
        address(
            uint160(
                uint256(
                    keccak256(
                        abi.encodePacked(bytes2(0xd694), shim, bytes1(0x01))
                    )
                )
            )
        );
    return settler;
}
```

</details>

### AllowanceHolder addresses

AllowanceHolder is deployed to the following addresses depending on the most
advanced EVM hardfork supported on the chain. You can hardcode this address in
your integration.

* `0x0000000000001fF3684f28c67538d4D072C22734` on chains supporting the Cancun
  hardfork (Ethereum Mainnet, Ethereum Sepolia, Polygon, Base, Optimism,
  Arbitrum, Blast, Bnb)
* `0x0000000000005E88410CcDFaDe4a5EfaE4b49562` on chains supporting the Shanghai
  hardfork (Avalanche, Scroll, Mantle)
* `0x000000000000175a8b9bC6d539B3708EEd92EA6c` on chains supporting the London
  hardfork (Linea)

### Permit2 address

Permit2 is deployed to `0x000000000022D473030F116dDEE9F6B43aC78BA3` across all
chains. You can hardcode this address in your integration.

### Examples

#### TypeScript ([viem](https://viem.sh/))

<details>
<summary>Click to see TypeScript example of getting Settler addresses</summary>

```TypeScript
import { createPublicClient, http, parseAbi } from 'viem';

(async function main() {
    const client = createPublicClient({
        transport: http(process.env.RPC_URL),
    });

    const deployer = "0x00000000000004533Fe15556B1E086BB1A72cEae";
    const tokenDescriptions = {
        2: "taker submitted",
        3: "metatransaction",
    };

    const deployerAbi = parseAbi([
        "function prev(uint128) external view returns (address)",
        "function ownerOf(uint256) external view returns (address)",
        "function next(uint128) external view returns (address)",
    ]);
    const functionDescriptions = {
        "prev": "previous",
        "ownerOf": "current",
        "next": "next",
    };

    const blockNumber = await client.getBlockNumber();
    for (let tokenId in tokenDescriptions) {
        for (let functionName in functionDescriptions) {
            let addr = await client.readContract({
                address: deployer,
                abi: deployerAbi,
                functionName,
                args: [tokenId],
                blockNumber,
            });
            console.log(functionDescriptions[functionName] + " " + tokenDescriptions[tokenId] + " settler address " + addr);
        }
    }

    // output:
    // previous taker submitted settler address 0x07E594aA718bB872B526e93EEd830a8d2a6A1071
    // current taker submitted settler address 0x2c4B05349418Ef279184F07590E61Af27Cf3a86B
    // next taker submitted settler address 0x70bf6634eE8Cb27D04478f184b9b8BB13E5f4710
    // previous metatransaction settler address 0x25b81CE58AB0C4877D25A96Ad644491CEAb81048
    // current metatransaction settler address 0xAE11b95c8Ebb5247548C279A00120B0ACadc7451
    // next metatransaction settler address 0x12D737470fB3ec6C3DeEC9b518100Bec9D520144
})();
```

</details>

#### JavaScript ([Ethers.js](https://docs.ethers.org/v5/))

<details>
<summary>Click to see JavaScript example of getting Settler addresses</summary>

Note that this example uses version 5 of `Ethers.js`. The current version of
`Ethers.js` is 6, which is not compatible with this snippet.

```JavaScript
"use strict";
const {ethers} = require("ethers");

(async function main() {
  const provider = new ethers.providers.JsonRpcProvider(process.env.RPC_URL);

  const deployerAddress = "0x00000000000004533Fe15556B1E086BB1A72cEae";
  const tokenDescriptions = {
    2: "taker submitted",
    3: "metatransaction",
  };

  const deployerAbi = [
    "function prev(uint128) external view returns (address)",
    "function ownerOf(uint256) external view returns (address)",
    "function next(uint128) external view returns (address)",
  ];
  const functionDescriptions = {
    "prev": "previous",
    "ownerOf": "current",
    "next": "next",
  };

  const deployer = new ethers.Contract(deployerAddress, deployerAbi, provider);
  for (let tokenId in tokenDescriptions) {
    for (let functionName in functionDescriptions) {
      let addr = await deployer[functionName](tokenId);
      console.log(functionDescriptions[functionName] + " " + tokenDescriptions[tokenId] + " settler address " + addr);
    }
  }

  // output:
  // previous taker submitted settler address 0x07E594aA718bB872B526e93EEd830a8d2a6A1071
  // current taker submitted settler address 0x2c4B05349418Ef279184F07590E61Af27Cf3a86B
  // next taker submitted settler address 0x70bf6634eE8Cb27D04478f184b9b8BB13E5f4710
  // previous metatransaction settler address 0x25b81CE58AB0C4877D25A96Ad644491CEAb81048
  // current metatransaction settler address 0xAE11b95c8Ebb5247548C279A00120B0ACadc7451
  // next metatransaction settler address 0x12D737470fB3ec6C3DeEC9b518100Bec9D520144
})();
```

</details>

#### Rust ([Alloy](https://github.com/alloy-rs))

<details>
<summary>Cargo.toml</summary>

```toml
[package]
name = "scratch"
version = "0.1.0"
edition = "2021"

[dependencies]
alloy = { git = "https://github.com/alloy-rs/alloy", rev = "e22d9be", features = [
    "contract",
    "network",
    "providers",
    "provider-http",
    "rpc-client",
    "rpc-types-eth",
    "rpc-types-trace",
] }
eyre = "0.6.12"
tokio = { version = "1.37.0", features = ["rt-multi-thread", "macros"] }
```

</details>

<details>
<summary>Click to see Rust example of getting Settler addresses</summary>

```Rust
use alloy::{
    network::TransactionBuilder,
    primitives::{address, Address, Bytes, U256},
    providers::{Provider, ProviderBuilder},
    rpc::types::eth::{BlockId, TransactionRequest},
    sol,
    sol_types::SolCall,
};
use eyre::Result;
use std::collections::HashMap;
use std::env;

const DEPLOYER_ADDRESS: Address = address!("00000000000004533Fe15556B1E086BB1A72cEae");

sol! {
    function prev(uint128 featureId) external view returns (address pastTokenOwner);
    function ownerOf(uint256 tokenId) external view returns (address tokenOwner);
    function next(uint128 featureId) external view returns (address futureTokenOwner);
}

#[tokio::main]
async fn main() -> Result<()> {
    let provider = ProviderBuilder::new().on_http(env::var("RPC_URL")?.parse()?);
    let block_id = BlockId::number(provider.get_block_number().await?);

    let token_ids = vec![2, 3];
    let token_descriptions = HashMap::from([(2, "taker submitted"), (3, "metatransaction")]);

    for token_id in token_ids.iter() {
        {
            let tx = TransactionRequest::default()
                .with_to(DEPLOYER_ADDRESS)
                .with_input(Bytes::from(
                    prevCall {
                        featureId: *token_id,
                    }
                    .abi_encode(),
                ));
            let past_owner =
                prevCall::abi_decode_returns(&provider.call(&tx).block(block_id).await?, false)?
                    .pastTokenOwner;
            println!(
                "previous {0:} settler address {1:}",
                token_descriptions[token_id], past_owner
            );
        }
        {
            let tx = TransactionRequest::default()
                .with_to(DEPLOYER_ADDRESS)
                .with_input(Bytes::from(
                    ownerOfCall {
                        tokenId: U256::from(*token_id),
                    }
                    .abi_encode(),
                ));
            let token_owner =
                ownerOfCall::abi_decode_returns(&provider.call(&tx).block(block_id).await?, false)?
                    .tokenOwner;
            println!(
                "current {0:} settler address {1:}",
                token_descriptions[token_id], token_owner
            );
        }
        {
            let tx = TransactionRequest::default()
                .with_to(DEPLOYER_ADDRESS)
                .with_input(Bytes::from(
                    nextCall {
                        featureId: *token_id,
                    }
                    .abi_encode(),
                ));
            let future_owner =
                nextCall::abi_decode_returns(&provider.call(&tx).block(block_id).await?, false)?
                    .futureTokenOwner;
            println!(
                "next {0:} settler address {1:}",
                token_descriptions[token_id], future_owner
            );
        }
    }

    // output:
    // previous taker submitted settler address 0x07E594aA718bB872B526e93EEd830a8d2a6A1071
    // current taker submitted settler address 0x2c4B05349418Ef279184F07590E61Af27Cf3a86B
    // next taker submitted settler address 0x70bf6634eE8Cb27D04478f184b9b8BB13E5f4710
    // previous metatransaction settler address 0x25b81CE58AB0C4877D25A96Ad644491CEAb81048
    // current metatransaction settler address 0xAE11b95c8Ebb5247548C279A00120B0ACadc7451
    // next metatransaction settler address 0x12D737470fB3ec6C3DeEC9b518100Bec9D520144

    Ok(())
}
```

</details>

#### Python ([web3.py](https://web3py.readthedocs.io/en/stable/))

<details>
<summary>Click to see Python example of getting Settler addresses</summary>

```Python
import os, web3

w3 = web3.Web3(web3.Web3.HTTPProvider(os.getenv("RPC_URL")))
deployer_address = "0x00000000000004533Fe15556B1E086BB1A72cEae"
token_descriptions = {
    2: "taker submitted",
    3: "metatransaction",
}

deployer_abi = [
    {
        "constant": True,
        "inputs": [{"name": "featureId", "type": "uint128"}],
        "name": "prev",
        "outputs": [{"name": "pastTokenOwner", "type": "address"}],
        "payable": False,
        "type": "function",
    },
    {
        "constant": True,
        "inputs": [{"name": "tokenId", "type": "uint256"}],
        "name": "ownerOf",
        "outputs": [{"name": "tokenOwner", "type": "address"}],
        "payable": False,
        "type": "function",
    },
    {
        "constant": True,
        "inputs": [{"name": "featureId", "type": "uint128"}],
        "name": "next",
        "outputs": [{"name": "futureTokenOwner", "type": "address"}],
        "payable": False,
        "type": "function",
    },
]
function_descriptions = {
    "prev": "previous",
    "ownerOf": "current",
    "next": "next",
}

deployer = w3.eth.contract(address=deployer_address, abi=deployer_abi)

for token_id, token_description in token_descriptions.items():
    for function_name, function_description in function_descriptions.items():
        settler_address = getattr(deployer.functions, function_name)(token_id).call()
        print(
            function_description,
            token_description,
            "settler address",
            settler_address,
        )

# output:
# previous taker submitted settler address 0x07E594aA718bB872B526e93EEd830a8d2a6A1071
# current taker submitted settler address 0x2c4B05349418Ef279184F07590E61Af27Cf3a86B
# next taker submitted settler address 0x70bf6634eE8Cb27D04478f184b9b8BB13E5f4710
# previous metatransaction settler address 0x25b81CE58AB0C4877D25A96Ad644491CEAb81048
# current metatransaction settler address 0xAE11b95c8Ebb5247548C279A00120B0ACadc7451
# next metatransaction settler address 0x12D737470fB3ec6C3DeEC9b518100Bec9D520144
```

</details>

#### Bash ([Foundry `cast`](https://book.getfoundry.sh/cast/))

<details>
<summary>Click to see Bash (cast) example of getting Settler addresses</summary>

```Bash
#!/bin/bash

set -Eeufo pipefail -o posix

if ! hash cast &>/dev/null ; then
    echo 'foundry is not installed' >&2
    exit 1
fi

declare -r deployer='0x00000000000004533Fe15556B1E086BB1A72cEae'

declare -A token_descriptions
token_descriptions[2]='taker submitted'
token_descriptions[3]='metatransaction'
declare -r -A token_descriptions

declare -r -a function_signatures=('prev(uint128)(address)' 'ownerOf(uint256)(address)' 'next(uint128)(address)')
declare -A function_descriptions
function_descriptions["${function_signatures[0]%%(*}"]='previous'
function_descriptions["${function_signatures[1]%%(*}"]='current'
function_descriptions["${function_signatures[2]%%(*}"]='next'
declare -r -A function_descriptions

declare -i token_id
for token_id in "${!token_descriptions[@]}" ; do
    declare function_signature
    for function_signature in "${function_signatures[@]}" ; do
        declare addr
        addr="$(cast call --rpc-url "$RPC_URL" "$deployer" "$function_signature" "$token_id")"
        function_signature="${function_signature%%(*}"
        echo "${function_descriptions["$function_signature"]}"' '"${token_descriptions[$token_id]}"' settler address '"$addr" >&2
    done
done

# output:
# previous metatransaction settler address 0x25b81CE58AB0C4877D25A96Ad644491CEAb81048
# current metatransaction settler address 0xAE11b95c8Ebb5247548C279A00120B0ACadc7451
# next metatransaction settler address 0x12D737470fB3ec6C3DeEC9b518100Bec9D520144
# previous taker submitted settler address 0x07E594aA718bB872B526e93EEd830a8d2a6A1071
# current taker submitted settler address 0x2c4B05349418Ef279184F07590E61Af27Cf3a86B
# next taker submitted settler address 0x70bf6634eE8Cb27D04478f184b9b8BB13E5f4710
```

</details>

### Checking out the commit of a Settler

Settler emits the following event when it is deployed:

```Solidity
event GitCommit(bytes20 indexed);
```

By retrieving the argument of this event, you get the git commit from which the
Settler was built. For convenience, the script [`./sh/checkout_settler_commit.sh
<CHAIN_NAME>`](sh/checkout_settler_commit.sh) will pull the latest Settler
address, read the deployment event, and checkout the git commit.

## Bug Bounty Program

0x hosts a bug bounty on Immunefi at the address
https://immunefi.com/bug-bounty/0x .

If you have found a vulnerability in our project, it must be submitted through
Immunefi's platform. Immunefi will handle bug bounty communications.

See the bounty page at Immunefi for more details on accepted vulnerabilities,
payout amounts, and rules of participation.

Users who violate the rules of participation will not receive bug bounty payouts
and may be temporarily suspended or banned from the bug bounty program.

## Custody

Custody, not like the delicious custardy, is when the token(s) being traded are
temporarily owned by the Settler contract. This sometimes implies an additional,
non-optimal transfer. There are multiple reasons that Settler takes custody of
the token, here are a few:

- In the middle of a Multihop trade (except AMMs like UniswapV2 and VelodromeV2)
- To split tokens among multiple liquidity sources (Multiplex)
- To distribute positive slippage from an AMM
- To pay fees to a fee recipient in the buy token from an AMM
- Trading against an inefficient AMM that only supports `transferFrom(msg.sender)` (e.g Curve)

For the above reasons, there are settlement paths in Settler which allow for
custody of the sell token or the buy token. You will see the usage of `custody`
to represent this. Sell token or Buy token or both custody is represented by
`custody`.

## Gas usage

Gas cost snapshots are stored under `./forge-snapshots`. The scope is minimized
by using [forge-gas-snapshot](https://github.com/marktoda/forge-gas-snapshot).

There is an initial cost for Permit2 when the token has not been previously
used. This adds some non-negligble cost as the storage is changed from a 0 for
the first time. For this reason we compare warm (where the nonce is non-0) and
cold.

Note: The following is more akin to `gasLimit` than it is `gasUsed`, this is due
to the difficulty in calculating pinpoint costs (and rebates) in Foundry
tests. Real world usage will be slightly lower, but it serves as a useful
comparison.

[//]: # "BEGIN TABLES"

| VIP                 | DEX        | Pair      | Gas    | %      |
| ------------------- | ---------- | --------- | ------ | ------ |
| 0x V4 VIP           | Uniswap V3 | USDC/WETH | 124669 | 0.00%  |
| 0x V4 Multiplex     | Uniswap V3 | USDC/WETH | 138525 | 11.11% |
| Settler VIP (warm)  | Uniswap V3 | USDC/WETH | 136342 | 9.36%  |
| AllowanceHolder VIP | Uniswap V3 | USDC/WETH | 125828 | 0.93%  |
| UniswapRouter V3    | Uniswap V3 | USDC/WETH | 120978 | -2.96% |
|                     |            |           |        |        |
| 0x V4 VIP           | Uniswap V3 | DAI/WETH  | 112103 | 0.00%  |
| 0x V4 Multiplex     | Uniswap V3 | DAI/WETH  | 125959 | 12.36% |
| Settler VIP (warm)  | Uniswap V3 | DAI/WETH  | 123770 | 10.41% |
| AllowanceHolder VIP | Uniswap V3 | DAI/WETH  | 113256 | 1.03%  |
| UniswapRouter V3    | Uniswap V3 | DAI/WETH  | 108412 | -3.29% |
|                     |            |           |        |        |
| 0x V4 VIP           | Uniswap V3 | USDT/WETH | 114910 | 0.00%  |
| 0x V4 Multiplex     | Uniswap V3 | USDT/WETH | 128766 | 12.06% |
| Settler VIP (warm)  | Uniswap V3 | USDT/WETH | 126586 | 10.16% |
| AllowanceHolder VIP | Uniswap V3 | USDT/WETH | 116072 | 1.01%  |
| UniswapRouter V3    | Uniswap V3 | USDT/WETH | 111091 | -3.32% |
|                     |            |           |        |        |

| Custody              | DEX        | Pair      | Gas    | %       |
| -------------------- | ---------- | --------- | ------ | ------- |
| 0x V4 TransformERC20 | Uniswap V3 | USDC/WETH | 244603 | 0.00%   |
| Settler              | Uniswap V3 | USDC/WETH | 167096 | -31.69% |
| AllowanceHolder      | Uniswap V3 | USDC/WETH | 156732 | -35.92% |
|                      |            |           |        |         |
| 0x V4 TransformERC20 | Uniswap V3 | DAI/WETH  | 221601 | 0.00%   |
| Settler              | Uniswap V3 | DAI/WETH  | 150468 | -32.10% |
| AllowanceHolder      | Uniswap V3 | DAI/WETH  | 140104 | -36.78% |
|                      |            |           |        |         |
| 0x V4 TransformERC20 | Uniswap V3 | USDT/WETH | 228500 | 0.00%   |
| Settler              | Uniswap V3 | USDT/WETH | 157141 | -31.23% |
| AllowanceHolder      | Uniswap V3 | USDT/WETH | 146777 | -35.76% |
|                      |            |           |        |         |

| MetaTransactions | DEX        | Pair      | Gas    | %       |
| ---------------- | ---------- | --------- | ------ | ------- |
| 0x V4 Multiplex  | Uniswap V3 | USDC/WETH | 208118 | 0.00%   |
| Settler          | Uniswap V3 | USDC/WETH | 170424 | -18.11% |
|                  |            |           |        |         |
| 0x V4 Multiplex  | Uniswap V3 | DAI/WETH  | 195552 | 0.00%   |
| Settler          | Uniswap V3 | DAI/WETH  | 153802 | -21.35% |
|                  |            |           |        |         |
| 0x V4 Multiplex  | Uniswap V3 | USDT/WETH | 198359 | 0.00%   |
| Settler          | Uniswap V3 | USDT/WETH | 160475 | -19.10% |
|                  |            |           |        |         |

| RFQ             | DEX     | Pair      | Gas    | %       |
| --------------- | ------- | --------- | ------ | ------- |
| 0x V4           | 0x V4   | USDC/WETH | 97930  | 0.00%   |
| Settler         | Settler | USDC/WETH | 114364 | 16.78%  |
| Settler         | 0x V4   | USDC/WETH | 206574 | 110.94% |
| AllowanceHolder | Settler | USDC/WETH | 106499 | 8.75%   |
|                 |         |           |        |         |
| 0x V4           | 0x V4   | DAI/WETH  | 78456  | 0.00%   |
| Settler         | Settler | DAI/WETH  | 94884  | 20.94%  |
| Settler         | 0x V4   | DAI/WETH  | 176658 | 125.17% |
| AllowanceHolder | Settler | DAI/WETH  | 87025  | 10.92%  |
|                 |         |           |        |         |
| 0x V4           | 0x V4   | USDT/WETH | 89568  | 0.00%   |
| Settler         | Settler | USDT/WETH | 105996 | 18.34%  |
| Settler         | 0x V4   | USDT/WETH | 191990 | 114.35% |
| AllowanceHolder | Settler | USDT/WETH | 98137  | 9.57%   |
|                 |         |           |        |         |

| Curve             | DEX                   | Pair      | Gas    | %       |
| ----------------- | --------------------- | --------- | ------ | ------- |
| Settler           | CurveV2 Tricrypto VIP | USDC/WETH | 231412 | NaN%    |
|                   |                       |           |        |         |
|                   |                       |           |        |         |
| 0x V4             | Curve                 | USDT/WETH | 452672 | 0.00%   |
| Settler           | Curve                 | USDT/WETH | 422762 | -6.61%  |
| Settler           | CurveV2 Tricrypto VIP | USDT/WETH | 243773 | -46.15% |
| Curve             | Curve                 | USDT/WETH | 341761 | -24.50% |
| Curve Swap Router | Curve                 | USDT/WETH | 412038 | -8.98%  |
|                   |                       |           |        |         |

| DODO V1 | DEX     | Pair      | Gas    | %     |
| ------- | ------- | --------- | ------ | ----- |
| Settler | DODO V1 | USDC/WETH | 308607 | 0.00% |
|         |         |           |        |       |
|         |         |           |        |       |
|         |         |           |        |       |

| Buy token fee     | DEX        | Pair      | Gas    | %     |
| ----------------- | ---------- | --------- | ------ | ----- |
| Settler - custody | Uniswap V3 | USDC/WETH | 174265 | 0.00% |
|                   |            |           |        |       |
| Settler - custody | Uniswap V3 | DAI/WETH  | 161693 | 0.00% |
|                   |            |           |        |       |
| Settler - custody | Uniswap V3 | USDT/WETH | 164509 | 0.00% |
|                   |            |           |        |       |

| Sell token fee | DEX        | Pair      | Gas    | %       |
| -------------- | ---------- | --------- | ------ | ------- |
| Settler        | Uniswap V3 | USDC/WETH | 182790 | 0.00%   |
|                |            |           |        |         |
| Settler        | Uniswap V3 | DAI/WETH  | 162106 | 0.00%   |
|                |            |           |        |         |
| Settler        | Uniswap V3 | USDT/WETH | 170555 | 0.00%   |
| Settler        | Curve      | USDT/WETH | 434107 | 154.53% |
|                |            |           |        |         |

| AllowanceHolder                      | DEX            | Pair      | Gas    | %       |
| ------------------------------------ | -------------- | --------- | ------ | ------- |
| execute                              | Uniswap V3 VIP | USDC/WETH | 125828 | 0.00%   |
| Settler - external move then execute | Uniswap V3     | USDC/WETH | 140612 | 11.75%  |
| execute                              | RFQ            | USDC/WETH | 106499 | -15.36% |
|                                      |                |           |        |         |
| execute                              | Uniswap V3 VIP | DAI/WETH  | 113256 | 0.00%   |
| Settler - external move then execute | Uniswap V3     | DAI/WETH  | 129615 | 14.44%  |
| execute                              | RFQ            | DAI/WETH  | 87025  | -23.16% |
|                                      |                |           |        |         |
| execute                              | Uniswap V3 VIP | USDT/WETH | 116072 | 0.00%   |
| Settler - external move then execute | Uniswap V3     | USDT/WETH | 136603 | 17.69%  |
| execute                              | RFQ            | USDT/WETH | 98137  | -15.45% |
|                                      |                |           |        |         |

| AllowanceHolder sell token fees | DEX | Pair      | Gas    | %      |
| ------------------------------- | --- | --------- | ------ | ------ |
| no fee                          | RFQ | USDC/WETH | 106499 | 0.00%  |
| proportional fee                | RFQ | USDC/WETH | 154471 | 45.04% |
| fixed fee                       | RFQ | USDC/WETH | 122769 | 15.28% |
|                                 |     |           |        |        |
| no fee                          | RFQ | DAI/WETH  | 87025  | 0.00%  |
| proportional fee                | RFQ | DAI/WETH  | 126885 | 45.80% |
| fixed fee                       | RFQ | DAI/WETH  | 99121  | 13.90% |
|                                 |     |           |        |        |
| no fee                          | RFQ | USDT/WETH | 98137  | 0.00%  |
| proportional fee                | RFQ | USDT/WETH | 143629 | 46.36% |
| fixed fee                       | RFQ | USDT/WETH | 111345 | 13.46% |
|                                 |     |           |        |        |

[//]: # "END TABLES"

### Settler vs X

#### Settler vs 0xV4

The Settler contracts must perform additional work over 0xV4, namely, invalidate
the state of the `Permit2` signed message, this is essentially an additional
`SSTORE` that must always be performed. `Permit2` also does an `ecrecover` and
(in the metatransaction case) a cold `EXTCODESIZE`. On the other side, Settler
does not need to perform the same Feature implementation lookup that 0xV4
requires as a proxy. Settler's implicit reentrancy guard uses transient
storage.

With the Curve VIP, 0xV4 has to use a LiquidityProviderSandbox as calling
untrusted/arbitrary code is a risk in the protocol. Settler can be more lax with
the calls that it makes to other contracts because it does not hold TVL or
allowances. Settler does not have an equivalent of the liquidity sandbox, making
calls directly to Curve-like contracts.

#### Settler vs Curve

The Curve pool does not allow for a `recipient` to be specified, nor does it
allow for tokens to be `transfer`'d directly into the pool prior to calling the
pool contract. Due to these limitations there is overhead from the `transfer`
out of the Settler contract to the user.  This same limitation applies to the
Curve Swap Router.

## Actions

See
[ISettlerActions](https://github.com/0xProject/0x-settler/blob/master/src/ISettlerActions.sol)
for a list of actions and their parameters. The list of actions, their names,
the type and number of arguments, and the availability by chain is _**NOT
STABLE**_. Do not rely on ABI encoding/decoding of actions directly.

### UniswapV3

This settlement path is optimized by performing the Permit2 in the
`uniswapV3SwapCallback` function performing a `permit2TransferFrom` and avoiding
an additional `transfer`. This is further benefitted from tokens being sent to a
pool with an already initialized balance, rathan than to Settler as a temporary
intermediary.

The action `UNISWAPV3_VIP` exposes this behaviour and it should not be used with
any other action that interacts directly with Permit2 (e.g
`TRANSFER_FROM`). This is a recommendation; under extraordinary circumstances it
is only possible to achieve the required behavior with multiple Permit2
interactions. Except in the case of metatransaction Settlers, it is possible to
do multiple Permit2 interactions in the same Settler call.

# Risk

Since Settler has no outstanding allowances, and no usage of `transferFrom` or
arbitrary calls, overall risk of user funds loss is greatly reduced.

Permit2 allowances (with short dated expiration) still has some risk. Namely,
`Alice` permit2 being intercepted and a malicious transaction from `Mallory`,
which spends `Alice`'s funds, transferring it to `Mallory`.

To protect funds we must validate the actions being performed originate from the
Permit2 signer. This is simple in the case where `msg.sender` is the signer of
the Permit2 message. To support metatransactions we utilise the `witness`
functionality of Permit2 to ensure the actions are intentional from `Alice` as
`msg.sender` is a different address.

## Gas Comparisons

Day by day it gets harder to get a fair real world gas comparison. With rebates
and token balances initialized or not, and the difficulty of setting up the
world, touching storage, then performing the test.

To make gas comparisons fair we will use the following methodology:

- Market Makers have balances of both tokens. Since AMM Pools have non-zero
  balances of both tokens this is a fair comparison.
- The Taker does not have a balance of the token being bought.
- Fee Recipient has a non-zero balance of the fee tokens.
- Nonces for Permit2 and Rfq orders (0x V4) are initialized.
- `setUp` is used as much as possible with limited setup performed in the
  test. Warmup trades are avoided completely as to not warm up storage access.

# Technical Reference

## Permit2 Based Flows

We utilise `Permit2` transfers with an `SignatureTransfer`. Allowing users to
sign a coupon allowing our contracts to move their tokens. Permit2 uses
`PermitTransferFrom` struct for transfers.

`Permit2` provides the following guarantees:

- Funds can only be transferred from the user who signed the Permit2 coupon
- Funds can only be transferred by the `spender` specified in the Permit2 coupon
- Settler may only transfer an amount up to the amount specified in the Permit2 coupon
- Settler may only transfer a token specified in the Permit2 coupon
- Coupons expire after a certain time specified as `deadline`
- Coupons can only be used once

```Solidity
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
```

With this it is simple to transfer the user assets to a specific destination, as
well as take fixed fees. The biggest restriction is that we must consume this
permit entirely once. We cannot perform the permit transfer at different times
consuming different amounts.

The user signs a Permit2 coupon, giving Settler the ability to spend a specific
amount of their funds for a time duration. The EIP712 type the user signs is as
follows:

```
PermitTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline)
TokenPermissions(address token,uint256 amount)
```

This signed coupon is then provided in the calldata to the `Settler.execute`
function.

Due to this design, the user is prompted for an action two times when performing
a trade. Once to sign the Permit2 coupon, and once to call the `Settler.execute`
function. This is a tradeoff we are willing to make to avoid passive allowances.

In a metatransaction flow, the user is prompted only once.

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

The above example shows the simplest form of settlement in Settler. We abuse
some of the sequence diagram notation to get the point across. Token transfers
are represented by dashes (-->). Normal contract calls are represented by solid
lines. Highlighted in purple is the Permit2 interaction.

For the sake of brevity, following diagrams will have a simplified
representation to showcase the internal flow. This is what we are actually
interested in describing. The initial user interaction (e.g their call to
Settler) and the final transfer is omitted unless it is relevant to highlight in
the flow. Function calls to the DEX may only be representative of the flow, not
the accurate function name.

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

## `BASIC` Flow

This is the most basic flow and a flow that a number of dexes
support. Essentially it is the "call function on DEX, DEX takes tokens from us,
DEX gives us tokens". It has inefficiencies as `transferFrom` is more gas
expensive than `transfer` and we are required to check/set allowances to the
DEX. Typically this DEX also does not support a `recipient` field, introducing
yet another needless `transfer` in simple swaps.

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

Settler has a number of specialised fill flows and will add more overtime as we
add support for more dexes.

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

In this flow we avoid extraneous transfers with two optimisations. Firstly, we
utilise the `recipient` field of UniswapV3, providing the User as the recipient
and avoiding an extra transfer. Secondly during the `uniswapV3Callback` we
execute the Permit2 transfer, paying the UniswapV3 pool instead of the Settler
contract, avoiding an extra transfer.

This allows us to achieve **no custody** during this flow and is an extremely
gas efficient way to fill a single UniswapV3 pool, or single chain of UniswapV3
pools.

Note this has the following limitations:

- Single UniswapV3 pool or single chain of pools (e.g ETH->DAI->USDC)
- Cannot support a split between pools (e.g ETH->USDC 5bps and ETH->USDC 1bps)
  as Permit2 transfer can only occur once. a 0xV4 equivalent would be
  `sellTokenForTokenToUniswapV3` as opposed to
  `MultiPlex[sellTokenForEthToUniswapV3,sellTokenForEthToUniswapV3]`.

## RFQ

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

For RFQ we utilize 2 Permit2 transfers, one for the `Market Maker->User` and
another for `User->Market Maker`. This allows us to achieve **no custody**
during this flow and is an extremely gas efficient way to fill RFQ orders. We
simply validate the RFQ order (e.g Taker/msg.sender).

Note the `permitWitnessTransferFrom`, we utilise the `witness` functionality of
Permit2 which allows arbitrary data to be attached to the Permit2 coupon. This
arbitrary data is the actual RFQ order itself, containing the taker/msg.sender
and maker/taker amount and token fields.

A Market maker signs a slightly different Permit2 coupon than a User which
contains additional fields. The EIP712 type the Market Maker signs is as
follows:

```
PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,Consideration consideration)
Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)
TokenPermissions(address token,uint256 amount)"
```

With values as follows

```json
{
    permitted: {
        token: makerToken,
        amount: makerAmount
    },
    spender: settlerAddress,
    nonce: unOrderedNonce,
    deadline: deadlineUnixTimestamp,
    consideration: {
        token: takerToken,
        amount: takerAmount,
        counterParty: taker,
        partialFillAllowed: partialFillAllowed
    }
}
```

We use the Permit2 guarantees of a Permit2 coupon to ensure the following:

- RFQ Order cannot be filled more than once
- RFQ Orders expire
- RFQ Orders are signed by the Market Maker

## Fees in Basic Flow

In the most Basic flow, Settler has **taken custody**, usually in both
assets. So a fee can be paid out be Settler.

### Sell token fee

```mermaid
sequenceDiagram
    autonumber
    rect rgba(133, 81, 231, 0.5)
        USDC-->>Settler: permitTransfer
    end
    opt sell token fee
        Settler-->>Fee Recipient: transfer
    end
    Settler->>DEX: swap
    USDC-->>DEX: transfer
    WETH-->>Settler: transfer
    WETH-->>User: transfer
```

While it is possible to utilise Permit2 to pay out the Sell token fee using a
batch permit, we do not use that feature in Settler due to the substantial gas
overhead in the single-transfer case.


<details>
<summary>potential batch flow CURRENTLY UNUSED</summary>

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

</details>

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

<details>

<summary>potential batch flow CURRENTLY UNUSED</summary>

## Fees via Permit2

It is possible to collect fees via Permit2, which is typically in the token that
the Permit2 is offloading (e.g the sell token for that counterparty). To perform
this we use the Permit2 batch functionality where the second item in the batch
is the fee.

### RFQ fees via Permit2

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

Using the Batch functionality we can do one or more transfers from either the
User or the Market Maker. Allowing us to take either a buy token fee or a sell
token fee, or both, during RFQ order settlement.

This allows us to achieve **no custody** during this flow and is an extremely
gas efficient way to fill RFQ orders with fees.

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

It is possible to collect sell token fees via Permit2 with the UniswapV3 VIP as
well, using the Permit2 batch functionality. This flow is similar to the RFQ
fees.

This allows us to achieve **no custody** during this flow and is an extremely
gas efficient way to fill UniswapV3 with sell token fees.

</details>

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

Since UniswapV3 only supports a single `recipient`, to collect buy token fees,
Settler must **take custody** of the buy token. These additional transfers makes
settlement with UniswapV3 and buy token fees slightly more expensive than with
sell token fees.

## MetaTransactions

Similar to RFQ orders, MetaTransactions use the Permit2 with witness. In this
case the witness is the MetaTransaction itself, containing the actions the user
wants to execute. This gives MetaTransactions access to the same flows above,
with a different entrypoint contract and function signature. In this case, the
signature is a separate argument from the actions so that the actions can be
signed-over by the metatransaction taker.

The EIP712 type the user signs when wanting to perform a metatransaction is:

```
PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,SlippageAndActions slippageAndActions)
SlippageAndActions(address recipient,address buyToken,uint256 minAmountOut,bytes[] actions)
TokenPermissions(address token,uint256 amount)
```

Where `actions` is added and contains the encoded actions the to perform.

## AllowanceHolder

As an intermediary step, we provide the `AllowanceHolder` contract. This sits
infront of Settler and acts as transparently as possible. 0x Settler has a one
way trust relationship to `AllowanceHolder`. The true `msg.sender` is forwarded
from `AllowanceHolder` to 0x Settler in a similar way to
[ERC-2771](https://eips.ethereum.org/EIPS/eip-2771). `Permit2` is not used in
conjunction with `AllowanceHolder`

`exec`: An EOA or a smart contract wallet can utilise this function to perform a
swap via 0x Settler. Tokens are transferred efficiently and on-demand as the
swap executes. Unlike in Permit2 flows, it is possible to make multiple
optimized transfers of the same ephemeral allowance without reauthorizing.

Highlighted in orange is the standard token transfer operations. Note: these are
not the most effiecient swaps available, just enough to demonstrate the point.

`transferFrom` transfers the tokens on demand in the middle of the swap

```mermaid
sequenceDiagram
    autonumber
    User->>AllowanceHolder: exec
    AllowanceHolder->>Settler: execute
    Settler->>UniswapV3: swap
    WETH-->>Settler: transfer
    UniswapV3->>Settler: uniswapV3Callback
    Settler->>AllowanceHolder: transferFrom
    rect rgba(255, 148, 112, 0.5)
        USDC-->>UniswapV3: transferFrom(User, UniswapV3, amt)
    end
    WETH-->>User: transfer
```

# How to deploy

## How to pause the contracts

First, decide how much of everyone's day you're going to ruin. Is the bug
contained to a single `Settler` instance? Or is the bug pervasive? If the bug is
pervasive, you're going to completely ruin everybody's day. Skip steps 3 through
6 below.

You need to be an approved deployer. The "pause" operation is 1-of-n, not 2-of-n
like deploying a new `Settler`. `0x1CeC01DC0fFEE5eB5aF47DbEc1809F2A7c601C30`
(ice cold coffees) is the address of the pauser contract. It's at the same
address on all chains unless somebody screwed up the vanity addresses and didn't
update this document. On Linea, the address of the pauser contract is
`0xBE71A746C7AE0f9D18E6DB4f71d09732B0Ee5b9c` because the code deployed to the
usual address relies on `PUSH0`, which is not supported on that chain. When
Linea adopts the Shanghai hardfork (`PUSH0`), remove the preceeding sentence
from this document.

0. Go to that address on the relevant block explorer.

1. Click on the "Contract" tab.

![Click on "Contract"](img/pause0.png?raw=true)

2. Click on the "Write Contract" tab.

![Click on "Write Contract"](img/pause1.png?raw=true)

3. Click on "remove", the first one.

![Click on the first "remove"](img/pause2.png?raw=true)

4. Click on "Connect to Web3" and allow your wallet to connect. You must connect
   with the address that you use to deploy.

![Click on "Connect to Web3"](img/pause3.png?raw=true)

5. Paste the address of the buggy `Settler` instance.

![Paste the bad Settler address in the box](img/pause4.png?raw=true)

6. Click "Write" and confirm the transaction in your wallet. You have successfully ruined everybody's day :+1:

![Click on "Write"](img/pause5.png?raw=true)

7. This is the step to take if you want to completely shut down the
   protocol. You really hate that everybody is having a nice day. Instead of
   clicking on "remove"; click on "removeAll".

8. Click on "Connect to Web3" and allow your wallet to connect. You must connect
   with the address that you use to deploy.

![Click on "Connect to Web3"](img/pause6.png?raw=true)

9. Enter the "feature" number in the text box. This is probably 2 for
   taker-submitted for 3 for gasless/metatransaction, unless something major has
   changed and nobody bothered to update this document.

![Enter the "feature" number (2 or 3) in the text box](img/pause7.png?raw=true)

10. Click "Write" and confirm the transaction in your wallet. You have _really_ ruined everybody's day :+1:

![Click on "Write"](img/pause8.png?raw=true)

## How to deploy a new `Settler` to a chain that is already set up

Populate `api_secrets.json` by copying
[`api_secrets.json.template`](api_secrets.json.template) and adding your own
block explorer API key and RPC.

You need 2 signers to do this. Each signer needs to run
[`./sh/confirm_new_settler.sh
<CHAIN_NAME>`](sh/confirm_new_settler.sh). Following the prompts, this will sign
the Safe transaction required to submit the deployment. Once two signers have
run this script, the transaction will appear in the [Safe
dApp](https://app.safe.global/) as a pending transaction. Anybody can pay the
gas to execute this, but probably whoever holds `deployer.zeroexprotocol.eth`
will do it (presently Duncan).

On some chains, the [Safe Transaction
Service](https://docs.safe.global/core-api/transaction-service-overview) doesn't
exist. On these chains, instead of uploading the signature to be viewed in the
Safe dApp, `confirm_new_settler.sh` will save a `*.txt` file containing a hex
encoded 65-byte signature. This file needs to be sent verbatim (with filename
intact) to whomever will be doing transaction submission (again,
`deployer.zeroexprotocol.eth` -- presently Duncan). Then the person doing
transaction submission places _both_ `*.txt` files in the root of this
repository and runs [`./sh/deploy_new_settler.sh
<CHAIN_NAME>`](sh/deploy_new_settler.sh). This interacts with the Safe contracts
directly without going through the Safe dApp. The downside of this approach is
the lack of the extremely helpful [Tenderly](https://dashboard.tenderly.co/)
integration that helps review the transaction before submission. Of course, it's
possible to do similar simulations with Foundry, but the UX is much worse.

Now that the contract is deployed on-chain you need to run
[`./sh/verify_settler.sh <CHAIN_NAME>`](sh/verify_settler.sh). This will
(attempt to) verify Settler on both the Etherscan for the chain and
[Sourcify](https://sourcify.dev/). If this fails, it's probably because
[Foundry's source verification is
flaky](https://github.com/foundry-rs/foundry/issues/8470). Try deploying the
contracts in the normal way (without going through the 2 signer ceremony above)
to a testnet and verifying them there to make sure this doesn't
happen.

## How to deploy to a new chain

Zeroth, verify the configuration for your chain in
[`chain_config.json`](chain_config.json) and
[`script/SafeConfig.sol`](script/SafeConfig.sol).

First, you need somebody to give you a copy of `secrets.json`. If you don't have
this, give up. Also populate `api_secrets.json` by copying
[`api_secrets.json.template`](api_secrets.json.template) and adding your own
block explorer API key and RPC.

Second, test for common opcode support:

<details>
<summary>Click for instructions on how to run opcode tests</summary>

```bash
export FOUNDRY_EVM_VERSION=london
declare -r deployer_eoa='YOUR EOA ADDRESS HERE'
declare -r rpc_url='YOUR RPC URL HERE' # http://localhost:1248 if using frame.sh
declare -r -i chainid='CHAIN ID TO TEST HERE'
forge clean
forge build src/ChainCompatibility.sol
declare txid
# you might need to add the `--gas-price` and/or `--gas-limit` flags here; some chains are weird about that
txid="$(cast send --json --rpc-url "$rpc_url" --chain $chainid --from $deployer_eoa --create "$(forge inspect src/ChainCompatibility.sol:ChainCompatibility bytecode)" | jq -rM .transactionHash)"
declare -r txid
cast receipt --json --rpc-url "$rpc_url" --chain $chainid $txid | jq -r '.logs[] | { stage: .data[2:66], success: .data[66:130], gas: .data[130:] }'
```

The `stage` fields should be in order (0 through 3). Stage 0 is
`SELFDESTRUCT`. Stage 1 is `PUSH0`. Stage 2 is `TSTORE`/`TLOAD`. Stage 3 is
`MCOPY`. If any entry has `success` of zero, that is strong evidence that the
corresponding opcode is not supported. If `success` is zero, the corresponding
`gas` value should be approximately 100000 (`0x186a0`). Another value in the
`gas` field suggests that something bizarre is going on, meriting manual
investigation. You can also use the `gas` field to see if the opcodes have the
expected gas cost. In particular, you should verify that the gas cost for
`SELFDESTRUCT` is approximately 5000 (`0x1388`). If `success` for `SELFDESTRUCT`
is 1, but `gas` is over 51220 (`0xc814`), you will need to make changes to
`Create3.sol`.

If `PUSH0` is not supported, then `isShanghai` should be `false` in
`chain_config.json`. If any of `TSTORE`/`TLOAD`/`MCOPY` are not supported, then
`isCancun` should be `false` in `chain_config.json`.

You may be tempted to use a blockchain explorer (e.g. Etherscan or Tenderly) to
examine the trace of the resulting transaction or to read the logs. You may also
be tempted to do an `eth_call`, local fork, devnet, or some other form of
advanced simulation. _**DO NOT DO THIS**_. These tools cannot be trusted; they
**will** lie to you. You must submit this transaction on-chain, wait for it to
be confirmed, and then retrieve the receipt (like the above snippet). The
blockchain cannot lie about the logs emitted by a transaction that become part
of its receipt.

</details>

Third, you need have enough native asset in each of the deployer addresses
listed in [`secrets.json.template`](secrets.json.template) to perform the
deployment. If how much isn't obvious to you, you can run the main deployment
script with `BROADCAST=no` to simulate. This can be a little wonky on L2s, so
beware and overprovision the amount of native asset.

Fourth, deploy `AllowanceHolder`. Obviously, if you're deploying to a
Cancun-supporting chain, you don't need to fund the deployer for the old
`AllowanceHolder` (and vice versa). Run [`./sh/deploy_allowanceholder.sh
<CHAIN_NAME>`](sh/deploy_allowanceholder.sh). Note that
`deploy_allowanceholder.sh` doesn't give you a chance to back out. There is no
prompt, it just deploys `AllowanceHolder`.

Fifth, check that the Safe deployment on the new chain is complete. You can
check this by running the main deployment script with `BROADCAST=no`. If it
completes without reverting, you don't need to do anything. If the Safe
deployment on the new chain is incomplete, run [`./sh/deploy_safe_infra.sh
<CHAIN_NAME>`](sh/deploy_safe_infra.sh). You will have to modify this script.

Sixth, make _damn_ sure that you've got the correct configuration in
[`chain_config.json`](chain_config.json). If you screw this up, you'll burn the
vanity address. Run [`BROADCAST=no ./sh/deploy_new_chain.sh
<CHAIN_NAME>`](sh/deploy_new_chain.sh) a bunch of times. Deploy to a
testnet. Simulate each individual transaction in
[Tenderly](https://dashboard.tenderly.co/).

Finally, run `BROADCAST=yes ./sh/deploy_new_chain.sh <CHAIN_NAME>`. Cross your
fingers. If something goes wrong (most commonly, the last transaction runs out
of gas; this is only a minor problem), you'll need to edit either
`sh/deploy_new_chain.sh` or
[`script/DeploySafes.s.sol`](script/DeploySafes.s.sol) to skip the parts of the
deployment you've already done. Tweak `gasMultiplierPercent` and
`minGasPriceGwei` in `chain_config.json`.

Congratulations, `Settler` is deployed on a new chain! :tada:
