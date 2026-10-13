// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Script} from "@forge-std/Script.sol";

contract SignDeployment is Script {
    function run(address signer, bytes32 digest) external view returns (uint8 yParity, bytes32 r, bytes32 s) {
        uint256 privateKey = vm.envUint("DEPLOYMENT_PRIVATE_KEY");
        require(vm.addr(privateKey) == signer, "Private key does not match deployer");
        (yParity, r, s) = vm.sign(privateKey, digest);
        yParity -= 27;
    }
}
