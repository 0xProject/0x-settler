// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import "forge-std/Script.sol";
import {Vm} from "forge-std/Vm.sol";

import {IERC721View, Deployer, Nonce} from "src/deployer/Deployer.sol";

contract Deploy is Script {
    Deployer internal constant deployer = Deployer(0x00000000000004533Fe15556B1E086BB1A72cEae);

    function run(uint128 feature, bytes calldata initCode) public {
        require(address(deployer).code.length > 0, "No deployer");
        (address authorized, uint96 deadline) = deployer.authorized(feature);
        require(authorized != address(0), "Nobody is authorized");
        require(block.timestamp + 1 days > deadline, "Deadline too soon");

        address predicted = deployer.next(feature);
        console.log("Deploying to", predicted);

        vm.recordLogs();
        vm.startBroadcast(authorized);

        (address deployed, Nonce nonce) = deployer.deploy(feature, initCode);

        vm.stopBroadcast();

        assert(predicted == deployed);

        console.log("Feature-specific deployment nonce", Nonce.unwrap(nonce));

        Vm.Log[] memory logs = vm.getRecordedLogs();
        require(logs.length >= 2, "Wrong logs");
        for (uint256 i; i < logs.length; i++) {
            Vm.Log memory log = logs[i];
            if (log.emitter == address(deployer)) {
                assert(log.topics.length == 4);
                assert(log.data.length == 0);
                if (log.topics[0] == Deployer.Deployed.selector) {
                    assert(abi.decode(bytes.concat(log.topics[1]), (uint128)) == feature);
                    assert(Nonce.unwrap(abi.decode(bytes.concat(log.topics[2]), (Nonce))) == Nonce.unwrap(nonce));
                    assert(abi.decode(bytes.concat(log.topics[3]), (address)) == predicted);
                } else if (log.topics[0] == IERC721View.Transfer.selector) {
                    console.log("Old deployment", abi.decode(bytes.concat(log.topics[1]), (address)));
                    assert(abi.decode(bytes.concat(log.topics[2]), (address)) == predicted);
                    assert(abi.decode(bytes.concat(log.topics[3]), (uint256)) == feature);
                } else {
                    revert("Unknown event");
                }
            }
        }
    }
}
