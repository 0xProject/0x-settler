// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Script} from "forge-std/Script.sol";
import {Vm} from "forge-std/Vm.sol";
import {console} from "forge-std/console.sol";

import {Settler} from "src/Settler.sol";
import {IDeployer, IERC721View, Feature, Nonce} from "src/deployer/IDeployer.sol";

contract Deploy is Script {
    IDeployer internal constant deployer = IDeployer(0x00000000000004533Fe15556B1E086BB1A72cEae);

    function run(Feature feature, bytes calldata constructorArgs) public {
        require(address(deployer).code.length > 0, "No deployer");
        (address authorized, uint40 deadline) = deployer.authorized(feature);
        require(authorized != address(0), "Nobody is authorized");
        require(block.timestamp + 1 days > deadline, "Deadline too soon");

        address predicted = deployer.next(feature);
        console.log("Deploying to", predicted);

        vm.recordLogs();
        vm.startBroadcast(authorized);

        (address deployed, Nonce nonce) =
            deployer.deploy(feature, bytes.concat(type(Settler).creationCode, constructorArgs));

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
                if (log.topics[0] == IDeployer.Deployed.selector) {
                    assert(abi.decode(bytes.concat(log.topics[1]), (Feature)) == feature);
                    assert(abi.decode(bytes.concat(log.topics[2]), (Nonce)) == nonce);
                    assert(abi.decode(bytes.concat(log.topics[3]), (address)) == predicted);
                } else if (log.topics[0] == IERC721View.Transfer.selector) {
                    console.log("Old deployment", abi.decode(bytes.concat(log.topics[1]), (address)));
                    assert(abi.decode(bytes.concat(log.topics[2]), (address)) == predicted);
                    assert(abi.decode(bytes.concat(log.topics[3]), (Feature)) == feature);
                } else {
                    revert("Unknown event");
                }
            }
        }
    }
}
