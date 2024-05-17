// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Script} from "forge-std/Script.sol";
import {Settler} from "src/Settler.sol";
import {IDeployer, Feature} from "src/deployer/IDeployer.sol";

interface ISafeExecute {
    enum Operation {
        Call,
        DelegateCall
    }

    function execTransaction(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        uint256 safeTxGas,
        uint256 baseGas,
        uint256 gasPrice,
        address gasToken,
        address refundReceiver,
        bytes calldata signatures
    ) external payable returns (bool);
}

contract DeploySettlerSingle is Script {
    function run(address deployerProxy, ISafeExecute deploymentSafe, Feature feature, bytes calldata constructorArgs)
        external
    {
        uint256 moduleDeployerKey = vm.envUint("ICECOLDCOFFEE_DEPLOYER_KEY");
        address moduleDeployer = vm.addr(moduleDeployerKey);

        bytes memory deploymentSignature = abi.encodePacked(uint256(uint160(moduleDeployer)), bytes32(0), uint8(1));
        bytes memory deployCall =
            abi.encodeCall(IDeployer.deploy, (feature, bytes.concat(type(Settler).creationCode, constructorArgs)));

        vm.startBroadcast(moduleDeployerKey);

        deploymentSafe.execTransaction(
            deployerProxy,
            0,
            deployCall,
            ISafeExecute.Operation.Call,
            0,
            0,
            0,
            address(0),
            address(0),
            deploymentSignature
        );

        vm.stopBroadcast();
    }
}
