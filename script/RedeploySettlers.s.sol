// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SafeMultisend, ISafeExecute, ISafeOwners} from "./SafeMultisend.sol";
import {Deployer, Feature} from "src/deployer/Deployer.sol";
import {SafeConfig} from "./SafeConfig.sol";

contract RedeploySettlers is SafeMultisend {
    function _execDelegateCall(address safe, address multicall, bytes memory data, bytes memory signature)
        internal
        returns (bool)
    {
        return ISafeExecute(safe)
            .execTransaction(
                multicall, 0, data, ISafeExecute.Operation.DelegateCall, 0, 0, 0, address(0), address(0), signature
            );
    }

    function _deployCall(
        string calldata chainDisplayName,
        Feature feature,
        string memory flatSuffix,
        string memory contractSuffix,
        bytes calldata constructorArgs
    ) internal view returns (bytes memory) {
        return abi.encodeCall(
            Deployer.deploy,
            (
                feature,
                bytes.concat(
                    vm.getCode(string.concat(chainDisplayName, flatSuffix, ":", chainDisplayName, contractSuffix)),
                    constructorArgs
                )
            )
        );
    }

    function run(
        address moduleDeployer,
        address proxyDeployer,
        address iceColdCoffee,
        address deployerProxy,
        address deploymentSafe,
        address upgradeSafe,
        address safeMulticall,
        Feature takerSubmittedFeature,
        Feature metaTxFeature,
        Feature intentFeature,
        Feature bridgeFeature,
        string calldata chainDisplayName,
        bytes calldata constructorArgs,
        address[] calldata solvers
    ) public {
        require(safeMulticall.codehash == multicallHash, "Safe multicall codehash");

        require(Feature.unwrap(takerSubmittedFeature) == 2, "wrong taker-submitted feature (tokenId)");
        require(Feature.unwrap(metaTxFeature) == 3, "wrong metatransaction feature (tokenId)");
        require(Feature.unwrap(intentFeature) == 4, "wrong intents feature (tokenId)");
        require(Feature.unwrap(bridgeFeature) == 5, "wrong bridge feature (tokenId)");

        // Keys are optional so the script can be dry-run in simulation without decrypting secrets.
        uint256 moduleDeployerKey = vm.envOr("ICECOLDCOFFEE_DEPLOYER_KEY", uint256(0));
        uint256 proxyDeployerKey = vm.envOr("DEPLOYER_PROXY_DEPLOYER_KEY", uint256(0));
        if (moduleDeployerKey != 0) {
            require(vm.addr(moduleDeployerKey) == moduleDeployer, "module deployer key/address mismatch");
        }
        if (proxyDeployerKey != 0) {
            require(vm.addr(proxyDeployerKey) == proxyDeployer, "proxy deployer key/address mismatch");
        }

        require(deploymentSafe.code.length > 0, "deployment safe not deployed");
        require(upgradeSafe.code.length > 0, "upgrade safe not deployed");
        require(deployerProxy.code.length > 0, "deployer proxy not deployed");
        require(iceColdCoffee.code.length > 0, "iceColdCoffee module not deployed");
        require(
            ISafeOwners(deploymentSafe).isModuleEnabled(iceColdCoffee),
            "iceColdCoffee module not enabled on deployment safe"
        );
        {
            address[] memory currentOwners = ISafeOwners(deploymentSafe).getOwners();
            require(
                currentOwners.length == 1 && currentOwners[0] == moduleDeployer,
                "deployment safe is not sole-owned by moduleDeployer"
            );
            require(ISafeOwners(deploymentSafe).getThreshold() == 1, "deployment safe threshold != 1");
        }
        {
            address[] memory currentOwners = ISafeOwners(upgradeSafe).getOwners();
            require(
                currentOwners.length == 1 && currentOwners[0] == proxyDeployer,
                "upgrade safe is not sole-owned by proxyDeployer"
            );
            require(ISafeOwners(upgradeSafe).getThreshold() == 1, "upgrade safe threshold != 1");
        }
        require(Deployer(deployerProxy).owner() == upgradeSafe, "deployer proxy not owned by upgrade safe");
        require(Deployer(deployerProxy).pendingOwner() == address(0), "deployer proxy has pending owner transfer");

        // `authorize` reverts on uninitialized features; `setDescription` is intentionally not re-called.
        require(Deployer(deployerProxy).descriptionHash(takerSubmittedFeature) != 0, "taker feature not initialized");
        require(Deployer(deployerProxy).descriptionHash(metaTxFeature) != 0, "metatx feature not initialized");
        require(Deployer(deployerProxy).descriptionHash(intentFeature) != 0, "intent feature not initialized");
        require(Deployer(deployerProxy).descriptionHash(bridgeFeature) != 0, "bridge feature not initialized");

        address predictedTakerSubmittedSettler = Deployer(deployerProxy).next(takerSubmittedFeature);
        address predictedMetaTxSettler = Deployer(deployerProxy).next(metaTxFeature);
        address predictedIntentSettler = Deployer(deployerProxy).next(intentFeature);
        address predictedBridgeSettler = Deployer(deployerProxy).next(bridgeFeature);
        require(predictedTakerSubmittedSettler.code.length == 0, "predicted taker settler slot occupied");
        require(predictedMetaTxSettler.code.length == 0, "predicted metatx settler slot occupied");
        require(predictedIntentSettler.code.length == 0, "predicted intent settler slot occupied");
        require(predictedBridgeSettler.code.length == 0, "predicted bridge settler slot occupied");

        bytes memory takerSubmittedAuthorizeCall = abi.encodeCall(
            Deployer.authorize, (takerSubmittedFeature, deploymentSafe, uint40(block.timestamp + 365 days))
        );
        bytes memory metaTxAuthorizeCall =
            abi.encodeCall(Deployer.authorize, (metaTxFeature, deploymentSafe, uint40(block.timestamp + 365 days)));
        bytes memory intentAuthorizeCall =
            abi.encodeCall(Deployer.authorize, (intentFeature, deploymentSafe, uint40(block.timestamp + 365 days)));
        bytes memory bridgeAuthorizeCall =
            abi.encodeCall(Deployer.authorize, (bridgeFeature, deploymentSafe, uint40(block.timestamp + 365 days)));

        bytes memory takerSubmittedDeployCall =
            _deployCall(chainDisplayName, takerSubmittedFeature, "TakerSubmittedFlat.sol", "Settler", constructorArgs);
        bytes memory metaTxDeployCall =
            _deployCall(chainDisplayName, metaTxFeature, "MetaTxnFlat.sol", "SettlerMetaTxn", constructorArgs);
        bytes memory intentDeployCall =
            _deployCall(chainDisplayName, intentFeature, "IntentFlat.sol", "SettlerIntent", constructorArgs);
        bytes memory bridgeDeployCall =
            _deployCall(chainDisplayName, bridgeFeature, "BridgeSettlerFlat.sol", "BridgeSettler", constructorArgs);

        address[] memory upgradeOwners = SafeConfig.getUpgradeSafeSigners();
        bytes[] memory changeOwnersCalls =
            _encodeChangeOwners(upgradeSafe, SafeConfig.upgradeSafeThreshold, proxyDeployer, upgradeOwners);
        assert(changeOwnersCalls.length == upgradeOwners.length + 1);
        bytes[] memory upgradeSetupCalls = new bytes[](4 + changeOwnersCalls.length);
        upgradeSetupCalls[0] = _encodeMultisend(deployerProxy, takerSubmittedAuthorizeCall);
        upgradeSetupCalls[1] = _encodeMultisend(deployerProxy, metaTxAuthorizeCall);
        upgradeSetupCalls[2] = _encodeMultisend(deployerProxy, intentAuthorizeCall);
        upgradeSetupCalls[3] = _encodeMultisend(deployerProxy, bridgeAuthorizeCall);
        for (uint256 i; i < changeOwnersCalls.length; i++) {
            upgradeSetupCalls[i + 4] = changeOwnersCalls[i];
        }
        bytes memory upgradeSetupCall = _encodeMultisend(upgradeSetupCalls);

        address[] memory deployerOwners = SafeConfig.getDeploymentSafeSigners();
        changeOwnersCalls =
            _encodeChangeOwners(deploymentSafe, SafeConfig.deploymentSafeThreshold, moduleDeployer, deployerOwners);
        assert(changeOwnersCalls.length == deployerOwners.length + 1);

        bytes[] memory deploySetupCalls1 = new bytes[](2);
        deploySetupCalls1[0] = _encodeMultisend(deployerProxy, takerSubmittedDeployCall);
        deploySetupCalls1[1] = _encodeMultisend(deployerProxy, metaTxDeployCall);
        bytes memory deploySetupCall1 = _encodeMultisend(deploySetupCalls1);

        bytes[] memory deploySetupCalls2 = new bytes[](2);
        deploySetupCalls2[0] = _encodeMultisend(deployerProxy, intentDeployCall);
        deploySetupCalls2[1] = _encodeMultisend(deployerProxy, bridgeDeployCall);
        bytes memory deploySetupCall2 = _encodeMultisend(deploySetupCalls2);

        bytes memory deploySetupCall3 = _encodeMultisend(_encodeSolversMultisend(predictedIntentSettler, solvers));

        bytes memory deploySetupCall4 = _encodeMultisend(changeOwnersCalls);

        bytes memory deploymentSignature = abi.encodePacked(uint256(uint160(moduleDeployer)), bytes32(0), uint8(1));
        bytes memory upgradeSignature = abi.encodePacked(uint256(uint160(proxyDeployer)), bytes32(0), uint8(1));

        uint256[] memory gasSplits = new uint256[](7);

        if (proxyDeployerKey != 0) vm.startBroadcast(proxyDeployerKey);
        else vm.startBroadcast(proxyDeployer);

        // configure the deployer (authorize; set new owners)
        gasSplits[0] = gasleft();
        _execDelegateCall(upgradeSafe, safeMulticall, upgradeSetupCall, upgradeSignature);
        gasSplits[1] = gasleft();
        vm.stopBroadcast();

        if (moduleDeployerKey != 0) vm.startBroadcast(moduleDeployerKey);
        else vm.startBroadcast(moduleDeployer);

        // deploy settlers; register solvers; set new owners
        gasSplits[2] = gasleft();
        _execDelegateCall(deploymentSafe, safeMulticall, deploySetupCall1, deploymentSignature);

        gasSplits[3] = gasleft();
        _execDelegateCall(deploymentSafe, safeMulticall, deploySetupCall2, deploymentSignature);

        gasSplits[4] = gasleft();
        if (solvers.length > 0) {
            _execDelegateCall(deploymentSafe, safeMulticall, deploySetupCall3, deploymentSignature);
        }

        gasSplits[5] = gasleft();
        _execDelegateCall(deploymentSafe, safeMulticall, deploySetupCall4, deploymentSignature);

        gasSplits[6] = gasleft();
        vm.stopBroadcast();

        _assertEip7825(gasSplits);

        require(
            Deployer(deployerProxy).ownerOf(Feature.unwrap(takerSubmittedFeature)) == predictedTakerSubmittedSettler,
            "predicted taker submitted settler address mismatch"
        );
        require(
            Deployer(deployerProxy).ownerOf(Feature.unwrap(metaTxFeature)) == predictedMetaTxSettler,
            "predicted metatransaction settler address mismatch"
        );
        require(
            Deployer(deployerProxy).ownerOf(Feature.unwrap(intentFeature)) == predictedIntentSettler,
            "predicted intent settler address mismatch"
        );
        require(
            Deployer(deployerProxy).ownerOf(Feature.unwrap(bridgeFeature)) == predictedBridgeSettler,
            "predicted bridgesettler address mismatch"
        );
        require(
            keccak256(abi.encodePacked(ISafeOwners(deploymentSafe).getOwners()))
                == keccak256(abi.encodePacked(deployerOwners)),
            "deployment safe owners mismatch"
        );
        require(
            ISafeOwners(deploymentSafe).getThreshold() == SafeConfig.deploymentSafeThreshold,
            "deployment safe threshold mismatch"
        );
        require(
            keccak256(abi.encodePacked(ISafeOwners(upgradeSafe).getOwners()))
                == keccak256(abi.encodePacked(upgradeOwners)),
            "upgrade safe owners mismatch"
        );
        require(
            ISafeOwners(upgradeSafe).getThreshold() == SafeConfig.upgradeSafeThreshold,
            "upgrade safe threshold mismatch"
        );
        {
            (bool success, bytes memory returndata) =
                predictedIntentSettler.staticcall(abi.encodeWithSignature("getSolvers()"));
            if (!success) {
                assembly ("memory-safe") {
                    revert(add(0x20, returndata), mload(returndata))
                }
            }
            require(keccak256(returndata) == keccak256(abi.encode(solvers)), "solvers/`getSolvers()` mismatch");
        }
    }
}
