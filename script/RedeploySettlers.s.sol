// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SafeMultisend, ISafeExecute, ISafeFactory, ISafeOwners} from "./SafeMultisend.sol";
import {Deployer, Feature} from "src/deployer/Deployer.sol";
import {SafeConfig} from "./SafeConfig.sol";
import {SafeBytecodes} from "./SafeCode.sol";

interface ISafeMigration {
    function migrateL2WithFallbackHandler() external;
    function SAFE_L2_SINGLETON() external view returns (address);
    function SAFE_FALLBACK_HANDLER() external view returns (address);
}

contract RedeploySettlers is SafeMultisend {
    // Canonical Safe `SafeMigration` (v1.4.1) contract, deployed deterministically across non-EraVm chains.
    bytes32 internal constant safeMigrationCodehash =
        0xc00d7921460cd5a05393e7772e634bd7d212f356356aa3a77f0120a9b8e25e99;

    // Switch the upgrade Safe's singleton (and fallback handler) from Safe v1.3.0 to v1.4.1 by `DelegateCall`ing
    // the `SafeMigration` contract. The migration contract is pinned by codehash and cross-checked to target
    // exactly the configured v1.4.1 singleton/fallback handler, so a wrong/absent address can't mis-migrate.
    function _migrateUpgradeSafe(
        SafeCompatConfig memory safeCompatConfig,
        address upgradeSafe,
        address safeMigration,
        address safeSingletonV141,
        address safeFallbackV141,
        bytes memory upgradeSignature
    ) internal {
        require(safeMigration.codehash == safeMigrationCodehash, "unexpected SafeMigration codehash");
        require(
            ISafeMigration(safeMigration).SAFE_L2_SINGLETON() == safeSingletonV141, "SafeMigration singleton mismatch"
        );
        require(
            ISafeMigration(safeMigration).SAFE_FALLBACK_HANDLER() == safeFallbackV141, "SafeMigration fallback mismatch"
        );

        _execTransaction(
            safeCompatConfig,
            ISafeExecute(upgradeSafe),
            safeMigration,
            0,
            abi.encodeCall(ISafeMigration.migrateL2WithFallbackHandler, ()),
            ISafeExecute.Operation.DelegateCall,
            0,
            0,
            0,
            address(0),
            address(0),
            upgradeSignature
        );

        require(
            address(uint160(uint256(vm.load(upgradeSafe, 0)))) == safeSingletonV141,
            "upgrade safe not migrated to v1.4.1"
        );
        require(
            address(uint160(uint256(vm.load(upgradeSafe, fallbackSlot)))) == safeFallbackV141,
            "upgrade safe fallback not migrated to v1.4.1"
        );
    }

    function _execDelegateCall(
        SafeCompatConfig memory safeCompatConfig,
        address safe,
        address multicall,
        bytes memory data,
        bytes memory signature
    ) internal returns (bool) {
        return _execTransaction(
            safeCompatConfig,
            ISafeExecute(safe),
            multicall,
            0,
            data,
            ISafeExecute.Operation.DelegateCall,
            0,
            0,
            0,
            address(0),
            address(0),
            signature
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
        bool isEraVm,
        address moduleDeployer,
        address proxyDeployer,
        address iceColdCoffee,
        address deployerProxy,
        address deploymentSafe,
        address upgradeSafe,
        ISafeFactory safeFactory,
        address safeSingleton,
        address safeFallback,
        address safeMulticall,
        address safeSingletonV141,
        address safeFallbackV141,
        address safeMigration,
        bool migrateUpgradeSafe,
        Feature takerSubmittedFeature,
        Feature metaTxFeature,
        Feature intentFeature,
        Feature bridgeFeature,
        string calldata chainDisplayName,
        bytes calldata constructorArgs,
        address[] calldata solvers
    ) public {
        // EraVm: Settler/Deployer are EVM-emulated (EVM-derived addresses, so Create3 prediction and the
        // Deployer reads work as-is); only the native zkSync Safes are reached through eraVmCompat.
        SafeCompatConfig memory safeCompatConfig = SafeCompatConfig({
            isEraVm: SafeConfig.isEraVm(),
            privateKey: 0,
            safeFactory: safeFactory,
            safeSingleton: safeSingleton,
            safeFallback: safeFallback,
            safeMulticall: safeMulticall,
            safeBytecodes: SafeBytecodes("", "", "", "", "", "", "", "")
        });
        safeCompatConfig.safeBytecodes.load(vm);
        if (safeCompatConfig.isEraVm) safeCompatConfig.safeBytecodes.loadV141(vm);

        require(isEraVm == safeCompatConfig.isEraVm, "isEraVm mismatch");
        _assertSafeInfraCodehashes(safeCompatConfig);

        require(Feature.unwrap(takerSubmittedFeature) == 2, "wrong taker-submitted feature (tokenId)");
        require(Feature.unwrap(metaTxFeature) == 3, "wrong metatransaction feature (tokenId)");
        require(Feature.unwrap(intentFeature) == 4, "wrong intents feature (tokenId)");
        require(Feature.unwrap(bridgeFeature) == 5, "wrong bridge feature (tokenId)");
        require(solvers.length > 0, "solvers must not be empty");

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
            _isModuleEnabled(safeCompatConfig, ISafeOwners(deploymentSafe), iceColdCoffee),
            "iceColdCoffee module not enabled on deployment safe"
        );
        {
            address[] memory currentOwners = _getOwners(safeCompatConfig, ISafeOwners(deploymentSafe));
            require(
                currentOwners.length == 1 && currentOwners[0] == moduleDeployer,
                "deployment safe is not sole-owned by moduleDeployer"
            );
            require(_getThreshold(safeCompatConfig, ISafeOwners(deploymentSafe)) == 1, "deployment safe threshold != 1");
        }
        {
            address[] memory currentOwners = _getOwners(safeCompatConfig, ISafeOwners(upgradeSafe));
            require(
                currentOwners.length == 1 && currentOwners[0] == proxyDeployer,
                "upgrade safe is not sole-owned by proxyDeployer"
            );
            require(_getThreshold(safeCompatConfig, ISafeOwners(upgradeSafe)) == 1, "upgrade safe threshold != 1");
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

        bytes[] memory authorizeCalls = new bytes[](4);
        authorizeCalls[0] = _encodeMultisend(deployerProxy, takerSubmittedAuthorizeCall);
        authorizeCalls[1] = _encodeMultisend(deployerProxy, metaTxAuthorizeCall);
        authorizeCalls[2] = _encodeMultisend(deployerProxy, intentAuthorizeCall);
        authorizeCalls[3] = _encodeMultisend(deployerProxy, bridgeAuthorizeCall);
        bytes memory authorizeTx = _encodeMultisend(authorizeCalls);

        // The upgradeSafe handoff is deferred to the very last tx, so the proxyDeployer keeps control until
        // the revive fully lands; a partial failure (e.g. a deploy tx hitting the gas cap) stays re-runnable.
        address[] memory upgradeOwners = SafeConfig.getUpgradeSafeSigners();
        bytes[] memory upgradeChangeOwnersCalls =
            _encodeChangeOwners(upgradeSafe, SafeConfig.upgradeSafeThreshold, proxyDeployer, upgradeOwners);
        assert(upgradeChangeOwnersCalls.length == upgradeOwners.length + 1);
        bytes memory upgradeChangeOwnersTx = _encodeMultisend(upgradeChangeOwnersCalls);

        address[] memory deployerOwners = SafeConfig.getDeploymentSafeSigners();
        bytes[] memory deploymentChangeOwnersCalls =
            _encodeChangeOwners(deploymentSafe, SafeConfig.deploymentSafeThreshold, moduleDeployer, deployerOwners);
        assert(deploymentChangeOwnersCalls.length == deployerOwners.length + 1);
        bytes memory deploymentChangeOwnersTx = _encodeMultisend(deploymentChangeOwnersCalls);

        bytes memory takerDeployTx = _wrapSingleMultisend(_encodeMultisend(deployerProxy, takerSubmittedDeployCall));
        bytes memory metaTxDeployTx = _wrapSingleMultisend(_encodeMultisend(deployerProxy, metaTxDeployCall));
        bytes memory intentDeployTx = _wrapSingleMultisend(_encodeMultisend(deployerProxy, intentDeployCall));
        bytes memory bridgeDeployTx = _wrapSingleMultisend(_encodeMultisend(deployerProxy, bridgeDeployCall));

        bytes memory solversTx = _encodeMultisend(_encodeSolversMultisend(predictedIntentSettler, solvers));

        bytes memory deploymentSignature = abi.encodePacked(uint256(uint160(moduleDeployer)), bytes32(0), uint8(1));
        bytes memory upgradeSignature = abi.encodePacked(uint256(uint160(proxyDeployer)), bytes32(0), uint8(1));

        uint256[] memory gasSplits = new uint256[](migrateUpgradeSafe ? 12 : 11);

        _startBroadcast(safeCompatConfig, proxyDeployerKey, proxyDeployer);

        // authorize the deploymentSafe for each feature (upgradeSafe ownership left untouched for now)
        gasSplits[0] = gasleft();
        _execDelegateCall(safeCompatConfig, upgradeSafe, safeMulticall, authorizeTx, upgradeSignature);
        gasSplits[1] = gasleft();
        _stopBroadcast(safeCompatConfig);

        _startBroadcast(safeCompatConfig, moduleDeployerKey, moduleDeployer);

        // deploy settlers; register solvers; hand the deploymentSafe back to its multisig
        gasSplits[2] = gasleft();
        _execDelegateCall(safeCompatConfig, deploymentSafe, safeMulticall, takerDeployTx, deploymentSignature);

        gasSplits[3] = gasleft();
        _execDelegateCall(safeCompatConfig, deploymentSafe, safeMulticall, metaTxDeployTx, deploymentSignature);

        gasSplits[4] = gasleft();
        _execDelegateCall(safeCompatConfig, deploymentSafe, safeMulticall, intentDeployTx, deploymentSignature);

        gasSplits[5] = gasleft();
        _execDelegateCall(safeCompatConfig, deploymentSafe, safeMulticall, bridgeDeployTx, deploymentSignature);

        gasSplits[6] = gasleft();
        _execDelegateCall(safeCompatConfig, deploymentSafe, safeMulticall, solversTx, deploymentSignature);

        gasSplits[7] = gasleft();
        _execDelegateCall(
            safeCompatConfig, deploymentSafe, safeMulticall, deploymentChangeOwnersTx, deploymentSignature
        );

        gasSplits[8] = gasleft();
        _stopBroadcast(safeCompatConfig);

        // finally, optionally migrate the upgradeSafe to Safe v1.4.1, then hand it back to its multisig
        _startBroadcast(safeCompatConfig, proxyDeployerKey, proxyDeployer);
        uint256 gasIdx = 9;
        if (migrateUpgradeSafe) {
            gasSplits[gasIdx++] = gasleft();
            _migrateUpgradeSafe(
                safeCompatConfig, upgradeSafe, safeMigration, safeSingletonV141, safeFallbackV141, upgradeSignature
            );
        }
        gasSplits[gasIdx++] = gasleft();
        _execDelegateCall(safeCompatConfig, upgradeSafe, safeMulticall, upgradeChangeOwnersTx, upgradeSignature);
        gasSplits[gasIdx] = gasleft();
        _stopBroadcast(safeCompatConfig);

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
            keccak256(abi.encodePacked(_getOwners(safeCompatConfig, ISafeOwners(deploymentSafe))))
                == keccak256(abi.encodePacked(deployerOwners)),
            "deployment safe owners mismatch"
        );
        require(
            _getThreshold(safeCompatConfig, ISafeOwners(deploymentSafe)) == SafeConfig.deploymentSafeThreshold,
            "deployment safe threshold mismatch"
        );
        require(
            keccak256(abi.encodePacked(_getOwners(safeCompatConfig, ISafeOwners(upgradeSafe))))
                == keccak256(abi.encodePacked(upgradeOwners)),
            "upgrade safe owners mismatch"
        );
        require(
            _getThreshold(safeCompatConfig, ISafeOwners(upgradeSafe)) == SafeConfig.upgradeSafeThreshold,
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
