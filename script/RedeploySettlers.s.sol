// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Script} from "@forge-std/Script.sol";
import {Deployer, Feature} from "src/deployer/Deployer.sol";
import {SafeConfig} from "./SafeConfig.sol";

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

interface ISafeOwners {
    function addOwnerWithThreshold(address owner, uint256 _threshold) external;
    function removeOwner(address prevOwner, address owner, uint256 _threshold) external;
    function changeThreshold(uint256 _threshold) external;
    function getOwners() external view returns (address[] memory);
    function getThreshold() external view returns (uint256);
    function isModuleEnabled(address module) external view returns (bool);
}

/// @notice Redeploys Settlers on an abandoned chain and restores Safe signers.
contract RedeploySettlers is Script {
    bytes32 internal constant multicallHash = 0xa9865ac2d9c7a1591619b188c4d88167b50df6cc0c5327fcbd1c8c75f7c066ad;

    function _encodeMultisend(bytes[] memory calls) internal view returns (bytes memory result) {
        // The Gnosis multicall contract uses a very obnoxious packed encoding
        // that is very similar to, but not exactly the same as
        // `abi.encodePacked`
        assembly ("memory-safe") {
            result := mload(0x40)
            mstore(add(0x04, result), 0x8d80ff0a) // selector for `multiSend(bytes)`
            mstore(add(0x24, result), 0x20)
            let bytes_length_ptr := add(0x44, result)
            mstore(bytes_length_ptr, 0x00)
            for {
                let i := add(0x20, calls)
                let end := add(i, shl(0x05, mload(calls)))
                let dst := add(0x20, bytes_length_ptr)
            } lt(i, end) { i := add(0x20, i) } {
                let src := mload(i)
                let len := mload(src)
                src := add(0x20, src)

                // We're using the old identity precompile version instead of
                // the MCOPY opcode version because I don't want to have to deal
                // with maintaining two versions of this
                if or(xor(returndatasize(), len), iszero(staticcall(gas(), 0x04, src, len, dst, len))) {
                    invalid()
                }

                dst := add(dst, len)
                mstore(bytes_length_ptr, add(len, mload(bytes_length_ptr)))
            }
            mstore(result, add(0x44, mload(bytes_length_ptr)))
            mstore(0x40, add(0x20, add(mload(result), result)))
        }
    }

    function _encodeMultisend(address safe, bytes memory call) internal pure returns (bytes memory) {
        return abi.encodePacked(
            uint8(ISafeExecute.Operation.Call),
            safe,
            uint256(0), // value
            call.length,
            call
        );
    }

    function _encodeChangeOwners(address safe, uint256 threshold, address oldOwner, address[] memory newOwners)
        internal
        view
        returns (bytes[] memory)
    {
        bytes[] memory subCalls = new bytes[](newOwners.length + 1);
        for (uint256 i; i < newOwners.length; i++) {
            bytes memory data =
                abi.encodeCall(ISafeOwners.addOwnerWithThreshold, (newOwners[newOwners.length - i - 1], 1));
            subCalls[i] = _encodeMultisend(safe, data);
        }
        {
            bytes memory data =
                abi.encodeCall(ISafeOwners.removeOwner, (newOwners[newOwners.length - 1], oldOwner, threshold));
            subCalls[newOwners.length] = _encodeMultisend(safe, data);
        }
        return subCalls;
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

        uint256 moduleDeployerKey = vm.envUint("ICECOLDCOFFEE_DEPLOYER_KEY");
        uint256 proxyDeployerKey = vm.envUint("DEPLOYER_PROXY_DEPLOYER_KEY");
        require(vm.addr(moduleDeployerKey) == moduleDeployer, "module deployer key/address mismatch");
        require(vm.addr(proxyDeployerKey) == proxyDeployer, "proxy deployer key/address mismatch");

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
        bytes[] memory deploySetupCalls = new bytes[](4 + solvers.length + changeOwnersCalls.length);
        deploySetupCalls[0] = _encodeMultisend(deployerProxy, takerSubmittedDeployCall);
        deploySetupCalls[1] = _encodeMultisend(deployerProxy, metaTxDeployCall);
        deploySetupCalls[2] = _encodeMultisend(deployerProxy, intentDeployCall);
        deploySetupCalls[3] = _encodeMultisend(deployerProxy, bridgeDeployCall);
        {
            address prevSolver = 0x0000000000000000000000000000000000000001;
            for (uint256 i; i < solvers.length; i++) {
                address solver = solvers[i];
                deploySetupCalls[i + 4] = _encodeMultisend(
                    predictedIntentSettler,
                    abi.encodeWithSignature("setSolver(address,address,bool)", prevSolver, solver, true)
                );
                prevSolver = solver;
            }
        }
        for (uint256 i; i < changeOwnersCalls.length; i++) {
            deploySetupCalls[i + 4 + solvers.length] = changeOwnersCalls[i];
        }
        bytes memory deploySetupCall = _encodeMultisend(deploySetupCalls);

        bytes memory deploymentSignature = abi.encodePacked(uint256(uint160(moduleDeployer)), bytes32(0), uint8(1));
        bytes memory upgradeSignature = abi.encodePacked(uint256(uint160(proxyDeployer)), bytes32(0), uint8(1));

        uint256[] memory gasSplits = new uint256[](4);

        vm.startBroadcast(proxyDeployerKey);

        // configure the deployer (authorize; set new owners)
        gasSplits[0] = gasleft();
        ISafeExecute(upgradeSafe)
            .execTransaction(
                safeMulticall,
                0,
                upgradeSetupCall,
                ISafeExecute.Operation.DelegateCall,
                0,
                0,
                0,
                address(0),
                address(0),
                upgradeSignature
            );
        gasSplits[1] = gasleft();
        vm.stopBroadcast();

        vm.startBroadcast(moduleDeployerKey);

        // deploy settlers; register solvers; set new owners
        gasSplits[2] = gasleft();
        ISafeExecute(deploymentSafe)
            .execTransaction(
                safeMulticall,
                0,
                deploySetupCall,
                ISafeExecute.Operation.DelegateCall,
                0,
                0,
                0,
                address(0),
                address(0),
                deploymentSignature
            );
        gasSplits[3] = gasleft();
        vm.stopBroadcast();

        for (uint256 i = 1; i < gasSplits.length; i++) {
            require(gasSplits[i] + 15728639 > gasSplits[i - 1], "transaction is likely to exceed EIP-7825 limit");
        }

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
