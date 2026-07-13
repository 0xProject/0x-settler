// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SafeMultisend, ISafeExecute, ISafeFactory, ISafeOwners} from "./SafeMultisend.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";
import {Create3} from "src/utils/Create3.sol";
import {ZeroExSettlerDeployerSafeModule} from "src/deployer/SafeModule.sol";
import {Deployer, Feature, Nonce, salt} from "src/deployer/Deployer.sol";
import {ERC1967UUPSProxy} from "src/proxy/ERC1967UUPSProxy.sol";
import {SafeConfig} from "./SafeConfig.sol";
import {SafeBytecodes} from "./SafeCode.sol";

interface ISafeSetup {
    function setup(
        address[] calldata owners,
        uint256 threshold,
        address to,
        bytes calldata data,
        address fallbackHandler,
        address paymentToken,
        uint256 payment,
        address payable paymentReceiver
    ) external;
}

interface ISafeModule {
    function enableModule(address module) external;
}

contract DeploySafes is SafeMultisend {
    uint256 internal constant safeDeploymentSaltNonce = 0;

    // This is derived from calling `proxyCreationCode()` on the factory and then decoding the EraVm-style encoded
    // inithash from that blob.
    // ref: https://web.archive.org/web/20251108135035/https://docs.zksync.io/zksync-protocol/era-vm/differences/evm-instructions#datasize-dataoffset-datacopy
    // ref: https://web.archive.org/web/20251108134721/https://matter-labs.github.io/zksync-era/core/latest/guides/advanced/12_alternative_vm_intro.html#bytecode-hashes
    bytes32 internal constant safeProxyInitHashEraVm =
        0x0100004124426fb9ebb25e27d670c068e52f9ba631bd383279a188be47e3f86d;
    bytes32 internal constant safeProxyHashEraVm = 0x3d70c4a51cf0b92f04e5e281833aeece55198933569c08f5d11fcc45c495253e;

    function _createProxyWithNonce(SafeCompatConfig memory compatConfig, bytes memory initializer, uint256 saltNonce)
        private
        eraVmCompat(
            compatConfig.isEraVm,
            compatConfig.privateKey,
            ISafeExecute(address(0)),
            compatConfig.safeFactory,
            compatConfig.safeSingleton,
            compatConfig.safeFallback,
            compatConfig.safeMulticall,
            compatConfig.safeBytecodes
        )
        returns (address deployedSafe)
    {
        bool isEraVm = compatConfig.isEraVm;
        ISafeFactory safeFactory = compatConfig.safeFactory;
        address safeSingleton = compatConfig.safeSingleton;
        deployedSafe = safeFactory.createProxyWithNonce(safeSingleton, initializer, saltNonce);

        if (isEraVm) {
            bytes32 constructorHash = keccak256(abi.encode(safeSingleton));
            bytes32 eraVmCreate2Salt = keccak256(abi.encode(keccak256(initializer), saltNonce));

            // Foundry does not and cannot simulate EraVM bytecode, so we have to blindly assume that this is the
            // correct derivation. We lie to the rest of the script about this address.
            address deployedSafeEraVm = AddressDerivation.deriveDeterministicContractEraVm(
                address(safeFactory), eraVmCreate2Salt, safeProxyInitHashEraVm, constructorHash
            );
            require(deployedSafeEraVm.codehash == 0);

            // Set up the EraVm-pattern deployed address state to match the EVM-pattern deployed address.
            vm.etch(deployedSafeEraVm, compatConfig.safeBytecodes.proxyCodeEraVm);
            vm.copyStorage(deployedSafe, deployedSafeEraVm);
            deployedSafe = deployedSafeEraVm;
            require(deployedSafe.codehash == safeProxyHashEraVm);

            // We are unable to check whether the configuration will succeed on EraVm, but we assume that the EVM
            // bytecode overrides done in the `eraVmCompat` modifier are faithful.
        }
    }

    function run(
        bool isEraVm,
        address moduleDeployer,
        address proxyDeployer,
        address iceColdCoffee,
        address deployerProxy,
        address deploymentSafe,
        address upgradeSafe,
        address daoSafe,
        ISafeFactory safeFactory,
        address safeSingleton,
        address safeFallback,
        address safeMulticall,
        Feature takerSubmittedFeature,
        Feature metaTxFeature,
        Feature intentFeature,
        Feature bridgeFeature,
        Feature daoFeature,
        string calldata initialDescriptionTakerSubmitted,
        string calldata initialDescriptionMetaTx,
        string calldata initialDescriptionIntent,
        string calldata initialDescriptionBridge,
        string calldata initialDescriptionDao,
        string calldata chainDisplayName,
        bytes calldata constructorArgs,
        address[] calldata solvers
    ) public {
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

        require(isEraVm == safeCompatConfig.isEraVm, "isEraVm mismatch");
        _assertSafeInfraCodehashes(safeCompatConfig);

        require(Feature.unwrap(takerSubmittedFeature) == 2, "wrong taker-submitted feature (tokenId)");
        require(Feature.unwrap(metaTxFeature) == 3, "wrong metatransaction feature (tokenId)");
        require(Feature.unwrap(intentFeature) == 4, "wrong intents feature (tokenId)");
        require(Feature.unwrap(bridgeFeature) == 5, "wrong bridge feature (tokenId)");
        require(Feature.unwrap(daoFeature) == 1001, "wrong DAO feature (tokenId)");

        uint256 moduleDeployerKey = vm.envUint("ICECOLDCOFFEE_DEPLOYER_KEY");
        uint256 proxyDeployerKey = vm.envUint("DEPLOYER_PROXY_DEPLOYER_KEY");
        require(vm.addr(moduleDeployerKey) == moduleDeployer, "module deployer key/address mismatch");
        require(vm.addr(proxyDeployerKey) == proxyDeployer, "proxy deployer key/address mismatch");

        require(
            AddressDerivation.deriveContract(moduleDeployer, 0) == iceColdCoffee,
            "module -- key/deployed address mismatch"
        );
        require(
            AddressDerivation.deriveContract(proxyDeployer, 0) == deployerProxy,
            "deployer proxy -- key/deployed address mismatch"
        );
        require(vm.getNonce(moduleDeployer) == 0, "module -- deployer already has transactions");
        require(vm.getNonce(proxyDeployer) == 0, "deployer proxy -- deployer already has transactions");

        require(deploymentSafe.code.length == 0, "deployment safe is already deployed");
        require(upgradeSafe.code.length == 0, "upgrade safe is already deployed");

        // precompute safe addresses
        address[] memory owners = new address[](1);
        owners[0] = moduleDeployer;
        bytes memory deploymentInitializer = abi.encodeCall(
            ISafeSetup.setup, (owners, 1, address(0), new bytes(0), safeFallback, address(0), 0, payable(address(0)))
        );
        bytes32 deploymentDerivedSalt =
            keccak256(bytes.concat(keccak256(deploymentInitializer), bytes32(safeDeploymentSaltNonce)));
        owners[0] = proxyDeployer;
        bytes memory upgradeInitializer = abi.encodeCall(
            ISafeSetup.setup, (owners, 1, address(0), new bytes(0), safeFallback, address(0), 0, payable(address(0)))
        );
        bytes32 upgradeDerivedSalt =
            keccak256(bytes.concat(keccak256(upgradeInitializer), bytes32(safeDeploymentSaltNonce)));

        bytes memory daoInitializer = abi.encodeCall(
            ISafeSetup.setup,
            (
                SafeConfig.getDAOSafeSigners(),
                SafeConfig.daoSafeThreshold,
                address(0),
                new bytes(0),
                safeFallback,
                address(0),
                0,
                payable(address(0))
            )
        );
        bytes32 daoSafeSalt =
            keccak256(bytes.concat(keccak256(daoInitializer), bytes32(safeDeploymentSaltNonce)));

        if (safeCompatConfig.isEraVm) {
            bytes32 constructorHash = keccak256(abi.encode(safeSingleton));

            require(
                AddressDerivation.deriveDeterministicContractEraVm(
                    address(safeFactory), deploymentDerivedSalt, safeProxyInitHashEraVm, constructorHash
                ) == deploymentSafe,
                "deployment safe address mismatch"
            );
            require(
                AddressDerivation.deriveDeterministicContractEraVm(
                    address(safeFactory), upgradeDerivedSalt, safeProxyInitHashEraVm, constructorHash
                ) == upgradeSafe,
                "upgrade safe address mismatch"
            );
            require(
                AddressDerivation.deriveDeterministicContractEraVm(
                    address(safeFactory), daoSafeSalt, safeProxyInitHashEraVm, constructorHash
                ) == daoSafe,
                "dao safe address mismatch"
            );
        } else {
            bytes memory creationCode = safeFactory.proxyCreationCode();
            bytes32 initHash = keccak256(bytes.concat(creationCode, bytes32(uint256(uint160(safeSingleton)))));

            require(
                AddressDerivation.deriveDeterministicContract(address(safeFactory), deploymentDerivedSalt, initHash)
                    == deploymentSafe,
                "deployment safe address mismatch"
            );
            require(
                AddressDerivation.deriveDeterministicContract(address(safeFactory), upgradeDerivedSalt, initHash)
                    == upgradeSafe,
                "upgrade safe address mismatch"
            );
            require(
                AddressDerivation.deriveDeterministicContract(address(safeFactory), daoSafeSalt, initHash)
                    == daoSafe,
                "dao safe address mismatch"
            );
        }

        // after everything is deployed, we're going to need to set up permissions; these are those calls
        bytes memory addModuleCall = abi.encodeCall(ISafeModule.enableModule, (iceColdCoffee));
        bytes memory acceptOwnershipCall = abi.encodeWithSignature("acceptOwnership()");

        bytes memory takerSubmittedSetDescriptionCall =
            abi.encodeCall(Deployer.setDescription, (takerSubmittedFeature, initialDescriptionTakerSubmitted));
        bytes memory takerSubmittedAuthorizeCall = abi.encodeCall(
            Deployer.authorize, (takerSubmittedFeature, deploymentSafe, uint40(block.timestamp + 365 days))
        );
        bytes memory takerSubmittedDeployCall = abi.encodeCall(
            Deployer.deploy,
            (
                takerSubmittedFeature,
                bytes.concat(
                    vm.getCode(string.concat(chainDisplayName, "TakerSubmittedFlat.sol:", chainDisplayName, "Settler")),
                    constructorArgs
                )
            )
        );
        address predictedTakerSubmittedSettler =
            Create3.predict(salt(takerSubmittedFeature, Nonce.wrap(1)), deployerProxy);

        bytes memory metaTxSetDescriptionCall =
            abi.encodeCall(Deployer.setDescription, (metaTxFeature, initialDescriptionMetaTx));
        bytes memory metaTxAuthorizeCall =
            abi.encodeCall(Deployer.authorize, (metaTxFeature, deploymentSafe, uint40(block.timestamp + 365 days)));
        bytes memory metaTxDeployCall = abi.encodeCall(
            Deployer.deploy,
            (
                metaTxFeature,
                bytes.concat(
                    vm.getCode(string.concat(chainDisplayName, "MetaTxnFlat.sol:", chainDisplayName, "SettlerMetaTxn")),
                    constructorArgs
                )
            )
        );
        address predictedMetaTxSettler = Create3.predict(salt(metaTxFeature, Nonce.wrap(1)), deployerProxy);

        bytes memory intentSetDescriptionCall =
            abi.encodeCall(Deployer.setDescription, (intentFeature, initialDescriptionIntent));
        bytes memory intentAuthorizeCall =
            abi.encodeCall(Deployer.authorize, (intentFeature, deploymentSafe, uint40(block.timestamp + 365 days)));
        bytes memory intentDeployCall = abi.encodeCall(
            Deployer.deploy,
            (
                intentFeature,
                bytes.concat(
                    vm.getCode(string.concat(chainDisplayName, "IntentFlat.sol:", chainDisplayName, "SettlerIntent")),
                    constructorArgs
                )
            )
        );
        address predictedIntentSettler = Create3.predict(salt(intentFeature, Nonce.wrap(1)), deployerProxy);

        bytes memory bridgeSetDescriptionCall =
            abi.encodeCall(Deployer.setDescription, (bridgeFeature, initialDescriptionBridge));
        bytes memory bridgeAuthorizeCall =
            abi.encodeCall(Deployer.authorize, (bridgeFeature, deploymentSafe, uint40(block.timestamp + 365 days)));
        bytes memory bridgeDeployCall = abi.encodeCall(
            Deployer.deploy,
            (
                bridgeFeature,
                bytes.concat(
                    vm.getCode(
                        string.concat(chainDisplayName, "BridgeSettlerFlat.sol:", chainDisplayName, "BridgeSettler")
                    ),
                    constructorArgs
                )
            )
        );
        address predictedBridgeSettler = Create3.predict(salt(bridgeFeature, Nonce.wrap(1)), deployerProxy);

        // DAO feature: initialize and authorize DAO Safe for feature 1001
        bytes memory daoSetDescriptionCall =
            abi.encodeCall(Deployer.setDescription, (daoFeature, initialDescriptionDao));
        bytes memory daoAuthorizeCall = abi.encodeCall(
            Deployer.authorize, (daoFeature, daoSafe, uint40(block.timestamp + 365 days))
        );

        address[] memory upgradeOwners = SafeConfig.getUpgradeSafeSigners();
        bytes[] memory changeOwnersCalls =
            _encodeChangeOwners(upgradeSafe, SafeConfig.upgradeSafeThreshold, proxyDeployer, upgradeOwners);
        assert(changeOwnersCalls.length == upgradeOwners.length + 1);
        bytes[] memory upgradeSetupCalls = new bytes[](11 + changeOwnersCalls.length);
        upgradeSetupCalls[0] = _encodeMultisend(deployerProxy, acceptOwnershipCall);
        upgradeSetupCalls[1] = _encodeMultisend(deployerProxy, takerSubmittedSetDescriptionCall);
        upgradeSetupCalls[2] = _encodeMultisend(deployerProxy, takerSubmittedAuthorizeCall);
        upgradeSetupCalls[3] = _encodeMultisend(deployerProxy, metaTxSetDescriptionCall);
        upgradeSetupCalls[4] = _encodeMultisend(deployerProxy, metaTxAuthorizeCall);
        upgradeSetupCalls[5] = _encodeMultisend(deployerProxy, intentSetDescriptionCall);
        upgradeSetupCalls[6] = _encodeMultisend(deployerProxy, intentAuthorizeCall);
        upgradeSetupCalls[7] = _encodeMultisend(deployerProxy, bridgeSetDescriptionCall);
        upgradeSetupCalls[8] = _encodeMultisend(deployerProxy, bridgeAuthorizeCall);
        upgradeSetupCalls[9] = _encodeMultisend(deployerProxy, daoSetDescriptionCall);
        upgradeSetupCalls[10] = _encodeMultisend(deployerProxy, daoAuthorizeCall);
        for (uint256 i; i < changeOwnersCalls.length; i++) {
            upgradeSetupCalls[i + 11] = changeOwnersCalls[i];
        }
        bytes memory upgradeSetupCall = _encodeMultisend(upgradeSetupCalls);

        address[] memory deployerOwners = SafeConfig.getDeploymentSafeSigners();
        changeOwnersCalls =
            _encodeChangeOwners(deploymentSafe, SafeConfig.deploymentSafeThreshold, moduleDeployer, deployerOwners);
        assert(changeOwnersCalls.length == deployerOwners.length + 1);
        bytes[] memory deploySetupCalls = new bytes[](5 + solvers.length + changeOwnersCalls.length);
        deploySetupCalls[0] = _encodeMultisend(deploymentSafe, addModuleCall);
        deploySetupCalls[1] = _encodeMultisend(deployerProxy, takerSubmittedDeployCall);
        deploySetupCalls[2] = _encodeMultisend(deployerProxy, metaTxDeployCall);
        deploySetupCalls[3] = _encodeMultisend(deployerProxy, intentDeployCall);
        deploySetupCalls[4] = _encodeMultisend(deployerProxy, bridgeDeployCall);
        {
            bytes[] memory solverCalls = _encodeSolversMultisend(predictedIntentSettler, solvers);
            for (uint256 i; i < solverCalls.length; i++) {
                deploySetupCalls[i + 5] = solverCalls[i];
            }
        }
        for (uint256 i; i < changeOwnersCalls.length; i++) {
            deploySetupCalls[i + 5 + solvers.length] = changeOwnersCalls[i];
        }
        bytes memory deploySetupCall = _encodeMultisend(deploySetupCalls);

        bytes memory deploymentSignature = abi.encodePacked(uint256(uint160(moduleDeployer)), bytes32(0), uint8(1));
        bytes memory upgradeSignature = abi.encodePacked(uint256(uint160(proxyDeployer)), bytes32(0), uint8(1));

        uint256[] memory gasSplits = new uint256[](11);

        _startBroadcast(safeCompatConfig, moduleDeployerKey, moduleDeployer);

        // first, we deploy the module to get the correct address
        gasSplits[0] = gasleft();
        address deployedModule = address(new ZeroExSettlerDeployerSafeModule(deploymentSafe));
        // next, we deploy the implementation we're going to need when we take ownership of the proxy
        gasSplits[1] = gasleft();
        address deployerImpl = address(new Deployer(1));
        // now we deploy the safe that's responsible *ONLY* for deploying new instances
        gasSplits[2] = gasleft();
        address deployedDeploymentSafe =
            _createProxyWithNonce(safeCompatConfig, deploymentInitializer, safeDeploymentSaltNonce);

        // deploy the DAO multisig with its actual signers (skip if already deployed by someone else;
        // the CREATE2 address is fully determined by the initializer, so the config is guaranteed correct)
        gasSplits[3] = gasleft();
        address deployedDaoSafe;
        if (daoSafe.code.length == 0) {
            deployedDaoSafe =
                _createProxyWithNonce(safeCompatConfig, daoInitializer, safeDeploymentSaltNonce);
        } else {
            deployedDaoSafe = daoSafe;
        }

        gasSplits[4] = gasleft();
        _stopBroadcast(safeCompatConfig);

        _startBroadcast(safeCompatConfig, proxyDeployerKey, proxyDeployer);

        // first we deploy the proxy for the deployer to get the correct address
        gasSplits[5] = gasleft();
        address deployedDeployerProxy =
            ERC1967UUPSProxy.create(deployerImpl, abi.encodeCall(Deployer.initialize, (upgradeSafe)));
        // then we deploy the safe that's going to own the proxy
        gasSplits[6] = gasleft();
        address deployedUpgradeSafe =
            _createProxyWithNonce(safeCompatConfig, upgradeInitializer, safeDeploymentSaltNonce);

        // configure the deployer (accept ownership; set descriptions; authorize; set new owners)
        gasSplits[7] = gasleft();
        _execTransaction(
            safeCompatConfig,
            ISafeExecute(upgradeSafe),
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

        gasSplits[8] = gasleft();
        _stopBroadcast(safeCompatConfig);

        _startBroadcast(safeCompatConfig, moduleDeployerKey, moduleDeployer);

        // add rollback module; deploy settlers; set new owners
        gasSplits[9] = gasleft();
        _execTransaction(
            safeCompatConfig,
            ISafeExecute(deploymentSafe),
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

        gasSplits[10] = gasleft();
        _stopBroadcast(safeCompatConfig);

        _assertEip7825(gasSplits);

        require(deployedModule == iceColdCoffee, "deployment/prediction mismatch");
        require(deployedDeploymentSafe == deploymentSafe, "deployed safe/predicted safe mismatch");
        require(deployedDaoSafe == daoSafe, "dao safe deployed/predicted safe mismatch");
        require(deployedUpgradeSafe == upgradeSafe, "upgrade deployed safe/predicted safe mismatch");
        require(deployedDeployerProxy == deployerProxy, "deployer proxy predicted mismatch");
        require(Deployer(deployerProxy).owner() == upgradeSafe, "deployer not owned by upgrade safe");
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
            keccak256(abi.encodePacked(_getOwners(safeCompatConfig, ISafeOwners(upgradeSafe))))
                == keccak256(abi.encodePacked(upgradeOwners)),
            "upgrade safe owners mismatch"
        );
        require(
            keccak256(abi.encodePacked(_getOwners(safeCompatConfig, ISafeOwners(daoSafe))))
                == keccak256(abi.encodePacked(SafeConfig.getDAOSafeSigners())),
            "dao safe owners mismatch"
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
