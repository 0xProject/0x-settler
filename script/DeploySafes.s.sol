// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Script} from "@forge-std/Script.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";
import {Create3} from "src/utils/Create3.sol";
import {ZeroExSettlerDeployerSafeModule} from "src/deployer/SafeModule.sol";
import {Deployer, Feature, Nonce, salt} from "src/deployer/Deployer.sol";
import {ERC1967UUPSProxy} from "src/proxy/ERC1967UUPSProxy.sol";
import {SafeConfig} from "./SafeConfig.sol";

interface ISafeFactory {
    function createProxyWithNonce(address singleton, bytes calldata initializer, uint256 saltNonce)
        external
        returns (address);
    function proxyCreationCode() external view returns (bytes memory);
}

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
}

interface ISafeModule {
    function enableModule(address module) external;
}

interface ISafeMulticall {
    /// @dev Sends multiple transactions and reverts all if one fails.
    /// @param transactions Encoded transactions. Each transaction is encoded as a packed bytes of
    ///                     operation has to be uint8(0) in this version (=> 1 byte),
    ///                     to as a address (=> 20 bytes),
    ///                     value as a uint256 (=> 32 bytes),
    ///                     data length as a uint256 (=> 32 bytes),
    ///                     data as bytes.
    ///                     see abi.encodePacked for more information on packed encoding
    /// @notice The code is for most part the same as the normal MultiSend (to keep compatibility),
    ///         but reverts if a transaction tries to use a delegatecall.
    /// @notice This method is payable as delegatecalls keep the msg.value from the previous call
    ///         If the calling method (e.g. execTransaction) received ETH this would revert otherwise
    function multiSend(bytes memory transactions) external payable;
}

contract DeploySafes is Script {
    bytes32 internal constant singletonHash = 0x21842597390c4c6e3c1239e434a682b054bd9548eee5e9b1d6a4482731023c0f;
    bytes32 internal constant singletonHashEraVm = 0xe2ca068330339d608367d83a0b25545efe39e619098597699ab8ff828cb1ddd8;
    bytes32 internal constant factoryHash = 0x337d7f54be11b6ed55fef7b667ea5488db53db8320a05d1146aa4bd169a39a9b;
    bytes32 internal constant factoryHashEraVm = 0x55daa5d390d283edbc5fa835bd53befce45179c758feaac8c149a95850d0a6b6;
    bytes32 internal constant fallbackHash = 0x03e69f7ce809e81687c69b19a7d7cca45b6d551ffdec73d9bb87178476de1abf;
    bytes32 internal constant fallbackHashEraVm = 0x017e9a83d5513f503fb85274f4d1ad1811040d7caa31772750ffb08638c28fbb;
    bytes32 internal constant multicallHash = 0xa9865ac2d9c7a1591619b188c4d88167b50df6cc0c5327fcbd1c8c75f7c066ad;
    bytes32 internal constant multicallHashEraVm = 0x064ddbf252714bcd4cb79f679e8c12df96d998ce07bbb13b3118c1dbf4a31942;

    // This is derived from calling `proxyCreationCode()` on the
    // factory and then decoding the EraVm-style encoded inithash from
    // that blob.
    // ref: https://docs.zksync.io/zksync-protocol/era-vm/differences/evm-instructions#datasize-dataoffset-datacopy
    // ref: https://matter-labs.github.io/zksync-era/core/latest/guides/advanced/12_alternative_vm_intro.html#bytecode-hashes
    bytes32 internal constant safeProxyInitHashEraVm =
        0x0100004124426fb9ebb25e27d670c068e52f9ba631bd383279a188be47e3f86d;

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
                if or(xor(returndatasize(), len), iszero(staticcall(gas(), 0x04, src, len, dst, len))) { invalid() }

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

    function run(
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
        Feature takerSubmittedFeature,
        Feature metaTxFeature,
        Feature intentFeature,
        Feature bridgeFeature,
        string calldata initialDescriptionTakerSubmitted,
        string calldata initialDescriptionMetaTx,
        string calldata initialDescriptionIntent,
        string calldata initialDescriptionBridge,
        string calldata chainDisplayName,
        bytes calldata constructorArgs,
        address[] calldata solvers
    ) public {
        bool isEraVm = SafeConfig.isEraVm();
        require(address(safeFactory).codehash == (isEraVm ? factoryHashEraVm : factoryHash), "Safe factory codehash");
        require(safeSingleton.codehash == (isEraVm ? singletonHashEraVm : singletonHash), "Safe singleton codehash");
        require(safeFallback.codehash == (isEraVm ? fallbackHashEraVm : fallbackHash), "Safe fallback codehash");
        require(safeMulticall.codehash == (isEraVm ? multicallHashEraVm : multicallHash), "Safe multicall codehash");

        require(Feature.unwrap(takerSubmittedFeature) == 2, "wrong taker-submitted feature (tokenId)");
        require(Feature.unwrap(metaTxFeature) == 3, "wrong metatransaction feature (tokenId)");
        require(Feature.unwrap(intentFeature) == 4, "wrong intents feature (tokenId)");
        require(Feature.unwrap(bridgeFeature) == 5, "wrong bridge feature (tokenId)");

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
        bytes32 safeDeploymentSalt = bytes32(0);
        owners[0] = moduleDeployer;
        bytes memory deploymentInitializer = abi.encodeCall(
            ISafeSetup.setup, (owners, 1, address(0), new bytes(0), safeFallback, address(0), 0, payable(address(0)))
        );
        bytes32 deploymentDerivedSalt = keccak256(bytes.concat(keccak256(deploymentInitializer), safeDeploymentSalt));
        owners[0] = proxyDeployer;
        bytes memory upgradeInitializer = abi.encodeCall(
            ISafeSetup.setup, (owners, 1, address(0), new bytes(0), safeFallback, address(0), 0, payable(address(0)))
        );
        bytes32 upgradeDerivedSalt = keccak256(bytes.concat(keccak256(upgradeInitializer), safeDeploymentSalt));

        if (isEraVm) {
            bytes32 constructorHash = keccak256(abi.encode(safeSingleton));

            require(
                AddressDerivation.deriveDeterministicContractZkSync(
                    address(safeFactory), deploymentDerivedSalt, safeProxyInitHashEraVm, constructorHash
                ) == deploymentSafe,
                "deployment safe address mismatch"
            );
            require(
                AddressDerivation.deriveDeterministicContractZkSync(
                    address(safeFactory), upgradeDerivedSalt, safeProxyInitHashEraVm, constructorHash
                ) == deploymentSafe,
                "upgrade safe address mismatch"
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

        address[] memory upgradeOwners = SafeConfig.getUpgradeSafeSigners();
        bytes[] memory changeOwnersCalls =
            _encodeChangeOwners(upgradeSafe, SafeConfig.upgradeSafeThreshold, proxyDeployer, upgradeOwners);
        assert(changeOwnersCalls.length == upgradeOwners.length + 1);
        bytes[] memory upgradeSetupCalls = new bytes[](9 + changeOwnersCalls.length);
        upgradeSetupCalls[0] = _encodeMultisend(deployerProxy, acceptOwnershipCall);
        upgradeSetupCalls[1] = _encodeMultisend(deployerProxy, takerSubmittedSetDescriptionCall);
        upgradeSetupCalls[2] = _encodeMultisend(deployerProxy, takerSubmittedAuthorizeCall);
        upgradeSetupCalls[3] = _encodeMultisend(deployerProxy, metaTxSetDescriptionCall);
        upgradeSetupCalls[4] = _encodeMultisend(deployerProxy, metaTxAuthorizeCall);
        upgradeSetupCalls[5] = _encodeMultisend(deployerProxy, intentSetDescriptionCall);
        upgradeSetupCalls[6] = _encodeMultisend(deployerProxy, intentAuthorizeCall);
        upgradeSetupCalls[7] = _encodeMultisend(deployerProxy, bridgeSetDescriptionCall);
        upgradeSetupCalls[8] = _encodeMultisend(deployerProxy, bridgeAuthorizeCall);
        for (uint256 i; i < changeOwnersCalls.length; i++) {
            upgradeSetupCalls[i + 9] = changeOwnersCalls[i];
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
            address prevSolver = 0x0000000000000000000000000000000000000001;
            for (uint256 i; i < solvers.length; i++) {
                address solver = solvers[i];
                deploySetupCalls[i + 5] = _encodeMultisend(
                    predictedIntentSettler,
                    abi.encodeWithSignature("setSolver(address,address,bool)", prevSolver, solver, true)
                );
                prevSolver = solver;
            }
        }
        for (uint256 i; i < changeOwnersCalls.length; i++) {
            deploySetupCalls[i + 5 + solvers.length] = changeOwnersCalls[i];
        }
        bytes memory deploySetupCall = _encodeMultisend(deploySetupCalls);

        bytes memory deploymentSignature = abi.encodePacked(uint256(uint160(moduleDeployer)), bytes32(0), uint8(1));
        bytes memory upgradeSignature = abi.encodePacked(uint256(uint160(proxyDeployer)), bytes32(0), uint8(1));

        uint256[] memory gasSplits = new uint256[](10);

        vm.startBroadcast(moduleDeployerKey);

        // first, we deploy the module to get the correct address
        gasSplits[0] = gasleft();
        address deployedModule = address(new ZeroExSettlerDeployerSafeModule(deploymentSafe));
        // next, we deploy the implementation we're going to need when we take ownership of the proxy
        gasSplits[1] = gasleft();
        address deployerImpl = address(new Deployer(1));
        // now we deploy the safe that's responsible *ONLY* for deploying new instances
        gasSplits[2] = gasleft();
        address deployedDeploymentSafe = safeFactory.createProxyWithNonce(safeSingleton, deploymentInitializer, 0);

        gasSplits[3] = gasleft();
        vm.stopBroadcast();

        vm.startBroadcast(proxyDeployerKey);

        // first we deploy the proxy for the deployer to get the correct address
        gasSplits[4] = gasleft();
        address deployedDeployerProxy =
            ERC1967UUPSProxy.create(deployerImpl, abi.encodeCall(Deployer.initialize, (upgradeSafe)));
        // then we deploy the safe that's going to own the proxy
        gasSplits[5] = gasleft();
        address deployedUpgradeSafe = safeFactory.createProxyWithNonce(safeSingleton, upgradeInitializer, 0);

        // configure the deployer (accept ownership; set descriptions; authorize; set new owners)
        gasSplits[6] = gasleft();
        ISafeExecute(upgradeSafe).execTransaction(
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

        gasSplits[7] = gasleft();
        vm.stopBroadcast();

        vm.startBroadcast(moduleDeployerKey);

        // add rollback module; deploy settlers; set new owners
        gasSplits[8] = gasleft();
        ISafeExecute(deploymentSafe).execTransaction(
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

        gasSplits[9] = gasleft();
        vm.stopBroadcast();

        {
            uint256 gasPrev = gasSplits[0];
            for (uint256 i = 1; i < gasSplits.length; i++) {
                require(gasPrev + 15728639 > (gasPrev = gasSplits[i]), "transaction is likely to exceed EIP-7825 limit");
            }
        }

        require(deployedModule == iceColdCoffee, "deployment/prediction mismatch");
        require(deployedDeploymentSafe == deploymentSafe, "deployed safe/predicted safe mismatch");
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
            keccak256(abi.encodePacked(ISafeOwners(deploymentSafe).getOwners()))
                == keccak256(abi.encodePacked(deployerOwners)),
            "deployment safe owners mismatch"
        );
        require(
            keccak256(abi.encodePacked(ISafeOwners(upgradeSafe).getOwners()))
                == keccak256(abi.encodePacked(upgradeOwners)),
            "upgrade safe owners mismatch"
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
