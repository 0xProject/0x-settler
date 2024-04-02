// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Script} from "forge-std/Script.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";
import {ZeroExSettlerDeployerSafeModule} from "src/deployer/SafeModule.sol";
import {Deployer, Feature} from "src/deployer/Deployer.sol";
import {ERC1967UUPSProxy} from "src/proxy/ERC1967UUPSProxy.sol";
import {Settler} from "src/Settler.sol";

import {console} from "forge-std/console.sol";

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

interface ISafeModule {
    function enableModule(address module) external;
}

contract DeploySafes is Script {
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
        Feature feature,
        string calldata initialDescription,
        bytes calldata constructorArgs
    ) public {
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
        bytes memory creationCode = safeFactory.proxyCreationCode();
        bytes32 initHash = keccak256(bytes.concat(creationCode, bytes32(uint256(uint160(safeSingleton)))));

        address[] memory owners = new address[](1);
        owners[0] = moduleDeployer;
        bytes memory deploymentInitializer = abi.encodeCall(
            ISafeSetup.setup, (owners, 1, address(0), new bytes(0), safeFallback, address(0), 0, payable(address(0)))
        );
        owners[0] = proxyDeployer;
        bytes memory upgradeInitializer = abi.encodeCall(
            ISafeSetup.setup, (owners, 1, address(0), new bytes(0), safeFallback, address(0), 0, payable(address(0)))
        );
        require(
            AddressDerivation.deriveDeterministicContract(
                address(safeFactory), keccak256(bytes.concat(keccak256(deploymentInitializer), bytes32(0))), initHash
            ) == deploymentSafe,
            "deployment safe address mismatch"
        );
        require(
            AddressDerivation.deriveDeterministicContract(
                address(safeFactory), keccak256(bytes.concat(keccak256(upgradeInitializer), bytes32(0))), initHash
            ) == upgradeSafe,
            "upgrade safe address mismatch"
        );

        // after everything is deployed, we're going to need to set up permissions; these are those calls
        bytes memory addModuleCall = abi.encodeCall(ISafeModule.enableModule, (iceColdCoffee));
        bytes memory acceptOwnershipCall = abi.encodeWithSignature("acceptOwnership()");
        bytes memory setDescriptionCall = abi.encodeCall(Deployer.setDescription, (feature, initialDescription));
        bytes memory authorizeCall =
            abi.encodeCall(Deployer.authorize, (feature, deploymentSafe, uint40(block.timestamp + 365 days)));
        bytes memory deployCall =
            abi.encodeCall(Deployer.deploy, (feature, bytes.concat(type(Settler).creationCode, constructorArgs)));
        bytes memory deploymentSignature = abi.encodePacked(uint256(uint160(moduleDeployer)), bytes32(0), uint8(1));
        bytes memory upgradeSignature = abi.encodePacked(uint256(uint160(proxyDeployer)), bytes32(0), uint8(1));

        vm.startBroadcast(moduleDeployerKey);

        // first, we deploy the module to get the correct address
        address deployedModule = address(new ZeroExSettlerDeployerSafeModule(deploymentSafe));
        // next, we deploy the implementation we're going to need when we take ownership of the proxy
        address deployerImpl = address(new Deployer());
        // now we deploy the safe that's responsible *ONLY* for deploying new instances
        address deployedDeploymentSafe = safeFactory.createProxyWithNonce(safeSingleton, deploymentInitializer, 0);
        // install the module in the deployment safe so that *anybody* can roll back deployments
        ISafeExecute(deploymentSafe).execTransaction(
            deploymentSafe,
            0,
            addModuleCall,
            ISafeExecute.Operation.Call,
            0,
            0,
            0,
            address(0),
            address(0),
            deploymentSignature
        );

        vm.stopBroadcast();

        vm.startBroadcast(proxyDeployerKey);

        // first we deploy the proxy for the deployer to get the correct address
        address deployedDeployerProxy =
            ERC1967UUPSProxy.create(deployerImpl, abi.encodeCall(Deployer.initialize, (upgradeSafe)));
        // then we deploy the safe that's going to own the proxy
        address deployedUpgradeSafe = safeFactory.createProxyWithNonce(safeSingleton, upgradeInitializer, 0);
        // then the safe takes ownership of the proxy
        ISafeExecute(upgradeSafe).execTransaction(
            deployerProxy,
            0,
            acceptOwnershipCall,
            ISafeExecute.Operation.Call,
            0,
            0,
            0,
            address(0),
            address(0),
            upgradeSignature
        );

        // give the deployment safe permission to deploy instances (for 1 year)
        ISafeExecute(upgradeSafe).execTransaction(
            deployerProxy,
            0,
            setDescriptionCall,
            ISafeExecute.Operation.Call,
            0,
            0,
            0,
            address(0),
            address(0),
            upgradeSignature
        );
        ISafeExecute(upgradeSafe).execTransaction(
            deployerProxy,
            0,
            authorizeCall,
            ISafeExecute.Operation.Call,
            0,
            0,
            0,
            address(0),
            address(0),
            upgradeSignature
        );

        vm.stopBroadcast();

        vm.startBroadcast(moduleDeployerKey);

        ISafeExecute(deploymentSafe).execTransaction(
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

        require(deployedModule == iceColdCoffee, "deployment/prediction mismatch");
        require(deployedDeploymentSafe == deploymentSafe, "deployed safe/predicted safe mismatch");
        require(deployedUpgradeSafe == upgradeSafe, "upgrade deployed safe/predicted safe mismatch");
        require(deployedDeployerProxy == deployerProxy, "deployer proxy predicted mismatch");
        require(Deployer(deployerProxy).owner() == upgradeSafe, "deployer not owned by upgrade safe");
    }
}
