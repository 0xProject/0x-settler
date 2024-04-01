// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Script} from "forge-std/Script.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";
import {ZeroExSettlerDeployerSafeModule} from "src/deployer/SafeModule.sol";

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

contract DeploySafes is Script {
    address internal constant iceColdCoffee = 0x1CeC01DC0fFEE5eB5aF47DbEc1809F2A7c601C30;

    function run(address safe, ISafeFactory safeFactory, address safeSingleton, address safeFallback) public {
        uint256 deployerKey = vm.envUint("ICECOLDCOFFEE_DEPLOYER_KEY");
        address deployer = vm.addr(deployerKey);
        require(AddressDerivation.deriveContract(deployer, 0) == iceColdCoffee, "private key/deployed address mismatch");
        require(safe.code.length == 0, "safe is already deployed");
        require(vm.getNonce(deployer) == 0, "deployer already has transactions");

        address[] memory owners = new address[](1);
        owners[0] = deployer;
        bytes memory initializer = abi.encodeCall(
            ISafeSetup.setup, (owners, 1, address(0), new bytes(0), safeFallback, address(0), 0, payable(address(0)))
        );
        bytes memory creationCode = safeFactory.proxyCreationCode();
        bytes32 salt = keccak256(bytes.concat(keccak256(initializer), bytes32(0)));
        bytes32 initHash = keccak256(bytes.concat(creationCode, bytes32(uint256(uint160(safeSingleton)))));
        require(
            AddressDerivation.deriveDeterministicContract(address(safeFactory), salt, initHash) == safe,
            "safe address mismatch"
        );

        vm.startBroadcast(deployerKey);

        address deployed = address(new ZeroExSettlerDeployerSafeModule(safe));
        address deployedSafe = safeFactory.createProxyWithNonce(safeSingleton, initializer, 0);

        vm.stopBroadcast();

        require(deployed == iceColdCoffee, "deployment/prediction mismatch");
        require(deployedSafe == safe, "deployed safe/predicted safe mismatch");
    }
}
