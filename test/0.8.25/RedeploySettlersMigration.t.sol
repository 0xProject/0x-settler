// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";

import {RedeploySettlers} from "script/RedeploySettlers.s.sol";
import {SafeMultisend, ISafeFactory, ISafeOwners} from "script/SafeMultisend.sol";
import {SafeBytecodes, load} from "script/SafeCode.sol";

interface ISafe {
    function addOwnerWithThreshold(address owner, uint256 threshold) external;
    function removeOwner(address prevOwner, address owner, uint256 threshold) external;
    function getOwners() external view returns (address[] memory);
    function getThreshold() external view returns (uint256);
    function getStorageAt(uint256 offset, uint256 length) external view returns (bytes memory);
    // `masterCopy()` is implemented by the proxy itself, so it reports the singleton regardless of version.
    function masterCopy() external view returns (address);
}

// Exposes the internal migration helper so the real production code path is exercised (no reimplementation).
contract RedeploySettlersHarness is RedeploySettlers {
    function exposed_migrateUpgradeSafe(
        SafeCompatConfig memory safeCompatConfig,
        address upgradeSafe,
        address safeMigration,
        address safeSingletonV141,
        address safeFallbackV141,
        bytes memory upgradeSignature
    ) external {
        _migrateUpgradeSafe(
            safeCompatConfig, upgradeSafe, safeMigration, safeSingletonV141, safeFallbackV141, upgradeSignature
        );
    }

    function exposed_getOwners(SafeCompatConfig memory safeCompatConfig, address safe)
        external
        returns (address[] memory)
    {
        return _getOwners(safeCompatConfig, ISafeOwners(safe));
    }
}

// Fork test of `RedeploySettlers._migrateUpgradeSafe` against the real Safe v1.3.0 upgrade Safe and the real
// canonical `SafeMigration` contract on Mainnet, at a block before the upgrade Safe was actually migrated.
contract RedeploySettlersMigrationTest is Test {
    // The real upgrade Safe; at the pinned block it is still on Safe v1.3.0.
    address internal constant UPGRADE_SAFE = 0xf36b9f50E59870A24F42F9Ba43b2aD0A4b8f2F51;
    address internal constant V130_SINGLETON = 0xfb1bffC9d739B8D520DaF37dF666da4C687191EA;
    address internal constant V141_SINGLETON = 0x29fcB43b46531BcA003ddC8FCB67FFE91900C762;
    address internal constant V141_FALLBACK = 0xfd0732Dc9E303f09fCEf3a7388Ad10A83459Ec99;
    address internal constant SAFE_MIGRATION = 0x526643F69b81B008F46d95CD5ced5eC0edFFDaC6;
    uint256 internal constant FALLBACK_SLOT = uint256(keccak256("fallback_manager.handler.address"));

    RedeploySettlersHarness internal harness;

    function setUp() public {
        vm.createSelectFork(vm.envString("MAINNET_RPC_URL"), 23183520);
        harness = RedeploySettlersHarness(address(0xdeadbeef));
        vm.etch(address(harness), vm.getDeployedCode("RedeploySettlersMigration.t.sol:RedeploySettlersHarness"));
        vm.allowCheatcodes(address(harness));

        // Reproduce the revive precondition: the upgrade Safe is sole-owned by the caller (here the harness,
        // which is what `execTransaction`s the migration), threshold 1. `addOwnerWithThreshold` prepends the
        // new owner, so the original owners can each be removed with the harness as their predecessor.
        ISafe safe = ISafe(UPGRADE_SAFE);
        address[] memory oldOwners = safe.getOwners();
        vm.startPrank(UPGRADE_SAFE);
        safe.addOwnerWithThreshold(address(harness), 1);
        for (uint256 i; i < oldOwners.length; i++) {
            safe.removeOwner(address(harness), oldOwners[i], 1);
        }
        vm.stopPrank();
    }

    function _signature() internal view returns (bytes memory) {
        // Pre-validated "msg.sender is owner" signature (v=1); valid because the harness both owns the Safe and
        // is the `execTransaction` caller.
        return abi.encodePacked(uint256(uint160(address(harness))), bytes32(0), uint8(1));
    }

    function test_migrateUpgradeSafe_migratesV130ToV141() external {
        ISafe safe = ISafe(UPGRADE_SAFE);
        assertEq(safe.masterCopy(), V130_SINGLETON, "precondition: upgrade Safe is on v1.3.0");

        SafeMultisend.SafeCompatConfig memory safeCompatConfig; // non-EraVm: all-zero/false is sufficient
        harness.exposed_migrateUpgradeSafe(
            safeCompatConfig, UPGRADE_SAFE, SAFE_MIGRATION, V141_SINGLETON, V141_FALLBACK, _signature()
        );

        assertEq(safe.masterCopy(), V141_SINGLETON, "singleton switched to v1.4.1");
        assertEq(
            abi.decode(safe.getStorageAt(FALLBACK_SLOT, 1), (address)), V141_FALLBACK, "fallback switched to v1.4.1"
        );

        // Ownership/threshold must be untouched by the migration.
        address[] memory owners = safe.getOwners();
        assertEq(owners.length, 1, "owner count unchanged");
        assertEq(owners[0], address(harness), "owner unchanged");
        assertEq(safe.getThreshold(), 1, "threshold unchanged");
    }

    function test_migrateUpgradeSafe_revertsOnWrongMigrationContract() external {
        SafeMultisend.SafeCompatConfig memory safeCompatConfig;
        // V130_SINGLETON has a different codehash than the canonical SafeMigration.
        vm.expectRevert(bytes("unexpected SafeMigration codehash"));
        harness.exposed_migrateUpgradeSafe(
            safeCompatConfig, UPGRADE_SAFE, V130_SINGLETON, V141_SINGLETON, V141_FALLBACK, _signature()
        );
    }

    function test_migrateUpgradeSafe_revertsOnFallbackMismatch() external {
        SafeMultisend.SafeCompatConfig memory safeCompatConfig;
        // Correct migration contract and singleton, but a fallback handler it doesn't actually install.
        vm.expectRevert(bytes("SafeMigration fallback mismatch"));
        harness.exposed_migrateUpgradeSafe(
            safeCompatConfig, UPGRADE_SAFE, SAFE_MIGRATION, V141_SINGLETON, address(0xdead), _signature()
        );
    }

    function test_migrateUpgradeSafe_revertsOnSingletonMismatch() external {
        SafeMultisend.SafeCompatConfig memory safeCompatConfig;
        // Correct migration contract, but a target singleton it doesn't actually migrate to.
        vm.expectRevert(bytes("SafeMigration singleton mismatch"));
        harness.exposed_migrateUpgradeSafe(
            safeCompatConfig, UPGRADE_SAFE, SAFE_MIGRATION, address(0xdead), V141_FALLBACK, _signature()
        );
    }
}

// Fork test of the EraVm compatibility wrapper against Abstract's real v1.4.1 upgrade Safe.
contract RedeploySettlersEraVmCompatTest is Test {
    address internal constant UPGRADE_SAFE = 0x0a3ba9036e62df32fAeC7753c3372B4375c6E20A;
    address internal constant V130_SINGLETON = 0x1727c2c531cf966f902E5927b98490fDFb3b2b70;
    address internal constant V130_FACTORY = 0xDAec33641865E4651fB43181C6DB6f7232Ee91c2;
    address internal constant V130_FALLBACK = 0x2f870a80647BbC554F3a0EBD093f11B4d2a7492A;
    address internal constant V130_MULTICALL = 0xf220D3b4DFb23C4ade8C88E526C1353AbAcbC38F;

    function test_getOwners_supportsV141SafeOnEraVm() external {
        vm.createSelectFork(vm.envString("ABSTRACT_MAINNET_RPC_URL"));

        SafeBytecodes memory safeBytecodes;
        safeBytecodes.load(vm);
        safeBytecodes.loadV141(vm);
        SafeMultisend.SafeCompatConfig memory safeCompatConfig = SafeMultisend.SafeCompatConfig({
            isEraVm: true,
            privateKey: 0,
            safeFactory: ISafeFactory(V130_FACTORY),
            safeSingleton: V130_SINGLETON,
            safeFallback: V130_FALLBACK,
            safeMulticall: V130_MULTICALL,
            safeBytecodes: safeBytecodes
        });

        RedeploySettlersHarness harness = RedeploySettlersHarness(address(0xdeadbeef));
        vm.etch(address(harness), vm.getDeployedCode("RedeploySettlersMigration.t.sol:RedeploySettlersHarness"));
        vm.allowCheatcodes(address(harness));
        address[] memory owners = harness.exposed_getOwners(safeCompatConfig, UPGRADE_SAFE);
        assertGt(owners.length, 0);
    }
}
