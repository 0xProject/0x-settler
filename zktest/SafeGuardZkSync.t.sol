// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";

interface ISafeGuardEraVmHarness {
    function predictCreate2(bytes32 inithash) external view returns (address);
    function isSupportedFactory(address deployer) external view returns (bool);
    function isSupportedProxyCodeHash(bytes32 codeHash) external view returns (bool);
    function evmVersionDummyCreationCodeLength() external view returns (uint256);
    function evmVersionDummyCreationCodeHash() external view returns (bytes32);
    function evmVersionDummyExpectedHash() external view returns (bytes32);
}

interface ISafeGuardOnePointThreeEraVmWrapper is ISafeGuardEraVmHarness {
    function singletonInithash() external view returns (bytes32);
    function fallbackInithash() external view returns (bytes32);
    function multisendInithash() external view returns (bytes32);
}

interface ISafeGuardOnePointFourPointOneEraVmWrapper is ISafeGuardEraVmHarness {
    function singletonInithash() external view returns (bytes32);
    function fallbackInithash() external view returns (bytes32);
    function multisendInithash() external view returns (bytes32);
}

contract TestSafeGuardZkSyncArtifacts is Test {
    address internal constant eraVmFactory = 0xaECDbB0a3B1C6D1Fe1755866e330D82eC81fD4FD;

    address internal constant safeSingleton1_3EraVm = 0x1727c2c531cf966f902E5927b98490fDFb3b2b70;
    address internal constant fallback1_3EraVm = 0x2f870a80647BbC554F3a0EBD093f11B4d2a7492A;
    address internal constant multicall1_3EraVm = 0xf220D3b4DFb23C4ade8C88E526C1353AbAcbC38F;
    address internal constant safeSingleton1_4EraVm = 0x610fcA2e0279Fa1F8C00c8c2F71dF522AD469380;
    address internal constant fallback1_4EraVm = 0x9301E98DD367135f21bdF66f342A249c9D5F9069;
    address internal constant multicall1_4EraVm = 0x0408EF011960d02349d50286D20531229BCef773;

    bytes32 internal constant safeSingleton1_3EraVmInitHash =
        0x0100080f935a1a562e892e1e71d9a0ca8cd349d19a413e0b7e7172c5e8c83ed1;
    bytes32 internal constant fallback1_3EraVmInitHash =
        0x010002416a25dcb4ee218297a41538dde5937bbf8b64e5d3656217e27fd04d19;
    bytes32 internal constant multicall1_3EraVmInitHash =
        0x0100002daeda170fa43cc4e00e452a18debfe54f988fa3484ab08e7f22ee79d5;
    bytes32 internal constant safeSingleton1_4EraVmInitHash =
        0x010006c19437ff25b448f038f7ea0a4c910e0ae9cd8e55f2d199b7916b72eb1e;
    bytes32 internal constant fallback1_4EraVmInitHash =
        0x01000227ab67505fb2fa65c81aceddb0a46ddbf3b974583188beda4c5e90417c;
    bytes32 internal constant multicall1_4EraVmInitHash =
        0x0100002f5fb8e4746cf6c3f70d2aba9d82d3f2045150860e9cfb7a336caa9690;

    bytes32 internal constant proxyCodeHash1_3EraVm =
        0x0100004124426fb9ebb25e27d670c068e52f9ba631bd383279a188be47e3f86d;
    bytes32 internal constant proxyCodeHash1_4EraVm =
        0x0100003b6cfa15bd7d1cae1c9c022074524d7785d34859ad0576d8fab4305d4f;
    bytes32 internal constant proxyRuntimeKeccakEraVm =
        0x3d70c4a51cf0b92f04e5e281833aeece55198933569c08f5d11fcc45c495253e;
    bytes32 internal constant evmVersionDummyEraVmCreationCodeHash =
        0xfce4b7826969737d1006560c768bc061ede964f30aea2c10743c4abd11f1ae3b;

    function _etchHarness(string memory artifactPath, string memory label) private returns (address target) {
        target = makeAddr(label);
        vm.etch(target, vm.getCode(artifactPath));
    }

    function testGetCodeLoadsPrebuiltGuardArtifact() external view {
        bytes memory creationCode =
            vm.getCode("zkout/SafeGuard.sol/ZeroExSettlerDeployerSafeGuardOnePointThreeEraVm.json");
        assertGt(creationCode.length, 0);
    }

    function testEraVmDummyHashMatchesZkCreationCodeDescriptor() external {
        ISafeGuardEraVmHarness harness = ISafeGuardEraVmHarness(
            _etchHarness("zkout/SafeGuardWrappers.sol/SafeGuardEraVmHarness.json", "SafeGuardEraVmHarness")
        );
        bytes memory artifactCreationCode = vm.getCode("zkout/SafeGuard.sol/EvmVersionDummy.json");

        assertGt(artifactCreationCode.length, harness.evmVersionDummyCreationCodeLength());
        assertEq(harness.evmVersionDummyCreationCodeLength(), 0x84);
        assertEq(harness.evmVersionDummyCreationCodeHash(), evmVersionDummyEraVmCreationCodeHash);
        assertEq(harness.evmVersionDummyExpectedHash(), evmVersionDummyEraVmCreationCodeHash);
        assertTrue(keccak256(artifactCreationCode) != evmVersionDummyEraVmCreationCodeHash);
    }

    function testEraVmCreate2FormulaMatchesKnownAddresses() external pure {
        assertEq(_deriveEraVmContract(eraVmFactory, safeSingleton1_3EraVmInitHash), safeSingleton1_3EraVm);
        assertEq(_deriveEraVmContract(eraVmFactory, fallback1_3EraVmInitHash), fallback1_3EraVm);
        assertEq(_deriveEraVmContract(eraVmFactory, multicall1_3EraVmInitHash), multicall1_3EraVm);
        assertEq(_deriveEraVmContract(eraVmFactory, safeSingleton1_4EraVmInitHash), safeSingleton1_4EraVm);
        assertEq(_deriveEraVmContract(eraVmFactory, fallback1_4EraVmInitHash), fallback1_4EraVm);
        assertEq(_deriveEraVmContract(eraVmFactory, multicall1_4EraVmInitHash), multicall1_4EraVm);
    }

    function testEraVmHarnessAcceptsEraVmFactoryAndProxyCodeHashes() external {
        ISafeGuardEraVmHarness harness = ISafeGuardEraVmHarness(
            _etchHarness("zkout/SafeGuardWrappers.sol/SafeGuardEraVmHarness.json", "SafeGuardEraVmHarness")
        );

        assertTrue(harness.isSupportedFactory(eraVmFactory));
        assertTrue(harness.isSupportedProxyCodeHash(proxyCodeHash1_3EraVm));
        assertTrue(harness.isSupportedProxyCodeHash(proxyCodeHash1_4EraVm));
        assertFalse(harness.isSupportedProxyCodeHash(proxyRuntimeKeccakEraVm));

        vm.startPrank(eraVmFactory);
        assertEq(harness.predictCreate2(safeSingleton1_3EraVmInitHash), safeSingleton1_3EraVm);
        assertEq(harness.predictCreate2(fallback1_3EraVmInitHash), fallback1_3EraVm);
        assertEq(harness.predictCreate2(multicall1_3EraVmInitHash), multicall1_3EraVm);
        vm.stopPrank();
    }

    function testOnePointThreeEraVmWrapperExposesExpectedInithashesAndDerivations() external {
        ISafeGuardOnePointThreeEraVmWrapper wrapper = ISafeGuardOnePointThreeEraVmWrapper(
            _etchHarness(
                "zkout/SafeGuardWrappers.sol/SafeGuardOnePointThreeEraVmWrapper.json",
                "SafeGuardOnePointThreeEraVmWrapper"
            )
        );

        assertEq(wrapper.singletonInithash(), safeSingleton1_3EraVmInitHash);
        assertEq(wrapper.fallbackInithash(), fallback1_3EraVmInitHash);
        assertEq(wrapper.multisendInithash(), multicall1_3EraVmInitHash);
        assertTrue(wrapper.isSupportedFactory(eraVmFactory));
        assertTrue(wrapper.isSupportedProxyCodeHash(proxyCodeHash1_3EraVm));
        assertTrue(wrapper.isSupportedProxyCodeHash(proxyCodeHash1_4EraVm));
        assertFalse(wrapper.isSupportedProxyCodeHash(proxyRuntimeKeccakEraVm));

        vm.startPrank(eraVmFactory);
        assertEq(wrapper.predictCreate2(wrapper.singletonInithash()), safeSingleton1_3EraVm);
        assertEq(wrapper.predictCreate2(wrapper.fallbackInithash()), fallback1_3EraVm);
        assertEq(wrapper.predictCreate2(wrapper.multisendInithash()), multicall1_3EraVm);
        vm.stopPrank();
    }

    function testOnePointFourPointOneEraVmWrapperExposesExpectedInithashesAndDerivations() external {
        ISafeGuardOnePointFourPointOneEraVmWrapper wrapper = ISafeGuardOnePointFourPointOneEraVmWrapper(
            _etchHarness(
                "zkout/SafeGuardWrappers.sol/SafeGuardOnePointFourPointOneEraVmWrapper.json",
                "SafeGuardOnePointFourPointOneEraVmWrapper"
            )
        );

        assertEq(wrapper.singletonInithash(), safeSingleton1_4EraVmInitHash);
        assertEq(wrapper.fallbackInithash(), fallback1_4EraVmInitHash);
        assertEq(wrapper.multisendInithash(), multicall1_4EraVmInitHash);
        assertTrue(wrapper.isSupportedFactory(eraVmFactory));
        assertTrue(wrapper.isSupportedProxyCodeHash(proxyCodeHash1_3EraVm));
        assertTrue(wrapper.isSupportedProxyCodeHash(proxyCodeHash1_4EraVm));
        assertFalse(wrapper.isSupportedProxyCodeHash(proxyRuntimeKeccakEraVm));

        vm.startPrank(eraVmFactory);
        assertEq(wrapper.predictCreate2(wrapper.singletonInithash()), safeSingleton1_4EraVm);
        assertEq(wrapper.predictCreate2(wrapper.fallbackInithash()), fallback1_4EraVm);
        assertEq(wrapper.predictCreate2(wrapper.multisendInithash()), multicall1_4EraVm);
        vm.stopPrank();
    }

    function _deriveEraVmContract(address deployer, bytes32 inithash) private pure returns (address) {
        return address(
            uint160(
                uint256(
                    keccak256(
                        bytes.concat(
                            keccak256("zksyncCreate2"),
                            bytes32(uint256(uint160(deployer))),
                            bytes32(0),
                            inithash,
                            keccak256("")
                        )
                    )
                )
            )
        );
    }
}
