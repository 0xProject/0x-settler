// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {
    ISafeMinimal,
    EvmVersionDummy,
    ZeroExSettlerDeployerSafeGuardBase,
    ZeroExSettlerDeployerSafeGuardEraVm,
    ZeroExSettlerDeployerSafeGuardOnePointThreeEraVm,
    ZeroExSettlerDeployerSafeGuardOnePointFourPointOneEraVm
} from "src/deployer/SafeGuard.sol";

contract SafeGuardEraVmHarness is ZeroExSettlerDeployerSafeGuardEraVm {
    constructor(ISafeMinimal _safe, bytes32 singletonInithash, bytes32 fallbackInithash, bytes32 multisendInithash)
        ZeroExSettlerDeployerSafeGuardBase(_safe, singletonInithash, fallbackInithash, multisendInithash)
    {}

    function predictCreate2(bytes32 inithash) external view returns (address) {
        return _predictCreate2(inithash);
    }

    function isSupportedFactory(address deployer) external pure returns (bool) {
        return _isSupportedFactory(deployer);
    }

    function isSupportedProxyCodeHash(bytes32 codeHash) external pure returns (bool) {
        return _isSupportedProxyCodeHash(codeHash);
    }

    function evmVersionDummyCreationCodeLength() external pure returns (uint256) {
        return type(EvmVersionDummy).creationCode.length;
    }

    function evmVersionDummyCreationCodeHash() external pure returns (bytes32) {
        return keccak256(type(EvmVersionDummy).creationCode);
    }

    function evmVersionDummyExpectedHash() external pure returns (bytes32) {
        return _EVM_VERSION_DUMMY_INITHASH();
    }
}

contract SafeGuardOnePointThreeEraVmWrapper is ZeroExSettlerDeployerSafeGuardOnePointThreeEraVm {
    constructor(ISafeMinimal _safe) ZeroExSettlerDeployerSafeGuardOnePointThreeEraVm(_safe) {}

    function singletonInithash() external pure returns (bytes32) {
        return _SAFE_SINGLETON_1_3_INITHASH();
    }

    function fallbackInithash() external pure returns (bytes32) {
        return _SAFE_FALLBACK_1_3_INITHASH();
    }

    function multisendInithash() external pure returns (bytes32) {
        return _SAFE_MULTISEND_1_3_INITHASH();
    }

    function predictCreate2(bytes32 inithash) external view returns (address) {
        return _predictCreate2(inithash);
    }

    function isSupportedFactory(address deployer) external pure returns (bool) {
        return _isSupportedFactory(deployer);
    }

    function isSupportedProxyCodeHash(bytes32 codeHash) external pure returns (bool) {
        return _isSupportedProxyCodeHash(codeHash);
    }
}

contract SafeGuardOnePointFourPointOneEraVmWrapper is ZeroExSettlerDeployerSafeGuardOnePointFourPointOneEraVm {
    constructor(ISafeMinimal _safe) ZeroExSettlerDeployerSafeGuardOnePointFourPointOneEraVm(_safe) {}

    function singletonInithash() external pure returns (bytes32) {
        return _SAFE_SINGLETON_1_4_INITHASH();
    }

    function fallbackInithash() external pure returns (bytes32) {
        return _SAFE_FALLBACK_1_4_INITHASH();
    }

    function multisendInithash() external pure returns (bytes32) {
        return _SAFE_MULTISEND_1_4_INITHASH();
    }

    function predictCreate2(bytes32 inithash) external view returns (address) {
        return _predictCreate2(inithash);
    }

    function isSupportedFactory(address deployer) external pure returns (bool) {
        return _isSupportedFactory(deployer);
    }

    function isSupportedProxyCodeHash(bytes32 codeHash) external pure returns (bool) {
        return _isSupportedProxyCodeHash(codeHash);
    }
}
