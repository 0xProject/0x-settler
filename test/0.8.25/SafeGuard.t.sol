// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {Vm} from "@forge-std/Vm.sol";

import {
    ISafeMinimal as ISafeMinimalInternal,
    ZeroExSettlerDeployerSafeGuardBase,
    ZeroExSettlerDeployerSafeGuardOnePointThreeEraVm,
    ZeroExSettlerDeployerSafeGuardOnePointFourPointOneEraVm
} from "src/deployer/SafeGuard.sol";
import {ItoA} from "src/utils/ItoA.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";

interface ISafeSetup {
    function addOwnerWithThreshold(address owner, uint256 _threshold) external;

    function removeOwner(address prevOwner, address owner, uint256 _threshold) external;

    function getOwners() external view returns (address[] memory);

    function setGuard(address guard) external;

    function setFallbackHandler(address handler) external;
}

enum Operation {
    Call,
    DelegateCall
}

interface ISafe {
    function execTransaction(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        uint256 safeTxGas,
        uint256 baseGas,
        uint256 gasPrice,
        address gasToken,
        address payable refundReceiver,
        bytes memory signatures
    ) external payable returns (bool);

    event ExecutionFailure(bytes32 txHash, uint256 payment);

    event ExecutionSuccess(bytes32 txHash, uint256 payment);

    function nonce() external view returns (uint256);

    function approveHash(bytes32 hashToApprove) external;

    event ApproveHash(bytes32 indexed approvedHash, address indexed owner);

    function isOwner(address) external view returns (bool);

    function enableModule(address) external;

    function getStorageAt(uint256 offset, uint256 length) external view returns (bytes memory);

    function masterCopy() external view returns (address);
}

interface ISafeOnePointFour {
    // `txHash` argument is indexed in 1.4
    event ExecutionSuccess(bytes32 indexed txHash, uint256 payment);
}

interface IGuard {
    function checkTransaction(
        address to,
        uint256 value,
        bytes memory data,
        Operation operation,
        uint256 safeTxGas,
        uint256 baseGas,
        uint256 gasPrice,
        address gasToken,
        address payable refundReceiver,
        bytes memory signatures,
        address msgSender
    ) external;

    function checkAfterExecution(bytes32 txHash, bool success) external;
}

interface IZeroExSettlerDeployerSafeGuard is IGuard {
    event TimelockUpdated(uint256 oldDelay, uint256 newDelay);
    event SafeTransactionEnqueued(
        bytes32 indexed txHash,
        uint256 timelockEnd,
        address indexed to,
        uint256 value,
        bytes data,
        Operation operation,
        uint256 safeTxGas,
        uint256 baseGas,
        uint256 gasPrice,
        address gasToken,
        address payable refundReceiver,
        uint256 indexed nonce,
        bytes signatures
    );
    event SafeTransactionCanceled(bytes32 indexed txHash, address indexed canceledBy);
    event ResignTxHash(bytes32 indexed txHash);
    event LockDown(address indexed lockedDownBy, bytes32 indexed unlockTxHash);
    event Unlocked();

    error PermissionDenied();
    error NoDelegateCall();
    error GuardNotInstalled();
    error GuardIsOwner();
    error TimelockNotElapsed(bytes32 txHash, uint256 timelockEnd);
    error TimelockElapsed(bytes32 txHash, uint256 timelockEnd);
    error AlreadyQueued(bytes32 txHash);
    error NotQueued(bytes32 txHash);
    error LockedDown(address lockedDownBy);
    error NotLockedDown();
    error UnexpectedUpgrade(address newSingleton);
    error Reentrancy();
    error ModuleInstalled(address module);
    error NotEnoughOwners(uint256 ownerCount);
    error ThresholdTooLow(uint256 threshold);
    error NotUnanimous(bytes32 txHash);
    error TxHashNotApproved(bytes32 txHash);

    function timelockEnd(bytes32) external view returns (uint256);
    function lockedDownBy() external view returns (address);
    function delay() external view returns (uint24);
    function safe() external view returns (address);

    function enqueue(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        uint256 safeTxGas,
        uint256 baseGas,
        uint256 gasPrice,
        address gasToken,
        address payable refundReceiver,
        uint256 nonce,
        bytes calldata signatures
    ) external;

    function setDelay(uint24) external;

    function resignTxHash(address owner) external view returns (bytes32);

    function cancel(bytes32 txHash) external;

    function unlockTxHash() external view returns (bytes32);

    function lockDown() external;

    function unlock() external;
}

interface IMulticall {
    function multiSend(bytes memory transactions) external payable;
}

contract MigrationDummy {
    address private singleton;

    function migrate(address newSingleton, address newFallbackHandler) external {
        singleton = newSingleton;
        ISafeSetup(address(this)).setFallbackHandler(newFallbackHandler);
    }
}

contract SafeGuardHarness is ZeroExSettlerDeployerSafeGuardBase {
    constructor(
        ISafeMinimalInternal _safe,
        bytes32 singletonInithash,
        bytes32 fallbackInithash,
        bytes32 multisendInithash
    ) ZeroExSettlerDeployerSafeGuardBase(_safe, singletonInithash, fallbackInithash, multisendInithash) {}

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

contract SafeGuardOnePointThreeEraVmWrapper is ZeroExSettlerDeployerSafeGuardOnePointThreeEraVm {
    constructor(ISafeMinimalInternal _safe) ZeroExSettlerDeployerSafeGuardOnePointThreeEraVm(_safe) {}

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
    constructor(ISafeMinimalInternal _safe) ZeroExSettlerDeployerSafeGuardOnePointFourPointOneEraVm(_safe) {}

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

contract TestSafeGuardZkSync is Test {
    address internal constant evmFactory = 0x914d7Fec6aaC8cd542e72Bca78B30650d45643d7;
    address internal constant eraVmFactory = 0xaECDbB0a3B1C6D1Fe1755866e330D82eC81fD4FD;

    bytes32 internal constant safeSingleton1_3InitHash =
        0x49f30800a6ac5996a48b80c47ff20f19f8728812498a2a7fe75a14864fab6438;
    bytes32 internal constant fallback1_3InitHash = 0x272190de126b4577e187d9f00b9ca5daeae76d771965d734876891a51f9c43d8;
    bytes32 internal constant multicall1_3InitHash = 0x35e699c3e43ec3e03a101730ab916c5e540893eaaf806451e929d138c3ff53b7;
    bytes32 internal constant safeSingleton1_4InitHash =
        0x3555bd3ee95b1c6605c602740d71efaf200068e0395ccd701ac82ab8e42307bd;
    bytes32 internal constant fallback1_4InitHash = 0x5a63128db658d8601220c014848acd6c27b855a0427f0181eb3ba8c25e2d3e95;
    bytes32 internal constant multicall1_4InitHash = 0xa7934433f19155c708af2674b14c6c8b591fedbed7b01ce8cf64014f307468a0;

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

    function _etchOnePointThreeEraVmWrapper() private returns (SafeGuardOnePointThreeEraVmWrapper wrapper) {
        address target = makeAddr("SafeGuardOnePointThreeEraVmWrapper");
        vm.etch(target, vm.getDeployedCode("SafeGuard.t.sol:SafeGuardOnePointThreeEraVmWrapper"));
        return SafeGuardOnePointThreeEraVmWrapper(target);
    }

    function _etchOnePointFourPointOneEraVmWrapper()
        private
        returns (SafeGuardOnePointFourPointOneEraVmWrapper wrapper)
    {
        address target = makeAddr("SafeGuardOnePointFourPointOneEraVmWrapper");
        vm.etch(target, vm.getDeployedCode("SafeGuard.t.sol:SafeGuardOnePointFourPointOneEraVmWrapper"));
        return SafeGuardOnePointFourPointOneEraVmWrapper(target);
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

    function testAddressSelectionStillUsesCreate2OnEvm() external {
        vm.startPrank(evmFactory);
        SafeGuardHarness harness = new SafeGuardHarness(
            ISafeMinimalInternal(address(0)), safeSingleton1_3InitHash, fallback1_3InitHash, multicall1_3InitHash
        );

        assertEq(
            harness.predictCreate2(safeSingleton1_3InitHash),
            AddressDerivation.deriveDeterministicContract(evmFactory, bytes32(0), safeSingleton1_3InitHash)
        );
        assertEq(
            harness.predictCreate2(fallback1_3InitHash),
            AddressDerivation.deriveDeterministicContract(evmFactory, bytes32(0), fallback1_3InitHash)
        );
        assertEq(
            harness.predictCreate2(multicall1_3InitHash),
            AddressDerivation.deriveDeterministicContract(evmFactory, bytes32(0), multicall1_3InitHash)
        );
        vm.stopPrank();
    }

    function testEraVmCreate2FormulaMatchesKnownAddresses() external pure {
        assertEq(_deriveEraVmContract(eraVmFactory, safeSingleton1_3EraVmInitHash), safeSingleton1_3EraVm);
        assertEq(_deriveEraVmContract(eraVmFactory, fallback1_3EraVmInitHash), fallback1_3EraVm);
        assertEq(_deriveEraVmContract(eraVmFactory, multicall1_3EraVmInitHash), multicall1_3EraVm);
        assertEq(_deriveEraVmContract(eraVmFactory, safeSingleton1_4EraVmInitHash), safeSingleton1_4EraVm);
        assertEq(_deriveEraVmContract(eraVmFactory, fallback1_4EraVmInitHash), fallback1_4EraVm);
        assertEq(_deriveEraVmContract(eraVmFactory, multicall1_4EraVmInitHash), multicall1_4EraVm);
    }

    function testBaseHarnessRejectsEraVmFactoryAndProxyCodeHashes() external {
        vm.prank(evmFactory);
        SafeGuardHarness harness = new SafeGuardHarness(
            ISafeMinimalInternal(address(0)), safeSingleton1_3InitHash, fallback1_3InitHash, multicall1_3InitHash
        );

        assertFalse(harness.isSupportedFactory(eraVmFactory));
        assertFalse(harness.isSupportedProxyCodeHash(proxyCodeHash1_3EraVm));
        assertFalse(harness.isSupportedProxyCodeHash(proxyCodeHash1_4EraVm));
        assertFalse(harness.isSupportedProxyCodeHash(proxyRuntimeKeccakEraVm));
    }

    function testOnePointThreeEraVmWrapperExposesExpectedInithashesAndDerivations() external {
        SafeGuardOnePointThreeEraVmWrapper wrapper = _etchOnePointThreeEraVmWrapper();

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
        SafeGuardOnePointFourPointOneEraVmWrapper wrapper = _etchOnePointFourPointOneEraVmWrapper();

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
}

contract TestSafeGuard is Test {
    using ItoA for uint256;

    address internal constant factory = 0x914d7Fec6aaC8cd542e72Bca78B30650d45643d7;
    ISafe internal constant safe = ISafe(0xf36b9f50E59870A24F42F9Ba43b2aD0A4b8f2F51);
    address internal constant onePointThreeSingleton = 0xfb1bffC9d739B8D520DaF37dF666da4C687191EA;
    IZeroExSettlerDeployerSafeGuard internal guard;
    uint256 internal pokeCounter;

    Vm.Wallet[] internal owners;

    function setUp() public {
        ISafeSetup _safe = ISafeSetup(address(safe));

        vm.createSelectFork(vm.envString("MAINNET_RPC_URL"), 23183520);
        vm.label(address(this), "FoundryTest");

        string memory mnemonic = "test test test test test test test test test test test junk";
        address[] memory oldOwners = _safe.getOwners();

        for (uint256 i; i < oldOwners.length + 1; i++) {
            owners.push(vm.createWallet(vm.deriveKey(mnemonic, uint32(i)), string.concat("Owner #", i.itoa())));
        }

        vm.startPrank(address(_safe));
        for (uint256 i; i < owners.length; i++) {
            _safe.addOwnerWithThreshold(owners[i].addr, 2);
        }
        for (uint256 i = 0; i < oldOwners.length; i++) {
            _safe.removeOwner(owners[0].addr, oldOwners[i], 2);
        }
        vm.stopPrank();

        bytes memory creationCode = bytes.concat(
            vm.getCode("SafeGuard.sol:ZeroExSettlerDeployerSafeGuardOnePointThree"),
            abi.encode(0xf36b9f50E59870A24F42F9Ba43b2aD0A4b8f2F51)
        );
        guard = IZeroExSettlerDeployerSafeGuard(
            AddressDerivation.deriveDeterministicContract(factory, bytes32(0), keccak256(creationCode))
        );

        vm.prank(address(_safe));
        _safe.setGuard(address(guard));

        (bool success, bytes memory returndata) = factory.call(bytes.concat(bytes32(0), creationCode));
        assertTrue(success);
        assertEq(address(uint160(bytes20(returndata))), address(guard));

        vm.prank(address(_safe));
        guard.setDelay(uint24(1 weeks));

        // Heck yeah, bubble sort
        {
            Vm.Wallet memory tmp;
            for (uint256 i = 1; i < owners.length; i++) {
                for (uint256 j = i; j > 0; j--) {
                    if (owners[j - 1].addr > owners[j].addr) {
                        tmp = owners[j - 1];
                        owners[j - 1] = owners[j];
                        owners[j] = tmp;
                    }
                }
            }
            for (uint256 i; i < owners.length - 1; i++) {
                assertLt(uint160(owners[i].addr), uint160(owners[i + 1].addr));
            }
        }
    }

    function poke() external returns (uint256) {
        require(msg.sender == address(safe));
        return ++pokeCounter;
    }

    function _signSafeEncoded(Vm.Wallet storage signer, bytes32 hash) internal returns (bytes memory) {
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(signer, hash);
        return abi.encodePacked(r, s, v);
    }

    function _enqueuePoke()
        internal
        returns (
            address to,
            uint256 value,
            bytes memory data,
            Operation operation,
            uint256 safeTxGas,
            uint256 baseGas,
            uint256 gasPrice,
            address gasToken,
            address payable refundReceiver,
            uint256 nonce,
            bytes32 txHash,
            bytes memory signatures
        )
    {
        to = address(this);
        value = 0 ether;
        data = abi.encodeCall(this.poke, ());
        operation = Operation.Call;
        safeTxGas = 0;
        baseGas = 0;
        gasPrice = 0;
        gasToken = address(0);
        refundReceiver = payable(address(0));
        nonce = safe.nonce();

        txHash = keccak256(
            bytes.concat(
                hex"1901",
                keccak256(
                    abi.encode(
                        keccak256("EIP712Domain(uint256 chainId,address verifyingContract)"), block.chainid, safe
                    )
                ),
                keccak256(
                        abi.encode(
                            keccak256(
                                "SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)"
                            ),
                            to,
                            value,
                            keccak256(data),
                            operation,
                            safeTxGas,
                            baseGas,
                            gasPrice,
                            gasToken,
                            refundReceiver,
                            nonce
                        )
                    )
            )
        );

        signatures = abi.encodePacked(_signSafeEncoded(owners[0], txHash), _signSafeEncoded(owners[1], txHash));

        vm.expectEmit(true, true, true, true, address(guard));
        emit IZeroExSettlerDeployerSafeGuard.SafeTransactionEnqueued(
            txHash,
            guard.delay() + vm.getBlockTimestamp(),
            to,
            value,
            data,
            operation,
            safeTxGas,
            baseGas,
            gasPrice,
            gasToken,
            refundReceiver,
            nonce,
            signatures
        );

        guard.enqueue(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, nonce, signatures
        );
    }

    function testHappyPath() public {
        address singleton = safe.masterCopy();
        assertEq(
            abi.decode(safe.getStorageAt(uint256(keccak256("guard_manager.guard.address")), 1), (address)),
            address(guard)
        );
        (
            address to,
            uint256 value,
            bytes memory data,
            Operation operation,
            uint256 safeTxGas,
            uint256 baseGas,
            uint256 gasPrice,
            address gasToken,
            address payable refundReceiver,,
            bytes32 txHash,
            bytes memory signatures
        ) = _enqueuePoke();

        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        vm.expectCall(
            address(guard),
            abi.encodeCall(
                guard.checkTransaction,
                (
                    to,
                    value,
                    data,
                    operation,
                    safeTxGas,
                    baseGas,
                    gasPrice,
                    gasToken,
                    refundReceiver,
                    signatures,
                    address(this)
                )
            )
        );
        vm.expectCall(address(guard), abi.encodeCall(guard.checkAfterExecution, (txHash, true)));
        vm.expectEmit(true, true, true, true, address(safe));
        if (singleton == onePointThreeSingleton) {
            emit ISafe.ExecutionSuccess(txHash, 0);
        } else {
            emit ISafeOnePointFour.ExecutionSuccess(txHash, 0);
        }
        safe.execTransaction(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, signatures
        );

        assertEq(pokeCounter, 1);
    }

    function testTimelockNonExpiry() external {
        (
            address to,
            uint256 value,
            bytes memory data,
            Operation operation,
            uint256 safeTxGas,
            uint256 baseGas,
            uint256 gasPrice,
            address gasToken,
            address payable refundReceiver,,
            bytes32 txHash,
            bytes memory signatures
        ) = _enqueuePoke();

        vm.warp(vm.getBlockTimestamp() + guard.delay());

        vm.expectRevert(
            abi.encodeWithSelector(
                IZeroExSettlerDeployerSafeGuard.TimelockNotElapsed.selector, txHash, vm.getBlockTimestamp()
            )
        );
        safe.execTransaction(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, signatures
        );
    }

    function testCancelHappyPath() external {
        (
            address to,
            uint256 value,
            bytes memory data,
            Operation operation,
            uint256 safeTxGas,
            uint256 baseGas,
            uint256 gasPrice,
            address gasToken,
            address payable refundReceiver,,
            bytes32 txHash,
            bytes memory signatures
        ) = _enqueuePoke();

        address owner = owners[owners.length - 1].addr;

        bytes32 resignTxHash = guard.resignTxHash(owner);

        vm.startPrank(owner);

        vm.expectEmit(true, true, true, true, address(safe));
        emit ISafe.ApproveHash(resignTxHash, owner);
        safe.approveHash(resignTxHash);

        vm.expectEmit(true, true, true, true, address(guard));
        emit IZeroExSettlerDeployerSafeGuard.ResignTxHash(resignTxHash);
        vm.expectEmit(true, true, true, true, address(guard));
        emit IZeroExSettlerDeployerSafeGuard.SafeTransactionCanceled(txHash, owner);
        guard.cancel(txHash);

        vm.stopPrank();

        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        vm.expectRevert(
            abi.encodeWithSelector(
                IZeroExSettlerDeployerSafeGuard.TimelockNotElapsed.selector, txHash, type(uint256).max
            )
        );
        safe.execTransaction(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, signatures
        );
    }

    function testCancelNoApprove() external {
        (,,,,,,,,,, bytes32 txHash,) = _enqueuePoke();

        bytes32 resignTxHash = guard.resignTxHash(owners[3].addr);

        vm.prank(owners[3].addr);
        vm.expectRevert(
            abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.TxHashNotApproved.selector, resignTxHash)
        );
        guard.cancel(txHash);
    }

    function testCancelNotOwner() external {
        (,,,,,,,,,, bytes32 txHash,) = _enqueuePoke();

        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.PermissionDenied.selector));
        guard.cancel(txHash);
    }

    function testLockDownHappyPath()
        public
        returns (
            address to,
            uint256 value,
            bytes memory data,
            Operation operation,
            uint256 safeTxGas,
            uint256 baseGas,
            uint256 gasPrice,
            address gasToken,
            address payable refundReceiver,
            bytes32 txHash,
            bytes memory signatures
        )
    {
        (
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver,, txHash, signatures
        ) = _enqueuePoke();

        bytes32 unlockTxHash = guard.unlockTxHash();

        vm.startPrank(owners[3].addr);

        vm.expectEmit(true, true, true, true, address(safe));
        emit ISafe.ApproveHash(unlockTxHash, owners[3].addr);
        safe.approveHash(unlockTxHash);

        vm.expectEmit(true, true, true, true, address(guard));
        emit IZeroExSettlerDeployerSafeGuard.LockDown(owners[3].addr, unlockTxHash);
        guard.lockDown();

        vm.stopPrank();

        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.LockedDown.selector, owners[3].addr));
        safe.execTransaction(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, signatures
        );
    }

    function testLockDownNoUnlock() external {
        bytes32 unlockTxHash = guard.unlockTxHash();

        vm.prank(owners[3].addr);

        vm.expectRevert(
            abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.TxHashNotApproved.selector, unlockTxHash)
        );
        guard.lockDown();
    }

    function testLockDownNoCancel() external {
        (,,,,,,,,,, bytes32 txHash,) = _enqueuePoke();

        address owner = owners[3].addr;

        bytes32 resignTxHash = guard.resignTxHash(owner);
        bytes32 unlockTxHash = guard.unlockTxHash();

        vm.startPrank(owner);
        safe.approveHash(resignTxHash);
        guard.cancel(txHash);
        safe.approveHash(unlockTxHash);
        vm.stopPrank();

        bytes32 newResignTxHash = guard.resignTxHash(owner);
        assertNotEq(resignTxHash, newResignTxHash);

        vm.prank(owner);
        vm.expectRevert(
            abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.TxHashNotApproved.selector, newResignTxHash)
        );
        guard.lockDown();
    }

    function testLockDownWithCancel() external {
        (,,,,,,,,,, bytes32 txHash,) = _enqueuePoke();

        address owner = owners[3].addr;

        bytes32 resignTxHash = guard.resignTxHash(owner);
        bytes32 unlockTxHash = guard.unlockTxHash();

        vm.startPrank(owner);
        safe.approveHash(resignTxHash);
        guard.cancel(txHash);
        safe.approveHash(unlockTxHash);
        vm.stopPrank();

        bytes32 newResignTxHash = guard.resignTxHash(owner);
        assertNotEq(resignTxHash, newResignTxHash);

        vm.startPrank(owner);
        safe.approveHash(newResignTxHash);
        guard.lockDown();
        vm.stopPrank();
    }

    function testResign() external {
        (,,,,,,,,,, bytes32 txHash,) = _enqueuePoke();

        address owner = owners[3].addr;

        bytes32 resignTxHash = guard.resignTxHash(owner);

        vm.startPrank(owner);
        safe.approveHash(resignTxHash);
        guard.cancel(txHash);
        vm.stopPrank();

        address prevOwner = owners[0].addr;

        bytes memory data = abi.encodeWithSignature("removeOwner(address,address,uint256)", prevOwner, owner, 2);
        txHash = keccak256(
            bytes.concat(
                hex"1901",
                keccak256(
                    abi.encode(
                        keccak256("EIP712Domain(uint256 chainId,address verifyingContract)"), block.chainid, safe
                    )
                ),
                keccak256(
                        abi.encode(
                            keccak256(
                                "SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)"
                            ),
                            safe,
                            0,
                            keccak256(data),
                            Operation.Call,
                            0,
                            0,
                            0,
                            address(0),
                            payable(address(0)),
                            safe.nonce()
                        )
                    )
            )
        );
        assertEq(txHash, resignTxHash);

        bytes memory signatures = abi.encodePacked(
            _signSafeEncoded(owners[0], txHash), bytes32(uint256(uint160(owner))), bytes32(0), uint8(1)
        );
        guard.enqueue(
            address(safe), 0, data, Operation.Call, 0, 0, 0, address(0), payable(address(0)), safe.nonce(), signatures
        );

        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        vm.expectEmit(true, true, true, true, address(safe));
        emit ISafe.ExecutionSuccess(txHash, 0);
        safe.execTransaction(
            address(safe), 0, data, Operation.Call, 0, 0, 0, address(0), payable(address(0)), signatures
        );

        assertFalse(safe.isOwner(owner));
    }

    function testInstallModule() external {
        bytes memory data = abi.encodeCall(safe.enableModule, (address(this)));
        bytes32 txHash = keccak256(
            bytes.concat(
                hex"1901",
                keccak256(
                    abi.encode(
                        keccak256("EIP712Domain(uint256 chainId,address verifyingContract)"), block.chainid, safe
                    )
                ),
                keccak256(
                        abi.encode(
                            keccak256(
                                "SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)"
                            ),
                            safe,
                            0 ether,
                            keccak256(data),
                            Operation.Call,
                            0,
                            0,
                            0 gwei,
                            address(0),
                            payable(address(0)),
                            safe.nonce()
                        )
                    )
            )
        );

        bytes memory signatures =
            abi.encodePacked(_signSafeEncoded(owners[0], txHash), _signSafeEncoded(owners[1], txHash));

        guard.enqueue(
            address(safe),
            0 ether,
            data,
            Operation.Call,
            0,
            0,
            0 gwei,
            address(0),
            payable(address(0)),
            safe.nonce(),
            signatures
        );
        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        vm.expectRevert(abi.encodeWithSignature("ModuleInstalled(address)", address(this)));
        safe.execTransaction(
            address(safe), 0 ether, data, Operation.Call, 0, 0, 0 gwei, address(0), payable(address(0)), signatures
        );
    }

    function testUnlockHappyPath() external {
        (
            address to,
            uint256 value,
            bytes memory data,
            Operation operation,
            uint256 safeTxGas,
            uint256 baseGas,
            uint256 gasPrice,
            address gasToken,
            address payable refundReceiver,,
            bytes memory signatures
        ) = testLockDownHappyPath();

        {
            address unlockTo = address(guard);
            uint256 unlockValue = 0 ether;
            bytes memory unlockData = abi.encodeCall(guard.unlock, ());
            Operation unlockOperation = Operation.Call;
            uint256 unlockSafeTxGas = 0;
            uint256 unlockBaseGas = 0;
            uint256 unlockGasPrice = 0;
            address unlockGasToken = address(0);
            address payable unlockRefundReceiver = payable(address(0));

            bytes32 unlockTxHash = keccak256(
                bytes.concat(
                    hex"1901",
                    keccak256(
                        abi.encode(
                            keccak256("EIP712Domain(uint256 chainId,address verifyingContract)"), block.chainid, safe
                        )
                    ),
                    keccak256(
                        abi.encode(
                            keccak256(
                                "SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)"
                            ),
                            unlockTo,
                            unlockValue,
                            keccak256(unlockData),
                            unlockOperation,
                            unlockSafeTxGas,
                            unlockBaseGas,
                            unlockGasPrice,
                            unlockGasToken,
                            unlockRefundReceiver,
                            safe.nonce()
                        )
                    )
                )
            );

            bytes memory unlockSignatures = abi.encodePacked(
                _signSafeEncoded(owners[0], unlockTxHash),
                _signSafeEncoded(owners[1], unlockTxHash),
                _signSafeEncoded(owners[2], unlockTxHash),
                uint256(uint160(owners[3].addr)),
                bytes32(0),
                uint8(1),
                _signSafeEncoded(owners[4], unlockTxHash)
            );

            vm.expectEmit(true, true, true, true, address(safe));
            emit ISafe.ExecutionSuccess(unlockTxHash, 0);
            safe.execTransaction(
                unlockTo,
                unlockValue,
                unlockData,
                unlockOperation,
                unlockSafeTxGas,
                unlockBaseGas,
                unlockGasPrice,
                unlockGasToken,
                unlockRefundReceiver,
                unlockSignatures
            );
        }

        vm.expectRevert("GS026");
        safe.execTransaction(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, signatures
        );

        testHappyPath();
    }

    function testUnlockNotUnanimous() external {
        testLockDownHappyPath();

        address unlockTo = address(guard);
        uint256 unlockValue = 0 ether;
        bytes memory unlockData = abi.encodeCall(guard.unlock, ());
        Operation unlockOperation = Operation.Call;
        uint256 unlockSafeTxGas = 0;
        uint256 unlockBaseGas = 0;
        uint256 unlockGasPrice = 0;
        address unlockGasToken = address(0);
        address payable unlockRefundReceiver = payable(address(0));

        bytes32 unlockTxHash = keccak256(
            bytes.concat(
                hex"1901",
                keccak256(
                    abi.encode(
                        keccak256("EIP712Domain(uint256 chainId,address verifyingContract)"), block.chainid, safe
                    )
                ),
                keccak256(
                        abi.encode(
                            keccak256(
                                "SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)"
                            ),
                            unlockTo,
                            unlockValue,
                            keccak256(unlockData),
                            unlockOperation,
                            unlockSafeTxGas,
                            unlockBaseGas,
                            unlockGasPrice,
                            unlockGasToken,
                            unlockRefundReceiver,
                            safe.nonce()
                        )
                    )
            )
        );

        bytes memory unlockSignatures = abi.encodePacked(
            _signSafeEncoded(owners[1], unlockTxHash),
            _signSafeEncoded(owners[2], unlockTxHash),
            uint256(uint160(owners[3].addr)),
            bytes32(0),
            uint8(1)
        );

        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.NotUnanimous.selector, unlockTxHash));
        safe.execTransaction(
            unlockTo,
            unlockValue,
            unlockData,
            unlockOperation,
            unlockSafeTxGas,
            unlockBaseGas,
            unlockGasPrice,
            unlockGasToken,
            unlockRefundReceiver,
            unlockSignatures
        );

        // This just validates that the signatures as encoded are otherwise
        // valid in the absence of the guard's checks
        vm.store(address(safe), keccak256("guard_manager.guard.address"), bytes32(0));
        vm.expectEmit(true, true, true, true, address(safe));
        emit ISafe.ExecutionSuccess(unlockTxHash, 0);
        safe.execTransaction(
            unlockTo,
            unlockValue,
            unlockData,
            unlockOperation,
            unlockSafeTxGas,
            unlockBaseGas,
            unlockGasPrice,
            unlockGasToken,
            unlockRefundReceiver,
            unlockSignatures
        );
    }

    IMulticall internal constant _MULTICALL = IMulticall(0xA1dabEF33b3B82c7814B6D82A79e50F4AC44102B);

    function _encodeMulticallPoke()
        internal
        returns (
            address to,
            uint256 value,
            bytes memory data,
            Operation operation,
            uint256 safeTxGas,
            uint256 baseGas,
            uint256 gasPrice,
            address gasToken,
            address payable refundReceiver,
            uint256 nonce,
            bytes32 txHash,
            bytes memory signatures
        )
    {
        to = address(_MULTICALL);
        value = 0 ether;
        data = abi.encodeCall(this.poke, ());
        data = abi.encodePacked(uint8(Operation.Call), address(this), uint256(0 ether), uint256(data.length), data);
        data = abi.encodeCall(_MULTICALL.multiSend, (data));
        operation = Operation.DelegateCall;
        safeTxGas = 0;
        baseGas = 0;
        gasPrice = 0;
        gasToken = address(0);
        refundReceiver = payable(address(0));
        nonce = safe.nonce();

        txHash = keccak256(
            bytes.concat(
                hex"1901",
                keccak256(
                    abi.encode(
                        keccak256("EIP712Domain(uint256 chainId,address verifyingContract)"), block.chainid, safe
                    )
                ),
                keccak256(
                        abi.encode(
                            keccak256(
                                "SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)"
                            ),
                            to,
                            value,
                            keccak256(data),
                            operation,
                            safeTxGas,
                            baseGas,
                            gasPrice,
                            gasToken,
                            refundReceiver,
                            nonce
                        )
                    )
            )
        );

        signatures = abi.encodePacked(_signSafeEncoded(owners[0], txHash), _signSafeEncoded(owners[1], txHash));
    }

    function testMulticall0() external {
        (
            address to,
            uint256 value,
            bytes memory data,
            Operation operation,
            uint256 safeTxGas,
            uint256 baseGas,
            uint256 gasPrice,
            address gasToken,
            address payable refundReceiver,
            uint256 nonce,,
            bytes memory signatures
        ) = _encodeMulticallPoke();

        guard.enqueue(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, nonce, signatures
        );
    }

    function testMulticall1() external {
        (
            address to,
            uint256 value,
            bytes memory data,
            Operation operation,
            uint256 safeTxGas,
            uint256 baseGas,
            uint256 gasPrice,
            address gasToken,
            address payable refundReceiver,
            uint256 nonce,,
            bytes memory signatures
        ) = _encodeMulticallPoke();

        guard.enqueue(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, nonce, signatures
        );
        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);
        safe.execTransaction(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, signatures
        );
    }

    function testOnePointFour() external {
        // uninstall the 1.3 guard
        vm.store(address(safe), keccak256("guard_manager.guard.address"), bytes32(0));

        // migrate to 1.4.1
        address onePointFourSingleton = 0x29fcB43b46531BcA003ddC8FCB67FFE91900C762;
        address onePointFourFallback = 0xfd0732Dc9E303f09fCEf3a7388Ad10A83459Ec99;

        MigrationDummy migration = new MigrationDummy();

        bytes memory data = abi.encodeCall(migration.migrate, (onePointFourSingleton, onePointFourFallback));
        bytes32 txHash = keccak256(
            bytes.concat(
                hex"1901",
                keccak256(
                    abi.encode(
                        keccak256("EIP712Domain(uint256 chainId,address verifyingContract)"), block.chainid, safe
                    )
                ),
                keccak256(
                        abi.encode(
                            keccak256(
                                "SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)"
                            ),
                            address(migration),
                            0 wei,
                            keccak256(data),
                            Operation.DelegateCall,
                            0,
                            0,
                            0 gwei,
                            address(0),
                            payable(address(0)),
                            safe.nonce()
                        )
                    )
            )
        );
        bytes memory signatures =
            abi.encodePacked(_signSafeEncoded(owners[0], txHash), _signSafeEncoded(owners[1], txHash));

        safe.execTransaction(
            address(migration),
            0 wei,
            data,
            Operation.DelegateCall,
            0,
            0,
            0 gwei,
            address(0),
            payable(address(0)),
            signatures
        );

        // check that we successfully migrated to 1.4.1
        assertEq(safe.masterCopy(), onePointFourSingleton);

        // the 1.4.1 guard has to be deployed *before* being enabled
        bytes memory creationCode = bytes.concat(
            vm.getCode("SafeGuard.sol:ZeroExSettlerDeployerSafeGuardOnePointFourPointOne"), abi.encode(address(safe))
        );
        guard = IZeroExSettlerDeployerSafeGuard(
            AddressDerivation.deriveDeterministicContract(factory, bytes32(0), keccak256(creationCode))
        );
        (bool success, bytes memory returndata) = factory.call(bytes.concat(bytes32(0), creationCode));
        assertTrue(success);
        assertEq(address(uint160(bytes20(returndata))), address(guard));

        // install the guard
        data = abi.encodeCall(ISafeSetup.setGuard, (address(guard)));
        txHash = keccak256(
            bytes.concat(
                hex"1901",
                keccak256(
                    abi.encode(
                        keccak256("EIP712Domain(uint256 chainId,address verifyingContract)"), block.chainid, safe
                    )
                ),
                keccak256(
                        abi.encode(
                            keccak256(
                                "SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)"
                            ),
                            address(safe),
                            0 wei,
                            keccak256(data),
                            Operation.Call,
                            0,
                            0,
                            0 gwei,
                            address(0),
                            payable(address(0)),
                            safe.nonce()
                        )
                    )
            )
        );
        signatures = abi.encodePacked(_signSafeEncoded(owners[0], txHash), _signSafeEncoded(owners[1], txHash));

        safe.execTransaction(
            address(safe), 0 wei, data, Operation.Call, 0, 0, 0 gwei, address(0), payable(address(0)), signatures
        );

        testHappyPath();
    }
}
