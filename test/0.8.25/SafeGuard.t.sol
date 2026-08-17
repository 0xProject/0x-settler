// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {Vm} from "@forge-std/Vm.sol";

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

    function getThreshold() external view returns (uint256);

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
    event Uninstalled();

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
    error GuardCheckNotEnforced(uint256 callIndex, address target, bytes data);
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

interface ISafeMigration {
    function migrateL2WithFallbackHandler() external;
}

contract MigrationDummy {
    address private singleton;

    function migrate(address newSingleton, address newFallbackHandler) external {
        singleton = newSingleton;
        ISafeSetup(address(this)).setFallbackHandler(newFallbackHandler);
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

contract TestSafeGuardOperations is Test {
    using ItoA for uint256;

    address internal constant _FACTORY = 0x914d7Fec6aaC8cd542e72Bca78B30650d45643d7;
    ISafe internal constant _SAFE = ISafe(0xf36b9f50E59870A24F42F9Ba43b2aD0A4b8f2F51);
    address internal constant _SAFE_MIGRATION = 0x526643F69b81B008F46d95CD5ced5eC0edFFDaC6;
    address internal constant _ONE_POINT_FOUR_SINGLETON = 0x29fcB43b46531BcA003ddC8FCB67FFE91900C762;
    IMulticall internal constant _MULTICALL = IMulticall(0x9641d764fc13c8B624c04430C7356C1C7C8102e2);
    uint24 internal constant _TIMELOCK_DELAY = uint24(5 days);
    bytes32 internal constant _DOMAIN_SEPARATOR_TYPEHASH =
        keccak256("EIP712Domain(uint256 chainId,address verifyingContract)");
    bytes32 internal constant _SAFE_TX_TYPEHASH = keccak256(
        "SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)"
    );

    IZeroExSettlerDeployerSafeGuard internal _guard;
    Vm.Wallet[] internal _owners;
    uint256 internal _pokeCounter;

    struct SafeTx {
        address to;
        uint256 value;
        bytes data;
        Operation operation;
        uint256 safeTxGas;
        uint256 baseGas;
        uint256 gasPrice;
        address gasToken;
        address payable refundReceiver;
        uint256 nonce;
    }

    function setUp() public {
        vm.createSelectFork(vm.envString("MAINNET_RPC_URL"), 23183520);

        ISafeSetup safeSetup = ISafeSetup(address(_SAFE));
        address[] memory oldOwners = safeSetup.getOwners();
        string memory mnemonic = "test test test test test test test test test test test junk";
        for (uint256 i; i < 5; i++) {
            _owners.push(vm.createWallet(vm.deriveKey(mnemonic, uint32(i)), string.concat("Owner #", i.itoa())));
        }

        vm.startPrank(address(_SAFE));
        for (uint256 i; i < _owners.length; i++) {
            safeSetup.addOwnerWithThreshold(_owners[i].addr, 3);
        }
        for (uint256 i; i < oldOwners.length; i++) {
            safeSetup.removeOwner(_owners[0].addr, oldOwners[i], 3);
        }
        vm.stopPrank();

        Vm.Wallet memory temporaryOwner;
        for (uint256 i = 1; i < _owners.length; i++) {
            for (uint256 j = i; j > 0; j--) {
                if (_owners[j - 1].addr > _owners[j].addr) {
                    temporaryOwner = _owners[j - 1];
                    _owners[j - 1] = _owners[j];
                    _owners[j] = temporaryOwner;
                }
            }
        }

        assertEq(safeSetup.getOwners().length, 5);
        assertEq(_SAFE.getThreshold(), 3);

        vm.store(address(_SAFE), keccak256("guard_manager.guard.address"), bytes32(0));
        _migrateSafe();
        assertEq(_SAFE.masterCopy(), _ONE_POINT_FOUR_SINGLETON);

        bytes memory creationCode = bytes.concat(
            vm.getCode("SafeGuard.sol:ZeroExSettlerDeployerSafeGuardOnePointFourPointOne"), abi.encode(address(_SAFE))
        );
        _guard = IZeroExSettlerDeployerSafeGuard(
            AddressDerivation.deriveDeterministicContract(_FACTORY, bytes32(0), keccak256(creationCode))
        );
        (bool success, bytes memory returndata) = _FACTORY.call(bytes.concat(bytes32(0), creationCode));
        assertTrue(success);
        assertEq(address(uint160(bytes20(returndata))), address(_guard));

        vm.prank(address(_SAFE));
        safeSetup.setGuard(address(_guard));
        vm.prank(address(_SAFE));
        _guard.setDelay(_TIMELOCK_DELAY);

        assertEq(_guard.safe(), address(_SAFE));
        assertEq(_guard.delay(), _TIMELOCK_DELAY);
        assertEq(
            abi.decode(_SAFE.getStorageAt(uint256(keccak256("guard_manager.guard.address")), 1), (address)),
            address(_guard)
        );
    }

    function poke() external returns (uint256) {
        require(msg.sender == address(_SAFE));
        return ++_pokeCounter;
    }

    function _migrateSafe() internal {
        SafeTx memory safeTx = SafeTx({
            to: _SAFE_MIGRATION,
            value: 0,
            data: abi.encodeCall(ISafeMigration.migrateL2WithFallbackHandler, ()),
            operation: Operation.DelegateCall,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: _SAFE.nonce()
        });
        _execute(safeTx, _sign(_safeTxHash(safeTx)));
    }

    function _pokeTx() internal view returns (SafeTx memory) {
        return SafeTx({
            to: address(this),
            value: 0,
            data: abi.encodeCall(this.poke, ()),
            operation: Operation.Call,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: _SAFE.nonce()
        });
    }

    function _safeTxHash(SafeTx memory safeTx) internal view returns (bytes32) {
        return keccak256(
            bytes.concat(
                hex"1901",
                keccak256(abi.encode(_DOMAIN_SEPARATOR_TYPEHASH, block.chainid, _SAFE)),
                keccak256(
                    abi.encode(
                        _SAFE_TX_TYPEHASH,
                        safeTx.to,
                        safeTx.value,
                        keccak256(safeTx.data),
                        safeTx.operation,
                        safeTx.safeTxGas,
                        safeTx.baseGas,
                        safeTx.gasPrice,
                        safeTx.gasToken,
                        safeTx.refundReceiver,
                        safeTx.nonce
                    )
                )
            )
        );
    }

    function _sign(bytes32 txHash) internal returns (bytes memory signatures) {
        for (uint256 i; i < 3; i++) {
            (uint8 v, bytes32 r, bytes32 s) = vm.sign(_owners[i], txHash);
            signatures = abi.encodePacked(signatures, r, s, v);
        }
    }

    function _enqueue(SafeTx memory safeTx, bytes memory signatures) internal {
        _guard.enqueue(
            safeTx.to,
            safeTx.value,
            safeTx.data,
            safeTx.operation,
            safeTx.safeTxGas,
            safeTx.baseGas,
            safeTx.gasPrice,
            safeTx.gasToken,
            safeTx.refundReceiver,
            safeTx.nonce,
            signatures
        );
    }

    function _execute(SafeTx memory safeTx, bytes memory signatures) internal returns (bool) {
        return _SAFE.execTransaction(
            safeTx.to,
            safeTx.value,
            safeTx.data,
            safeTx.operation,
            safeTx.safeTxGas,
            safeTx.baseGas,
            safeTx.gasPrice,
            safeTx.gasToken,
            safeTx.refundReceiver,
            signatures
        );
    }

    function _subcall(address target, bytes memory data) internal pure returns (bytes memory) {
        return abi.encodePacked(uint8(Operation.Call), target, uint256(0), data.length, data);
    }

    function test_Timelock_EnqueueStrictDelayExecute_Succeeds() external {
        SafeTx memory safeTx = _pokeTx();
        bytes32 txHash = _safeTxHash(safeTx);
        bytes memory signatures = _sign(txHash);
        uint256 timelockEnd = block.timestamp + _guard.delay();

        vm.expectEmit(true, true, true, true, address(_guard));
        emit IZeroExSettlerDeployerSafeGuard.SafeTransactionEnqueued(
            txHash,
            timelockEnd,
            safeTx.to,
            safeTx.value,
            safeTx.data,
            safeTx.operation,
            safeTx.safeTxGas,
            safeTx.baseGas,
            safeTx.gasPrice,
            safeTx.gasToken,
            safeTx.refundReceiver,
            safeTx.nonce,
            signatures
        );
        _enqueue(safeTx, signatures);

        vm.warp(timelockEnd);
        vm.expectRevert(
            abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.TimelockNotElapsed.selector, txHash, timelockEnd)
        );
        _execute(safeTx, signatures);

        vm.warp(timelockEnd + 1);
        vm.expectEmit(true, true, true, true, address(_SAFE));
        emit ISafeOnePointFour.ExecutionSuccess(txHash, 0);
        assertTrue(_execute(safeTx, signatures));
        assertEq(_pokeCounter, 1);
    }

    function test_Timelock_NeverEnqueued_RevertsNotQueued() external {
        SafeTx memory safeTx = _pokeTx();
        bytes32 txHash = _safeTxHash(safeTx);

        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.NotQueued.selector, txHash));
        _execute(safeTx, _sign(txHash));
    }

    function test_Multisend_MissingInterleavedCheck_RevertsGuardCheckNotEnforced() external {
        bytes memory pokeData = abi.encodeCall(this.poke, ());
        bytes memory calls = bytes.concat(_subcall(address(this), pokeData), _subcall(address(this), pokeData));
        SafeTx memory safeTx = SafeTx({
            to: address(_MULTICALL),
            value: 0,
            data: abi.encodeCall(_MULTICALL.multiSend, (calls)),
            operation: Operation.DelegateCall,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: _SAFE.nonce()
        });

        vm.expectRevert(
            abi.encodeWithSelector(
                IZeroExSettlerDeployerSafeGuard.GuardCheckNotEnforced.selector, uint256(1), address(this), pokeData
            )
        );
        _enqueue(safeTx, _sign(_safeTxHash(safeTx)));
    }

    function test_Abandon_QueuedGuardRemoval_Succeeds() external {
        SafeTx memory safeTx = SafeTx({
            to: address(_SAFE),
            value: 0,
            data: abi.encodeCall(ISafeSetup.setGuard, (address(0))),
            operation: Operation.Call,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: _SAFE.nonce()
        });
        bytes32 txHash = _safeTxHash(safeTx);
        bytes memory signatures = _sign(txHash);
        uint256 timelockEnd = block.timestamp + _guard.delay();
        _enqueue(safeTx, signatures);

        vm.warp(timelockEnd + 1);
        vm.expectEmit(true, true, true, true, address(_SAFE));
        emit ISafeOnePointFour.ExecutionSuccess(txHash, 0);
        vm.expectEmit(true, true, true, true, address(_guard));
        emit IZeroExSettlerDeployerSafeGuard.Uninstalled();
        assertTrue(_execute(safeTx, signatures));
        assertEq(
            abi.decode(_SAFE.getStorageAt(uint256(keccak256("guard_manager.guard.address")), 1), (address)), address(0)
        );

        SafeTx memory nextSafeTx = _pokeTx();
        vm.expectRevert(IZeroExSettlerDeployerSafeGuard.GuardNotInstalled.selector);
        _enqueue(nextSafeTx, _sign(_safeTxHash(nextSafeTx)));
    }
}

contract TestSafeGuardShellHelpers is Test {
    address internal constant _GUARD = 0x0000000000000000000000000000000000000009;

    function _multisendHelperScript() internal pure returns (string memory) {
        return string.concat(
            "set -Eeuo pipefail\n",
            "project_root=\"$1\"\n",
            "test_guard=\"$2\"\n",
            "shift 2\n",
            "chain_name=mainnet\n",
            "chainid=1\n",
            "rpc_url=unused\n",
            "safe_address=0x0000000000000000000000000000000000000006\n",
            "get_config() {\n",
            "case \"$1\" in\n",
            "safe.apiUrl) echo 'NOT SUPPORTED' ;;\n",
            "deployment.deployer) echo 0x0000000000000000000000000000000000000007 ;;\n",
            "governance.timelock) echo \"$test_guard\" ;;\n",
            "*) return 1 ;;\n",
            "esac\n",
            "}\n",
            "die() { echo \"$*\" >&2; return 1; }\n",
            "cast() {\n",
            "if [[ ${1-} == call ]]; then\n",
            "case \"${5-}\" in\n",
            "'VERSION()(string)') echo '\"1.4.1\"' ;;\n",
            "'nonce()(uint256)') echo 0 ;;\n",
            "'getOwners()(address[])') echo '[0x0000000000000000000000000000000000000001]' ;;\n",
            "'getStorageAt(uint256,uint256)(bytes)') echo 0x00 ;;\n",
            "*) return 1 ;;\n",
            "esac\n",
            "elif [[ ${1-} == parse-bytes32-address ]]; then\n",
            "cat >/dev/null\n",
            "echo \"$test_guard\"\n",
            "else\n",
            "command cast \"$@\"\n",
            "fi\n",
            "}\n",
            "source \"$project_root/sh/common_safe.sh\"\n",
            "build_multisend_calldata \"$@\"\n"
        );
    }

    function _confirmationHelperScript() internal pure returns (string memory) {
        return string.concat(
            "set -Eeuo pipefail\n",
            "project_root=\"$1\"\n",
            "mode=\"$2\"\n",
            "shift 2\n",
            "source \"$project_root/sh/common_safe_deployer.sh\"\n",
            "approved_signature() {\n",
            "cast concat-hex \"$(cast to-uint256 \"$1\")\" \"$(cast to-uint256 0)\" 0x01\n",
            "}\n",
            "signing_hash=0x0000000000000000000000000000000000000000000000000000000000000000\n",
            "case \"$mode\" in\n",
            "approved|insufficient)\n",
            "owners_array=(\"$1\" \"$2\" \"$3\" \"$4\" \"$5\")\n",
            "s1=\"$(approved_signature \"$1\")\"\n",
            "s2=\"$(approved_signature \"$2\")\"\n",
            "s3=\"$(approved_signature \"$3\")\"\n",
            "s4=\"$(approved_signature \"$4\")\"\n",
            "s5=\"$(approved_signature \"$5\")\"\n",
            "confirmations=\"$(jq -Mnc --arg o1 \"$1\" --arg o2 \"$2\" --arg o3 \"$3\" ",
            "--arg o4 \"$4\" --arg o5 \"$5\" --arg s1 \"$s1\" --arg s2 \"$s2\" --arg s3 \"$s3\" ",
            "--arg s4 \"$s4\" --arg s5 \"$s5\" ",
            "'[{owner:$o5,signature:$s5},{owner:$o2,signature:$s2},{owner:$o4,signature:$s4},",
            "{owner:$o1,signature:$s1},{owner:$o3,signature:$s3}]')\"\n",
            "normalized=\"$(_normalize_safe_confirmations \"$signing_hash\" \"$confirmations\")\"\n",
            "if [[ $mode == approved ]]; then\n",
            "_pack_safe_confirmations 3 \"$normalized\"\n",
            "else\n",
            "insufficient=\"$(jq -Mc '.[0:2]' <<<\"$normalized\")\"\n",
            "if _pack_safe_confirmations 3 \"$insufficient\" >/dev/null 2>&1; ",
            "then printf 0x00; else printf 0x01; fi\n",
            "fi\n",
            ";;\n",
            "contracts)\n",
            "owners_array=(\"$1\" \"$2\")\n",
            "first=\"$(cast concat-hex \"$(cast to-uint256 \"$1\")\" \"$(cast to-uint256 65)\" ",
            "0x00 \"$(cast to-uint256 3)\" 0xaabbcc)\"\n",
            "second_payload=0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20\n",
            "second=\"$(cast concat-hex \"$(cast to-uint256 \"$2\")\" \"$(cast to-uint256 65)\" ",
            "0x00 \"$(cast to-uint256 33)\" \"$second_payload\")\"\n",
            "confirmations=\"$(jq -Mnc --arg o1 \"$1\" --arg o2 \"$2\" --arg s1 \"$first\" ",
            "--arg s2 \"$second\" '[{owner:$o2,signature:$s2},{owner:$o1,signature:$s1}]')\"\n",
            "normalized=\"$(_normalize_safe_confirmations \"$signing_hash\" \"$confirmations\")\"\n",
            "_pack_safe_confirmations 2 \"$normalized\"\n",
            ";;\n",
            "esac\n"
        );
    }

    function _deadlineHelperScript() internal pure returns (string memory) {
        return string.concat(
            "set -Eeuo pipefail\n",
            "project_root=\"$1\"\n",
            "mode=\"$2\"\n",
            "multisend_calldata=\"$3\"\n",
            "feature=\"$4\"\n",
            "authority=\"$5\"\n",
            "source \"$project_root/sh/common_safe_deployer.sh\"\n",
            "multisend_sig='multiSend(bytes)'\n",
            "last_call=\"$(extract_last_multisend_call_data \"$multisend_calldata\")\"\n",
            "case \"$mode\" in\n",
            "last)\n",
            "echo \"$last_call\"\n",
            ";;\n",
            "deadline)\n",
            "deadline=\"$(extract_authorize_deadline \"$last_call\" \"$feature\" \"$authority\")\"\n",
            "cast to-uint256 \"$deadline\"\n",
            ";;\n",
            "reject)\n",
            "if extract_authorize_deadline \"$last_call\" \"$feature\" \"$authority\" >/dev/null; ",
            "then printf 0x00; else printf 0x01; fi\n",
            ";;\n",
            "esac\n"
        );
    }

    function _timelockFilterHelperScript() internal pure returns (string memory) {
        return string.concat(
            "set -Eeuo pipefail\n",
            "project_root=\"$1\"\n",
            "rpc_url=unused\n",
            "safe_guard=0x0000000000000000000000000000000000000009\n",
            "current_timestamp=1700000000\n",
            "cast() {\n",
            "if [[ ${1-} == block ]]; then\n",
            "[[ ${2-} == latest && ${3-} == --rpc-url && ${4-} == unused ",
            "&& ${5-} == --field && ${6-} == timestamp ]] || return 1\n",
            "echo \"$current_timestamp\"\n",
            "elif [[ ${1-} == call ]]; then\n",
            "[[ ${2-} == --json && ${3-} == --rpc-url && ${4-} == unused ",
            "&& ${5-} == \"$safe_guard\" && ${6-} == 'txInfo(bytes32)(uint256,address)' ]] || return 1\n",
            "case \"${7,,}\" in\n",
            "0x*01) echo '[\"115792089237316195423570985008687907853269984665640564039457584007913129639935\",",
            "\"0x0000000000000000000000000000000000000001\"]' ;;\n",
            "0x*02) echo '[\"0\",\"0x0000000000000000000000000000000000000000\"]' ;;\n",
            "0x*03) echo '[\"1700000000\",\"0x0000000000000000000000000000000000000000\"]' ;;\n",
            "0x*04) echo '[\"1699999999\",\"0x0000000000000000000000000000000000000000\"]' ;;\n",
            "0x*05) echo '[\"1700000001\",\"0x0000000000000000000000000000000000000000\"]' ;;\n",
            "*) return 1 ;;\n",
            "esac\n",
            "else\n",
            "command cast \"$@\"\n",
            "fi\n",
            "}\n",
            "source \"$project_root/sh/common_safe_deployer.sh\"\n",
            "transactions='[",
            "{\"safeTxHash\":\"0x0000000000000000000000000000000000000000000000000000000000000001\"},",
            "{\"safeTxHash\":\"0x0000000000000000000000000000000000000000000000000000000000000002\"},",
            "{\"safeTxHash\":\"0x0000000000000000000000000000000000000000000000000000000000000003\"},",
            "{\"safeTxHash\":\"0x0000000000000000000000000000000000000000000000000000000000000004\"},",
            "{\"safeTxHash\":\"0x0000000000000000000000000000000000000000000000000000000000000005\"}",
            "]'\n",
            "filtered=\"$(filter_sts_safe_transactions_by_timelock executable \"$transactions\")\"\n",
            "jq -Mr '\"0x\" + (map(.safeTxHash[2:]) | join(\"\"))' <<<\"$filtered\"\n"
        );
    }

    function _runMultisendHelper(address safeGuard, address[] memory targets, bytes[] memory payloads, uint256 count)
        internal
        returns (bytes memory)
    {
        string[] memory command = new string[](6 + count * 2);
        command[0] = "bash";
        command[1] = "-c";
        command[2] = _multisendHelperScript();
        command[3] = "bash";
        command[4] = vm.projectRoot();
        command[5] = vm.toString(safeGuard);
        for (uint256 i; i < count; i++) {
            command[6 + i * 2] = vm.toString(targets[i]);
            command[7 + i * 2] = vm.toString(payloads[i]);
        }
        return vm.ffi(command);
    }

    function _runConfirmationHelper(string memory mode, address[] memory confirmationOwners)
        internal
        returns (bytes memory)
    {
        string[] memory command = new string[](6 + confirmationOwners.length);
        command[0] = "bash";
        command[1] = "-c";
        command[2] = _confirmationHelperScript();
        command[3] = "bash";
        command[4] = vm.projectRoot();
        command[5] = mode;
        for (uint256 i; i < confirmationOwners.length; i++) {
            command[6 + i] = vm.toString(confirmationOwners[i]);
        }
        return vm.ffi(command);
    }

    function _runDeadlineHelper(string memory mode, bytes memory multisendCalldata, uint128 feature, address authority)
        internal
        returns (bytes memory)
    {
        string[] memory command = new string[](9);
        command[0] = "bash";
        command[1] = "-c";
        command[2] = _deadlineHelperScript();
        command[3] = "bash";
        command[4] = vm.projectRoot();
        command[5] = mode;
        command[6] = vm.toString(multisendCalldata);
        command[7] = vm.toString(uint256(feature));
        command[8] = vm.toString(authority);
        return vm.ffi(command);
    }

    function _runTimelockFilterHelper() internal returns (bytes memory) {
        string[] memory command = new string[](5);
        command[0] = "bash";
        command[1] = "-c";
        command[2] = _timelockFilterHelperScript();
        command[3] = "bash";
        command[4] = vm.projectRoot();
        return vm.ffi(command);
    }

    function _subcall(address target, bytes memory data) internal pure returns (bytes memory) {
        return abi.encodePacked(uint8(Operation.Call), target, uint256(0), data.length, data);
    }

    function _approvedHashSignature(address owner) internal pure returns (bytes memory) {
        return abi.encodePacked(bytes32(uint256(uint160(owner))), bytes32(0), uint8(1));
    }

    function testFFIBuildMultisendCalldata() external {
        address[] memory targets = new address[](3);
        targets[0] = 0x0000000000000000000000000000000000000011;
        targets[1] = 0x0000000000000000000000000000000000000022;
        targets[2] = 0x0000000000000000000000000000000000000033;

        bytes[] memory payloads = new bytes[](3);
        payloads[0] = hex"1234";
        payloads[1] = hex"aabbcc";
        payloads[2] = hex"deadbeef00";

        bytes memory first = _subcall(targets[0], payloads[0]);
        bytes memory second = _subcall(targets[1], payloads[1]);
        bytes memory third = _subcall(targets[2], payloads[2]);
        bytes memory checkGuard = _subcall(_GUARD, hex"919840ad");

        assertEq(_runMultisendHelper(_GUARD, targets, payloads, 1), abi.encodeCall(IMulticall.multiSend, (first)));
        assertEq(
            _runMultisendHelper(_GUARD, targets, payloads, 2),
            abi.encodeCall(IMulticall.multiSend, (bytes.concat(first, checkGuard, second)))
        );
        assertEq(
            _runMultisendHelper(_GUARD, targets, payloads, 3),
            abi.encodeCall(IMulticall.multiSend, (bytes.concat(first, checkGuard, second, checkGuard, third)))
        );
        assertEq(
            _runMultisendHelper(address(0), targets, payloads, 2),
            abi.encodeCall(IMulticall.multiSend, (bytes.concat(first, second)))
        );
    }

    function testFFIPackSafeConfirmations() external {
        address[] memory confirmationOwners = new address[](5);
        for (uint256 i; i < confirmationOwners.length; i++) {
            confirmationOwners[i] = address(uint160(i + 1));
        }

        bytes memory packed = _runConfirmationHelper("approved", confirmationOwners);
        assertEq(packed.length, 3 * 65);
        assertEq(
            packed,
            bytes.concat(
                _approvedHashSignature(confirmationOwners[0]),
                _approvedHashSignature(confirmationOwners[1]),
                _approvedHashSignature(confirmationOwners[2])
            )
        );
        assertEq(_runConfirmationHelper("insufficient", confirmationOwners), hex"01");

        address[] memory contractOwners = new address[](2);
        contractOwners[0] = 0x0000000000000000000000000000000000000011;
        contractOwners[1] = 0x0000000000000000000000000000000000000022;
        bytes memory secondPayload = hex"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20";
        bytes memory expectedContractSignatures = bytes.concat(
            abi.encodePacked(bytes32(uint256(uint160(contractOwners[0]))), bytes32(uint256(0x82)), uint8(0)),
            abi.encodePacked(bytes32(uint256(uint160(contractOwners[1]))), bytes32(uint256(0xa5)), uint8(0)),
            abi.encodePacked(bytes32(uint256(3)), hex"aabbcc"),
            abi.encodePacked(bytes32(uint256(33)), secondPayload)
        );
        assertEq(_runConfirmationHelper("contracts", contractOwners), expectedContractSignatures);
    }

    function testFFIReconstructAuthorizeDeadline() external {
        uint128 feature = 0x0123456789abcdef0123456789abcdef;
        address authority = 0x0000000000000000000000000000000000000044;
        uint40 deadline = 1_900_000_123;
        bytes memory authorizeData =
            abi.encodeWithSignature("authorize(uint128,address,uint40)", feature, authority, deadline);

        address[] memory targets = new address[](2);
        targets[0] = 0x0000000000000000000000000000000000000055;
        targets[1] = 0x0000000000000000000000000000000000000066;
        bytes[] memory payloads = new bytes[](2);
        payloads[0] = hex"deadbeef";
        payloads[1] = authorizeData;
        bytes memory multisendCalldata = _runMultisendHelper(_GUARD, targets, payloads, 2);

        assertEq(_runDeadlineHelper("last", multisendCalldata, feature, authority), authorizeData);
        assertEq(
            abi.decode(_runDeadlineHelper("deadline", multisendCalldata, feature, authority), (uint256)),
            uint256(deadline)
        );
        assertEq(_runDeadlineHelper("reject", multisendCalldata, feature + 1, authority), hex"01");
        assertEq(
            _runDeadlineHelper("reject", multisendCalldata, feature, 0x0000000000000000000000000000000000000045),
            hex"01"
        );
    }

    function testFFIFilterExecutableTransactionsByTimelock() external {
        assertEq(_runTimelockFilterHelper(), abi.encodePacked(bytes32(uint256(4))));
    }
}
