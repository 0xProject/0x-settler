// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {Vm} from "@forge-std/Vm.sol";

import {ItoA} from "src/utils/ItoA.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";

interface ISafeSetup {
    function addOwnerWithThreshold(address owner, uint256 _threshold) external;

    function removeOwner(address prevOwner, address owner, uint256 _threshold) external;

    function changeThreshold(uint256 _threshold) external;

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
    error GuardRemoved();
    error GuardIsOwner();
    error TimelockNotElapsed(bytes32 txHash, uint256 timelockEnd);
    error TimelockElapsed(bytes32 txHash, uint256 timelockEnd);
    error AlreadyQueued(bytes32 txHash);
    error NotQueued(bytes32 txHash);
    error LockedDown(address lockedDownBy);
    error NotLockedDown();
    error UnexpectedUpgrade(address newSingleton);
    error Reentrancy();
    error ERC20SponsorshipUnsafe(address gasToken);
    error ModuleInstalled(address module);
    error IncorrectFallbackHandler(address handler);
    error GuardCheckNotEnforced(uint256 callIndex, address target, bytes data);
    error EvenNumberOfMultiCalls(uint256 callsCount);
    error NotEnoughOwners(uint256 ownerCount);
    error ThresholdTooLow(uint256 threshold);
    error ThresholdTooHigh(uint256 threshold);
    error NotUnanimous(bytes32 txHash);
    error TxHashNotApproved(bytes32 txHash);
    error ConfusedDeputy(uint256 callIndex, address target, bytes data);
    error CannotCancelOwnResignation(bytes32 txHash);
    error CannotEnqueuePastTransaction(bytes32 txHash, uint256 nonce);

    // This matches the contract's `mapping(bytes32 => TxInfo) public txInfo` auto-generated getter.
    function txInfo(bytes32) external view returns (uint256 timelockEnd, address cantCancel);
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

    function check() external view;
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

// Helper that, when invoked during a Safe transaction's execution phase, re-enters the Guard. The Guard's
// reentrancy lock is set between `checkTransaction` and `checkAfterExecution`, so the re-entrant call reverts
// `Reentrancy()`. We capture the revert selector instead of bubbling it because Safe's `execute` swallows
// inner revert reasons (surfacing only `GS013`) when `safeTxGas == 0 && gasPrice == 0`.
contract ReentrantTarget {
    IZeroExSettlerDeployerSafeGuard public immutable guard;
    bytes4 public capturedSelector;

    constructor(IZeroExSettlerDeployerSafeGuard _guard) {
        guard = _guard;
    }

    function attack() external {
        // `lockDown()` runs the `normalOperation` modifier (which checks the reentrancy lock) before
        // `onlyOwner`, so this reverts `Reentrancy()` even though we are not an owner.
        try guard.lockDown() {}
        catch (bytes memory reason) {
            capturedSelector = bytes4(reason);
        }
    }
}

contract TestSafeGuard is Test {
    using ItoA for uint256;

    address internal constant factory = 0x914d7Fec6aaC8cd542e72Bca78B30650d45643d7;
    ISafe internal constant safe = ISafe(0xf36b9f50E59870A24F42F9Ba43b2aD0A4b8f2F51);
    address internal constant onePointThreeSingleton = 0xfb1bffC9d739B8D520DaF37dF666da4C687191EA;
    IMulticall internal constant _MULTICALL = IMulticall(0xA1dabEF33b3B82c7814B6D82A79e50F4AC44102B);
    IZeroExSettlerDeployerSafeGuard internal guard;
    uint256 internal pokeCounter;

    Vm.Wallet[] internal owners;

    bytes32 internal constant _DOMAIN_SEPARATOR_TYPEHASH =
        keccak256("EIP712Domain(uint256 chainId,address verifyingContract)");
    bytes32 internal constant _SAFE_TX_TYPEHASH = keccak256(
        "SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)"
    );

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

    struct Call {
        address to;
        uint256 value;
        bytes data;
    }

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
        // The suite operates on a 3-of-5 Safe. This is the smallest configuration that exercises the
        // `_getThresholdAfterResign` decrement branch (`ownerCount - threshold == _MINIMUM_THRESHOLD`).
        _safe.changeThreshold(3);
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

    // ----- signing / hashing helpers -----

    function _signSafeEncoded(Vm.Wallet storage signer, bytes32 hash) internal returns (bytes memory) {
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(signer, hash);
        return abi.encodePacked(r, s, v);
    }

    /// ECDSA-signs `hash` with the first `n` (address-sorted) owners, yielding a correctly-ordered
    /// signature blob. `n == getThreshold()` for the timelock path, `n == ownerCount` for unanimity.
    function _sign(uint256 n, bytes32 hash) internal returns (bytes memory sigs) {
        for (uint256 i; i < n; i++) {
            sigs = abi.encodePacked(sigs, _signSafeEncoded(owners[i], hash));
        }
    }

    /// The Safe "contract signature" encoding for an owner who pre-approved the hash via `approveHash`.
    /// Must be placed at the owner's sorted position within the blob.
    function _approveHashSig(address owner) internal pure returns (bytes memory) {
        return abi.encodePacked(bytes32(uint256(uint160(owner))), bytes32(0), uint8(1));
    }

    function _safeTxHash(SafeTx memory t) internal view returns (bytes32) {
        return keccak256(
            bytes.concat(
                hex"1901",
                keccak256(abi.encode(_DOMAIN_SEPARATOR_TYPEHASH, block.chainid, safe)),
                keccak256(
                    abi.encode(
                        _SAFE_TX_TYPEHASH,
                        t.to,
                        t.value,
                        keccak256(t.data),
                        t.operation,
                        t.safeTxGas,
                        t.baseGas,
                        t.gasPrice,
                        t.gasToken,
                        t.refundReceiver,
                        t.nonce
                    )
                )
            )
        );
    }

    function _pokeTx(uint256 nonce) internal view returns (SafeTx memory) {
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
            nonce: nonce
        });
    }

    function _enqueue(SafeTx memory t, bytes memory signatures) internal {
        guard.enqueue(
            t.to,
            t.value,
            t.data,
            t.operation,
            t.safeTxGas,
            t.baseGas,
            t.gasPrice,
            t.gasToken,
            t.refundReceiver,
            t.nonce,
            signatures
        );
    }

    function _exec(SafeTx memory t, bytes memory signatures) internal returns (bool) {
        return safe.execTransaction(
            t.to,
            t.value,
            t.data,
            t.operation,
            t.safeTxGas,
            t.baseGas,
            t.gasPrice,
            t.gasToken,
            t.refundReceiver,
            signatures
        );
    }

    /// Enqueues a standard `poke` transaction and asserts the `SafeTransactionEnqueued` event.
    function _enqueuePoke() internal returns (SafeTx memory t, bytes32 txHash, bytes memory signatures) {
        t = _pokeTx(safe.nonce());
        txHash = _safeTxHash(t);
        signatures = _sign(3, txHash);

        vm.expectEmit(true, true, true, true, address(guard));
        emit IZeroExSettlerDeployerSafeGuard.SafeTransactionEnqueued(
            txHash,
            guard.delay() + vm.getBlockTimestamp(),
            t.to,
            t.value,
            t.data,
            t.operation,
            t.safeTxGas,
            t.baseGas,
            t.gasPrice,
            t.gasToken,
            t.refundReceiver,
            t.nonce,
            signatures
        );
        _enqueue(t, signatures);
    }

    // ----- MultiSend helpers -----

    function _encodeSubcall(Call memory c) internal pure returns (bytes memory) {
        return abi.encodePacked(uint8(Operation.Call), c.to, c.value, c.data.length, c.data);
    }

    function _checkCall() internal view returns (Call memory) {
        return Call({to: address(guard), value: 0, data: abi.encodeCall(guard.check, ())});
    }

    /// Builds `MultiSendCallOnly.multiSend` calldata. When `interleaveCheck` is set, a `guard.check()`
    /// sub-call is inserted between each user sub-call (the structure the Guard requires).
    function _buildMultiSend(Call[] memory calls, bool interleaveCheck) internal view returns (bytes memory) {
        bytes memory packed;
        for (uint256 i; i < calls.length; i++) {
            if (interleaveCheck && i != 0) {
                packed = abi.encodePacked(packed, _encodeSubcall(_checkCall()));
            }
            packed = abi.encodePacked(packed, _encodeSubcall(calls[i]));
        }
        return abi.encodeCall(_MULTICALL.multiSend, (packed));
    }

    /// Builds `MultiSend` calldata from a raw, verbatim list of sub-calls (no interleaving), so malformed
    /// batches (even count, missing `check()`, ...) can be constructed deliberately.
    function _buildMultiSendRaw(Call[] memory calls) internal pure returns (bytes memory) {
        bytes memory packed;
        for (uint256 i; i < calls.length; i++) {
            packed = abi.encodePacked(packed, _encodeSubcall(calls[i]));
        }
        return abi.encodeCall(_MULTICALL.multiSend, (packed));
    }

    // ----- Safe reconfiguration helpers -----

    /// The linked-list predecessor of `owner`, matching the Guard's `SafeLib.getPrevOwner` (sentinel == 1).
    function _safePrevOwner(address owner) internal view returns (address prev) {
        address[] memory cur = ISafeSetup(address(safe)).getOwners();
        prev = address(1);
        for (uint256 i; i < cur.length; i++) {
            if (cur[i] == owner) {
                return prev;
            }
            prev = cur[i];
        }
        revert("owner not found");
    }

    /// Reconfigures the Safe down to `numOwners`/`threshold` via pranked self-calls. These are direct calls
    /// to the Safe's `authorized` functions, NOT `execTransaction`, so they bypass the Guard's
    /// `checkTransaction`/`checkAfterExecution` hooks entirely (the Guard runs only inside `execTransaction`).
    /// This is the same mechanism `setUp` uses to churn owners, and it lets edge-config fixtures reach states
    /// (e.g. 2-of-4) that the Guard would reject on a real transaction. We remove the largest-address owners
    /// so the sorted `owners` array stays sorted after `pop()`.
    function _reconfigureTo(uint256 numOwners, uint256 threshold) internal {
        require(numOwners <= owners.length && numOwners >= 1, "bad reconfigure");
        while (owners.length > numOwners) {
            uint256 remaining = owners.length - 1;
            _removeOwnerDirect(owners[owners.length - 1].addr, threshold <= remaining ? threshold : remaining);
            owners.pop();
        }
        vm.prank(address(safe));
        ISafeSetup(address(safe)).changeThreshold(threshold);
    }

    function _removeOwnerDirect(address owner, uint256 threshold) internal {
        address prev = _safePrevOwner(owner);
        vm.prank(address(safe));
        ISafeSetup(address(safe)).removeOwner(prev, owner, threshold);
    }

    // ===================================================================================================
    // Migrated / renamed existing tests (now 3-of-5)
    // ===================================================================================================

    function test_Timelock_EnqueueWarpExecute_Succeeds() public {
        address singleton = safe.masterCopy();
        assertEq(
            abi.decode(safe.getStorageAt(uint256(keccak256("guard_manager.guard.address")), 1), (address)),
            address(guard)
        );
        (SafeTx memory t, bytes32 txHash, bytes memory signatures) = _enqueuePoke();

        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        vm.expectCall(
            address(guard),
            abi.encodeCall(
                guard.checkTransaction,
                (
                    t.to,
                    t.value,
                    t.data,
                    t.operation,
                    t.safeTxGas,
                    t.baseGas,
                    t.gasPrice,
                    t.gasToken,
                    t.refundReceiver,
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
        _exec(t, signatures);

        assertEq(pokeCounter, 1);
    }

    function test_Timelock_ExecuteBeforeElapsed_RevertsTimelockNotElapsed() external {
        (SafeTx memory t, bytes32 txHash, bytes memory signatures) = _enqueuePoke();

        vm.warp(vm.getBlockTimestamp() + guard.delay());

        vm.expectRevert(
            abi.encodeWithSelector(
                IZeroExSettlerDeployerSafeGuard.TimelockNotElapsed.selector, txHash, vm.getBlockTimestamp()
            )
        );
        _exec(t, signatures);
    }

    function test_Cancel_BeforeTimelock_MarksCanceled() external {
        (SafeTx memory t, bytes32 txHash, bytes memory signatures) = _enqueuePoke();

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
        _exec(t, signatures);
    }

    function test_Cancel_NoResignApproval_RevertsTxHashNotApproved() external {
        (, bytes32 txHash,) = _enqueuePoke();

        bytes32 resignTxHash = guard.resignTxHash(owners[3].addr);

        vm.prank(owners[3].addr);
        vm.expectRevert(
            abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.TxHashNotApproved.selector, resignTxHash)
        );
        guard.cancel(txHash);
    }

    function test_Cancel_NotOwner_RevertsPermissionDenied() external {
        (, bytes32 txHash,) = _enqueuePoke();

        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.PermissionDenied.selector));
        guard.cancel(txHash);
    }

    function test_Lockdown_WithUnlockApproval_BlocksExecution()
        public
        returns (SafeTx memory t, bytes32 txHash, bytes memory signatures)
    {
        (t, txHash, signatures) = _enqueuePoke();

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
        _exec(t, signatures);
    }

    function test_Lockdown_NoUnlockApproval_RevertsTxHashNotApproved() external {
        bytes32 unlockTxHash = guard.unlockTxHash();

        vm.prank(owners[3].addr);

        vm.expectRevert(
            abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.TxHashNotApproved.selector, unlockTxHash)
        );
        guard.lockDown();
    }

    function test_Lockdown_StaleResignApproval_RevertsTxHashNotApproved() external {
        (, bytes32 txHash,) = _enqueuePoke();

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

    function test_Lockdown_NextNonceResignApproval_Succeeds() external {
        (, bytes32 txHash,) = _enqueuePoke();

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

    function test_Resign_DirectRemoveOwner_DecrementsThresholdAndRemoves() external {
        (, bytes32 txHash,) = _enqueuePoke();

        address owner = owners[3].addr;

        bytes32 resignTxHash = guard.resignTxHash(owner);

        vm.startPrank(owner);
        safe.approveHash(resignTxHash);
        guard.cancel(txHash);
        vm.stopPrank();

        // At 3-of-5, `_getThresholdAfterResign` decrements the threshold from 3 to 2 because
        // `ownerCount - threshold == _MINIMUM_THRESHOLD`. The resignation `removeOwner` therefore carries
        // threshold 2, leaving a valid 4-owner / threshold-2 Safe.
        address prevOwner = _safePrevOwner(owner);
        bytes memory data =
            abi.encodeWithSignature("removeOwner(address,address,uint256)", prevOwner, owner, uint256(2));
        SafeTx memory t = SafeTx({
            to: address(safe),
            value: 0,
            data: data,
            operation: Operation.Call,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        txHash = _safeTxHash(t);
        assertEq(txHash, resignTxHash);

        // 3 effective signatures: owners[0], owners[1] (ECDSA) + owners[3]'s pre-approval.
        bytes memory signatures = abi.encodePacked(_sign(2, txHash), _approveHashSig(owner));
        _enqueue(t, signatures);

        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        vm.expectEmit(true, true, true, true, address(safe));
        emit ISafe.ExecutionSuccess(txHash, 0);
        _exec(t, signatures);

        assertFalse(safe.isOwner(owner));
        assertEq(ISafeSetup(address(safe)).getOwners().length, 4);
        assertEq(safe.getThreshold(), 2);
    }

    function test_Execute_EnableModule_RevertsModuleInstalled() external {
        bytes memory data = abi.encodeCall(safe.enableModule, (address(this)));
        SafeTx memory t = SafeTx({
            to: address(safe),
            value: 0,
            data: data,
            operation: Operation.Call,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        bytes32 txHash = _safeTxHash(t);
        bytes memory signatures = _sign(3, txHash);

        _enqueue(t, signatures);
        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        vm.expectRevert(abi.encodeWithSignature("ModuleInstalled(address)", address(this)));
        _exec(t, signatures);
    }

    function test_Unlock_Unanimous_RestoresOperation() external {
        (SafeTx memory t,, bytes memory signatures) = test_Lockdown_WithUnlockApproval_BlocksExecution();

        {
            SafeTx memory u = SafeTx({
                to: address(guard),
                value: 0,
                data: abi.encodeCall(guard.unlock, ()),
                operation: Operation.Call,
                safeTxGas: 0,
                baseGas: 0,
                gasPrice: 0,
                gasToken: address(0),
                refundReceiver: payable(address(0)),
                nonce: safe.nonce()
            });
            bytes32 unlockTxHash = _safeTxHash(u);

            // Unanimous (5 effective): owners 0,1,2,4 ECDSA + owners[3]'s pre-approval (placed in sorted order).
            bytes memory unlockSignatures = abi.encodePacked(
                _signSafeEncoded(owners[0], unlockTxHash),
                _signSafeEncoded(owners[1], unlockTxHash),
                _signSafeEncoded(owners[2], unlockTxHash),
                _approveHashSig(owners[3].addr),
                _signSafeEncoded(owners[4], unlockTxHash)
            );

            vm.expectEmit(true, true, true, true, address(safe));
            emit ISafe.ExecutionSuccess(unlockTxHash, 0);
            _exec(u, unlockSignatures);
        }

        // The old queued poke can no longer execute: the unlock consumed the nonce, so its signatures
        // recover to the wrong addresses.
        vm.expectRevert("GS026");
        _exec(t, signatures);

        test_Timelock_EnqueueWarpExecute_Succeeds();
    }

    function test_Unlock_NotUnanimous_RevertsNotUnanimous() external {
        test_Lockdown_WithUnlockApproval_BlocksExecution();

        SafeTx memory u = SafeTx({
            to: address(guard),
            value: 0,
            data: abi.encodeCall(guard.unlock, ()),
            operation: Operation.Call,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        bytes32 unlockTxHash = _safeTxHash(u);

        // 3 effective (meets the threshold so the Safe accepts it, but < 5 owners so the Guard rejects it).
        bytes memory unlockSignatures = abi.encodePacked(
            _signSafeEncoded(owners[1], unlockTxHash),
            _signSafeEncoded(owners[2], unlockTxHash),
            _approveHashSig(owners[3].addr)
        );

        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.NotUnanimous.selector, unlockTxHash));
        _exec(u, unlockSignatures);

        // This just validates that the signatures as encoded are otherwise valid in the absence of the guard.
        vm.store(address(safe), keccak256("guard_manager.guard.address"), bytes32(0));
        vm.expectEmit(true, true, true, true, address(safe));
        emit ISafe.ExecutionSuccess(unlockTxHash, 0);
        _exec(u, unlockSignatures);
    }

    function test_Multicall_SingleCall_Enqueue_Succeeds() external {
        Call[] memory calls = new Call[](1);
        calls[0] = Call({to: address(this), value: 0, data: abi.encodeCall(this.poke, ())});
        SafeTx memory t = SafeTx({
            to: address(_MULTICALL),
            value: 0,
            data: _buildMultiSend(calls, false),
            operation: Operation.DelegateCall,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        bytes32 txHash = _safeTxHash(t);
        bytes memory signatures = _sign(3, txHash);

        _enqueue(t, signatures);
    }

    function test_Multicall_SingleCall_EnqueueExecute_Succeeds() external {
        Call[] memory calls = new Call[](1);
        calls[0] = Call({to: address(this), value: 0, data: abi.encodeCall(this.poke, ())});
        SafeTx memory t = SafeTx({
            to: address(_MULTICALL),
            value: 0,
            data: _buildMultiSend(calls, false),
            operation: Operation.DelegateCall,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        bytes32 txHash = _safeTxHash(t);
        bytes memory signatures = _sign(3, txHash);

        _enqueue(t, signatures);
        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);
        _exec(t, signatures);

        assertEq(pokeCounter, 1);
    }

    function test_Install_OnePointFourPointOne_Succeeds() external {
        // uninstall the 1.3 guard
        vm.store(address(safe), keccak256("guard_manager.guard.address"), bytes32(0));

        // migrate to 1.4.1
        address onePointFourSingleton = 0x29fcB43b46531BcA003ddC8FCB67FFE91900C762;
        address onePointFourFallback = 0xfd0732Dc9E303f09fCEf3a7388Ad10A83459Ec99;

        MigrationDummy migration = new MigrationDummy();

        {
            bytes memory data = abi.encodeCall(migration.migrate, (onePointFourSingleton, onePointFourFallback));
            SafeTx memory t = SafeTx({
                to: address(migration),
                value: 0,
                data: data,
                operation: Operation.DelegateCall,
                safeTxGas: 0,
                baseGas: 0,
                gasPrice: 0,
                gasToken: address(0),
                refundReceiver: payable(address(0)),
                nonce: safe.nonce()
            });
            bytes32 txHash = _safeTxHash(t);
            bytes memory signatures = _sign(3, txHash);
            _exec(t, signatures);
        }

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
        {
            bytes memory data = abi.encodeCall(ISafeSetup.setGuard, (address(guard)));
            SafeTx memory t = SafeTx({
                to: address(safe),
                value: 0,
                data: data,
                operation: Operation.Call,
                safeTxGas: 0,
                baseGas: 0,
                gasPrice: 0,
                gasToken: address(0),
                refundReceiver: payable(address(0)),
                nonce: safe.nonce()
            });
            bytes32 txHash = _safeTxHash(t);
            bytes memory signatures = _sign(3, txHash);
            _exec(t, signatures);
        }

        test_Timelock_EnqueueWarpExecute_Succeeds();
    }

    // ===================================================================================================
    // New happy paths
    // ===================================================================================================

    function test_Unanimous_NoEnqueue_ExecutesImmediately() external {
        // A transaction signed by *all* owners bypasses the timelock: no `enqueue`, no warp.
        SafeTx memory t = _pokeTx(safe.nonce());
        bytes32 txHash = _safeTxHash(t);
        bytes memory signatures = _sign(5, txHash);

        vm.expectEmit(true, true, true, true, address(safe));
        emit ISafe.ExecutionSuccess(txHash, 0);
        _exec(t, signatures);

        assertEq(pokeCounter, 1);
    }

    function test_Unanimous_WithApproveHashSigner_ExecutesImmediately() external {
        SafeTx memory t = _pokeTx(safe.nonce());
        bytes32 txHash = _safeTxHash(t);

        // owners[4] (largest address) pre-approves rather than ECDSA-signing. The unanimity check
        // (`checkNSignatures(ownerCount)`) counts the approval toward the required count.
        vm.prank(owners[4].addr);
        safe.approveHash(txHash);
        bytes memory signatures = abi.encodePacked(_sign(4, txHash), _approveHashSig(owners[4].addr));

        vm.expectEmit(true, true, true, true, address(safe));
        emit ISafe.ExecutionSuccess(txHash, 0);
        _exec(t, signatures);

        assertEq(pokeCounter, 1);
    }

    function test_Multicall_MultiActionInterleavedCheck_Succeeds() external {
        Call[] memory calls = new Call[](2);
        calls[0] = Call({to: address(this), value: 0, data: abi.encodeCall(this.poke, ())});
        calls[1] = Call({to: address(this), value: 0, data: abi.encodeCall(this.poke, ())});
        // Produces [poke, check, poke]: two user actions interleaved by a guard `check()`.
        SafeTx memory t = SafeTx({
            to: address(_MULTICALL),
            value: 0,
            data: _buildMultiSend(calls, true),
            operation: Operation.DelegateCall,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        bytes32 txHash = _safeTxHash(t);
        bytes memory signatures = _sign(3, txHash);

        _enqueue(t, signatures);
        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);
        _exec(t, signatures);

        assertEq(pokeCounter, 2);
    }

    function test_Lockdown_Relock_AfterUnlock_Succeeds() external {
        // Issue_01: a malicious owner can re-lock the Safe after it is unlocked.
        bytes32 unlockTxHash = guard.unlockTxHash();
        vm.startPrank(owners[3].addr);
        safe.approveHash(unlockTxHash);
        guard.lockDown();
        vm.stopPrank();
        assertEq(guard.lockedDownBy(), owners[3].addr);

        // Unanimous unlock consumes the nonce.
        SafeTx memory u = SafeTx({
            to: address(guard),
            value: 0,
            data: abi.encodeCall(guard.unlock, ()),
            operation: Operation.Call,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        assertEq(_safeTxHash(u), unlockTxHash);
        bytes memory unlockSignatures = abi.encodePacked(
            _signSafeEncoded(owners[0], unlockTxHash),
            _signSafeEncoded(owners[1], unlockTxHash),
            _signSafeEncoded(owners[2], unlockTxHash),
            _approveHashSig(owners[3].addr),
            _signSafeEncoded(owners[4], unlockTxHash)
        );
        _exec(u, unlockSignatures);
        assertEq(guard.lockedDownBy(), address(0));

        // Re-lock: the unlock hash is fresh (nonce advanced), so a new approval is required.
        bytes32 newUnlockTxHash = guard.unlockTxHash();
        assertNotEq(newUnlockTxHash, unlockTxHash);
        vm.startPrank(owners[3].addr);
        safe.approveHash(newUnlockTxHash);
        vm.expectEmit(true, true, true, true, address(guard));
        emit IZeroExSettlerDeployerSafeGuard.LockDown(owners[3].addr, newUnlockTxHash);
        guard.lockDown();
        vm.stopPrank();
        assertEq(guard.lockedDownBy(), owners[3].addr);
    }

    function test_SetDelay_EmitsEvent_AndPreservesQueuedTimelock() external {
        // INV2: changing the delay must not retroactively alter an already-queued transaction.
        (SafeTx memory t, bytes32 txHash, bytes memory signatures) = _enqueuePoke();
        (uint256 timelockEnd0,) = guard.txInfo(txHash);
        assertEq(timelockEnd0, vm.getBlockTimestamp() + 1 weeks);

        vm.expectEmit(true, true, true, true, address(guard));
        emit IZeroExSettlerDeployerSafeGuard.TimelockUpdated(1 weeks, 2 weeks);
        vm.prank(address(safe));
        guard.setDelay(uint24(2 weeks));

        (uint256 timelockEnd1,) = guard.txInfo(txHash);
        assertEq(timelockEnd1, timelockEnd0);

        // The original 1-week timelock still governs the queued tx.
        vm.warp(vm.getBlockTimestamp() + 1 weeks + 1 seconds);
        _exec(t, signatures);
        assertEq(pokeCounter, 1);
    }

    // ===================================================================================================
    // New sad paths (reachable)
    // ===================================================================================================

    function test_Execute_NeverQueuedNonUnanimous_RevertsNotQueued() external {
        SafeTx memory t = _pokeTx(safe.nonce());
        bytes32 txHash = _safeTxHash(t);
        bytes memory signatures = _sign(3, txHash);

        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.NotQueued.selector, txHash));
        _exec(t, signatures);
    }

    function test_Enqueue_PastNonce_RevertsCannotEnqueuePastTransaction() external {
        // Issue_11: enqueue must reject transactions whose nonce is already consumed.
        uint256 pastNonce = safe.nonce() - 1;
        SafeTx memory t = _pokeTx(pastNonce);
        bytes32 txHash = _safeTxHash(t);
        bytes memory signatures = _sign(3, txHash);

        vm.expectRevert(
            abi.encodeWithSelector(
                IZeroExSettlerDeployerSafeGuard.CannotEnqueuePastTransaction.selector, txHash, pastNonce
            )
        );
        _enqueue(t, signatures);
    }

    function test_Enqueue_Duplicate_RevertsAlreadyQueued() external {
        (SafeTx memory t, bytes32 txHash, bytes memory signatures) = _enqueuePoke();

        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.AlreadyQueued.selector, txHash));
        _enqueue(t, signatures);
    }

    function test_Cancel_AfterTimelockElapsed_RevertsTimelockElapsed() external {
        (, bytes32 txHash,) = _enqueuePoke();
        (uint256 timelockEnd,) = guard.txInfo(txHash);

        address owner = owners[3].addr;
        bytes32 resignTxHash = guard.resignTxHash(owner);
        vm.prank(owner);
        safe.approveHash(resignTxHash);

        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        vm.prank(owner);
        vm.expectRevert(
            abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.TimelockElapsed.selector, txHash, timelockEnd)
        );
        guard.cancel(txHash);
    }

    function test_Cancel_OwnResignation_RevertsCannotCancelOwnResignation() external {
        // Issue_05: an owner cannot cancel their own (directly-queued) resignation.
        address owner = owners[3].addr;
        address prevOwner = _safePrevOwner(owner);
        // The resignation `removeOwner` carries the decremented threshold 2 (see the resign test).
        bytes memory data =
            abi.encodeWithSignature("removeOwner(address,address,uint256)", prevOwner, owner, uint256(2));
        SafeTx memory t = SafeTx({
            to: address(safe),
            value: 0,
            data: data,
            operation: Operation.Call,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        bytes32 txHash = _safeTxHash(t);
        assertEq(txHash, guard.resignTxHash(owner));

        // Queue it with threshold signatures from *other* owners.
        _enqueue(t, _sign(3, txHash));

        // The owner pre-approves the resignation (also the cancel target) and tries to cancel it.
        vm.startPrank(owner);
        safe.approveHash(txHash);
        vm.expectRevert(
            abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.CannotCancelOwnResignation.selector, txHash)
        );
        guard.cancel(txHash);
        vm.stopPrank();
    }

    function test_Unlock_NotLockedDown_RevertsNotLockedDown() external {
        vm.prank(address(safe));
        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.NotLockedDown.selector));
        guard.unlock();
    }

    function test_Enqueue_DelegateCallNonMultiSend_RevertsNoDelegateCall() external {
        SafeTx memory t = SafeTx({
            to: address(this),
            value: 0,
            data: hex"",
            operation: Operation.DelegateCall,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        // `_checkDelegateCall` rejects any delegatecall target other than MultiSendCallOnly, before signatures.
        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.NoDelegateCall.selector));
        _enqueue(t, hex"");
    }

    function test_Enqueue_EvenMultiSendCount_RevertsEvenNumberOfMultiCalls() external {
        // [poke, check] is structurally well-interleaved but has an even sub-call count.
        Call[] memory calls = new Call[](2);
        calls[0] = Call({to: address(this), value: 0, data: abi.encodeCall(this.poke, ())});
        calls[1] = _checkCall();
        SafeTx memory t = SafeTx({
            to: address(_MULTICALL),
            value: 0,
            data: _buildMultiSendRaw(calls),
            operation: Operation.DelegateCall,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        bytes32 txHash = _safeTxHash(t);

        vm.expectRevert(
            abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.EvenNumberOfMultiCalls.selector, uint256(2))
        );
        _enqueue(t, _sign(3, txHash));
    }

    function test_Enqueue_MissingInterleavedCheck_RevertsGuardCheckNotEnforced() external {
        // [poke, poke, check]: the call at the odd index (1) must be `check()` but is a user call.
        bytes memory pokeData = abi.encodeCall(this.poke, ());
        Call[] memory calls = new Call[](3);
        calls[0] = Call({to: address(this), value: 0, data: pokeData});
        calls[1] = Call({to: address(this), value: 0, data: pokeData});
        calls[2] = _checkCall();
        SafeTx memory t = SafeTx({
            to: address(_MULTICALL),
            value: 0,
            data: _buildMultiSendRaw(calls),
            operation: Operation.DelegateCall,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        bytes32 txHash = _safeTxHash(t);

        vm.expectRevert(
            abi.encodeWithSelector(
                IZeroExSettlerDeployerSafeGuard.GuardCheckNotEnforced.selector, uint256(1), address(this), pokeData
            )
        );
        _enqueue(t, _sign(3, txHash));
    }

    function test_Enqueue_DirectConfusedDeputy_RevertsConfusedDeputy() external {
        // A direct call to the guard's own `checkAfterExecution` is a confused-deputy attempt.
        bytes memory data = abi.encodeCall(guard.checkAfterExecution, (bytes32(0), false));
        SafeTx memory t = SafeTx({
            to: address(guard),
            value: 0,
            data: data,
            operation: Operation.Call,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        vm.expectRevert(
            abi.encodeWithSelector(
                IZeroExSettlerDeployerSafeGuard.ConfusedDeputy.selector, uint256(0), address(guard), data
            )
        );
        _enqueue(t, hex"");
    }

    function test_Enqueue_MultiSendConfusedDeputy_RevertsConfusedDeputy() external {
        bytes memory confusedData = abi.encodeCall(guard.checkAfterExecution, (bytes32(0), false));
        Call[] memory calls = new Call[](1);
        calls[0] = Call({to: address(guard), value: 0, data: confusedData});
        SafeTx memory t = SafeTx({
            to: address(_MULTICALL),
            value: 0,
            data: _buildMultiSendRaw(calls),
            operation: Operation.DelegateCall,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        vm.expectRevert(
            abi.encodeWithSelector(
                IZeroExSettlerDeployerSafeGuard.ConfusedDeputy.selector, uint256(0), address(guard), confusedData
            )
        );
        _enqueue(t, hex"");
    }

    function test_Execute_Erc20Sponsorship_RevertsErc20SponsorshipUnsafe() external {
        // A privileged-call transaction (here a no-op `setFallbackHandler` to the current handler) with ERC20
        // gas sponsorship is rejected in `checkTransaction`. The no-op target means only the sponsorship gate
        // fires (not `IncorrectFallbackHandler`).
        address fallbackHandler =
            abi.decode(safe.getStorageAt(uint256(keccak256("fallback_manager.handler.address")), 1), (address));
        address gasToken = address(0xDEAD);
        bytes memory data = abi.encodeCall(ISafeSetup.setFallbackHandler, (fallbackHandler));
        SafeTx memory t = SafeTx({
            to: address(safe),
            value: 0,
            data: data,
            operation: Operation.Call,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 1,
            gasToken: gasToken,
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        bytes32 txHash = _safeTxHash(t);
        bytes memory signatures = _sign(3, txHash);

        _enqueue(t, signatures);
        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        vm.expectRevert(
            abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.ERC20SponsorshipUnsafe.selector, gasToken)
        );
        _exec(t, signatures);
    }

    function test_Execute_SetFallbackHandlerNonDefault_RevertsIncorrectFallbackHandler() external {
        address badHandler = address(0xBEEF);
        bytes memory data = abi.encodeCall(ISafeSetup.setFallbackHandler, (badHandler));
        SafeTx memory t = SafeTx({
            to: address(safe),
            value: 0,
            data: data,
            operation: Operation.Call,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        bytes32 txHash = _safeTxHash(t);
        bytes memory signatures = _sign(3, txHash);

        _enqueue(t, signatures);
        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        vm.expectRevert(
            abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.IncorrectFallbackHandler.selector, badHandler)
        );
        _exec(t, signatures);
    }

    function test_Execute_AddGuardAsOwner_RevertsGuardIsOwner() external {
        bytes memory data = abi.encodeCall(ISafeSetup.addOwnerWithThreshold, (address(guard), 3));
        SafeTx memory t = SafeTx({
            to: address(safe),
            value: 0,
            data: data,
            operation: Operation.Call,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        bytes32 txHash = _safeTxHash(t);
        bytes memory signatures = _sign(3, txHash);

        _enqueue(t, signatures);
        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.GuardIsOwner.selector));
        _exec(t, signatures);
    }

    function test_Execute_ChangeThresholdToOne_RevertsThresholdTooLow() external {
        bytes memory data = abi.encodeCall(ISafeSetup.changeThreshold, (1));
        SafeTx memory t = SafeTx({
            to: address(safe),
            value: 0,
            data: data,
            operation: Operation.Call,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        bytes32 txHash = _safeTxHash(t);
        bytes memory signatures = _sign(3, txHash);

        _enqueue(t, signatures);
        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.ThresholdTooLow.selector, uint256(1)));
        _exec(t, signatures);
    }

    function test_Execute_ChangeThresholdTooHigh_RevertsThresholdTooHigh() external {
        // 5 owners with threshold 4 leaves only 1 owner outside the threshold (< _MINIMUM_THRESHOLD).
        bytes memory data = abi.encodeCall(ISafeSetup.changeThreshold, (4));
        SafeTx memory t = SafeTx({
            to: address(safe),
            value: 0,
            data: data,
            operation: Operation.Call,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        bytes32 txHash = _safeTxHash(t);
        bytes memory signatures = _sign(3, txHash);

        _enqueue(t, signatures);
        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.ThresholdTooHigh.selector, uint256(4)));
        _exec(t, signatures);
    }

    function test_Execute_ReentrantGuardCall_RevertsReentrancy() external {
        ReentrantTarget target = new ReentrantTarget(guard);
        SafeTx memory t = SafeTx({
            to: address(target),
            value: 0,
            data: abi.encodeCall(target.attack, ()),
            operation: Operation.Call,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        bytes32 txHash = _safeTxHash(t);
        bytes memory signatures = _sign(3, txHash);

        _enqueue(t, signatures);
        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);
        // `attack()` re-enters the guard mid-execution and internally captures the revert (the Safe would
        // otherwise swallow it as GS013), so the outer transaction succeeds.
        _exec(t, signatures);

        assertEq(target.capturedSelector(), IZeroExSettlerDeployerSafeGuard.Reentrancy.selector);
    }

    function test_Check_CalledOutsideExecution_RevertsReentrancy() external {
        // `check()` is only valid mid-execution (reentrancy lock set); calling it directly reverts.
        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.Reentrancy.selector));
        guard.check();
    }

    function test_Multicall_RemoveGuardMidBatch_Reverts() external {
        // [setGuard(0), check, poke]: removing the guard mid-batch is caught by the interleaved `check()`,
        // which reverts `GuardRemoved`. Safe's `execute` swallows the inner reason, surfacing GS013.
        Call[] memory calls = new Call[](2);
        calls[0] = Call({to: address(safe), value: 0, data: abi.encodeCall(ISafeSetup.setGuard, (address(0)))});
        calls[1] = Call({to: address(this), value: 0, data: abi.encodeCall(this.poke, ())});
        SafeTx memory t = SafeTx({
            to: address(_MULTICALL),
            value: 0,
            data: _buildMultiSend(calls, true),
            operation: Operation.DelegateCall,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        bytes32 txHash = _safeTxHash(t);
        bytes memory signatures = _sign(3, txHash);

        _enqueue(t, signatures);
        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        vm.expectRevert("GS013");
        _exec(t, signatures);
    }

    function test_Enqueue_AfterGuardUninstalled_RevertsGuardNotInstalled() external {
        // Uninstall the guard through the timelock (single `setGuard(0)` action). On the post-check the guard
        // fails open and marks itself removed.
        bytes memory data = abi.encodeCall(ISafeSetup.setGuard, (address(0)));
        SafeTx memory t = SafeTx({
            to: address(safe),
            value: 0,
            data: data,
            operation: Operation.Call,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        bytes32 txHash = _safeTxHash(t);
        bytes memory signatures = _sign(3, txHash);

        _enqueue(t, signatures);
        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);
        vm.expectEmit(true, true, true, true, address(guard));
        emit IZeroExSettlerDeployerSafeGuard.Uninstalled();
        _exec(t, signatures);

        // The guard has failed open; further enqueues revert.
        SafeTx memory p = _pokeTx(safe.nonce());
        bytes32 pHash = _safeTxHash(p);
        bytes memory pSigs = _sign(3, pHash);
        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.GuardNotInstalled.selector));
        _enqueue(p, pSigs);
    }

    function test_Enqueue_FutureNonce_NonCancellableAfterDelay() external {
        // Issue_18: a future-nonce transaction can be queued, but becomes non-cancellable once its timelock
        // elapses (even though it still cannot execute until the Safe reaches that nonce).
        uint256 futureNonce = safe.nonce() + 1;
        SafeTx memory t = _pokeTx(futureNonce);
        bytes32 txHash = _safeTxHash(t);
        bytes memory signatures = _sign(3, txHash);
        _enqueue(t, signatures);

        (uint256 timelockEnd,) = guard.txInfo(txHash);

        address owner = owners[3].addr;
        bytes32 resignTxHash = guard.resignTxHash(owner);
        vm.prank(owner);
        safe.approveHash(resignTxHash);

        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);
        vm.prank(owner);
        vm.expectRevert(
            abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.TimelockElapsed.selector, txHash, timelockEnd)
        );
        guard.cancel(txHash);
    }

    // ===================================================================================================
    // New sad paths requiring a non-default owner/threshold configuration
    // ===================================================================================================

    function test_Execute_RemoveBelowMinimumOwners_RevertsNotEnoughOwners() external {
        _reconfigureTo(4, 2);

        address victim = owners[3].addr;
        address prevOwner = _safePrevOwner(victim);
        bytes memory data =
            abi.encodeWithSignature("removeOwner(address,address,uint256)", prevOwner, victim, uint256(2));
        SafeTx memory t = SafeTx({
            to: address(safe),
            value: 0,
            data: data,
            operation: Operation.Call,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        bytes32 txHash = _safeTxHash(t);
        bytes memory signatures = _sign(2, txHash);

        _enqueue(t, signatures);
        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.NotEnoughOwners.selector, uint256(3)));
        _exec(t, signatures);
    }

    function test_ForcedResignation_AtTwoOfFourFloor_Reverts() external {
        // Issue_03: at the 2-of-4 floor, a forced resignation cannot execute — removing any owner drops the
        // Safe below _MINIMUM_OWNERS. This is why the documented minimum deployment configuration is 2-of-5:
        // the guard's anti-griefing recovery is degenerate at the floor.
        _reconfigureTo(4, 2);

        address owner = owners[3].addr;
        address prevOwner = _safePrevOwner(owner);
        // `_getThresholdAfterResign` decrements 2 -> 1 here (ownerCount - threshold == _MINIMUM_THRESHOLD).
        bytes memory data =
            abi.encodeWithSignature("removeOwner(address,address,uint256)", prevOwner, owner, uint256(1));
        SafeTx memory t = SafeTx({
            to: address(safe),
            value: 0,
            data: data,
            operation: Operation.Call,
            safeTxGas: 0,
            baseGas: 0,
            gasPrice: 0,
            gasToken: address(0),
            refundReceiver: payable(address(0)),
            nonce: safe.nonce()
        });
        bytes32 txHash = _safeTxHash(t);
        assertEq(txHash, guard.resignTxHash(owner));
        bytes memory signatures = _sign(2, txHash);

        _enqueue(t, signatures);
        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        // The owner-count check precedes the threshold check, so `NotEnoughOwners` surfaces first.
        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.NotEnoughOwners.selector, uint256(3)));
        _exec(t, signatures);
    }

    function test_Timelock_RemoveNonSignerMakesUnanimous_BypassesTimelock() external {
        // Issue_16: a queued tx signed by K of K+1 owners can bypass its timelock if the lone non-signer is
        // removed during the timelock window — the K signatures then constitute unanimity.
        SafeTx memory t = _pokeTx(safe.nonce());
        bytes32 txHash = _safeTxHash(t);
        // Signed by owners 0..3 (4 of 5): non-unanimous, so it would normally require the timelock.
        bytes memory signatures = _sign(4, txHash);
        _enqueue(t, signatures);

        // Remove the lone non-signer (owners[4]) WITHOUT consuming a Safe nonce (a pranked direct call) so the
        // queued tx's hash stays valid, and drop the threshold to 2 so the resulting 4-owner Safe passes the
        // guard's post-checks. The removal mechanism is abstracted; what matters is the owner set shrinks to
        // exactly the signers.
        _removeOwnerDirect(owners[4].addr, 2);
        owners.pop();
        assertEq(ISafeSetup(address(safe)).getOwners().length, 4);

        // Execute BEFORE the timelock elapses: the 4 signatures now equal `ownerCount`, so the unanimity path
        // bypasses the timelock.
        vm.expectEmit(true, true, true, true, address(safe));
        emit ISafe.ExecutionSuccess(txHash, 0);
        _exec(t, signatures);
        assertEq(pokeCounter, 1);
    }

    // Note on `UnexpectedUpgrade`: it is not reachable while the guard is installed. Changing the Safe's
    // singleton (`masterCopy`) requires a DELEGATECALL to a migration contract, which the guard forbids
    // (`NoDelegateCall` — only MultiSendCallOnly is permitted, and its sub-calls are CALLs that cannot alter
    // the proxy's singleton slot). The only way to migrate is to first uninstall the guard, after which the
    // guard fails open and `checkAfterExecution` early-returns. `test_Install_OnePointFourPointOne_Succeeds`
    // exercises that realistic migration path.
}
