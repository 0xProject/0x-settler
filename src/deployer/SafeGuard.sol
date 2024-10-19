// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

enum Operation {
    Call,
    DelegateCall
}

interface ISafeMinimal {
    function encodeTransactionData(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        uint256 safeTxGas,
        uint256 baseGas,
        uint256 gasPrice,
        address gasToken,
        address payable refundReceiver,
        uint256 nonce
    ) external view returns (bytes memory);

    function checkNSignatures(bytes32 dataHash, bytes memory data, bytes memory signatures, uint256 requiredSignatures)
        external
        view;

    function nonce() external view returns (uint256);

    function isOwner(address) external view returns (bool);

    function getStorageAt(uint256 offset, uint256 length) external view returns (bytes memory);

    function approvedHashes(address owner, bytes32 txHash) external view returns (uint256);
}

library SafeLib {
    function getTransactionHash(
        ISafeMinimal safe,
        address to,
        uint256 value,
        bytes memory data,
        Operation operation,
        uint256 safeTxGas,
        uint256 baseGas,
        uint256 gasPrice,
        address gasToken,
        address payable refundReceiver,
        uint256 nonce
    ) internal view returns (bytes32) {
        return getTransactionHash(
            safe,
            safe.encodeTransactionData(
                to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, nonce
            )
        );
    }

    function getTransactionHash(ISafeMinimal, bytes memory signingData) internal pure returns (bytes32) {
        return keccak256(signingData);
    }
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

contract EvmVersionDummy {
    fallback() external {
        assembly ("memory-safe") {
            mstore(0x00, 0x01)
            return(0x00, 0x20)
        }
    }
}

contract ZeroExSettlerDeployerSafeGuard is IGuard {
    using SafeLib for ISafeMinimal;

    event TimelockUpdated(uint256 oldDelay, uint256 newDelay);
    event SafeTransactionEnqueued(
        bytes32 indexed txHash,
        uint256 timelockEnd,
        address to,
        uint256 value,
        bytes data,
        Operation operation,
        uint256 safeTxGas,
        uint256 baseGas,
        uint256 gasPrice,
        address gasToken,
        address payable refundReceiver,
        uint256 nonce
    );
    event SafeTransactionCanceled(bytes32 indexed txHash);
    event LockDown(address indexed lockedDownBy, bytes32 indexed unlockTxHash);
    event Unlocked();

    error PermissionDenied();
    error NoDelegateToGuard();
    error TimelockNotElapsed(bytes32 txHash, uint256 timelockEnd);
    error TimelockElapsed(bytes32 txHash, uint256 timelockEnd);
    error NotQueued(bytes32 txHash);
    error LockedDown(address lockedDownBy);
    error NotLockedDown();
    error UnlockHashNotApproved(bytes32 txHash);

    struct NextTransaction {
        bytes32 txHash;
        uint256 timelockEnd;
    }

    uint256 public delay;
    NextTransaction public nextTransaction;
    address public lockedDownBy;

    ISafeMinimal public immutable safe;
    bytes32 internal constant _EVM_VERSION_DUMMY_INITHASH = bytes32(0); // TODO: ensure London hardfork
    uint256 internal constant _OWNER_COUNT_SLOT = 3;

    constructor(address _safe, uint256 _delay) {
        assert(keccak256(type(EvmVersionDummy).creationCode) == _EVM_VERSION_DUMMY_INITHASH || block.chainid == 31337);
        safe = ISafeMinimal(_safe);
        delay = _delay;
        emit TimelockUpdated(0, _delay);
    }

    function _requireSafe() private view {
        if (msg.sender != address(safe)) {
            revert PermissionDenied();
        }
    }

    modifier onlySafe() {
        _requireSafe();
        _;
    }

    function _requireOwner() private view {
        if (!safe.isOwner(msg.sender)) {
            revert PermissionDenied();
        }
    }

    modifier onlyOwner() {
        _requireOwner();
        _;
    }

    function _requireNotLockedDown() private view {
        if (lockedDownBy != address(0)) {
            revert LockedDown(lockedDownBy);
        }
    }

    modifier notLockedDown() {
        _requireNotLockedDown();
        _;
    }

    function _requireLockedDown() private view {
        if (lockedDownBy == address(0)) {
            revert NotLockedDown();
        }
    }

    function _hashThisTx(
        ISafeMinimal _safe,
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        uint256 safeTxGas,
        uint256 baseGas,
        uint256 gasPrice,
        address gasToken,
        address payable refundReceiver
    ) private view returns (bytes32 txHash, bytes memory txHashData) {
        // The nonce has already been incremented past the value used in the currently-executing
        // transaction. We decrement it to get the value that was hashed to get the `txHash`.
        uint256 nonce;
        unchecked {
            nonce = _safe.nonce() - 1;
        }
        txHashData = _safe.encodeTransactionData(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, nonce
        );
        txHash = _safe.getTransactionHash(txHashData);
    }

    function checkTransaction(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        uint256 safeTxGas,
        uint256 baseGas,
        uint256 gasPrice,
        address gasToken,
        address payable refundReceiver,
        bytes calldata signatures,
        address // msgSender
    ) external override onlySafe /* `notLockedDown` is on `checkAfterExecution(...)` */ {
        ISafeMinimal _safe = ISafeMinimal(msg.sender);

        // There are 2 special cases to handle (transactions that don't require doing through the
        // timelock). A transaction that enqueues another transaction, and unlocking after a
        // lockdown.
        if (to == address(this)) {
            if (operation != Operation.Call) {
                revert NoDelegateToGuard();
            }
            uint256 selector = uint32(bytes4(data));
            if (selector == uint32(this.enqueue.selector)) {
                // A simple call to `enqueue` is always allowed. This is harmless and any additional
                // checks will be performed when the queue'd call is attempted.
                return;
            }
            if (selector == uint32(this.unlock.selector)) {
                // A call to `unlock` does not go through the timelock, but we require additional
                // signatures in order for the lockdown functionality to be effective, as a
                // protocol.

                // We have to check that we're locked down both here *and* in `unlock()` to
                // ensure that the stored approved hash that is registered prior to calling
                // `lockDown()` can't be wasted before `lockDown()` is actually called.
                _requireLockedDown();

                // Calling `unlock()` requires unanimous signatures, i.e. a threshold equal to the
                // owner count. The owner who called `lockDown()` has already signed (to prevent
                // griefing).
                uint256 ownerCount = abi.decode(_safe.getStorageAt(_OWNER_COUNT_SLOT, 1), (uint256));

                // Due to a quirk of how `checkNSignatures` works (sometimes validating `msg.sender`
                // for gas optimization), we could end up in a bizarre situation if `address(this)`
                // is an owner. Let's just prohibit that entirely.
                require(!_safe.isOwner(address(this))); // TODO: the copy of this check in `lockDown()` may be sufficient

                // `txHashData` is used here for an outdated, nonstandard variant of nested
                // ERC1271 signatures that passes the signing hash as `bytes` instead of as
                // `bytes32`
                (bytes32 txHash, bytes memory txHashData) = _hashThisTx(
                    _safe, to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver
                );
                _safe.checkNSignatures(txHash, txHashData, signatures, ownerCount);

                return;
            }
        }

        // We're not in either of the 2 special cases. The checks that need to be performed here are
        // 1) that the transaction was previously queued through `enqueue` and 2) that `delay` has
        // elapsed since `enqueue` was called.
        {
            (bytes32 txHash,) =
                _hashThisTx(_safe, to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver);
            if (txHash != nextTransaction.txHash) {
                revert NotQueued(txHash);
            }
            uint256 timelockEnd = nextTransaction.timelockEnd;
            if (block.timestamp <= timelockEnd) {
                revert TimelockNotElapsed(txHash, timelockEnd);
            }
        }

        delete nextTransaction;
    }

    // The `notLockedDown` modifier prevents all transactions while the Safe is in lockdown _except_
    // the call to `unlock`.
    function checkAfterExecution(bytes32, bool) external view override onlySafe notLockedDown {}

    function enqueue(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        uint256 safeTxGas,
        uint256 baseGas,
        uint256 gasPrice,
        address gasToken,
        address payable refundReceiver
    ) external onlySafe {
        ISafeMinimal _safe = ISafeMinimal(msg.sender);

        // This is not the same as `_hashThisTx` because we're hashing the _next_ transaction to be
        // executed by the Safe, not the transaction _currently_ executing.
        uint256 nonce = _safe.nonce();
        bytes32 txHash = _safe.getTransactionHash(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, nonce
        );

        uint256 timelockEnd = block.timestamp + delay;
        (nextTransaction.txHash, nextTransaction.timelockEnd) = (txHash, timelockEnd);

        emit SafeTransactionEnqueued(
            txHash,
            timelockEnd,
            to,
            value,
            data,
            operation,
            safeTxGas,
            baseGas,
            gasPrice,
            gasToken,
            refundReceiver,
            nonce
        );
    }

    /// It's totally possible to brick the timelock (and consequently, the entire safe) if you set
    /// the delay too long. Don't do that.
    function setDelay(uint256 newDelay) external onlySafe {
        emit TimelockUpdated(delay, newDelay);
        delay = newDelay;
    }

    function cancel(bytes32 txHash) external onlyOwner {
        if (txHash != nextTransaction.txHash) {
            revert NotQueued(txHash);
        }
        uint256 timelockEnd = nextTransaction.timelockEnd;
        if (block.timestamp > timelockEnd) {
            revert TimelockElapsed(txHash, timelockEnd);
        }
        delete nextTransaction;
        emit SafeTransactionCanceled(txHash);
    }

    function lockDownTxHash() public view returns (bytes32) {
        uint256 nonce = safe.nonce();
        return safe.getTransactionHash(
            address(this),
            0 ether,
            abi.encodeCall(this.unlock, ()),
            Operation.Call,
            0,
            0,
            0,
            address(0),
            payable(address(0)),
            nonce
        );
    }

    function lockDown() external onlyOwner notLockedDown {
        require(!safe.isOwner(address(this)));
        bytes32 txHash = lockDownTxHash();
        if (safe.approvedHashes(msg.sender, txHash) != 1) {
            revert UnlockHashNotApproved(txHash);
        }
        lockedDownBy = msg.sender;
        emit LockDown(msg.sender, txHash);
    }

    function unlock() external onlySafe {
        _requireLockedDown();
        delete lockedDownBy;
        emit Unlocked();
    }
}
