// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

enum Operation {
    Call,
    DelegateCall
}

interface ISafeMinimal {
    function checkNSignatures(bytes32 dataHash, bytes memory data, bytes memory signatures, uint256 requiredSignatures)
        external
        view;

    function checkSignatures(bytes32 dataHash, bytes memory data, bytes memory signatures) external view;

    function nonce() external view returns (uint256);

    function isOwner(address) external view returns (bool);

    function getStorageAt(uint256 offset, uint256 length) external view returns (bytes memory);

    function approvedHashes(address owner, bytes32 txHash) external view returns (uint256);
}

library SafeLib {
    function encodeTransactionData(
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
    ) internal view returns (bytes memory) {
        bytes32 safeTxHash = keccak256(
            abi.encode(
                SAFE_TX_TYPEHASH(safe),
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
        );
        return abi.encodePacked(hex"1901", domainSeparator(safe), safeTxHash);
    }

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
            encodeTransactionData(
                safe, to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, nonce
            )
        );
    }

    function getTransactionHash(ISafeMinimal, bytes memory txHashData) internal pure returns (bytes32) {
        return keccak256(txHashData);
    }

    uint256 private constant _OWNER_COUNT_SLOT = 3;

    function ownerCount(ISafeMinimal safe) internal view returns (uint256) {
        return abi.decode(safe.getStorageAt(_OWNER_COUNT_SLOT, 1), (uint256));
    }

    function DOMAIN_SEPARATOR_TYPEHASH(ISafeMinimal) internal pure returns (bytes32) {
        // keccak256(
        //     "EIP712Domain(uint256 chainId,address verifyingContract)"
        // );
        return 0x47e79534a245952e8b16893a336b85a3d9ea9fa8c573f3d803afb92a79469218;
    }

    function domainSeparator(ISafeMinimal safe) internal view returns (bytes32) {
        return keccak256(abi.encode(DOMAIN_SEPARATOR_TYPEHASH(safe), block.chainid, safe));
    }

    function SAFE_TX_TYPEHASH(ISafeMinimal) internal pure returns (bytes32) {
        // keccak256(
        //     "SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)"
        // );
        return 0xbb8310d486368db6bd6f849402fdd73ad53d316b5a4b2644ad6efe0f941286d8;
    }

    uint256 private constant _SINGLETON_SLOT = 0;

    function singleton(ISafeMinimal safe) internal view returns (address) {
        return abi.decode(safe.getStorageAt(_SINGLETON_SLOT, 1), (address));
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
        uint256 nonce,
        bytes signatures
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
    error UnexpectedUpgrade(address newSingleton);

    uint256 public delay;
    mapping(bytes32 => uint256) public timelockEnd;
    address public lockedDownBy;

    ISafeMinimal public immutable safe;
    bytes32 internal constant _EVM_VERSION_DUMMY_INITHASH = bytes32(0); // TODO: ensure London hardfork
    address internal constant _SINGLETON = 0xfb1bffC9d739B8D520DaF37dF666da4C687191EA;

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
    ) external view override onlySafe {
        ISafeMinimal _safe = ISafeMinimal(msg.sender);

        // The nonce has already been incremented past the value used in the
        // currently-executing transaction. We decrement it to get the value that was hashed
        // to get the `txHash`.
        uint256 nonce = _safe.nonce() - 1;

        // `txHashData` is used here for an outdated, nonstandard variant of nested ERC1271
        // signatures that passes the signing hash as `bytes` instead of as `bytes32`. This only
        // matters for the `checkNSignatures` call when validating before `unlock()`.
        bytes memory txHashData = _safe.encodeTransactionData(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, nonce
        );
        bytes32 txHash = _safe.getTransactionHash(txHashData);

        // The call to `this.unlock()` is special-cased.
        if (to == address(this)) {
            if (operation != Operation.Call) {
                revert NoDelegateToGuard();
            }
            if (uint256(uint32(bytes4(data))) == uint256(uint32(this.unlock.selector))) {
                // A call to `unlock` does not go through the timelock, but we require additional
                // signatures in order for the lockdown functionality to be effective, as a
                // protocol.

                // We have to check that we're locked down both here *and* in `unlock()` to
                // ensure that the stored approved hash that is registered prior to calling
                // `lockDown()` can't be wasted before `lockDown()` is actually called.
                _requireLockedDown();

                // Calling `unlock()` requires unanimous signatures, i.e. a threshold equal to the
                // owner count. We go beyond the usual requirement of just the threshold. The owner
                // who called `lockDown()` has already signed (to prevent griefing).
                uint256 ownerCount = _safe.ownerCount();
                _safe.checkNSignatures(txHash, txHashData, signatures, ownerCount);

                return;
            }
        }
        // Fall through to the "normal" case, where we're doing anything except calling
        // `this.unlock()`. The checks that need to be performed here are 1) that the Safe is not
        // locked down, 2) that the transaction was previously queued through `enqueue` and 3) that
        // `delay` has elapsed since `enqueue` was called.

        // We check that the Safe is not locked down twice. We have to check it here to ensure that
        // we're not smuggling a call to `unlock()` through (e.g.) a delegatecall to
        // MultiSendCallOnly.
        _requireNotLockedDown();

        uint256 _timelockEnd = timelockEnd[txHash];

        if (_timelockEnd == 0) {
            revert NotQueued(txHash);
        }
        if (block.timestamp <= _timelockEnd) {
            revert TimelockNotElapsed(txHash, _timelockEnd);
        }
    }

    // We check that the Safe is not locked down twice. We have to check it here to ensure that the
    // call to `unlock()` can't revert and burn signatures (increase the nonce), resulting in a
    // bricked/griefing attack by a malicious owner.
    function checkAfterExecution(bytes32, bool) external view override onlySafe notLockedDown {
        ISafeMinimal _safe = ISafeMinimal(msg.sender);

        // Due to a quirk of how `checkNSignatures` works (called as a precondition to `unlock`;
        // sometimes it validates `msg.sender` instead of a signature, for gas optimization), we
        // could end up in a bizarre situation if `address(this)` is an owner. This would make our
        // introspection checks wrong. Let's just prohibit that entirely.
        require(!_safe.isOwner(address(this)));

        // A malicious upgrade could lie to us about this. We're not trying to prevent that. We're
        // trying to prevent an unexpected upgrade that may break our ability to reliably introspect
        // the aspects of the Safe that are required for the correct function of this guard.
        address singleton = _safe.singleton();
        if (singleton != _SINGLETON) {
            revert UnexpectedUpgrade(singleton);
        }
    }

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
    ) external {
        bytes memory txHashData = safe.encodeTransactionData(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, nonce
        );
        bytes32 txHash = safe.getTransactionHash(txHashData);
        safe.checkSignatures(txHash, txHashData, signatures);

        uint256 _timelockEnd = block.timestamp + delay;
        timelockEnd[txHash] = _timelockEnd;

        emit SafeTransactionEnqueued(
            txHash,
            _timelockEnd,
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
    }

    /// It's totally possible to brick the timelock (and consequently, the entire Safe) if you set
    /// the delay too long. Don't do that.
    function setDelay(uint256 newDelay) external onlySafe {
        emit TimelockUpdated(delay, newDelay);
        delay = newDelay;
    }

    function cancel(bytes32 txHash) external onlyOwner {
        uint256 _timelockEnd = timelockEnd[txHash];
        if (_timelockEnd == 0) {
            revert NotQueued(txHash);
        }
        if (block.timestamp > _timelockEnd) {
            revert TimelockElapsed(txHash, _timelockEnd);
        }
        timelockEnd[txHash] = type(uint256).max;
        emit SafeTransactionCanceled(txHash);
    }

    function lockDownTxHash() public view notLockedDown returns (bytes32) {
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

    function lockDown() external onlyOwner {
        bytes32 txHash = lockDownTxHash();

        // By requiring that the locker has preapproved the `txHash` for the call to `unlock`, we
        // prevent a single rogue signer from bricking the Safe.
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
