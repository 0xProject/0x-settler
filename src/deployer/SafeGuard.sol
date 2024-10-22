// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

// This enum is derived from the code deployed to 0xfb1bffC9d739B8D520DaF37dF666da4C687191EA
enum Operation {
    Call,
    DelegateCall
}

// This interface is excerpted from the contract at 0xfb1bffC9d739B8D520DaF37dF666da4C687191EA
interface ISafeMinimal {
    function checkNSignatures(bytes32 dataHash, bytes memory data, bytes memory signatures, uint256 requiredSignatures)
        external
        view;

    function checkSignatures(bytes32 dataHash, bytes memory data, bytes memory signatures) external view;

    function nonce() external view returns (uint256);

    function isOwner(address) external view returns (bool);

    function getStorageAt(uint256 offset, uint256 length) external view returns (bytes memory);

    function approvedHashes(address owner, bytes32 txHash) external view returns (uint256);

    // This function is not part of the interface at 0xfb1bffC9d739B8D520DaF37dF666da4C687191EA
    // . It's part of the implicit interface on the proxy contract(s) created by the factory at
    // 0xc22834581ebc8527d974f8a1c97e1bea4ef910bc .
    function masterCopy() external view returns (address);
}

// This library is a reimplementation of the functionality of the functions by the same name in
// 0xfb1bffC9d739B8D520DaF37dF666da4C687191EA
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
        return abi.encodePacked(bytes2(0x1901), domainSeparator(safe), safeTxHash);
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

    function OWNER_COUNT_SLOT(ISafeMinimal) internal pure returns (uint256) {
        return 3;
    }

    function ownerCount(ISafeMinimal safe) internal view returns (uint256) {
        return abi.decode(safe.getStorageAt(OWNER_COUNT_SLOT(safe), 1), (uint256));
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

    function GUARD_SLOT(ISafeMinimal) internal pure returns (uint256) {
        // keccak256("guard_manager.guard.address")
        return 0x4a204f620c8c5ccdca3fd54d003badd85ba500436a431f0cbda4f558c93c34c8;
    }

    function getGuard(ISafeMinimal safe) internal view returns (address) {
        return abi.decode(safe.getStorageAt(GUARD_SLOT(safe), 1), (address));
    }
}

// This interface is excerpted from `GuardManager.sol` in 0xfb1bffC9d739B8D520DaF37dF666da4C687191EA
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
    event SafeTransactionCanceled(bytes32 indexed txHash);
    event LockDown(address indexed lockedDownBy);
    event Unlocked();

    error PermissionDenied();
    error NoDelegateToGuard();
    error GuardNotInstalled();
    error GuardIsOwner();
    error TimelockNotElapsed(bytes32 txHash, uint256 timelockEnd);
    error TimelockElapsed(bytes32 txHash, uint256 timelockEnd);
    error NotQueued(bytes32 txHash);
    error LockedDown(address lockedDownBy);
    error NotLockedDown();
    error UnlockHashNotApproved(bytes32 txHash);
    error UnexpectedUpgrade(address newSingleton);

    mapping(bytes32 => uint256) public timelockEnd;
    uint40 public delay;
    address public lockedDownBy;
    bool private _guardRemoved;

    ISafeMinimal public constant safe = ISafeMinimal(0xf36b9f50E59870A24F42F9Ba43b2aD0A4b8f2F51);

    address private constant _SINGLETON = 0xfb1bffC9d739B8D520DaF37dF666da4C687191EA;
    address private constant _SAFE_SINGLETON_FACTORY = 0x914d7Fec6aaC8cd542e72Bca78B30650d45643d7;

    // This is the correct hash only if this contract has been compiled for the London hardfork
    bytes32 private constant _EVM_VERSION_DUMMY_INITHASH =
        0xe7bcbbfee5c3a9a42621a8cbb24d1eade8e9469bc40e23d16b5d0607ba27027a;

    constructor() safetyChecks {
        // The checks applied by the `safetyChecks` modifier ensure that the Guard is safely
        // installed in the Safe _at the time it is deployed_. The author knows of no way to enforce
        // that the Guard is installed atomic with its deployment. This introduces a TOCTOU
        // vulnerability. Therefore, extensive simulation and excessive caution are imperative in
        // this process. If the Guard is installed in a Safe where these checks fail, the Safe is
        // bricked. Once the Guard is successfully deployed, the behavior ought to be sane, even in
        // bizarre and outrageous circumstances.

        assert(keccak256(type(EvmVersionDummy).creationCode) == _EVM_VERSION_DUMMY_INITHASH || block.chainid == 31337);
        assert(msg.sender == _SAFE_SINGLETON_FACTORY);
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
        address locker = lockedDownBy;
        if (locker != address(0)) {
            revert LockedDown(locker);
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

    modifier lockedDown() {
        _requireLockedDown();
        _;
    }

    function _safetyChecks() private view {
        // Because the hardcoded `safe` address is computed using the `CREATE2` pattern from trusted
        // initcode, we know that once deployed, it cannot be redeployed with different code. This
        // provides a toehold of trust that we can extend to perform some very stringent safety
        // checks that ensure the behavior of the system as a whole is as expected. We do not need
        // to recheck this, ever. If the Safe is ever `SELFDESTRUCT`'d, we may encounter bizarre
        // behavior with the value of `safe.masterCopy()` changing out from under us while we aren't
        // watching. We try our best to deal with this, but are limited in what is possible.

        // Once we've established that the code in `safe` is expected (provided that it exists), we
        // can be sure that the result of calling `masterCopy()` is trustworthy. The address
        // `_SINGLETON` is computed using the `CREATE2` pattern from trusted initcode (this does not
        // use Nick's Method for deployment, so it's not permissionless, but it is trustless). So if
        // the result of `masterCopy()` is the expected value, we can also trust the
        // implementation's behavior for further checks.
        {
            address singleton = safe.masterCopy();
            if (singleton != _SINGLETON) {
                revert UnexpectedUpgrade(singleton);
            }
        }

        // If the Guard is uninstalled, it is now useless. Signal that to anybody who might care by
        // reverting.
        if (safe.getGuard() != address(this) || _guardRemoved) {
            revert GuardNotInstalled();
        }

        // Due to a quirk of how `checkNSignatures` works (called as a guarded precondition to
        // `unlock`; sometimes it validates `msg.sender` instead of a signature, for gas
        // optimization), we could end up in a bizarre situation if `address(this)` is an
        // owner. This would make our introspection checks wrong. Let's just prohibit that entirely.
        if (safe.isOwner(address(this))) {
            revert GuardIsOwner();
        }
    }

    modifier safetyChecks() {
        _safetyChecks();
        _;
    }

    function _requireApprovedUnlock() private view onlyOwner {
        // By requiring that the Safe owner has preapproved the `txHash` for the call to `unlock`,
        // we prevent a single rogue signer from bricking the Safe.
        bytes32 txHash = unlockTxHash();
        if (safe.approvedHashes(msg.sender, txHash) != 1) {
            revert UnlockHashNotApproved(txHash);
        }
    }

    modifier antiGriefing() {
        _requireApprovedUnlock();
        _;
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
    ) external override onlySafe {
        ISafeMinimal _safe = ISafeMinimal(msg.sender);

        if (_safe.masterCopy() != _SINGLETON) {
            // Either the Safe has been `SELFDESTRUCT`'d and recreated at the same address (without
            // the Guard) and then upgraded to a new singleton/implementation, or the Guard has been
            // removed and then the Safe upgraded. Either way, we cannot know anything about the
            // state of the Safe or the environment in which we're executing. We prefer to fail open
            // rather than brick.
            //
            // We cannot be guaranteed to be able to detect the former case. We do as much as we
            // can, but the design of the EVM frustrates further surety.
            _guardRemoved = true;
        }

        if (_guardRemoved) {
            // There are three ways for this branch to be reached. The first is that Safe has been
            // `SELFDESTRUCT`'d and recreated. In this case, we can assume nothing about the
            // behavior of the Safe. The second case is if the Guard is uninstalled and then
            // reinstalled. Unfortunately, we can't distinguish this case from the third case. To
            // avoid applying restrictions in circumstances we can't be completely certain about, we
            // prefer to fail open rather than accidentally brick something. The third case is that
            // the Guard has been uninstalled and now the Safe is calling `checkTransaction` through
            // `execute`. Because `execute` provides complete freedom in the calls that may be
            // performed both before and after this call, we cannot safely clear `_guardRemoved`
            // because we don't know that the post-conditions in `checkAfterExecution` will be
            // enforced.
            return;
        }

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

    function checkAfterExecution(bytes32, bool) external override onlySafe {
        if (_guardRemoved) {
            // See comment in the same branch of `checkTransaction`.
            return;
        }

        // We check that the Safe is not locked down twice. We have to check it here to ensure that
        // the call to `unlock()` can't revert and burn signatures (increase the nonce), resulting
        // in a bricked/griefing attack by a malicious owner.
        //
        // This is here instead of using the `notLockedDown` modifier so that we avoid bricking if
        // there's unexpected metamorphism or if the Guard is uninstalled.
        _requireNotLockedDown();

        ISafeMinimal _safe = ISafeMinimal(msg.sender);

        // Prevent an unexpected upgrade that may break our ability to reliably introspect the
        // aspects of the Safe that are required for the correct function of this guard.
        {
            address singleton = _safe.masterCopy();
            if (singleton != _SINGLETON) {
                revert UnexpectedUpgrade(singleton);
            }
        }

        // Due to a quirk of how `checkNSignatures` works (called as a guarded precondition to
        // `unlock`; sometimes it validates `msg.sender` instead of a signature, for gas
        // optimization), we could end up in a bizarre situation if `address(this)` is an
        // owner. This would make our introspection checks wrong. Let's just prohibit that entirely.
        if (_safe.isOwner(address(this))) {
            revert GuardIsOwner();
        }

        // Unlike the `safetyChecks` modifier, we permit `_safe.getGuard()` to be values other than
        // `address(this)`. This allows uninstallation of the guard (through the timelock,
        // obviously) to later permit upgrades to other singleton implementation contracts. It is
        // not possible to un-set `_guardRemoved` once set. This completely disables the guard.
        if (_safe.getGuard() != address(this)) {
            _guardRemoved = true;
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
    ) external safetyChecks {
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
    function setDelay(uint40 newDelay) external onlySafe {
        emit TimelockUpdated(delay, newDelay);
        delay = newDelay;
    }

    function unlockTxHash() public view notLockedDown safetyChecks returns (bytes32) {
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

    function cancel(bytes32 txHash) external antiGriefing {
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

    function lockDown() external antiGriefing {
        lockedDownBy = msg.sender;
        emit LockDown(msg.sender);
    }

    function unlock() external onlySafe lockedDown {
        delete lockedDownBy;
        emit Unlocked();
    }
}
