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

    function removeOwner(address prevOwner, address oldOwner, uint256 threshold) external;

    function isOwner(address) external view returns (bool);

    function getThreshold() external view returns (uint256);

    function getStorageAt(uint256 offset, uint256 length) external view returns (bytes memory);

    function approvedHashes(address owner, bytes32 txHash) external view returns (bool);

    function getModulesPaginated(address start, uint256 pageSize)
        external
        view
        returns (address[] memory array, address next);

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

    function OWNERS_SLOT(ISafeMinimal) internal pure returns (uint256) {
        return 2;
    }

    function getPrevOwner(ISafeMinimal safe, address owner) internal view returns (address) {
        address cursor = address(1);
        while (true) {
            address nextOwner =
                abi.decode(safe.getStorageAt(uint256(keccak256(abi.encode(cursor, OWNERS_SLOT(safe)))), 1), (address));
            if (nextOwner == owner) {
                return cursor;
            }
            cursor = nextOwner;
        }
        revert(); // unreachable
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

    mapping(bytes32 => uint256) public timelockEnd;
    address public lockedDownBy;
    uint24 public delay;
    bool private _reentrancyGuard;
    bool private _guardRemoved;

    ISafeMinimal public constant safe = ISafeMinimal(0xf36b9f50E59870A24F42F9Ba43b2aD0A4b8f2F51);
    uint256 internal constant _MINIMUM_OWNERS = 3;
    uint256 internal constant _MINIMUM_THRESHOLD = 2;

    address private constant _SINGLETON = 0xfb1bffC9d739B8D520DaF37dF666da4C687191EA;
    address private constant _SAFE_SINGLETON_FACTORY = 0x914d7Fec6aaC8cd542e72Bca78B30650d45643d7;

    // This is the correct hash only if this contract has been compiled for the London hardfork
    bytes32 private constant _EVM_VERSION_DUMMY_INITHASH =
        0xe7bcbbfee5c3a9a42621a8cbb24d1eade8e9469bc40e23d16b5d0607ba27027a;

    constructor() {
        assert(keccak256(type(EvmVersionDummy).creationCode) == _EVM_VERSION_DUMMY_INITHASH || block.chainid == 31337);
        assert(msg.sender == _SAFE_SINGLETON_FACTORY);

        // These checks ensure that the Guard is safely installed in the Safe at the time it is
        // deployed, with the exception of the installation and subsequent concealment of a
        // malicious Safe module. The author knows of no way to enforce that the Guard is installed
        // atomic with its deployment. This introduces a TOCTOU vulnerability. Therefore, extensive
        // simulation and excessive caution are imperative in this process. If the Guard is
        // installed in a Safe where these checks fail, the Safe is bricked. Once the Guard is
        // successfully deployed, the behavior ought to be sane, even in bizarre and outrageous
        // circumstances.
        _checkAfterExecution(safe);
        assert(!_guardRemoved);
    }

    function setDelay(uint24 newDelay) external onlySafe {
        emit TimelockUpdated(delay, newDelay);
        delay = newDelay;
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

    function _requireLockedDown() private view {
        if (lockedDownBy == address(0)) {
            revert NotLockedDown();
        }
    }

    function _requireNotRemoved() private view {
        // If the guard has been removed, it's possible that the Safe may have been subsequently
        // `SELFDESTRUCT`'d through a `DELEGATECALL` or any number of other, unsafe state
        // modifications (including installation of Module). Consequently, we can perform no other
        // checks or make other assumptions about the state of the Safe.
        if (_guardRemoved) {
            revert GuardNotInstalled();
        }
    }

    modifier normalOperation() {
        _requireNotRemoved();
        _requireNotLockedDown();
        _;
    }

    function _requirePreApproved(bytes32 txHash) private view {
        // By requiring that the Safe owner has preapproved the `txHash`, we prevent a single rogue
        // signer from bricking the Safe.
        if (!safe.approvedHashes(msg.sender, txHash)) {
            revert TxHashNotApproved(txHash);
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
    ) external override onlySafe {
        if (_guardRemoved) {
            // There are two ways for this branch to be reached. The first way is if the Guard is
            // uninstalled and then reinstalled. Unfortunately, we can't distinguish this case from
            // the second way. To avoid applying restrictions in circumstances we can't be
            // completely certain about, we prefer to fail open rather than accidentally brick
            // something. The second way is that the Guard has been uninstalled and now the Safe is
            // calling `checkTransaction` through `execute`. Because `execute` provides complete
            // freedom in the calls that may be performed both before and after this call, we cannot
            // safely clear `_guardRemoved` because we don't know that the post-conditions in
            // `checkAfterExecution` will be enforced.
            return;
        }

        if (_reentrancyGuard) {
            revert Reentrancy();
        }
        _reentrancyGuard = true;

        // At this point, we can be confident that we are executing inside of a call to
        // `execTransaction`, but not inside `execute`. We can rely on `checkAfterExecution` to
        // enforce its postconditions.

        // After extensive consideration, the ability to do `DELEGATECALL`'s to other contracts,
        // including narrowly limiting that to the use of the Safe-approved `MultiCallSendOnly`
        // contract (0xA1dabEF33b3B82c7814B6D82A79e50F4AC44102B), creates ways to brick/compromise
        // the Safe in ways that cannot be detected by simple pre-/post-conditions applied in
        // `checkTransaction` and `checkAfterExecution`. For example, allowing `MultiCallSendOnly`
        // creates the possibility of the installation of a malicious Module through `addModule`,
        // execution of a `DELEGATECALL` to an attacker-controlled contract through
        // `execTransactionFromModule`, and then removing that malicious module from the ability of
        // `getModulesPaginated` (or any other mechanism) to enumerate (i.e. setting slot
        // 0xcc69885fda6bcc1a4ace058b4a62bf5e179ea78fd58a1ccd71c22cc9b688792f to 1) all in a single
        // atomic transaction that will pass the postconditions.
        //
        // Therefore, due to a complete inability to secure the Safe against malicious/incompetent
        // owners, `Operation.DelegateCall` is prohibited.
        if (operation != Operation.Call) {
            revert NoDelegateCall();
        }

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

        // Any transaction with unanimous signatures can bypass the timelock. This mechanism is also
        // critical to the anti-griefing provisions. The pre-signed transaction(s) required when
        // calling `lockDown()` or `cancel(...)` can be combined with signatures from well-behaved
        // keyholders to un-brick the safe and remove the misbehaving actors. Unanimous transactions
        // also cannot be `cancel(...)`'d.
        try _safe.checkNSignatures(txHash, txHashData, signatures, _safe.ownerCount()) {
            return;
        } catch {
            // The signatures are not unanimous; proceed to the timelock. If the call is to
            // `unlock()`, we bail out because it *MUST* be unanimous.
            if (to == address(this) && uint256(uint32(bytes4(data))) == uint256(uint32(this.unlock.selector))) {
                revert NotUnanimous(txHash);
            }
        }

        // Fall through to the "normal" case. The checks that need to be performed here are 1) that
        // the Safe is not locked down (checked in `checkAfterExecution`), 2) that the transaction
        // was previously queued through `enqueue` and 3) that `delay` has elapsed since `enqueue`
        // was called.
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

        if (!_reentrancyGuard) {
            revert Reentrancy();
        }
        _reentrancyGuard = false;

        // We have to check that we're not locked down here (instead of in `checkTransaction`) to
        // ensure that the call to `unlock()` can't revert and burn the stored signatures
        // (`safe.approvedHashes(...)`; i.e. increase the nonce), resulting in a bricked Safe via a
        // griefing attack by a malicious owner.
        //
        // This is here instead of using the `notLockedDown` modifier so that we avoid bricking if
        // the Guard is uninstalled.
        _requireNotLockedDown();

        ISafeMinimal _safe = ISafeMinimal(msg.sender);

        _checkAfterExecution(_safe);
    }

    function _checkAfterExecution(ISafeMinimal _safe) private {
        // The knowledge that the hardcoded `safe` address is computed using the `CREATE2` pattern
        // from trusted initcode (and a factory likewise deployed by trusted initcode) gives us a
        // pretty strong toehold of trust. We do not need to recheck this, ever. Furthermore,
        // introspecting the proxy's implementation contract via the trustworthy `masterCopy()`
        // accessor (which bypasses the implementation and only executes proxy bytecode) and
        // constraining it to be another address deployed from trusted initcode gives us a full
        // complement of function selectors that can be used for postcondition checks.
        //
        // None of the aforementioned deployments use a "Nick's Method" deployment, so while these
        // assumptions are trustless, they are _*NOT*_ permissionless.
        {
            address singleton = _safe.masterCopy();
            if (singleton != _SINGLETON) {
                revert UnexpectedUpgrade(singleton);
            }
        }

        // The presence of a Module means that the state of the Safe may be modified in
        // unpredictable ways in between the enforcement of the pre-/post-conditions applied by
        // `checkTransaction` and `checkAfterExecution`. Namely, it could cause a `DELEGATECALL` and
        // consequently arbitrary modification of the state of the proxy (including
        // `SELFDESTRUCT`). Therefore, we prohibit the installation of modules.
        {
            (address[] memory modules,) = _safe.getModulesPaginated(address(1), 1);
            if (modules.length != 0) {
                revert ModuleInstalled(modules[0]);
            }
        }

        // Due to a quirk of how `checkNSignatures` works (called as a guarded precondition to
        // `unlock`; sometimes it validates `msg.sender` instead of a signature, for gas
        // optimization), we could end up in a bizarre situation if `address(this)` is an
        // owner. This would make our introspection checks wrong. Let's just prohibit that entirely.
        if (_safe.isOwner(address(this))) {
            revert GuardIsOwner();
        }

        // Some basic safety checks. If violated, the game theory of the `lockDown`/`unlock` game
        // becomes degenerate.
        {
            uint256 ownerCount = _safe.ownerCount();
            if (ownerCount < _MINIMUM_OWNERS) {
                revert NotEnoughOwners(ownerCount);
            }
        }
        {
            uint256 threshold = _safe.getThreshold();
            if (threshold < _MINIMUM_THRESHOLD) {
                revert ThresholdTooLow(threshold);
            }
        }

        // We do not revert if `_safe.getGuard()` returns a value other than `address(this)`. This
        // allows uninstallation of the guard (through the timelock, obviously) to later permit
        // upgrades to other singleton implementation contracts. However, we do set the
        // `_guardRemoved` flag, which disables all Guard functionality (failing open). It is not
        // possible to un-set `_guardRemoved` once set.
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
    ) external normalOperation {
        // See comment in `checkTransaction`
        if (operation != Operation.Call) {
            revert NoDelegateCall();
        }

        bytes memory txHashData = safe.encodeTransactionData(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, nonce
        );
        bytes32 txHash = safe.getTransactionHash(txHashData);
        safe.checkSignatures(txHash, txHashData, signatures);

        uint256 _timelockEnd = block.timestamp + delay;
        if (timelockEnd[txHash] != 0) {
            revert AlreadyQueued(txHash);
        }
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

    function unlockTxHash() public view returns (bytes32) {
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

    function _removeOwnerTxHash(address prevOwner, address oldOwner, uint256 threshold, uint256 nonce)
        private
        view
        returns (bytes32)
    {
        return safe.getTransactionHash(
            address(safe),
            0 ether,
            abi.encodeCall(safe.removeOwner, (prevOwner, oldOwner, threshold)),
            Operation.Call,
            0,
            0,
            0,
            address(0),
            payable(address(0)),
            nonce
        );
    }

    function resignTxHash(address owner) external view returns (bytes32 txHash) {
        address prevOwner = safe.getPrevOwner(owner);
        uint256 threshold = safe.getThreshold();
        uint256 nonce = safe.nonce();
        if (
            lockedDownBy != address(0)
                || safe.approvedHashes(owner, txHash = _removeOwnerTxHash(prevOwner, owner, threshold, nonce))
        ) {
            nonce++;
            txHash = _removeOwnerTxHash(prevOwner, owner, threshold, nonce);
        }
    }

    function cancel(bytes32 txHash) external onlyOwner {
        uint256 nonce = safe.nonce();
        if (lockedDownBy != address(0)) {
            nonce++;
        }
        bytes32 resignHash = _removeOwnerTxHash(safe.getPrevOwner(msg.sender), msg.sender, safe.getThreshold(), nonce);
        _requirePreApproved(resignHash);

        uint256 _timelockEnd = timelockEnd[txHash];
        if (_timelockEnd == 0) {
            revert NotQueued(txHash);
        }
        if (block.timestamp > _timelockEnd) {
            revert TimelockElapsed(txHash, _timelockEnd);
        }
        timelockEnd[txHash] = type(uint256).max;
        emit ResignTxHash(resignHash);
        emit SafeTransactionCanceled(txHash, msg.sender);
    }

    function lockDown() external normalOperation onlyOwner {
        bytes32 txHash = unlockTxHash();
        _requirePreApproved(txHash);

        address prevOwner = safe.getPrevOwner(msg.sender);
        uint256 threshold = safe.getThreshold();
        uint256 nonce = safe.nonce();
        if (safe.approvedHashes(msg.sender, _removeOwnerTxHash(prevOwner, msg.sender, threshold, nonce))) {
            nonce++;
            bytes32 resignHash = _removeOwnerTxHash(prevOwner, msg.sender, threshold, nonce);
            _requirePreApproved(resignHash);
            emit ResignTxHash(resignHash);
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
