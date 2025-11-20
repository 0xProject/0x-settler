// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {IERC165} from "@forge-std/interfaces/IERC165.sol";

// This enum is derived from the code deployed to 0xfb1bffC9d739B8D520DaF37dF666da4C687191EA (1.3.0)
// or 0x29fcB43b46531BcA003ddC8FCB67FFE91900C762 (1.4.1)
enum Operation {
    Call,
    DelegateCall
}

// This interface is excerpted from the contract at 0xfb1bffC9d739B8D520DaF37dF666da4C687191EA
// (1.3.0) or 0x29fcB43b46531BcA003ddC8FCB67FFE91900C762 (1.4.1)
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

    // This function is not part of the interface at
    // 0xfb1bffC9d739B8D520DaF37dF666da4C687191EA/0x29fcB43b46531BcA003ddC8FCB67FFE91900C762 . It's
    // part of the implicit interface on the proxy contract(s) created by the factory at
    // 0x76E2cFc1F5Fa8F6a5b3fC4c8F4788F0116861F9B (1.1.1),
    // 0xc22834581ebc8527d974f8a1c97e1bea4ef910bc (1.3.0), or
    // 0x4e1DCf7AD4e460CfD30791CCC4F9c8a4f820ec67 (1.4.1) .
    function masterCopy() external view returns (address);
}

// This interface is derived from the code deployed to 0xA1dabEF33b3B82c7814B6D82A79e50F4AC44102B
// (1.3.0) or 0x9641d764fc13c8B624c04430C7356C1C7C8102e2 (1.4.1)
interface ISafeMultiSend {
    /// @dev Sends multiple transactions and reverts all if one fails.
    /// @param transactions Encoded transactions. Each transaction is encoded as a packed bytes of
    ///                     operation has to be uint8(0) in this version (=> 1 byte),
    ///                     to as a address (=> 20 bytes),
    ///                     value as a uint256 (=> 32 bytes),
    ///                     data length as a uint256 (=> 32 bytes),
    ///                     data as bytes.
    ///                     see abi.encodePacked for more information on packed encoding
    /// @notice The code is for most part the same as the normal MultiSend (to keep compatibility),
    ///         but reverts if a transaction tries to use a delegatecall.
    /// @notice This method is payable as delegatecalls keep the msg.value from the previous call
    ///         If the calling method (e.g. execTransaction) received ETH this would revert otherwise
    function multiSend(bytes memory transactions) external payable;
}

// This interface is excerpted from the contract at 0xfb1bffC9d739B8D520DaF37dF666da4C687191EA
// (1.3.0) or 0x29fcB43b46531BcA003ddC8FCB67FFE91900C762 (1.4.1)
interface ISafeForbidden {
    function enableModule(address) external;
}

// This library is a reimplementation of the functionality of the functions by the same name in
// 0xfb1bffC9d739B8D520DaF37dF666da4C687191EA (1.3.0) or 0x29fcB43b46531BcA003ddC8FCB67FFE91900C762
// (1.4.1)
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

    function FALLBACK_SLOT(ISafeMinimal) internal pure returns (uint256) {
        // keccak256("fallback_manager.handler.address")
        return 0x6c9a6c4a39284e37ed1cf53d337577d14212a4870fb976a4366c693b939918d5;
    }

    function getFallback(ISafeMinimal safe) internal view returns (address) {
        return abi.decode(safe.getStorageAt(FALLBACK_SLOT(safe), 1), (address));
    }
}

// This interface is excerpted from `GuardManager.sol` in 0xfb1bffC9d739B8D520DaF37dF666da4C687191EA
// (1.3.0) or 0x29fcB43b46531BcA003ddC8FCB67FFE91900C762 (1.4.1)
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

abstract contract ZeroExSettlerDeployerSafeGuardBase is IGuard {
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
    error IncorrectFallbackHandler(address handler);
    error NotEnoughOwners(uint256 ownerCount);
    error ThresholdTooLow(uint256 threshold);
    error NotUnanimous(bytes32 txHash);
    error TxHashNotApproved(bytes32 txHash);

    mapping(bytes32 => uint256) public timelockEnd;
    address public lockedDownBy;
    uint24 public delay;
    bool private _reentrancyGuard;
    bool private _guardRemoved;

    ISafeMinimal public immutable safe;
    uint256 internal constant _MINIMUM_OWNERS = 3;
    uint256 internal constant _MINIMUM_THRESHOLD = 2;

    address private immutable _SINGLETON;
    address private immutable _FALLBACK;
    address private immutable _MULTISEND;
    address private constant _CREATE2_FACTORY = 0x4e59b44847b379578588920cA78FbF26c0B4956C;
    address private constant _SAFE_SINGLETON_FACTORY = 0x914d7Fec6aaC8cd542e72Bca78B30650d45643d7;

    bytes32 private constant _SAFE_PROXY_1_1_CODEHASH =
        0xaea7d4252f6245f301e540cfbee27d3a88de543af8e49c5c62405d5499fab7e5;
    bytes32 private constant _SAFE_PROXY_1_3_CODEHASH =
        0xb89c1b3bdf2cf8827818646bce9a8f6e372885f8c55e5c07acbd307cb133b000;
    bytes32 private constant _SAFE_PROXY_1_4_CODEHASH =
        0xd7d408ebcd99b2b70be43e20253d6d92a8ea8fab29bd3be7f55b10032331fb4c;

    // This is the correct hash only if this contract has been compiled for the London hardfork
    bytes32 private constant _EVM_VERSION_DUMMY_INITHASH =
        0xe7bcbbfee5c3a9a42621a8cbb24d1eade8e9469bc40e23d16b5d0607ba27027a;

    function _constructorChecks() internal view returns (bool result) {
        result = keccak256(type(EvmVersionDummy).creationCode) == _EVM_VERSION_DUMMY_INITHASH || block.chainid == 31337;
        bytes32 safeCodeHash = address(safe).codehash;
        result = result
            && (
                safeCodeHash == _SAFE_PROXY_1_1_CODEHASH || safeCodeHash == _SAFE_PROXY_1_3_CODEHASH
                    || safeCodeHash == _SAFE_PROXY_1_4_CODEHASH
            );
        result = result && (msg.sender == _CREATE2_FACTORY || msg.sender == _SAFE_SINGLETON_FACTORY);
    }

    function _predictCreate2(bytes32 inithash) private view returns (address) {
        return address(
            uint160(uint256(keccak256(bytes.concat(bytes1(0xff), bytes20(uint160(msg.sender)), bytes32(0), inithash))))
        );
    }

    constructor(ISafeMinimal safe_, bytes32 singletonInithash, bytes32 fallbackInithash, bytes32 multisendInithash) {
        safe = safe_;
        _SINGLETON = _predictCreate2(singletonInithash);
        _FALLBACK = _predictCreate2(fallbackInithash);
        _MULTISEND = _predictCreate2(multisendInithash);
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

    function setDelay(uint24 newDelay) external onlySafe {
        emit TimelockUpdated(delay, newDelay);
        delay = newDelay;
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

        ISafeMinimal _safe = ISafeMinimal(msg.sender);

        // Obviously, any `DELEGATECALL` to an arbitrary contract could result in the concealment of
        // potentially malicious behavior that this Guard is no longer able to control. However,
        // even a seemingly-innocuous `DELEGATECALL` to the Safe-approved `MultiCallSendOnly`
        // contract (0xA1dabEF33b3B82c7814B6D82A79e50F4AC44102B [1.3.0],
        // 0x9641d764fc13c8B624c04430C7356C1C7C8102e2 [1.4.1]), creates ways to brick/compromise the
        // Safe in ways that cannot be detected by simple pre-/post-conditions applied in
        // `checkTransaction` and `checkAfterExecution`. For example we could install a malicious
        // Module through `enableModule`, execute a `DELEGATECALL` to a malicious contract via a
        // call to `execTransactionFromModule` from the malicious Module, and then use that
        // `DELEGATECALL`'d contract's direct access to the Safe's storage to remove the Module from
        // the ability of `getModulesPaginated` (or any other mechanism) to enumerate (i.e. setting
        // slot 0xcc69885fda6bcc1a4ace058b4a62bf5e179ea78fd58a1ccd71c22cc9b688792f to 1) all in a
        // single atomic transaction that will pass the postconditions.
        //
        // Therefore, we forbid all `DELEGATECALL`s to contracts except `MultiSendCallOnly`, and for
        // calls to `MultiSendCallOnly`, we do deep inspection of the payload to ensure that it's
        // not calling `enableModule`
        if (operation != Operation.Call) {
            if (to == _MULTISEND && uint256(uint32(bytes4(data))) == uint256(uint32(ISafeMultiSend.multiSend.selector)))
            {
                // Slice off the selector.
                bytes calldata multicalls = data[4:];
                // Follow the dynamic-type ABIencoding indirection to the `transactions` argument.
                multicalls = multicalls[uint256(bytes32(multicalls)):];
                // Decode `transactions` length.
                {
                    uint256 multicallsLength = uint256(bytes32(multicalls));
                    multicalls = multicalls[32:];
                    multicalls = multicalls[:multicallsLength];
                }

                // The encoding of the multicalls here is derived from the `MultiSendCallOnly`
                // contract deployed to 0xA1dabEF33b3B82c7814B6D82A79e50F4AC44102B (1.3.0) or
                // 0x9641d764fc13c8B624c04430C7356C1C7C8102e2 (1.4.1)
                while (multicalls.length != 0) {
                    // We use calldata array slicing syntax here, which is stricter than the
                    // assembly found in `MultiSendCallOnly`. `MultiSendCallOnly` will happily
                    // decode data that is past the (nominal) end of the `transactions` array, while
                    // this implementation will revert when encountering that.

                    // We ignore the first byte, which is always zero to indicate `Operation.Call`.
                    // The next 20 bytes are the target of the `CALL`.
                    multicalls = multicalls[1:];
                    address multicallTo = address(uint160(bytes20(multicalls)));
                    multicalls = multicalls[20:];
                    // We ignore the next 32 bytes because they are the `value`. The function we
                    // wish to forbid is `nonpayable`, so the value is always zero or irrelevant.
                    multicalls = multicalls[32:];
                    // The 32 bytes after that are the length of the payload/data, followed by the
                    // payload/data itself.
                    bytes calldata multicallData;
                    {
                        uint256 multicallDataLength = uint256(bytes32(multicalls));
                        multicalls = multicalls[32:];
                        multicallData = multicalls[:multicallDataLength];
                        multicalls = multicalls[multicallDataLength:];
                    }

                    // Forbid calls to `ISafeForbidden(address(_safe)).enableModule(...)`.
                    if (multicallTo == address(_safe) && multicallData.length >= 36) {
                        uint256 potentialModule = uint256(bytes32(multicallData[4:]));
                        if (potentialModule >> 160 == 0) {
                            revert ModuleInstalled(address(uint160(potentialModule)));
                        }
                    }
                }
            } else {
                revert NoDelegateCall();
            }
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
        _maybeSetGuardRemoved(_safe);
    }

    // This function has exactly the same checks as `_checkAfterExecution`, but is returns `false`
    // on failure of those checks instead of reverting.
    function _checkAfterExecutionReturnBool(ISafeMinimal _safe) internal view returns (bool result) {
        result = true;

        // See comments in `_checkAfterExecution` for an explanation of all these conditions
        result = result && _safe.masterCopy() == _SINGLETON;
        if (result) {
            (address[] memory modules,) = _safe.getModulesPaginated(address(1), 1);
            result = modules.length == 0;
        }
        result = result && _safe.getFallback() == _FALLBACK;
        result = result && !_safe.isOwner(address(this));
        result = result && _safe.ownerCount() >= _MINIMUM_OWNERS;
        result = result && _safe.getThreshold() >= _MINIMUM_THRESHOLD;
    }

    function _checkAfterExecution(ISafeMinimal _safe) private view {
        // The knowledge that the immutable `safe` address is computed using the `CREATE2` pattern
        // from trusted initcode (and a factory likewise deployed by trusted initcode) gives us a
        // pretty strong toehold of trust. We do not need to recheck this, ever. Furthermore,
        // introspecting the proxy's implementation contract via the trustworthy `masterCopy()`
        // accessor (which bypasses the implementation and only executes proxy bytecode) and
        // constraining it to be another address deployed from trusted initcode gives us a full
        // complement of function selectors that can be used for postcondition checks.
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

        // A malicious fallback handler can cause unexpected external non-static calls that, to an
        // ignorant operator, would cause malicious calls to privileged contracts. Out of an
        // abundance of caution, we forbid setting the fallback handler away from its default
        // value. Note: it's not possible to set the fallback handler to the address of the Safe
        // itself because that is not capable of calling `authorized` functions because it is
        // specifically the `fallback` handler.
        {
            address fallbackHandler = _safe.getFallback();
            if (fallbackHandler != _FALLBACK) {
                revert IncorrectFallbackHandler(fallbackHandler);
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
    }

    function _removeSelf() internal {
        _guardRemoved = true;
    }

    function _maybeSetGuardRemoved(ISafeMinimal _safe) internal {
        // We do not revert if `_safe.getGuard()` returns a value other than `address(this)`. This
        // allows uninstallation of the guard (through the timelock, obviously) to later permit
        // upgrades to other singleton implementation contracts. However, we do set the
        // `_guardRemoved` flag, which disables all Guard functionality (failing open). It is not
        // possible to un-set `_guardRemoved` once set.
        if (_safe.getGuard() != address(this)) {
            _removeSelf();
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

contract ZeroExSettlerDeployerSafeGuardOnePointThree is ZeroExSettlerDeployerSafeGuardBase {
    bytes32 private constant _SAFE_SINGLETON_1_3_INITHASH =
        0x49f30800a6ac5996a48b80c47ff20f19f8728812498a2a7fe75a14864fab6438;
    bytes32 private constant _SAFE_FALLBACK_1_3_INITHASH =
        0x272190de126b4577e187d9f00b9ca5daeae76d771965d734876891a51f9c43d8;
    bytes32 private constant _SAFE_MULTISEND_1_3_INITHASH =
        0x35e699c3e43ec3e03a101730ab916c5e540893eaaf806451e929d138c3ff53b7;

    constructor(ISafeMinimal safe_)
        ZeroExSettlerDeployerSafeGuardBase(
            safe_,
            _SAFE_SINGLETON_1_3_INITHASH,
            _SAFE_FALLBACK_1_3_INITHASH,
            _SAFE_MULTISEND_1_3_INITHASH
        )
    {
        // These checks ensure that the Guard is safely installed in the Safe at the time it is
        // deployed, with the exception of the installation and subsequent concealment of a
        // malicious Safe module. The author knows of no way to enforce that the Guard is installed
        // atomic with its deployment. This introduces a TOCTOU vulnerability. Therefore, extensive
        // simulation and excessive caution are imperative in this process. If the Guard is
        // installed in a Safe where these checks fail, the Guard silently disables itself in order
        // to avoid a bricked Safe. Once the Guard is successfully deployed, the behavior ought to
        // be sane, even in bizarre and outrageous circumstances.
        if (_constructorChecks() && _checkAfterExecutionReturnBool(safe_)) {
            _maybeSetGuardRemoved(safe_);
        } else {
            _removeSelf();
        }
    }
}

contract ZeroExSettlerDeployerSafeGuardOnePointFourPointOne is IERC165, ZeroExSettlerDeployerSafeGuardBase {
    bytes32 private constant _SAFE_SINGLETON_1_4_INITHASH =
        0x3555bd3ee95b1c6605c602740d71efaf200068e0395ccd701ac82ab8e42307bd;
    bytes32 private constant _SAFE_FALLBACK_1_4_INITHASH =
        0x5a63128db658d8601220c014848acd6c27b855a0427f0181eb3ba8c25e2d3e95;
    bytes32 private constant _SAFE_MULTISEND_1_4_INITHASH =
        0xa7934433f19155c708af2674b14c6c8b591fedbed7b01ce8cf64014f307468a0;

    constructor(ISafeMinimal safe_)
        ZeroExSettlerDeployerSafeGuardBase(
            safe_,
            _SAFE_SINGLETON_1_4_INITHASH,
            _SAFE_FALLBACK_1_4_INITHASH,
            _SAFE_MULTISEND_1_4_INITHASH
        )
    {
        // In contrast to the 1.3.0 Guard, the 1.4.1 Guard must be deployed *before* being enabled
        // in the Safe. However, because the Safe does an ERC165 check during the Guard enabling
        // process, we are able to perform a nearly atomic check. See the logic and comment in
        // `supportsInterface` below.
        assert(_constructorChecks());
    }

    /// @inheritdoc IERC165
    function supportsInterface(bytes4 interfaceID) external view override returns (bool) {
        if (uint32(interfaceID) == uint32(type(IERC165).interfaceId)) {
            return true;
        } else if (uint32(interfaceID) == 0xffffffff) {
            return false;
        } else {
            // These checks ensure that the Safe (with the exception of clandestine Modules) is in a
            // sane configuration at the time that the Guard is installed. Obviously because the
            // Guard's `checkAfterExecution` is not run during the installation, it's still possible
            // to misconfigure the Safe or conceal a Module after the Guard's installation (e.g. via
            // delegate'd MultiCall). However, presuming the Safe owners don't do that, at the
            // conclusion of the installation of the Guard, the behavior ought to remain sane, even
            // in bizarre and outrageous circumstances.
            ISafeMinimal safe_ = safe;
            return msg.sender == address(safe_) && uint32(interfaceID) == uint32(type(IGuard).interfaceId)
                && _checkAfterExecutionReturnBool(safe_);
        }
    }
}
