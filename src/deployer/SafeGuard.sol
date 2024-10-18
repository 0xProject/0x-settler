// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

enum Operation {
    Call,
    DelegateCall
}

interface ISafeMinimal {
    function getTransactionHash(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        uint256 safeTxGas,
        uint256 baseGas,
        uint256 gasPrice,
        address gasToken,
        address refundReceiver,
        uint256 _nonce
    ) external view returns (bytes32);

    function nonce() external view returns (uint256);
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
    event TimelockUpdated(uint256 oldDelay, uint256 newDelay);
    event SafeTransactionQueued(
        bytes32 indexed txHash,
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

    error PermissionDenied();
    error TimelockNotElapsed(uint256 timelockEnd);

    uint256 public delay;
    mapping(bytes32 => uint256) public queuedAt;

    ISafeMinimal public immutable safe;
    bytes32 internal constant evmVersionDummyInitHash = bytes32(0); // TODO: ensure London hardfork

    constructor(address _safe) {
        assert(keccak256(type(EvmVersionDummy).creationCode) == evmVersionDummyInitHash || block.chainid == 31337);
        safe = ISafeMinimal(_safe);
        delay = 1 weeks;
        emit TimelockUpdated(0, 1 weeks);
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
        bytes calldata, // signatures
        address // msgSender
    ) external view override onlySafe {
        ISafeMinimal _safe = ISafeMinimal(msg.sender);
        if (to == address(this)) {
            if (data.length >= 4) {
                uint256 selector;
                assembly ("memory-safe") {
                    selector := shr(0xe0, calldataload(data.offset))
                }
                if (selector == uint32(this.queue.selector)) {
                    return;
                }
            }
        }
        uint256 nonce;
        unchecked {
            nonce = _safe.nonce() - 1;
        }
        uint256 timelockEnd = queuedAt[_safe.getTransactionHash(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, nonce
        )] + delay;
        if (block.timestamp >= timelockEnd) {
            revert TimelockNotElapsed(timelockEnd);
        }
    }

    function checkAfterExecution(bytes32 txHash, bool success) external override onlySafe {}

    function queue(
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
        uint256 nonce = _safe.nonce();
        bytes32 txHash = _safe.getTransactionHash(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, nonce
        );
        queuedAt[txHash] = block.timestamp;
        emit SafeTransactionQueued(
            txHash, to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, nonce
        );
    }

    /// It's totally possible to brick the timelock (and consequently, the
    /// entire safe) if you set the delay too long. Don't do that.
    function setDelay(uint256 newDelay) external onlySafe {
        emit TimelockUpdated(delay, newDelay);
        delay = newDelay;
    }
}
