// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC5267} from "./interfaces/IERC5267.sol";
import {PERMIT_TYPEHASH} from "./interfaces/IEIP2612.sol";
import {AbstractContext} from "./Context.sol";
import {AccessListElem, PackedSignature, TransactionEncoder} from "./utils/TransactionEncoder.sol";
import {SafeTransferLib} from "./vendor/SafeTransferLib.sol";

abstract contract SingleSignatureDirtyHack is IERC5267, AbstractContext {
    using SafeTransferLib for IERC20;

    mapping(address => uint256) public nonces;

    error InvalidSigner(address expected, address actual);
    error NonceReplay(uint256 oldNonce, uint256 newNonce);
    error InvalidAllowance(uint256 expected, uint256 actual);
    error SignatureExpired(uint256 deadline);

    bytes32 private constant _DOMAIN_TYPEHASH = 0x8cad95687ba82c2ce50e74f7b754645e5117c3a5bec8151c0726d5857980a866;
    bytes32 private constant _NAMEHASH = 0x0000000000000000000000000000000000000000000000000000000000000000;
    string public constant name = ""; // TODO: needs a name
    uint256 private immutable _cachedChainId;
    bytes32 private immutable _cachedDomainSeparator;

    constructor() {
        require(_DOMAIN_TYPEHASH == keccak256("EIP712Domain(string name,uint256 chainId,address verifyingContract)"));
        require(_NAMEHASH == keccak256(bytes(name)));

        _cachedChainId = block.chainid;
        _cachedDomainSeparator = _computeDomainSeparator();
    }

    function _computeDomainSeparator() private view returns (bytes32 r) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(0x00, _DOMAIN_TYPEHASH)
            mstore(0x20, _NAMEHASH)
            mstore(0x40, chainid())
            mstore(0x60, address())
            r := keccak256(0x00, 0x80)
            mstore(0x40, ptr)
            mstore(0x60, 0x00)
        }
    }

    function _DOMAIN_SEPARATOR() internal view returns (bytes32) {
        return block.chainid == _cachedChainId ? _cachedDomainSeparator : _computeDomainSeparator();
    }

    function DOMAIN_SEPARATOR() external view returns (bytes32) {
        return _DOMAIN_SEPARATOR();
    }

    function _hashStruct(string calldata typeSuffix, TransferParams calldata transferParams)
        internal
        view
        returns (bytes32 signingHash)
    {
        bytes32 domainSep = _DOMAIN_SEPARATOR();
        address operator = _msgSender();
        uint256 deadline = transferParams.deadline;
        bytes32 structHash = transferParams.structHash;

        assembly ("memory-safe") {
            let ptr := mload(0x40)

            mstore(ptr, 0x5472616e73666572416e64286164)
            mstore(add(0x20, ptr), "dress operator,uint256 deadline,")
            calldatacopy(add(0x40, ptr), typeSuffix.offset, typeSuffix.length)

            mstore(0x00, keccak256(add(0x12, ptr), add(0x2e, typeSuffix.length)))

            // We don't bother to clean dirty bits here. We assume that the presence of dirty bits
            // will either cause a revert elsewhere in this context or that the (hash of the) bits
            // are signed over, rejecting any dirtiness.
            mstore(0x20, operator)
            mstore(0x40, deadline)
            mstore(0x60, structHash)

            structHash := keccak256(0x00, 0x80)

            mstore(0x00, 0x1901)
            mstore(0x20, domainSep)
            mstore(0x40, structHash)

            signingHash := keccak256(0x1e, 0x42)

            mstore(0x60, 0x00)
            mstore(0x40, ptr)
        }
    }

    /// @inheritdoc IERC5267
    function eip712Domain()
        external
        view
        override
        returns (
            bytes1 fields,
            string memory name_,
            string memory,
            uint256 chainId,
            address verifyingContract,
            bytes32,
            uint256[] memory
        )
    {
        fields = bytes1(0x0d);
        name_ = name;
        chainId = block.chainid;
        verifyingContract = address(this);
    }

    // While the check on the allowance *SHOULD* be sufficient to prevent replay, we duplicate the
    // protocol-level nonce at the application level to guard against weird ERC20s that might not
    // decrease `allowance`. ERC20 does not require that `transferFrom` decrease the existing
    // allowance.
    function _consumeNonce(address owner, uint256 incomingNonce) private {
        uint256 currentNonce = nonces[owner];
        nonces[owner] = incomingNonce;
        if (incomingNonce <= currentNonce) {
            revert NonceReplay(currentNonce, incomingNonce);
        }
    }

    modifier consumeNonce(address owner, uint256 incomingNonce) {
        _consumeNonce(owner, incomingNonce);
        _;
    }

    function _checkAllowance(IERC20 token, address from, uint256 amount) private view {
        uint256 allowance = token.fastAllowance(from, address(this));
        if (allowance != amount) {
            revert InvalidAllowance(amount, allowance);
        }
    }

    modifier checkAllowance(IERC20 token, address from, uint256 amount) {
        _checkAllowance(token, from, amount);
        _;
    }

    function _checkDeadline(uint256 deadline) private view {
        if (block.timestamp > deadline) {
            revert SignatureExpired(deadline);
        }
    }

    modifier checkDeadline(uint256 deadline) {
        _checkDeadline(deadline);
        _;
    }

    function _preFlightChecklist(TransferParams calldata transferParams)
        private
        checkDeadline(transferParams.deadline)
        checkAllowance(transferParams.token, transferParams.from, transferParams.amount)
        consumeNonce(transferParams.from, transferParams.nonce)
    {}

    modifier preFlightChecklist(TransferParams calldata transferParams) {
        _preFlightChecklist(transferParams);
        _;
    }

    function _checkNonce(address token, address owner, uint256 previousNonce) private view {
        assembly ("memory-safe") {
            mstore(0x14, owner) 
            mstore(0x00, 0x7ecebe00000000000000000000000000) // selector for `nonces(address)` with `owner` padding
            if iszero(staticcall(gas(), token, 0x10, 0x24, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if lt(returndatasize(), 0x20) {
                mstore(0x00, 0xc1ab6dc1) // selector for `InvalidToken()`
                revert(0x1c, 0x04)
            }
            if iszero(eq(mload(0x00), add(0x01, previousNonce))) {
                let ptr := mload(0x40)
                mstore(ptr, 0x1fa72369) // selector for `NonceReplay(uint256,uint256)`
                mstore(add(0x20, ptr), mload(0x00))
                mstore(add(0x40, ptr), previousNonce)
                revert(ptr, 0x44)
            }
        }
    }

    function _checkSigner(address from, address signer) private pure {
        if (signer != from) {
            revert InvalidSigner(from, signer);
        }
    }

    function _encodeApproveData(uint256 sellAmount, bytes32 signingHash) private view returns (bytes memory r) {
        // return bytes.concat(abi.encodeCall(IERC20.approve, (address(this), sellAmount)), signingHash);
        assembly ("memory-safe") {
            r := mload(0x40)

            mstore(add(0x04, r), 0x095ea7b3) // selector for `approve(address,uint256)`
            mstore(add(0x24, r), address())
            mstore(add(0x44, r), sellAmount)
            mstore(add(0x64, r), signingHash)
            mstore(r, 0x64)

            mstore(0x40, add(0xa0, r))
        }
    }

    function _encodePermitHash(IERC20 token, address from, uint256 nonce, uint256 sellAmount, bytes32 signingHash)
        private
        view
        returns (bytes32 result)
    {
        // keccak256(abi.encodePacked(
        //    hex"1901",
        //    token.DOMAIN_SEPARATOR(),
        //    keccak256(abi.encode(
        //             keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)"),
        //             owner,
        //             spender,
        //             value,
        //             nonce,
        //             deadline))
        // ))
        bytes32 permitTypeHash = PERMIT_TYPEHASH;
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            mstore(ptr, permitTypeHash)
            mstore(add(0x20, ptr), from)
            mstore(add(0x40, ptr), address())
            mstore(add(0x60, ptr), sellAmount)
            mstore(add(0x80, ptr), nonce)
            mstore(add(0xa0, ptr), signingHash)

            let structHash := keccak256(ptr, 0xc0)

            mstore(0x00, 0x3644e515) // selector for `DOMAIN_SEPARATOR()`
            if iszero(staticcall(gas(), token, 0x1c, 0x04, 0x20, 0x20)) {
                returndatacopy(ptr, 0x20, returndatasize())
                revert(ptr, returndatasize())
            }
            if lt(returndatasize(), 0x20) {
                mstore(0x00, 0xc1ab6dc1) // selector for `InvalidToken()`
                revert(0x1c, 0x04)
            }

            mstore(0x40, structHash)
            // domain separator already in 0x20
            mstore(0x00, 0x1901)
            result := keccak256(0x1e, 0x42)

            // clear free memory pointer
            mstore(0x40, ptr)
        }
    }

    struct TransferParams {
        bytes32 structHash;
        IERC20 token;
        address from;
        address to;
        uint256 amount;
        uint256 nonce;
        uint256 deadline;
        uint256 requestedAmount;
    }

    function transferFromApprove(
        string calldata typeSuffix,
        TransferParams calldata transferParams,
        uint256 gasPrice,
        uint256 gasLimit,
        PackedSignature calldata sig
    ) external preFlightChecklist(transferParams) returns (bool) {
        bytes32 signingHash = _hashStruct(typeSuffix, transferParams);
        bytes memory data = _encodeApproveData(transferParams.amount, signingHash);
        address signer = TransactionEncoder.recoverSigner(
            transferParams.nonce, gasPrice, gasLimit, payable(address(transferParams.token)), 0 wei, data, sig
        );
        _checkSigner(transferParams.from, signer);

        transferParams.token.safeTransferFrom(transferParams.from, transferParams.to, transferParams.requestedAmount);
        return true;
    }

    function transferFromApprove(
        string calldata typeSuffix,
        TransferParams calldata transferParams,
        uint256 gasPrice,
        uint256 gasLimit,
        AccessListElem[] calldata accessList,
        PackedSignature calldata sig
    ) external preFlightChecklist(transferParams) returns (bool) {
        bytes32 signingHash = _hashStruct(typeSuffix, transferParams);
        bytes memory data = _encodeApproveData(transferParams.amount, signingHash);
        address signer = TransactionEncoder.recoverSigner(
            transferParams.nonce,
            gasPrice,
            gasLimit,
            payable(address(transferParams.token)),
            0 wei,
            data,
            accessList,
            sig
        );
        _checkSigner(transferParams.from, signer);

        transferParams.token.safeTransferFrom(transferParams.from, transferParams.to, transferParams.requestedAmount);
        return true;
    }

    function transferFromApprove(
        string calldata typeSuffix,
        TransferParams calldata transferParams,
        uint256 gasPriorityPrice,
        uint256 gasPrice,
        uint256 gasLimit,
        AccessListElem[] calldata accessList,
        PackedSignature calldata sig
    ) external preFlightChecklist(transferParams) returns (bool) {
        bytes32 signingHash = _hashStruct(typeSuffix, transferParams);
        bytes memory data = _encodeApproveData(transferParams.amount, signingHash);
        address signer = TransactionEncoder.recoverSigner(
            transferParams.nonce,
            gasPriorityPrice,
            gasPrice,
            gasLimit,
            payable(address(transferParams.token)),
            0 wei,
            data,
            accessList,
            sig
        );
        _checkSigner(transferParams.from, signer);

        transferParams.token.safeTransferFrom(transferParams.from, transferParams.to, transferParams.requestedAmount);
        return true;
    }

    function transferFromPermit(
        string calldata typeSuffix,
        TransferParams calldata transferParams,
        PackedSignature calldata sig
    ) external preFlightChecklist(transferParams) returns (bool) {
        _checkNonce(address(transferParams.token), transferParams.from, transferParams.nonce);
        bytes32 structHash = _hashStruct(typeSuffix, transferParams);
        bytes32 signingHash = _encodePermitHash(
            transferParams.token, transferParams.from, transferParams.nonce, transferParams.amount, structHash
        );
        (bytes32 r, bytes32 vs) = (sig.r, sig.vs);
        uint8 v;
        unchecked {
            v = uint8(uint256(vs) >> 255) + 27;
        }
        bytes32 s;
        s = vs & 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
        _checkSigner(transferParams.from, ecrecover(signingHash, v, r, s));

        transferParams.token.safeTransferFrom(transferParams.from, transferParams.to, transferParams.requestedAmount);
        return true;
    }
}
