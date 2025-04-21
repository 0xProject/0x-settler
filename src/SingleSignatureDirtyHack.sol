// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC5267} from "./interfaces/IERC5267.sol";

import {AbstractContext} from "./Context.sol";

import {AccessListElem, TransactionEncoder} from "./utils/TransactionEncoder.sol";
import {SafeTransferLib} from "./vendor/SafeTransferLib.sol";

abstract contract SingleSignatureDirtyHack is IERC5267, AbstractContext {
    using SafeTransferLib for IERC20;

    mapping (address => uint256) public nonces;

    error InvalidSigner(address expected, address actual);
    error NonceReplay(uint256 oldNonce, uint256 newNonce);
    error InvalidAllowance(uint256 expected, uint256 actual);
    error SignatureExpired(uint256 expiry);

    bytes32 private constant _DOMAIN_TYPEHASH = 0x8cad95687ba82c2ce50e74f7b754645e5117c3a5bec8151c0726d5857980a866;
    bytes32 private constant _NAMEHASH = 0x0000000000000000000000000000000000000000000000000000000000000000;
    string public constant name = ""; // TODO: needs a name
    uint256 private immutable _cachedChainId;
    bytes32 private immutable _cachedDomainSeparator;

    string private constant _TYPE_PREFIX = "TransferAnd(address token,uint256 amount,address op,uint256 exp,";

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

    function _hashStruct(string calldata typeSuffix, IERC20 token, uint256 sellAmount, address operator, uint256 deadline, bytes32 structHash) internal view returns (bytes32 signingHash) {
        bytes32 domainSep = _DOMAIN_SEPARATOR();
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            mstore(ptr, "TransferAnd(address token,uint25")
            mstore(add(0x20, ptr), "6 amount,address op,uint256 exp,")
            calldatacopy(add(0x40, ptr), typeSuffix.offset, typeSuffix.length)

            mstore(ptr, keccak256(ptr, add(0x40, typeSuffix.length)))

            mstore(add(0x20, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, token))
            mstore(add(0x40, ptr), sellAmount)
            mstore(add(0x60, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, operator))
            mstore(add(0x80, ptr), deadline)
            mstore(add(0xa0, ptr), structHash)

            structHash := keccak256(ptr, 0xc0)

            mstore(0x00, 0x1901)
            mstore(0x20, domainSep)
            mstore(0x40, structHash)

            signingHash := keccak256(0x1e, 0x42)

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


    function _consumeNonce(address owner, uint256 newNonce) private {
        uint256 currentNonce = nonces[owner];
        nonces[owner] = newNonce;
        if (newNonce <= currentNonce) {
            revert NonceReplay(currentNonce, newNonce);
        }
    }

    function _checkAllowance(IERC20 token, address from, uint256 amount) private view {
        uint256 allowance = token.fastAllowance(from, address(this));
        if (allowance != amount) {
            revert InvalidAllowance(amount, allowance);
        }
    }

    function _checkDeadline(uint256 deadline) private view {
        if (block.timestamp > deadline) {
            revert SignatureExpired(deadline);
        }
    }

    function _checkSigner(address from, address signer) private pure {
        if (signer != from) {
            revert InvalidSigner(from, signer);
        }
    }

    function _encodeData(uint256 sellAmount, bytes32 signingHash) private view returns (bytes memory) {
        return bytes.concat(abi.encodeCall(IERC20.approve, (address(this), sellAmount)), signingHash);
    }

    function transferFrom155(
        string calldata typeSuffix,
        bytes32 structHash,
        address from,
        address to,
        uint256 nonce,
        uint256 deadline,
        uint256 gasPrice,
        uint256 gasLimit,
        IERC20 sellToken,
        uint256 sellAmount,
        uint256 requestedAmount,
        bytes32 r,
        bytes32 vs
    ) external returns (bool) {
        _checkDeadline(deadline);
        _checkAllowance(sellToken, from, sellAmount);
        _consumeNonce(from, nonce);

        bytes32 signingHash = _hashStruct(typeSuffix, sellToken, sellAmount, _msgSender(), deadline, structHash);

        bytes memory data = _encodeData(sellAmount, signingHash);
        address signer = TransactionEncoder.recoverSigner155(
            nonce, gasPrice, gasLimit, payable(address(sellToken)), 0 wei, data, r, vs
        );
        _checkSigner(from, signer);

        sellToken.safeTransferFrom(from, to, requestedAmount);
        return true;
    }

    function transferFrom2930(
        string calldata typeSuffix,
        bytes32 structHash,
        address from,
        address to,
        uint256 nonce,
        uint256 deadline,
        uint256 gasPrice,
        uint256 gasLimit,
        IERC20 sellToken,
        uint256 sellAmount,
        uint256 requestedAmount,
        AccessListElem[] memory accessList,
        bytes32 r,
        bytes32 vs
    ) external returns (bool) {
        _checkDeadline(deadline);
        _checkAllowance(sellToken, from, sellAmount);
        _consumeNonce(from, nonce);

        bytes32 signingHash = _hashStruct(typeSuffix, sellToken, sellAmount, _msgSender(), deadline, structHash);

        bytes memory data = _encodeData(sellAmount, signingHash);
        address signer = TransactionEncoder.recoverSigner2930(
            nonce, gasPrice, gasLimit, payable(address(sellToken)), 0 wei, data, accessList, r, vs
        );
        _checkSigner(from, signer);

        sellToken.safeTransferFrom(from, to, requestedAmount);
        return true;
    }

    function transferFrom1559(
        string calldata typeSuffix,
        bytes32 structHash,
        address from,
        address to,
        uint256 nonce,
        uint256 deadline,
        uint256 gasPriorityPrice,
        uint256 gasPrice,
        uint256 gasLimit,
        IERC20 sellToken,
        uint256 sellAmount,
        uint256 requestedAmount,
        AccessListElem[] memory accessList,
        bytes32 r,
        bytes32 vs
    ) external returns (bool) {
        _checkDeadline(deadline);
        _checkAllowance(sellToken, from, sellAmount);
        _consumeNonce(from, nonce);

        bytes32 signingHash = _hashStruct(typeSuffix, sellToken, sellAmount, _msgSender(), deadline, structHash);

        bytes memory data = _encodeData(sellAmount, signingHash);
        address signer = TransactionEncoder.recoverSigner1559(
            nonce, gasPriorityPrice, gasPrice, gasLimit, payable(address(sellToken)), 0 wei, data, accessList, r, vs
        );
        _checkSigner(from, signer);

        sellToken.safeTransferFrom(from, to, requestedAmount);
        return true;
    }
}
