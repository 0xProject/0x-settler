// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC5267} from "../interfaces/IERC5267.sol";
import {ISettlerBase} from "../interfaces/ISettlerBase.sol";
import {ISettlerTakerSubmitted} from "../interfaces/ISettlerTakerSubmitted.sol";

import {Context} from "../Context.sol";
import {SettlerSwapper} from "../SettlerSwapper.sol";

import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {FastLogic} from "../utils/FastLogic.sol";
import {LibZip} from "../vendor/LibZip.sol";

contract ZeroExEIP7702Wallet is IERC5267, Context, SettlerSwapper {
    using FastLogic for bool;
    using SafeTransferLib for IERC20;

    address private immutable _cachedThis;
    string public constant name = "ZeroExEIP7702Wallet";
    uint256 private immutable _cachedChainId;
    bytes32 private immutable _cachedDomainSeparator;

    error DeploymentFailed();
    error PermissionDenied();

    modifier onlyWallet() {
        require(address(this).code.length == 23);
        _;
    }

    modifier noDelegateCall() {
        require(address(this) == _cachedThis);
        _;
    }

    constructor() {
        require(_DOMAIN_TYPEHASH == keccak256("EIP712Domain(string name,uint256 chainId,address verifyingContract)"));
        require(_NAMEHASH == keccak256(bytes(name)));
        require(
            _SWAP_TYPEHASH
                == keccak256(
                    "Swap(uint256 nonce,address settler,address sellToken,uint256 sellAmount,address recipient,address buyToken,uint256 minAmountOut,bytes actions,bytes32 zid)"
                )
        );
        uint256 $int;
        Storage storage $ = _$();
        assembly ("memory-safe") {
            $int := $.slot
        }
        require($int == (uint256(_NAMEHASH) - 1) & 0xffffffffffffffffffffff00);

        require(
            (msg.sender == 0x4e59b44847b379578588920cA78FbF26c0B4956C && uint160(address(this)) >> 104 == 0)
                || block.chainid == 31337
        );
        _cachedThis = address(this);
        _cachedChainId = block.chainid;
        _cachedDomainSeparator = _computeDomainSeparator();
    }

    struct Storage {
        uint256 nonce;
    }

    function _$() internal pure returns (Storage storage $) {
        assembly ("memory-safe") {
            $.slot := 0x5e611d3f4dd0e8a5f6bcb900
        }
    }

    function _consumeNonce() internal returns (uint256) {
        return _$().nonce++;
    }

    function nonce() external view onlyWallet returns (uint256) {
        return _$().nonce;
    }

    /// @inheritdoc IERC5267
    function eip712Domain()
        external
        view
        override
        noDelegateCall
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

    function entryPoint(
        address payable wallet,
        ISettlerTakerSubmitted settler,
        IERC20 sellToken,
        uint256 sellAmount,
        ISettlerBase.AllowedSlippage calldata slippage,
        bytes calldata actions,
        bytes32 zid
    ) external noDelegateCall returns (bool) {
        bytes32 salt = _hashSwap(32, 0, _msgData()[4:]);
        assembly ("memory-safe") {
            // create a minimal proxy targeting this contract using the EIP712 signing hash of the
            // swap as the salt
            mstore(0x1d, 0x5af43d5f5f3e6022573d5ffd5b3d5ff3)
            mstore(0x0d, address())
            mstore(0x00, 0x60265f8160095f39f35f5f365f5f37365f6c)
            let proxy := create2(0x00, 0x0e, 0x2f, salt)
            if iszero(proxy) {
                mstore(0x00, 0x30116425) // selector for `DeploymentFailed()`.
                revert(0x1c, 0x04)
            }

            // verify that the newly-created `proxy` is the delegation target of `wallet`
            mstore(0x14, proxy)
            mstore(0x00, 0xef0100)
            if xor(keccak256(0x2d, 0x17), extcodehash(wallet)) {
                mstore(0x00, 0x1e092104) // selector for `PermissionDenied()`
                revert(0x1c, 0x04)
            }
        }
        require(ZeroExEIP7702Wallet(wallet).swap(settler, sellToken, sellAmount, slippage, actions, zid, bytes32(0), bytes32(0)));
        return true;
    }

    bytes32 private constant _DOMAIN_TYPEHASH = 0x8cad95687ba82c2ce50e74f7b754645e5117c3a5bec8151c0726d5857980a866;
    bytes32 private constant _NAMEHASH = 0xd4bb9fe1e9a5e4b7e7fe0f53ca19078208d7d1295e611d3f4dd0e8a5f6bcb94e;

    function _computeDomainSeparator() private view returns (bytes32 r) {
        address cachedThis = _cachedThis;
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(0x00, _DOMAIN_TYPEHASH)
            mstore(0x20, _NAMEHASH)
            mstore(0x40, chainid())
            mstore(0x60, and(0xffffffffffffffffffffffffff, cachedThis))
            r := keccak256(0x00, 0x80)
            mstore(0x40, ptr)
            mstore(0x60, 0x00)
        }
    }

    function _DOMAIN_SEPARATOR() internal view returns (bytes32) {
        return block.chainid == _cachedChainId ? _cachedDomainSeparator : _computeDomainSeparator();
    }

    function DOMAIN_SEPARATOR() external view noDelegateCall returns (bytes32) {
        return _DOMAIN_SEPARATOR();
    }

    bytes32 private constant _SWAP_TYPEHASH = 0x6b8324cf3912163fb49c7cdbdd16dec0d26b9759d5511e5ad304d77824bedc07;

    function _hashSwap(uint256 skipBytes, uint256 nonce_, bytes calldata encodedSwap)
        internal
        view
        returns (bytes32 signingHash)
    {
        bytes32 domainSep = _DOMAIN_SEPARATOR();
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            let actionsOffset := add(calldataload(add(add(0xe0, skipBytes), encodedSwap.offset)), encodedSwap.offset)
            let actionsLength := calldataload(actionsOffset)
            actionsOffset := add(0x20, actionsOffset)

            calldatacopy(ptr, actionsOffset, actionsLength)
            let actionsHash := keccak256(ptr, actionsLength)

            mstore(ptr, _SWAP_TYPEHASH)
            mstore(add(0x20, ptr), nonce_)
            calldatacopy(add(0x40, ptr), add(skipBytes, encodedSwap.offset), 0x100)
            mstore(add(0x100, ptr), actionsHash)
            let structHash := keccak256(ptr, 0x140)
            mstore(0x00, 0x1901)
            mstore(0x20, domainSep)
            mstore(0x40, structHash)

            signingHash := keccak256(0x1e, 0x42)

            mstore(0x40, ptr)
        }
    }

    function _verifySelfSignature(bytes32 signingHash, bytes32 r, bytes32 vs) internal view {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            mstore(0x00, signingHash)
            mstore(0x20, add(0x1b, shr(0xff, vs)))
            mstore(0x40, r)
            mstore(0x60, and(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, vs))
            pop(staticcall(gas(), 0x01, 0x00, 0x80, 0x00, 0x20))

            mstore(0x40, ptr)
            mstore(0x60, 0x00)

            if xor(address(), mul(mload(0x00), eq(returndatasize(), 0x20))) {
                mstore(0x00, 0x1e092104) // selector for `PermissionDenied()`
                revert(0x1c, 0x04)
            }
        }
    }

    function swap(
        ISettlerTakerSubmitted settler,
        IERC20 sellToken,
        uint256 sellAmount,
        ISettlerBase.AllowedSlippage calldata slippage,
        bytes calldata actions,
        bytes32 zid,
        bytes32 r,
        bytes32 vs
    ) external /* implicitly onlyWallet */ returns (bool) {
        uint256 nonce_ = _consumeNonce();
        if ((nonce_ != 0).or(_msgSender() != _cachedThis)) {
            _verifySelfSignature(_hashSwap(0, nonce_, _msgData()[4:]), r, vs);
        }

        requireValidSettler(settler);

        if (~sellAmount == 0) {
            _swapAll(settler, sellToken, slippage, actions, zid);
        } else {
            _swap(settler, sellToken, sellAmount, slippage, actions, zid);
        }
        return true;
    }

    function approvePermit2(IERC20 token) external onlyWallet returns (bool) {
        token.safeApprove(0x000000000022D473030F116dDEE9F6B43aC78BA3, type(uint256).max);
        return true;
    }

    fallback() external payable {
        LibZip.cdFallback();
    }

    receive() external payable onlyWallet {}
}
