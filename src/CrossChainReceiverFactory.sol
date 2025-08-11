// SPDX-License-Identifier: MIT
pragma solidity =0.8.28;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC165} from "@forge-std/interfaces/IERC165.sol";
import {IERC1271} from "./interfaces/IERC1271.sol";
import {IERC5267} from "./interfaces/IERC5267.sol";
import {IOwnable} from "./interfaces/IOwnable.sol";

import {ICrossChainReceiverFactory} from "./interfaces/ICrossChainReceiverFactory.sol";
import {AbstractOwnable, TwoStepOwnable} from "./utils/TwoStepOwnable.sol";
import {MultiCallContext, MULTICALL_ADDRESS} from "./multicall/MultiCallContext.sol";

import {FastLogic} from "./utils/FastLogic.sol";
import {Ternary} from "./utils/Ternary.sol";

interface IWrappedNative is IERC20 {
    function deposit() external payable;
    function withdraw(uint256) external;

    event Deposit(address indexed, uint256);
    event Withdrawal(address indexed, uint256);

    receive() external payable;
}

contract CrossChainReceiverFactory is ICrossChainReceiverFactory, MultiCallContext, TwoStepOwnable {
    using FastLogic for bool;
    using Ternary for bool;

    CrossChainReceiverFactory private immutable _cachedThis = this;
    uint168 private immutable _factoryWithFF =
        0xff0000000000000000000000000000000000000000 | uint168(uint160(address(this)));
    bytes32 private immutable _proxyInitHash = keccak256(
        bytes.concat(
            hex"60253d8160093d39f33d3d3d3d363d3d37363d6c",
            bytes13(uint104(uint160(address(this)))),
            hex"5af43d3d93803e602357fd5bf3"
        )
    );
    string public constant override name = "ZeroExCrossChainReceiver";
    bytes32 private constant _NAMEHASH = 0x819c7f86c24229cd5fed5a41696eb0cd8b3f84cc632df73cfd985e8b100980e8;
    IERC20 private constant _NATIVE = IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);
    address private constant _TOEHOLD = 0x4e59b44847b379578588920cA78FbF26c0B4956C;
    address private constant _WNATIVE_SETTER = 0x000000000000F01B1D1c8EEF6c6cF71a0b658Fbc;
    bytes32 private constant _WNATIVE_STORAGE_INITHASH = keccak256(
        abi.encodePacked(
            hex"326d",
            uint112(uint160(_WNATIVE_SETTER)),
            hex"1815601657fe5b7f60143603803560601c6d",
            uint112(uint160(_WNATIVE_SETTER)),
            hex"14336c",
            uint40(uint104(uint160(MULTICALL_ADDRESS)) >> 64),
            hex"3d527f",
            uint64(uint104(uint160(MULTICALL_ADDRESS))),
            hex"1416602e57fe5b3d54604b57583d55803d3d373d34f03d8159526d6045573dfd5b5260203df35b30ff60901b5952604e3df3"
        )
    );
    bytes32 private constant _WNATIVE_STORAGE_SALT = keccak256("Wrapped Native Token Address");
    address private constant _WNATIVE_STORAGE = address(
        uint160(
            uint256(
                keccak256(
                    abi.encodePacked(
                        hex"d694",
                        address(
                            uint160(
                                uint256(
                                    keccak256(
                                        abi.encodePacked(
                                            hex"ff", _TOEHOLD, _WNATIVE_STORAGE_SALT, _WNATIVE_STORAGE_INITHASH
                                        )
                                    )
                                )
                            )
                        ),
                        hex"01"
                    )
                )
            )
        )
    );
    IWrappedNative private immutable _WNATIVE =
        IWrappedNative(payable(address(uint160(uint256(bytes32(_WNATIVE_STORAGE.code))))));

    error DeploymentFailed();
    error ApproveFailed();

    constructor() payable {
        // This bit of bizarre functionality is required to accommodate Foundry's `deployCodeTo`
        // cheat code. It is a no-op at deploy time.
        if ((block.chainid == 31337).and(msg.sender == address(_WNATIVE)).and(msg.value > 1 wei)) {
            assembly ("memory-safe") {
                stop()
            }
        }

        require(((msg.sender == _TOEHOLD).and(uint160(address(this)) >> 104 == 0)).or(block.chainid == 31337));
        require(uint160(_WNATIVE_SETTER) >> 112 == 0);
        require(_NAMEHASH == keccak256(bytes(name)));

        // do some behavioral checks on `_WNATIVE`
        {
            // we need some value in order to perform the behavioral checks
            require(address(this).balance > 1 wei);

            // check that `_WNATIVE` is ERC20-ish
            uint256 wrappedBalance = _WNATIVE.balanceOf(address(this));

            // check that `_WNATIVE` has a `deposit()` function
            _WNATIVE.deposit{value: address(this).balance >> 1}();
            require(wrappedBalance < (wrappedBalance = _WNATIVE.balanceOf(address(this))));

            // check that `_WNATIVE` has a `fallback` function that deposits
            (bool success, bytes memory returndata) = payable(_WNATIVE).call{value: address(this).balance}("");
            require(success);
            require(returndata.length == 0);
            require(wrappedBalance < (wrappedBalance = _WNATIVE.balanceOf(address(this))));

            // check that `_WNATIVE` has a `withdraw(uint256)` function
            _WNATIVE.withdraw(wrappedBalance);
            require(address(this).balance == wrappedBalance);
            require(_WNATIVE.balanceOf(address(this)) == 0);

            // send value back to the origin
            (success,) = payable(tx.origin).call{value: address(this).balance}("");
            require(success);
        }
    }

    function _requireProxy() private view {
        require(this != _cachedThis);
    }

    modifier onlyProxy() {
        _requireProxy();
        _;
    }

    modifier noDelegateCall() {
        require(this == _cachedThis);
        _;
    }

    modifier onlyFactory() {
        require(msg.sender == address(_cachedThis));
        _;
    }

    /// @inheritdoc IERC165
    function supportsInterface(bytes4 interfaceId)
        public
        view
        override(IERC165, AbstractOwnable)
        onlyProxy
        returns (bool)
    {
        return super.supportsInterface(interfaceId);
    }

    // This function is overridden so that it is explicit that it is only meaningful on the
    // proxy. This also makes any function that is `onlyOwner` implicitly `onlyProxy`, including
    // `renounceOwnership` and `transferOwnership`.
    function owner() public view override(IOwnable, AbstractOwnable) onlyProxy returns (address) {
        return super.owner();
    }

    // Like `owner()`, function is overridden so that it is explicit that it is only meaningful on
    // the proxy. This also makes `acceptOwnership` and `rejectOwnership` implicitly `onlyProxy`.
    function pendingOwner() public view override onlyProxy returns (address) {
        return super.pendingOwner();
    }

    /// @inheritdoc IERC1271
    function isValidSignature(bytes32 hash, bytes calldata signature)
        external
        view
        override
        onlyProxy
        returns (bytes4)
    {
        // There are two types of signatures accepted:
        // 1. Merkle proof
        //    The encoded signature is formed by ABIEncoding `(address owner, bytes32[] proof)`.
        //    `keccak256(abi.encode(hash, block.chainid))` must be a leaf in the Merkle tree whose
        //    root formed the salt that deployed `address(this)`. The `owner` that is encoded must
        //    be the one that was used at deploy time, independent of any subsequent changes to
        //    `owner()`.
        // 2. ERC7739 defensively-rehashed nested typed data
        //    The signature must be constructed exactly as described by the ERC.
        //
        // Because the ERC7739 encoding of the nested signature begins with the ECDSA `r`, it is
        // computationally impractical (96-bit security level) to create a signature that can be
        // validly decoded both as an ERC7739 signature and as a Merkle proof signature (beginning
        // with a correctly padded address). This would require either computing `k` from a chosen
        // `r` for the ECDSA signature (violates the discrete logarithm) or controlling the upper 96
        // bits of `r` by choosing `k` (violates decisional Diffie-Hellman).

        // ERC7739 requires a specific response to `hash == 0x7739...7739 && signature == ""`. We
        // must return `bytes4(0x77390001)` in that case. This is the requirement of the current
        // revision of ERC7739; future ERC7739 versions may increment the return value.
        if (signature.length >> 6 == 0) {
            unchecked {
                // Forces the compiler to optimize for smaller bytecode size.
                return (signature.length == uint256(0)).and(uint256(hash) == ~signature.length / 0xffff * 0x7739)
                    .ternary(bytes4(0x77390001), bytes4(0xffffffff));
            }
        }

        // Merkle proof validation
        {
            address originalOwner;
            bool validOwner;
            assembly ("memory-safe") {
                // This assembly block decodes the `owner` of the ABIEncoded `(address owner,
                // bytes32[] proof)`, but without reverting if the padding bytes of `owner` are not
                // cleared. We also return a flag variable `validOwner` that indicates whether those
                // bytes are in fact clear.
                //     owner = abi.decode(signature, (address));
                originalOwner := calldataload(signature.offset)
                validOwner := iszero(shr(0xa0, originalOwner))
            }

            if (validOwner) {
                assembly ("memory-safe") {
                    // This assembly block is equivalent to:
                    //     hash = keccak256(abi.encode(hash, block.chainid));
                    // except that it's cheaper and doesn't allocate memory. We make the assumption
                    // here that `block.chainid` cannot alias a valid tree node or signing
                    // hash. Realistically, `block.chainid` cannot exceed 2**53 - 1 or it would
                    // cause significant issues elsewhere in the ecosystem. This also means that the
                    // sort order of the hash and the chainid is backwards from what
                    // `_getMerkleRoot` produces, again protecting us against extension attacks.
                    mstore(returndatasize(), hash)
                    mstore(0x20, chainid())
                    hash := keccak256(returndatasize(), 0x40)
                }

                bytes32[] calldata proof;
                assembly ("memory-safe") {
                    // This assembly block simply ABIDecodes `proof` as the second element of the
                    // encoded anonymous struct `(owner, proof)`. It omits range and overflow
                    // checking.
                    //     (, proof) = abi.decode(signature, (address, bytes32[]));
                    proof.offset := add(signature.offset, calldataload(add(0x20, signature.offset)))
                    proof.length := calldataload(proof.offset)
                    proof.offset := add(0x20, proof.offset)
                }

                return _verifyDeploymentRootHash(_getMerkleRoot(proof, hash), originalOwner).ternary(
                    IERC1271.isValidSignature.selector, bytes4(0xffffffff)
                );
            }
        }

        // ERC7739 validation
        return _verifyERC7739NestedTypedSignature(hash, signature, super.owner()).ternary(
            IERC1271.isValidSignature.selector, bytes4(0xffffffff)
        );
    }

    /// @inheritdoc IERC5267
    function eip712Domain()
        external
        view
        override
        onlyProxy
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

    /// @inheritdoc ICrossChainReceiverFactory
    function deploy(bytes32 root, bool setOwnerNotCleanup, address initialOwner)
        external
        override
        noDelegateCall
        returns (ICrossChainReceiverFactory proxy)
    {
        assembly ("memory-safe") {
            // derive the deployment salt from the owner
            mstore(0x14, initialOwner)
            mstore(returndatasize(), root)
            let salt := keccak256(returndatasize(), 0x34)

            // create a minimal proxy targeting this contract
            mstore(0x1a, 0x5af43d3d93803e602357fd5bf3)
            mstore(0x0d, address())
            mstore(returndatasize(), 0x60253d8160093d39f33d3d3d3d363d3d37363d6c)
            proxy := create2(returndatasize(), 0x0c, 0x2e, salt)
            if iszero(proxy) {
                mstore(returndatasize(), 0x30116425) // selector for `DeploymentFailed()`.
                revert(0x1c, 0x04)
            }

            // If `setOwnerNotCleanup == true`, this gets the selector for `setOwner(address)`,
            // otherwise you get the selector for `cleanup(address)`. In both cases, the selector is
            // appended with `argument`'s padding.
            let selector :=
                xor(0xfbacefce000000000000000000000000, mul(0xe803affb000000000000000000000000, setOwnerNotCleanup))
            // If `setOwnerNotCleanup == true`, this gets `initialOwner`, otherwise you get `proxy`.
            let argument := xor(proxy, mul(xor(proxy, initialOwner), setOwnerNotCleanup))

            // set the owner, or `selfdestruct`
            mstore(0x14, argument)
            mstore(returndatasize(), selector)
            if iszero(call(gas(), proxy, callvalue(), 0x10, 0x24, codesize(), returndatasize())) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
        }
    }

    /// @inheritdoc ICrossChainReceiverFactory
    function setOwner(address owner) external override onlyFactory {
        _setOwner(owner);
    }

    /// @inheritdoc ICrossChainReceiverFactory
    function approvePermit2(IERC20 token, uint256 amount) external override onlyProxy returns (bool) {
        if (token == _NATIVE) {
            token = _WNATIVE;
            assembly ("memory-safe") {
                if iszero(call(gas(), token, amount, codesize(), returndatasize(), codesize(), returndatasize())) {
                    let ptr := mload(0x40)
                    returndatacopy(ptr, 0x00, returndatasize())
                    revert(ptr, returndatasize())
                }
            }
        }
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            mstore(returndatasize(), 0x095ea7b3) // selector for `approve(address,uint256)`
            mstore(0x20, 0x000000000022D473030F116dDEE9F6B43aC78BA3) // Permit2
            mstore(0x40, amount)

            if iszero(call(gas(), token, callvalue(), 0x1c, 0x44, returndatasize(), 0x20)) {
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            // allow `approve` to either return `true` or empty to signal success
            if iszero(or(and(eq(mload(0x00), 0x01), lt(0x1f, returndatasize())), iszero(returndatasize()))) {
                mstore(0x00, 0x3e3f8f73) // selector for `ApproveFailed()`
                revert(0x1c, 0x04)
            }

            mstore(0x00, 0x01)
            return(0x00, 0x20)
        }
    }

    /// @inheritdoc ICrossChainReceiverFactory
    function call(address payable target, uint256 value, bytes calldata data)
        external
        override
        onlyOwner
        returns (bytes memory)
    {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            calldatacopy(ptr, data.offset, data.length)
            let success := call(gas(), target, value, ptr, data.length, codesize(), returndatasize())

            returndatacopy(add(0x40, ptr), 0x00, returndatasize())

            if iszero(success) { revert(add(0x40, ptr), returndatasize()) }

            mstore(add(0x20, ptr), returndatasize())
            mstore(ptr, 0x20)
            return(ptr, add(0x40, returndatasize()))
        }
    }

    /// @inheritdoc ICrossChainReceiverFactory
    function cleanup(address payable beneficiary) external override {
        if (msg.sender == address(_cachedThis)) {
            if (address(this).balance != 0) {
                IWrappedNative wnative = _WNATIVE;
                assembly ("memory-safe") {
                    if iszero(
                        call(gas(), wnative, selfbalance(), codesize(), returndatasize(), codesize(), returndatasize())
                    ) {
                        let ptr := mload(0x40)
                        returndatacopy(ptr, 0x00, returndatasize())
                        revert(ptr, returndatasize())
                    }
                }
            }
        } else {
            if (_msgSender() != owner()) {
                _permissionDenied();
            }
        }
        selfdestruct(beneficiary);
    }

    /// Modified from Solady (https://github.com/Vectorized/solady/blob/b609a9c79ce541c2beca7a7d247665e7c93942a3/src/utils/MerkleProofLib.sol)
    /// Modified from Solmate (https://github.com/transmissions11/solmate/blob/main/src/utils/MerkleProofLib.sol)
    function _getMerkleRoot(bytes32[] calldata proof, bytes32 leaf) private pure returns (bytes32 root) {
        assembly ("memory-safe") {
            if proof.length {
                // Left shifting by 5 is like multiplying by 32.
                let end := add(proof.offset, shl(0x05, proof.length))

                // Initialize offset to the offset of the proof in calldata.
                let offset := proof.offset

                // Iterate over proof elements to compute root hash.
                for {} true {} {
                    // Slot where the leaf should be put in scratch space. If
                    // leaf > calldataload(offset): slot 32, otherwise: slot 0.
                    let leafSlot := shl(0x05, lt(calldataload(offset), leaf))

                    // Store elements to hash contiguously in scratch space.
                    // The xor puts calldataload(offset) in whichever slot leaf
                    // is not occupying, so 0 if leafSlot is 32, and 32 otherwise.
                    mstore(leafSlot, leaf)
                    mstore(xor(0x20, leafSlot), calldataload(offset))

                    // Reuse leaf to store the hash to reduce stack operations.
                    leaf := keccak256(returndatasize(), 0x40) // Hash both slots of scratch space.

                    offset := add(0x20, offset) // Shift 1 word per cycle.

                    if iszero(lt(offset, end)) { break }
                }
            }
            root := leaf
        }
    }

    function _verifyDeploymentRootHash(bytes32 root, address originalOwner) internal view returns (bool result) {
        bytes32 initHash = _proxyInitHash;
        uint168 factoryWithFF = _factoryWithFF;
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            // derive creation salt
            mstore(0x14, originalOwner)
            mstore(returndatasize(), root)
            let salt := keccak256(returndatasize(), 0x34)

            // 0xff + factory + salt + hash(initCode)
            mstore(0x40, initHash)
            mstore(0x20, salt)
            mstore(returndatasize(), factoryWithFF)
            let computedAddress := keccak256(0x0b, 0x55)

            // restore clobbered memory
            mstore(0x40, ptr)

            // verify that `salt` was used to deploy `address(this)`
            result := eq(address(), and(0xffffffffffffffffffffffffffffffffffffffff, computedAddress))
        }
    }

    /// Modified from Solady (https://github.com/Vectorized/solady/blob/c4d32c3e6e89da0321fda127ff024eecd5b57bc6/src/accounts/ERC1271.sol#L120-L287) under the MIT license
    function _verifyERC7739NestedTypedSignature(bytes32 hash, bytes calldata signature, address owner_)
        internal
        view
        returns (bool result)
    {
        assembly ("memory-safe") {
            let ptr := mload(0x40) // Grab the free memory pointer.

            // Skip 2 words for the `typedDataSignTypehash` and `contents` struct hash.
            mstore(add(0x40, ptr), _NAMEHASH)
            mstore(add(0x60, ptr), chainid())
            mstore(add(0x80, ptr), address())

            // `c` is `contentsDescription.length`, which is stored in the last 2 bytes of the signature.
            let c := shr(0xf0, calldataload(add(signature.offset, sub(signature.length, 0x02))))
            let l := add(0x42, c) // Total length of appended data (32 + 32 + c + 2).
            let o := add(signature.offset, sub(signature.length, l)) // Offset of appended data.
            mstore(returndatasize(), 0x1901) // Store the "\x19\x01" prefix.
            calldatacopy(0x20, o, 0x40) // Copy the `APP_DOMAIN_SEPARATOR` and `contents` struct hash.
            for {} true {} {
                // Dismiss the signature as invalid if:
                // 1. the reconstructed hash doesn't match,
                // 2. the appended data is invalid, i.e.
                //    (`appendedData.length > signature.length || contentsDescription.length == 0`.)
                // 3. the ECDSA signature is not 64 bytes long
                if or(xor(keccak256(0x1e, 0x42), hash), or(xor(add(0x40, l), signature.length), iszero(c))) { break }

                // Now that it's apparent that the signature is well-formed relative to `hash`, the
                // `content` hash, and the application domain separator, we check that
                // `ContentsType` is syntactically well-formed while simultaneously preparing to
                // defensively rehash it into the nested `TypedDataSign` type.

                // Generate the EIP712 serialization `encodeType(TypedDataSign)` of the specific
                // instance of the `TypedDataSign` struct for this signature.
                // `TypedDataSign({ContentsName} contents,string name,...){ContentsType}`.
                let m := add(0xa0, ptr)
                mstore(m, "TypedDataSign(") // Store the start of `TypedDataSign`'s type encoding.
                let p := add(0x0e, m) // Advance 14 bytes to skip "TypedDataSign(".
                calldatacopy(p, add(0x40, o), c) // Copy `contentsName`, optimistically.
                mstore(add(p, c), 0x28) // Store a '(' *AFTER* the end (not *AT* the end).
                if iszero(eq(byte(returndatasize(), mload(sub(add(p, c), 0x01))), 0x29)) {
                    let e := returndatasize() // Length of `contentsName` in explicit mode.
                    for { let q := sub(add(p, c), 0x01) } 1 {} {
                        e := add(e, 0x01) // Scan backwards until we encounter a ')'.
                        if iszero(gt(lt(e, c), eq(byte(returndatasize(), mload(sub(q, e))), 0x29))) { break }
                    }
                    c := sub(c, e) // Truncate `contentsDescription` to `contentsType`.
                    calldatacopy(p, add(add(0x40, o), c), e) // Copy `contentsName`.
                    mstore8(add(p, e), 0x28) // Store a '(' exactly right *AT* the end.
                }

                // Check that `contentsName` is a well-formed EIP712 type name. `d & 1 == 1` means
                // that `contentsName` is invalid.
                let d := shr(byte(returndatasize(), mload(p)), 0x7fffffe000000000000010000000000) // Starts with `[a-z(]`.
                // Advance `p` until we encounter '('.
                for {} xor(0x28, shr(0xf8, mload(p))) { p := add(0x01, p) } {
                    d := or(shr(byte(returndatasize(), mload(p)), 0x120100000001), d) // Has a byte in ", )\x00".
                }

                // Finish out the shallow `encodeType(TypedDataSign)` with the fields from *OUR*
                // domain separator.
                mstore(p, " contents,string name,uint256 ch") // Store the rest of the encoding.
                mstore(add(0x20, p), "ainId,address verifyingContract)")
                p := add(0x40, p)
                // Complete the full, recursive serialization with the referenced type
                // `contentsType`.
                calldatacopy(p, add(0x40, o), c) // Copy `encodeType(contentsType)`.

                // The EIP712 `encodeType(TypedDataSign)` is now in memory, starting at `p`. Next,
                // we hash it along with `hashStruct(contentsType, contents)` (which is just the
                // fourth word of `signature`) to form `hashStruct(TypedDataSign, ...)`. Then we
                // combine it with the application domain separator (not our own domain separator)
                // to form the defensively-rehashed signing hash (the one that `owner_` actually
                // signed).

                // Fill in the missing fields of the `TypedDataSign`.
                calldatacopy(ptr, o, 0x40) // Copy the `contents` struct hash to `add(ptr, 0x20)`.
                mstore(ptr, keccak256(m, sub(add(p, c), m))) // Store `typeHash(TypedDataSign)`.
                // The "\x19\x01" prefix is already at 0x00.
                // `APP_DOMAIN_SEPARATOR` is already at 0x20.
                mstore(0x40, keccak256(ptr, 0xa0)) // `hashStruct(TypedDataSign, ...)`.
                // Compute the final hash. The hash will be corrupted if `contentsName` is invalid
                // from the above check (`d & 1 == 1`).
                hash := keccak256(0x1e, add(0x42, and(0x01, d)))

                // Verify the ECDSA signature by `owner_` over `hash`.
                let vs := calldataload(add(0x20, signature.offset))
                mstore(returndatasize(), hash)
                mstore(0x20, add(0x1b, shr(0xff, vs))) // `v`.
                mstore(0x40, calldataload(signature.offset)) // `r`.
                mstore(0x60, and(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, vs)) // `s`.
                let recovered := mload(staticcall(gas(), 0x01, returndatasize(), 0x80, 0x01, 0x20))
                result := gt(returndatasize(), shl(0x60, xor(owner_, recovered)))

                // Restore clobbered memory
                mstore(0x60, 0x00)
                break
            }
            // Restore clobbered memory
            mstore(0x40, ptr)
        }
    }

    receive() external payable override onlyProxy {
        if (msg.sender != address(_WNATIVE)) {
            IWrappedNative wnative = _WNATIVE;
            assembly ("memory-safe") {
                if iszero(call(gas(), wnative, callvalue(), codesize(), returndatasize(), codesize(), returndatasize()))
                {
                    let ptr := mload(0x40)
                    returndatacopy(ptr, 0x00, returndatasize())
                    revert(ptr, returndatasize())
                }
            }
        }
    }
}
